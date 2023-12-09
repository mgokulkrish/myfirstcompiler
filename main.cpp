#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <vector>

#include "KaleidoscopeJIT.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/StandardInstrumentations.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Scalar/Reassociate.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"

enum Token {
    tok_eof = -1,
    tok_extern = -2,
    tok_def = -3,

    tok_identifier = -4,
    tok_number = -5,
};

using namespace llvm;
using namespace llvm::orc;

static std::string IdentifierStr;
static double NumVal;

static int gettok(){
    static int LastChar = ' ';
    while(isspace(LastChar))
        LastChar = getchar();
    
    if(isalpha(LastChar)){
        IdentifierStr = LastChar;
        while(isalnum((LastChar = getchar())))
            IdentifierStr += LastChar;

        if(IdentifierStr == "def"){
            return tok_def;
        }

        if(IdentifierStr == "extern"){
            return tok_extern;
        }

        return tok_identifier;
    }

    // cannot handle error incase of multiple decimal points
    if(isdigit(LastChar) || LastChar == '.'){
        std::string NumStr;
        do{
            NumStr += LastChar;
            LastChar = getchar();
        }while(isdigit(LastChar) || LastChar == '.');

        NumVal = strtod(NumStr.c_str(), 0);
        return tok_number;
    }

    if(LastChar == '#'){
        do{
            LastChar = getchar();   
        } while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');
        
        if(LastChar != EOF){
            return gettok();
        }
    }

    if(LastChar == EOF){
        return tok_eof;
    }

    int ThisChar = LastChar;

    //have to check why are are eating the next character.
    LastChar = getchar();
    return ThisChar;
}


class ExprAST {
    public:
        virtual ~ExprAST() = default;
        virtual Value *codegen() = 0;
};

class NumberExprAST : public ExprAST {
    double Val;
public:
    NumberExprAST(double Val) : Val(Val){}
    Value *codegen() override;
};

class VariableExprAST : public ExprAST {
    std::string Name;
public:
    VariableExprAST(const std::string &Name) : Name(Name) {}
    Value *codegen() override;
};

// for binary operation
class BinaryExprAST : public ExprAST {
    char Op;
    std::unique_ptr<ExprAST> LHS, RHS;
public:
    BinaryExprAST(char Op, 
                std::unique_ptr<ExprAST> LHS,
                std::unique_ptr<ExprAST> RHS)
        : Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)){}
    Value *codegen() override;
};

// for function call statements
class CallExprAST : public ExprAST {
    std::string Callee;
    std::vector<std::unique_ptr<ExprAST>> Args;
public:
    CallExprAST(const std::string &Callee,
            std::vector<std::unique_ptr<ExprAST>> Args)
    : Callee(Callee), Args(std::move(Args)) {}
    Value *codegen() override;
};

//for function prototype : signature details
class PrototypeAST : public ExprAST {
    std::string Name;
    std::vector<std::string> Args;
public:
    PrototypeAST(const std::string &Name,
            std::vector<std::string> Args)
        : Name(Name), Args(std::move(Args)){}
    Function *codegen();
    const std::string &getName() const { return Name; }
};

// for funciton body
class FunctionAST : public ExprAST {
    std::unique_ptr<PrototypeAST> Proto;
    std::unique_ptr<ExprAST> Body;
public:
    FunctionAST(std::unique_ptr<PrototypeAST> Proto,
                std::unique_ptr<ExprAST> Body)
        : Proto(std::move(Proto)), Body(std::move(Body)) {}
    Function *codegen();
};


// helper functions
static int CurTok;
static int getNextToken() {
    CurTok = gettok();
    return CurTok;
}


/// LogError* - These are little helper functions for error handling.
std::unique_ptr<ExprAST> LogError(const char *Str) {
  fprintf(stderr, "Error: %s\n", Str);
  return nullptr;
}
std::unique_ptr<PrototypeAST> LogErrorP(const char *Str) {
  LogError(Str);
  return nullptr;
}

static std::unique_ptr<ExprAST> ParseExpression();

static std::unique_ptr<ExprAST> ParseNumberExpr(){
    auto Result = std::make_unique<NumberExprAST>(NumVal);
    getNextToken();
    return std::move(Result);
}

static std::unique_ptr<ExprAST> ParseParenExpr() {
  getNextToken(); 
  auto V = ParseExpression();
  if (!V)
    return nullptr;

  if (CurTok != ')')
    return LogError("expected ')'");
  getNextToken(); 
  return V;
}

static std::unique_ptr<ExprAST> ParseIdentifierExpr() {
  std::string IdName = IdentifierStr;
  getNextToken();

  if (CurTok != '(')
    return std::make_unique<VariableExprAST>(IdName);


  getNextToken();
  std::vector<std::unique_ptr<ExprAST>> Args;
  if (CurTok != ')') {
    while (true) {
      if (auto Arg = ParseExpression())
        Args.push_back(std::move(Arg));
      else
        return nullptr;

      if (CurTok == ')')
        break;

      if (CurTok != ',')
        return LogError("Expected ')' or ',' in argument list");
      getNextToken();
    }
  }

  getNextToken();
  return std::make_unique<CallExprAST>(IdName, std::move(Args));
}

static std::unique_ptr<ExprAST> ParsePrimary(){
    switch(CurTok){
        case tok_identifier: return ParseIdentifierExpr();
        case tok_number : return ParseNumberExpr();
        case '(' : return ParseParenExpr();
        default: return LogError("unknown token when expecting an expression");
    }
}

// binary expression parsing
static std::map<char, int> BinopPrecedence;

static int GetTokPrecedence() {
  if (!isascii(CurTok))
    return -1;

  int TokPrec = BinopPrecedence[CurTok];
  if (TokPrec <= 0) return -1;
  return TokPrec;
}

static std::unique_ptr<ExprAST> ParseBinOpRHS(int ExprPrec,
                                    std::unique_ptr<ExprAST> LHS){
    while(true){
        int TokPrec = GetTokPrecedence();
        if(TokPrec < ExprPrec){
            return LHS;
        }

        int BinOp = CurTok;
        getNextToken();

        auto RHS = ParsePrimary();
        if(!RHS){
            return nullptr;
        }

        int NextPrec = GetTokPrecedence();
        if(TokPrec < NextPrec){
            RHS = ParseBinOpRHS(TokPrec+1, std::move(RHS));
            if(!RHS){
                return nullptr;
            }
        }

        LHS = std::make_unique<BinaryExprAST>(BinOp, std::move(LHS), std::move(RHS)); 
    }                        
}

static std::unique_ptr<ExprAST> ParseExpression() {
    auto LHS = ParsePrimary();
    if(!LHS){
        return nullptr;
    }
    return ParseBinOpRHS(0, std::move(LHS));
}



static std::unique_ptr<PrototypeAST> ParsePrototye(){
    if(CurTok != tok_identifier){
        return LogErrorP("Expected function name ...");
    }

    std::string FnName = IdentifierStr;
    getNextToken();

    if(CurTok != '('){
        return LogErrorP("Expected (");
    }

    std::vector<std::string> ArgNames;
    while(getNextToken() == tok_identifier){
        ArgNames.push_back(IdentifierStr);
    }

    if(CurTok != ')'){
        return LogErrorP("Expected )");
    }

    getNextToken();
    return std::make_unique<PrototypeAST>(FnName, ArgNames);
}

static std::unique_ptr<FunctionAST> ParseDefintion(){
    getNextToken();
    auto Proto = ParsePrototye();
    if(!Proto){
        return nullptr;
    }

    auto Expr = ParseExpression();
    if(Expr != nullptr){
        return std::make_unique<FunctionAST>(std::move(Proto), std::move(Expr));
    }

    return nullptr;
}

static std::unique_ptr<PrototypeAST> ParseExtern(){
    getNextToken();
    return ParsePrototye();
}

static std::unique_ptr<FunctionAST> ParseTopLevelExpr(){
    auto Expr = ParseExpression();
    if(Expr != nullptr){
        auto Proto = std::make_unique<PrototypeAST>("_anony_fun", std::vector<std::string>());
        return std::make_unique<FunctionAST>(std::move(Proto), std::move(Expr));
    }

    return nullptr;
}

static std::unique_ptr<LLVMContext> TheContext;
static std::unique_ptr<Module> TheModule;
static std::unique_ptr<IRBuilder<>> Builder;
static std::map<std::string, Value *> NamedValues;
static std::unique_ptr<KaleidoscopeJIT> TheJIT;
static std::unique_ptr<FunctionPassManager> TheFPM;
static std::unique_ptr<LoopAnalysisManager> TheLAM;
static std::unique_ptr<FunctionAnalysisManager> TheFAM;
static std::unique_ptr<CGSCCAnalysisManager> TheCGAM;
static std::unique_ptr<ModuleAnalysisManager> TheMAM;
static std::unique_ptr<PassInstrumentationCallbacks> ThePIC;
static std::unique_ptr<StandardInstrumentations> TheSI;
static std::map<std::string, std::unique_ptr<PrototypeAST>> FunctionProtos;
static ExitOnError ExitOnErr;

Value *LogErrorV(const char *Str) {
  LogError(Str);
  return nullptr;
}

Function *getFunction(std::string Name) {
  if (auto *F = TheModule->getFunction(Name))
    return F;

  auto FI = FunctionProtos.find(Name);
  if (FI != FunctionProtos.end())
    return FI->second->codegen();

  // If no existing prototype exists, return null.
  return nullptr;
}

Value *NumberExprAST::codegen() {
  return ConstantFP::get(*TheContext, APFloat(Val));
}

Value *VariableExprAST::codegen() {
  Value *V = NamedValues[Name];
  if (!V)
    return LogErrorV("Unknown variable name");
  return V;
}

Value *BinaryExprAST::codegen() {
  Value *L = LHS->codegen();
  Value *R = RHS->codegen();
  if (!L || !R)
    return nullptr;

  switch (Op) {
  case '+':
    return Builder->CreateFAdd(L, R, "addtmp");
  case '-':
    return Builder->CreateFSub(L, R, "subtmp");
  case '*':
    return Builder->CreateFMul(L, R, "multmp");
  case '<':
    L = Builder->CreateFCmpULT(L, R, "cmptmp");
    return Builder->CreateUIToFP(L, Type::getDoubleTy(*TheContext), "booltmp");
  default:
    return LogErrorV("invalid binary operator");
  }
}

Value *CallExprAST::codegen() {
  Function *CalleeF = getFunction(Callee);
  if (!CalleeF)
    return LogErrorV("Unknown function referenced");

  if (CalleeF->arg_size() != Args.size())
    return LogErrorV("Incorrect # arguments passed");

  std::vector<Value *> ArgsV;
  for (unsigned i = 0, e = Args.size(); i != e; ++i) {
    ArgsV.push_back(Args[i]->codegen());
    if (!ArgsV.back())
      return nullptr;
  }

  return Builder->CreateCall(CalleeF, ArgsV, "calltmp");
}


Function *PrototypeAST::codegen() {
  std::vector<Type *> Doubles(Args.size(), Type::getDoubleTy(*TheContext));
  FunctionType *FT =
      FunctionType::get(Type::getDoubleTy(*TheContext), Doubles, false);

  Function *F =
      Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get());

  unsigned Idx = 0;
  for (auto &Arg : F->args())
    Arg.setName(Args[Idx++]);

  return F;
}

Function *FunctionAST::codegen() {
    auto &P = *Proto;
    FunctionProtos[Proto->getName()] = std::move(Proto);

    Function *TheFunction = getFunction(P.getName());

    if (!TheFunction)
        return nullptr;

    if (!TheFunction->empty())
        return (Function*)LogErrorV("Function cannot be redefined.");

    BasicBlock *BB = BasicBlock::Create(*TheContext, "entry", TheFunction);
    Builder->SetInsertPoint(BB);

    NamedValues.clear();
    for (auto &Arg : TheFunction->args())
        NamedValues[std::string(Arg.getName())] = &Arg;

    if (Value *RetVal = Body->codegen()) {
        Builder->CreateRet(RetVal);
        verifyFunction(*TheFunction);

        TheFPM->run(*TheFunction, *TheFAM);

            return TheFunction;
    }

    TheFunction->eraseFromParent();
    return nullptr;
}


static void InitializeModule(){

    TheContext = std::make_unique<LLVMContext>();
    TheModule = std::make_unique<Module>("funny jit", *TheContext);
    TheModule->setDataLayout(TheJIT->getDataLayout());

    Builder = std::make_unique<IRBuilder<>>(*TheContext);

    TheFPM = std::make_unique<FunctionPassManager>();
    TheLAM = std::make_unique<LoopAnalysisManager>();
    TheFAM = std::make_unique<FunctionAnalysisManager>();
    TheCGAM = std::make_unique<CGSCCAnalysisManager>();
    TheMAM = std::make_unique<ModuleAnalysisManager>();
    ThePIC = std::make_unique<PassInstrumentationCallbacks>();
    TheSI = std::make_unique<StandardInstrumentations>(*TheContext, true);
    TheSI->registerCallbacks(*ThePIC, TheMAM.get());

    // adding transforms
    TheFPM->addPass(InstCombinePass());
    TheFPM->addPass(ReassociatePass());
    TheFPM->addPass(GVNPass());
    TheFPM->addPass(SimplifyCFGPass());

    PassBuilder PB;
    PB.registerModuleAnalyses(*TheMAM);
    PB.registerFunctionAnalyses(*TheFAM);
    PB.crossRegisterProxies(*TheLAM, *TheFAM, *TheCGAM, *TheMAM);

}

static void HandleDefinition(){
    if(auto FnAST = ParseDefintion()){
        if(auto *FnIR = FnAST->codegen()){
            fprintf(stderr, "Parsed a function definition.\n");
            FnIR->print(errs());
            fprintf(stderr, "\n");
            ExitOnErr(TheJIT->addModule(
                ThreadSafeModule(std::move(TheModule), std::move(TheContext))));
            InitializeModule();
        }
    }else{
        getNextToken();
    }
}

static void HandleExtern(){
    if(auto ProtoAST = ParseExtern()){
        if (auto *FnIR = ProtoAST->codegen()) {
            fprintf(stderr, "Read extern: ");
            FnIR->print(errs());
            fprintf(stderr, "\n");
            FunctionProtos[ProtoAST->getName()] = std::move(ProtoAST);
        }
    }else{
        getNextToken();
    }
}

static void HandleTopLevelExpression() {
    if (auto FnAST = ParseTopLevelExpr()) {
        if (auto *FnIR = FnAST->codegen()) {
            fprintf(stderr, "Read top-level expression:");

            auto RT = TheJIT->getMainJITDylib().createResourceTracker();
            auto TSM = ThreadSafeModule(std::move(TheModule), std::move(TheContext));
            ExitOnErr(TheJIT->addModule(std::move(TSM), RT));
            InitializeModule();

            auto ExprSymbol = ExitOnErr(TheJIT->lookup("_anony_fun"));
            // assert(ExprSymbol);
            
            double (*FP)() = ExprSymbol.getAddress().toPtr<double (*)()>();
            fprintf(stderr, "Evaluate to %f\n", FP());

            ExitOnErr(RT->remove());

            // FnIR->print(errs());
            // fprintf(stderr, "\n");
            // // Remove the anonymous expression.
            // FnIR->eraseFromParent();
        }
    } else {
        getNextToken();
    }
}

// driver
static void MainLoop(){
    while(true){
        fprintf(stderr, "working>");
        
        switch (CurTok)
        {
            case tok_eof: return;
            case ';': getNextToken(); break;
            case tok_def: HandleDefinition(); break;
            case tok_extern: HandleExtern(); break;
            default: HandleTopLevelExpression();
                     break;
        }
    }
}

#ifdef _WIN32
#define DLLEXPORT __declspec(dllexport)
#else
#define DLLEXPORT
#endif

/// putchard - putchar that takes a double and returns 0.
extern "C" DLLEXPORT double putchard(double X) {
  fputc((char)X, stderr);
  return 0;
}

/// printd - printf that takes a double prints it as "%f\n", returning 0.
extern "C" DLLEXPORT double printd(double X) {
  fprintf(stderr, "%f\n", X);
  return 0;
}


int main(){
    InitializeNativeTarget();
    InitializeNativeTargetAsmPrinter();
    InitializeNativeTargetAsmParser();

    BinopPrecedence['<'] = 10;
    BinopPrecedence['+'] = 20;
    BinopPrecedence['-'] = 20;
    BinopPrecedence['*'] = 40;

    fprintf(stderr, "working> ");
    getNextToken();

    TheJIT = ExitOnErr(KaleidoscopeJIT::Create());
    InitializeModule();

    MainLoop();

    TheModule->print(errs(), nullptr);  
    return 0;
}