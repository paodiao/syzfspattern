#include <iostream>
#include <fstream>
#include <map>
#include <queue>
#include <deque>
#include <set>
#include <utility>
#include <cstdlib>
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include <string>
#include "llvm/IR/Value.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/Casting.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Constant.h"
#include "interPro.h"

//using namespace StaticAnalysis;
llvm::StringRef configVar;
int numOfValue = 0;

std::error_code EC;
enum sys::fs::OpenFlags F_None;
//std::string name = "encrypt";
//StringRef filename(name);
//StringRef filename(line_file);
//llvm::raw_fd_ostream file(filename, EC, F_None);


llvm::Value* maxValue;
llvm::Value* minValue;
int mapping = 0;
std::map<llvm::StringRef, llvm::Value *> var2sbMap;
llvm::Value* var;

std::string name1 = "sb_name";
llvm::StringRef filename1(name1);
//llvm::raw_fd_ostream file1(filename1, EC, F_None);

//std::string line;
//std::ifstream myfile( "sb_name", std::ifstream::in );

//string func_name = "PRS";  // removed: function name now loaded from CONFD_FUNC_NAME / function_name file
//string func_name = "validate_blocksize";
namespace StaticAnalysis{
	using namespace std;
	using namespace llvm;
	int depth = 0;
	std::map<Value *, bool> taintMap;
	//std::queue<Instruction *> taintInst;
	//std::queue<std::pair<Instruction *, unsigned> > taintInst;
	//std::deque<std::pair<Instruction *, unsigned> > dq;
	std::queue<std::pair<Instruction *, Instruction *> > taintInst;
	std::deque<std::pair<Instruction *, Instruction *> > dq;
	std::set<std::string> excludeSet;
	//std::deque<Instruction *> dq;
        struct InterProPass : public ModulePass {
		static char ID;
		//string func_name = "PRS";
		
		InterProPass() : ModulePass(ID) {}

		//declares all the functions of the pass
		virtual bool runOnModule(Module& m);
	};

void TaintAnalysis::Analysis(Function *func)
{
	//errs() << "inside the class constructor: " << func->getName() << "\n";
	for (Function::iterator b = func->begin(), be = func->end(); b != be; ++b) {
        BasicBlock& BB = *b;
        for (auto& I : BB) {
            errs() << "" << "\n";
			//TaintAnalysis::functionProcess(*func, NULL);
        }
    }
}

//Analyzes store instructions to taint relevant variables
void TaintAnalysis::taintStore(Instruction &I, std::map<Value *, bool> &taintMap, Instruction *line_no1)
{
    Value *op1 = I.getOperand(0);
    Value *op2 = I.getOperand(1);
    //Instruction *i = dyn_cast<Instruction>(&I);
	//MDNode* debug = I.getMetadata("dbg");
	if(taintMap.find(op1) != taintMap.end())
    {
        taintInst.push({&I, line_no1});
		//errs() << I << "\n";
		//taintInst.push(make_pair( &I, debug1));
		//errs() << taintInst.size() << "\n";
        StringRef name = op2->getName();
        if (excludeSet.find(name.str()) == excludeSet.end()) {
      		//if (!((name == "force") || (name == "flush") || (name == "force_min_size") || (name == "print_min_size") || (name == "use_stride") || (name == "undo_file") || (name == "new_size") || (name == "retval") || (name == "retval1") || (name == "tmp") || (name == "checkit") )) { 
			taintMap.insert(std::pair<Value *, bool>(op2, 1));
        }
	}

	if(taintMap.find(op2) != taintMap.end())
    {
        //errs() << I << "\n";
		taintInst.push({&I, line_no1});
	}
}

//Analyzes Binary instructions to taint relevant variables
void TaintAnalysis::taintBinaryOperator(Instruction &I, std::map<Value *, bool> &taintMap, Instruction *line_no1)
{
	//errs() << I << "\n";
    Value *op1 = I.getOperand(0);
    Value *op2 = I.getOperand(1);
    Value *op3 = dyn_cast<Value>(&I);
    Instruction *i = dyn_cast<Instruction>(&I);
	
    if(taintMap.find(op1) != taintMap.end())
    {
        taintMap.insert(std::pair<Value *, bool>(op3, 1));
        taintInst.push({i, line_no1});
	}
    else if (taintMap.find(op2) != taintMap.end())
    {
            taintMap.insert(std::pair<Value *, bool>(op3, 1));
            taintInst.push({i, line_no1});
    }
}

//Analyzes Load instructions to taint relevant variables
void TaintAnalysis::taintLoad(Instruction &I, std::map<Value *, bool> &taintMap, Instruction *line_no1)
{
    Value *op1 = I.getOperand(0);
    Value *op2 = dyn_cast<Value>(&I);
    Instruction *i = dyn_cast<Instruction>(&I);
	//MDNode* debug = I.getMetadata("dbg");
    if(taintMap.find(op1) != taintMap.end())
    {
        taintMap.insert(std::pair<Value *, bool>(op2, 1));
		//errs() << I <<"\n";
		//errs() << *op1 <<"\n";
        taintInst.push({i, line_no1});
		//taintInst.push(make_pair(i, NULL));
		/*errs() << taintInst.size() << "\n";
		while (!taintInst.empty()) {
            std::pair <llvm::Instruction* , llvm::MDNode*> test1 = taintInst.front();
            errs() << *test1.first << ":" << test1.second << "\n";
			taintInst.pop();
		}*/
    }
}

//Analyzes Icmp instructions to taint relevant variables
void TaintAnalysis::taintIcmp(Instruction &I, std::map<Value *, bool> &taintMap, Instruction *line_no1)
{
    Instruction *i = dyn_cast<Instruction>(&I);
    Value *v1 = dyn_cast<Instruction>(&I);
    for(unsigned j=0;j<I.getNumOperands(); j++) {
        Value* currOp = I.getOperand(j);
        if(taintMap.find(currOp) != taintMap.end())
        {
		    //errs() << "value found in map" << "\n";
            taintInst.push({i, line_no1});
            taintMap.insert(std::pair<Value *, bool>(v1, 1));
        }
    }
}

//Analyzes Fcmp instructions to taint relevant variables
void TaintAnalysis::taintFcmp(Instruction &I, std::map<Value *, bool> &taintMap, Instruction *line_no1)
{
        Instruction *i = dyn_cast<Instruction>(&I);
        //Value *v1 = dyn_cast<Instruction>(&I);
        Value *op2 = I.getOperand(0);

        if(taintMap.find(op2) != taintMap.end())
        {
            taintInst.push({&I, line_no1});
            // taintMap.insert(std::pair<Value *, bool>(v1, 1));
        }

}

//Analyzes GetElementPtr instructions to taint relevant variables
void TaintAnalysis::taintGetElementPtr(Instruction &I, std::map<Value *, bool> &taintMap, Instruction *line_no1)
{
    Instruction *i = dyn_cast<Instruction>(&I);
    Value *op1 = dyn_cast<Instruction>(&I);
    for(unsigned j=0;j<I.getNumOperands(); j++) {
        Value* currOp = I.getOperand(j);
        if(taintMap.find(currOp) != taintMap.end())
        {
            taintMap.insert(std::pair<Value *, bool>(op1, 1));
            taintInst.push({&I, line_no1});
        }
    }
}

//Analyzes Select instructions to taint relevant variables
void TaintAnalysis::taintSelect(Instruction &I, std::map<Value *, bool> &taintMap, Instruction *line_no1)
{
    Instruction *i = dyn_cast<Instruction>(&I);
    SelectInst *i1 =dyn_cast<SelectInst>(&I);
    Value* v1 = i1->getOperand(0);
    if(taintMap.find(v1) != taintMap.end())
    {
            //errs() << "select instruction :" << (*v1) <<"\n";
            taintInst.push({&I, line_no1});
    }
}

//Analyzes Conversion instructions to taint relevant variables
void TaintAnalysis::taintConversion(Instruction &I, std::map<Value *, bool> &taintMap, Instruction *line_no1)
{
    Value *op1 = I.getOperand(0);
    Value *op2 = dyn_cast<Value>(&I);

    if(taintMap.find(op1) != taintMap.end())
    {
            taintMap.insert(std::pair<Value *, bool>(op2, 1));
            taintInst.push({&I, line_no1});
    }
}

//Analyzes Branch instructions to taint relevant variables
void TaintAnalysis::taintBr(Instruction &I, std::map<Value *, bool> &taintMap, Instruction *line_no1)
{
    unsigned int a = I.getNumOperands();
    if (a > 1)
    {
        Value *op1 = I.getOperand(0);
        if(taintMap.find(op1) != taintMap.end())
        {
            //ICmpInst* Cinst = dyn_cast<ICmpInst>(&*op1);
            BranchInst* Binst = dyn_cast<BranchInst>(&I);
            taintInst.push({&I, line_no1});
            BasicBlock *Succ1 = Binst->getSuccessor(0);
            BasicBlock *Succ2 = Binst->getSuccessor(1);
            StringRef name1 = Succ1->getName();
            StringRef name2 = Succ2->getName();
            string s1 = "end";

            //When the branch label doesn't end with "end" then taint the first instruction of that branch
            if (name1.find(s1) == string::npos){
                Instruction* I3 = dyn_cast<Instruction>(&*(Succ1->begin()));
                taintInst.push({I3, line_no1});
                Value* v2 = dyn_cast<Value>(I3);
                taintMap.insert(std::pair<Value *, bool>(v2, 1));
        	}
            else if (name2.find(s1) == string::npos)
            {
                BasicBlock *Succ1 = Binst->getSuccessor(1);
                Instruction* I4 = dyn_cast<Instruction>(&*(Succ1->begin()));
                taintInst.push({I4, line_no1});
                Value* v3  = dyn_cast<Value>(I4);
                taintMap.insert(std::pair<Value *, bool>(v3, 1));
        	}
        }
    }
}

//Analyzes Phi instructions to taint relevant variables
void TaintAnalysis::taintPhi(Instruction &I, std::map<Value *, bool> &taintMap, Instruction *line_no1)
{
    Value *op1 = I.getOperand(0);
    Value *op2 = I.getOperand(1);
    Value *op3 = dyn_cast<Value>(&I);
    if(taintMap.find(op1) != taintMap.end())
    {
        taintMap.insert(std::pair<Value *, bool>(op3, 1));
        taintInst.push({&I, line_no1});
    }
    else if (taintMap.find(op2) != taintMap.end())
    {
        taintMap.insert(std::pair<Value *, bool>(op3, 1));
        taintInst.push({&I, line_no1});
    }
}

//Analyzes Call instructions to taint relevant variables
void TaintAnalysis::taintCallInst(Instruction &I, std::map<Value *, bool> &taintMap, Instruction *line_no1)
{
	//const DebugLoc &D = I.getDebugLoc();
	//unsigned line_no = D.getLine();
	Value* op1 = dyn_cast<Value>(&I);
    CallInst* call = dyn_cast<CallInst>(&I);
	//errs() << I << "\n";
	//Function *F = call->getCalledFunction();
	if (call->getCalledFunction() != NULL)
	{
		Function *F = call->getCalledFunction();
		unsigned int V2 = F->arg_size();
		for(int i = 0; i < V2; i++)
        {
            Value* V1 = call->getArgOperand(i);
            if(taintMap.find(V1) != taintMap.end())
            {
                taintMap.insert(std::pair<Value *, bool>(op1, 1));
                taintInst.push({&I, NULL});
				if (!F->hasExternalLinkage()){
					if (!F->isIntrinsic()){
                        TaintAnalysis::propogateTaintToArguments(i, I, F);
                        TaintAnalysis::functionProcess(*F, &I);
					}
				}
            }
        }

		//Parsing function when arguments are not tainted
		// if (!F->hasExternalLinkage() || F->isDSOLocal()){
		if (!F->hasExternalLinkage()){
			//errs() << F->getName() << ":" << I << "\n";
			TaintAnalysis::functionProcess(*F, &I);
			
		}
	}
}

void TaintAnalysis::propogateTaintToArguments(int taintedArgNo, Instruction &I, Function *F)
{
	//int taintedArgNo;
	//assert(taintedArgNo > 0);
	CallInst* call = dyn_cast<CallInst>(&I);

	//errs() << "Propagating Taint To Arguments.\n";
	//Function *func = call->getCalledFunction();
	//unsigned int V2 = func->arg_size();
	unsigned int V2 = F->arg_size();
	if (V2 > 0){
		Value *currArg = call->getArgOperand(taintedArgNo);
		Argument* i = F->getArg(taintedArgNo);
		taintMap.insert(std::pair<Value *, bool>(i, 1));
	}
}

//Prints the tainted instructions on the std output and also writes them on a file named "module"
void TaintAnalysis::printInst(std::queue<std::pair<Instruction *, Instruction *> >& taintInst, Module& m, llvm::raw_fd_ostream& file)
{
    //std::error_code EC;
    //enum sys::fs::OpenFlags F_None;
    //std::string name = "module";
	//StringRef filename(line_file);
    //llvm::raw_fd_ostream file(filename, EC, F_None);

    errs() <<"The size of the queue is: " << taintInst.size() << "\n";
    int size = taintInst.size();

    errs() <<"The tainted Instructions are: " << "\n";
    int i = 0;
	while (!taintInst.empty()) {
        std::pair <llvm::Instruction* , Instruction *> test1 = taintInst.front();
        dq.push_back(test1);
		if (test1.second == NULL)
			file << *test1.first << ":" << test1.second << "\n";
		else
			file << *test1.first << ":" << *test1.second << "\n";

		unsigned opcode = test1.first->getOpcode();
		if (opcode == llvm::Instruction::Call){
			CallInst* call = dyn_cast<CallInst>(test1.first);
			Function *F = call->getCalledFunction();
			if (F != NULL){
				StringRef name = F->getName();
				//if (name == "stderr" || name == "fprintf"){ //(for xfs)
				if (name == "fprintf" || name == "com_err" || name == "printf" ||
				    name == "vfprintf" || name == "fputs" ||
				    name == "error" || name == "usage" ||
				    name == "do_abort" || name == "do_error" || name == "do_warn" ||
				    name == "illegal_option" || name == "conflict" || name == "illegal" ||
				    name == "ntfs_log_redirect" || name == "error_msg" ||
				    name == "mkfs_usage" || name == "respec" ||
				    name == "mkntfs_usage" || name == "invalid_cfgfile_opt"){
					errs() << "found error output" << "\n";
					dataRange(test1.first, m, &file);
				}
			}
		}
        taintInst.pop();
		//file << test1 << "\n";
    }
    file.close();
}


//Gets the data range of parameters
void TaintAnalysis::dataRange(Instruction *Inst, Module& m, raw_fd_ostream* stream)
{	
	if (numOfValue < 2){
  		for(auto& F : m){
        	for (auto& B : F) {
            	for (auto& I : B) {
                	if (&I == Inst){
                    	errs() << "found fprintf in main file" << "\n";
                    	for (BasicBlock* Pred : predecessors(&B))
                    	{
                        	BasicBlock& predecessor = *Pred;
                        	for (auto& i : predecessor){
                            	errs() << i << "\n";
                            	unsigned opcode = i.getOpcode();
                            	errs() << opcode << "\n";
                            	if (opcode == llvm::Instruction::ICmp || opcode == llvm::Instruction::FCmp)
                            	{
                                	CmpInst* inst = dyn_cast<CmpInst>(&i);
                                	Value* op1 = i.getOperand(1);
                                	StringRef S = op1->getName();
                                	if (S.empty())
                                	{
                                    	llvm::CmpInst::Predicate p = inst->getPredicate();
                                    	if (inst->getPredicate() == 34 || inst->getPredicate() == 38)
                                    	{
                                        	//errs() << "Range is <= " << *i.getOperand(1)  << "\n";
                                        	Value* maxValue = i.getOperand(1);
                                        	errs() << "Max value is: " << *maxValue << "\n";
                                        	*stream << "Max value = " << *maxValue << "\n";
                                        	numOfValue = numOfValue + 1;
                                        	//errs() << numOfValue << "\n";
                                    	}
                                    	else if (inst->getPredicate() == 35 || inst->getPredicate() == 39 || inst->getPredicate() == 2)
                                    	{
                                        	Value* maxValue = i.getOperand(1);
                                        	errs() << "Max value is < " << *maxValue  << "\n";
                                        	*stream << "Max value = " << *maxValue << " - 1" << "\n";
                                        	numOfValue = numOfValue + 1;
                                    	}
                                    	else if (inst->getPredicate() == 36 || inst->getPredicate() == 40)
                                    	{
                                        	//errs() << "Range is >= " << *i.getOperand(1)  << "\n";
                                        	Value* minValue = i.getOperand(1);
                                        	errs() << "Min value is: " << *minValue << "\n";
                                        	*stream << "Min value = " << *minValue << "\n";
                                        	numOfValue = numOfValue + 1;
                                        	//errs() << numOfValue << "\n";
                                    	}
                                		else if (inst->getPredicate() == 37 || inst->getPredicate() == 41 || inst->getPredicate() == 4)
										{
                                        	Value* minValue = i.getOperand(1);
                                        	errs() << "Min value is : " << *i.getOperand(1)  << "+ 1" << "\n";
                                        	*stream << "Min value = " << *minValue << "+ 1" << "\n";
											numOfValue = numOfValue + 1;
                                    	}
                                	}
                            	}
                        	}
                    	}
                	}
            	}
        	}
    	}
	//errs() << "out of data range function" << "\n";
	}
}



//for inter-procedural pass
void TaintAnalysis::functionProcess (Function& F, Instruction* line_no1)
{
	for (auto& B : F) {
		for (auto& I : B) {
			visit(I, line_no1);
        }
    }
}

//for main function process (it comes under externalLinkage)
void TaintAnalysis::mainfunctionProcess(Function& F, Instruction* line_no1)
{
	errs() << "inside main function" << "\n";
	for (auto& B : F) {
		for (auto& I : B) {
			visit(I, line_no1);
			if (depth > 99){
				errs() << depth << "\n";
				break;
			}
			//errs() << F.getName() << ":" << I << "\n"; 
		}
		if (depth > 50){
            break;
		}
	}
}


//For each instruction, decides the type of the instruction and sends to relevant functions
void TaintAnalysis::visit(Instruction &I, Instruction*	line_no1)
{
	//errs() << I << "\n";;
	unsigned opcode = I.getOpcode();
    if (opcode == llvm::Instruction::Store)
    {
        TaintAnalysis::taintStore(I, taintMap, line_no1);
    }
	else if (opcode == llvm::Instruction::Call)
    {
        taintCallInst(I, taintMap, line_no1);
    }
    else if (opcode == llvm::Instruction::Load)
    {
        taintLoad(I, taintMap, line_no1);
    }
    else if (opcode == llvm::Instruction::ICmp)
    {
        taintIcmp(I, taintMap, line_no1);
    }
    else if (opcode == llvm::Instruction::FCmp)
    {
        taintFcmp(I, taintMap, line_no1);
    }
    else if (opcode == llvm::Instruction::GetElementPtr)
    {
        taintGetElementPtr(I, taintMap, line_no1);
    }
    else if (opcode == llvm::Instruction::Select)
    {
        taintSelect(I, taintMap, line_no1);
    }
    else if ((opcode == llvm::Instruction::And) || (opcode == llvm::Instruction::Or) || (opcode == llvm::Instruction::Xor)
                    || (opcode == llvm::Instruction::Shl) || (opcode == llvm::Instruction::LShr) || (opcode == llvm::Instruction::AShr))
    {
        taintBinaryOperator(I, taintMap, line_no1);
    }
    else if ((opcode == llvm::Instruction::Add) || (opcode == llvm::Instruction::FAdd) || (opcode == llvm::Instruction::Sub)
                    || (opcode == llvm::Instruction::FSub) || (opcode == llvm::Instruction::Mul) || (opcode == llvm::Instruction::FMul)
                    || (opcode == llvm::Instruction::UDiv) || (opcode == llvm::Instruction::SDiv) || (opcode == llvm::Instruction::FDiv)
                    || (opcode == llvm::Instruction::URem) || (opcode == llvm::Instruction::SRem) || (opcode == llvm::Instruction::FRem))
    {
        taintBinaryOperator(I, taintMap, line_no1);
    }
    else if ((opcode == llvm::Instruction::SExt) || (opcode == llvm::Instruction::Trunc) || (opcode == llvm::Instruction::ZExt))
    {
            taintConversion(I, taintMap, line_no1);
    }
    else if (opcode == llvm::Instruction::Br)
    {
            taintBr(I, taintMap, line_no1);
    }
    else if (opcode == llvm::Instruction::PHI)
    {
            taintPhi(I, taintMap, line_no1);
    }
	else
		return;
}

bool InterProPass::runOnModule(Module& m) {
	std::string line_file;
	//taking file name to write the taint traces
	char *env_trace = getenv("CONFD_TRACE_OUTPUT");
	if (env_trace) {
		line_file = env_trace;
		errs() << "found CONFD_TRACE_OUTPUT: " << line_file << "\n";
	} else {
		// Fallback: read from "file_name" text file
		char *trace_filename = getenv("CONFD_TRACE_FILE") ?
			getenv("CONFD_TRACE_FILE") : (char*)"file_name";
		std::ifstream infile_file(trace_filename);
		if (infile_file) {
			std::getline(infile_file, line_file);
			infile_file.close();
			errs() << "read trace output name from " << trace_filename << "\n";
		} else {
			line_file = "taint_trace";
			errs() << "no trace name specified, using taint_trace\n";
		}
	}
	llvm::raw_fd_ostream file(line_file + ".trace", EC, F_None);

	//taking function name as input: env var first, then file, no hardcoded fallback
	const char* function_name = nullptr;
	std::string func_str;
	char *Filename_func = getenv("CONFD_FUNC_NAME");
	if (Filename_func) {
		func_str = Filename_func;
	} else {
		std::ifstream infile("function_name");
		if (infile) {
			std::getline(infile, func_str);
			infile.close();
		}
	}
	if (func_str.empty()) {
		errs() << "ERROR: No function name specified.\n"
		       << "Set CONFD_FUNC_NAME environment variable "
		       << "or provide a 'function_name' file with the target function name.\n";
		exit(1);
	}
	function_name = func_str.c_str();

	errs() << "inside runOn module" << "\n";
	int flag1 = 0;

	//taking variable name as input
	char *Filename_var = getenv("CONFD_VAR_NAME");
	if (!Filename_var) Filename_var = (char*)"variable";
	std::ifstream infile_var(Filename_var);
	std::string line_var;
	std::getline(infile_var, line_var);
	const char* name_var;
	if (!line_var.empty()) {
		name_var = line_var.c_str();
		errs() << "name of the var:" << name_var << "\n";
	} else {
		errs() << "No variable name specified, cannot proceed with the Taint Analysis" << "\n";
		exit(0);
	}
	infile_var.close();

	// Load exclusion list from file (parameterized, no longer hardcoded per-FS)
	char *Filename_exclude = getenv("CONFD_EXCLUDE_FILE");
	if (!Filename_exclude) Filename_exclude = (char*)"exclude_vars";
	std::ifstream infile_exclude(Filename_exclude);
	std::string exclude_line;
	while (std::getline(infile_exclude, exclude_line)) {
		if (!exclude_line.empty() && exclude_line.back() == '\r')
			exclude_line.pop_back();
		if (!exclude_line.empty())
			StaticAnalysis::excludeSet.insert(exclude_line);
	}
	infile_exclude.close();

	for(auto& F : m){
		// Mode 5: scan entry function + known parameter-parsing sub-functions for taint sources
		if (F.getName() == function_name ||
	    	F.getName() == "parse_extended_opts" ||
	    	F.getName() == "parse_journal_opts" ||
	    	F.getName() == "f2fs_parse_options" ||
	    	F.getName() == "add_default_options" ||
	    	F.getName() == "block_opts_parser" ||
	    	F.getName() == "cfgfile_opts_parser" ||
	    	F.getName() == "data_opts_parser" ||
	    	F.getName() == "inode_opts_parser" ||
	    	F.getName() == "log_opts_parser" ||
	    	F.getName() == "meta_opts_parser" ||
	    	F.getName() == "naming_opts_parser" ||
	    	F.getName() == "proto_opts_parser" ||
	    	F.getName() == "rtdev_opts_parser" ||
	    	F.getName() == "sector_opts_parser" ||
	    	F.getName() == "erofs_mkfs_feat_set_legacy_compress" ||
	    	F.getName() == "erofs_mkfs_feat_set_ztailpacking" ||
	    	F.getName() == "erofs_mkfs_feat_set_fragments" ||
	    	F.getName() == "erofs_mkfs_feat_set_all_fragments" ||
	    	F.getName() == "erofs_mkfs_feat_set_dedupe" ||
	    	F.getName() == "erofs_mkfs_feat_set_fragdedupe"){

			errs() << "scanning function: " << F.getName() << "\n";
			for (auto& B : F) {
				for (auto& I : B) {
			        unsigned opcode = I.getOpcode();   	
					
					//for parameters that use a function to load them
					if (opcode == llvm::Instruction::Call)
                    {
                        CallInst* call = dyn_cast<CallInst>(&I);
                        Function *F1 = call->getCalledFunction();
                        if (F1 != NULL){
                            StringRef name = F1->getName();
							if(name.find(line_var) != StringRef::npos){
								errs() << F.getName() << "\n";
								errs() << "string: " << name << "\n";
                                Value* V = &I;
                                taintMap.insert(std::pair<Value *, bool>(V, 1));
                                taintInst.push({&I, NULL});

                            }
                        }
					}
						
					//for parameters that use global variables to load them and keep them in superblock
                    if (opcode == llvm::Instruction::Load)
                    {
                        Value *op1 = I.getOperand(0);
                        Value *op2 = dyn_cast<Value>(&I);
                        StringRef S = op1->getName();
						//errs() << S << "\n";
						if(S == name_var)
                        {
                            //errs() << S << "\n";
							errs() << *op1 << "\n";
                            Type* dataType = op1->getType();
                            errs() << *dataType << "\n";
							file << "Data type = " << *dataType << "\n";
                            taintMap.insert(std::pair<Value *, bool>(op1, 1));
                            //taintMap.insert(std::pair<Value *, bool>(op2, 1));
                            taintInst.push({&I, NULL});
                        }
                    }
					
					
					//unsigned opcode1 = I.getOpcode();
                    if (opcode == llvm::Instruction::Store)
                    {
                        Value *op1 = I.getOperand(0);
                        Value *op2 = I.getOperand(1);
                        StringRef S = op2->getName();
						std::string str;
                        llvm::raw_string_ostream ss(str);
                        ss << S;
                        const char* string1 = ss.str().c_str();
                        if (op2->getName() == name_var)
                        {
                            errs() << S << "\n";
                            Type* dataType = op2->getType();
                            errs() << *dataType << "\n";
							file << "Data type = " << *dataType << "\n";
                            taintMap.insert(std::pair<Value *, bool>(op2, 1));
                            //taintMap.insert(std::pair<Value *, bool>(op2, 1));
                            taintInst.push({&I, NULL});
                        }
                    }
                                        
					//for cross-component dependency, using the mapping information
                    if (opcode == llvm::Instruction::GetElementPtr)
					{
						Value *op1 = dyn_cast<Value>(&I);
						StringRef S = op1->getName();
                        int flag = 0;
                        if (S.find(line_var) != StringRef::npos)
                        {
                            errs() << S << "\n";
                            if (flag == 0)
                            {
                                //errs() << I << " : " << F.getName() << "\n";
								//TODO: 只对第一次遇到的名字与line_var相同的GEP做记录，不会遗漏吗？
                                if (flag1 == 0){
									Type* dataType = op1->getType();
                                    errs() << *dataType << "\n";
                                    file << "Data type = " << *dataType << "\n";
                                    flag1 = 1;
                                }
                                taintMap.insert(std::pair<Value *, bool>(op1, 1));
                                taintInst.push({&I, NULL});
                                //flag = 1;
                            }
                        }
					}

					// Mode 8: inline GEP Store text matching
					// Matches Store instructions where the GEP is inline in the operand (no named intermediate)
					if (opcode == llvm::Instruction::Store)
					{
						Value *op2 = I.getOperand(1);
						if (op2->getName().empty())
						{
							std::string str;
							llvm::raw_string_ostream ss(str);
							I.print(ss);
							if (str.find(line_var) != std::string::npos)
							{
								errs() << "inline Store match: " << I << "\n";
								Type* dataType = op2->getType();
								errs() << *dataType << "\n";
								file << "Data type = " << *dataType << "\n";
								taintMap.insert(std::pair<Value *, bool>(op2, 1));
								taintInst.push({&I, NULL});
							}
						}
					}			
				}
			}
		}
	}

    for(auto& F : m){
        if (F.getName() == function_name){
            errs() << "Hello from: "<< F.getName() << "\n";
			//depth = 0;
			TaintAnalysis::functionProcess(F, NULL);
			//TaintAnalysis::printInst(taintInst, m);
			//file.close();
        }
	}
	TaintAnalysis::printInst(taintInst, m, file);
    //file.close();
	//errs() << "end of analysis2" << "\n";
	return false;
}

}
//Registers the pass, pass name is "interpro", library is libSkeletonPass.so
char StaticAnalysis::InterProPass::ID = 0;
static RegisterPass<StaticAnalysis::InterProPass> SCCReg("interpro", "InterPro Pass");

