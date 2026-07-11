#include <fstream>
#include <queue>
#include <iostream>
#include <iterator>
#include "llvm/IR/GlobalVariable.h"
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
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace std;
using namespace llvm;

int numOfValue = 0;
std::error_code EC;
enum sys::fs::OpenFlags F_None;
std::string name = "critical";
int flag = 0; 
StringRef S;

// Helper: get a usable name from a Value that phase3 can resolve
static std::string getValName(Value *V) {
	StringRef n = V->getName();
	if (!n.empty())
		return n.str();
	// Fall back to getNameOrAsOperand which gives %N for unnamed values
	return V->getNameOrAsOperand();
}

namespace {
    struct TestPass : public ModulePass {

		//string func_name = "PRS";
		static char ID;
		TestPass() : ModulePass(ID) {}

		virtual bool runOnModule(Module& m);
		BasicBlock* predecessorBB(BasicBlock* B, llvm::raw_fd_ostream& file);
	};


//Goes to the predecessor Basic Block to get the parameter involved in the Error	
BasicBlock* TestPass::predecessorBB(BasicBlock* B, llvm::raw_fd_ostream& file)
{
	flag = flag + 1;
	if (numOfValue < 2){
		for (BasicBlock* Pred : predecessors(B))
    	{
			BasicBlock& predecessor = *Pred;
			for (auto& i : predecessor){
       			unsigned opcode = i.getOpcode();
            	if (opcode == llvm::Instruction::ICmp)
            	{
					errs() << "found icmp instructions" << "\n";
					errs() << i << "\n";
                	CmpInst* inst = dyn_cast<CmpInst>(&i);
                	Value* op1 = i.getOperand(0);
					Instruction* i1 = static_cast<Instruction*>(i.getOperand(0));
					unsigned opcode1 = i1->getOpcode();
					Value* op2 = i.getOperand(1);
					Instruction* i2 = dyn_cast<Instruction>(i.getOperand(1));
					if (i2)
					{
						//Instruction* i2 = static_cast<Instruction*>(i.getOperand(1));
						//unsigned opcode1 = i1->getOpcode();
						unsigned opcode2 = i2->getOpcode();
						errs() << opcode2 << "\n";
						//errs() << *i1 << ":" << *i2 << "\n";
						if (opcode1 == llvm::Instruction::Load && opcode2 == llvm::Instruction::Load){
							errs() << "found load instructions" << "\n";
							Value* op3 = i1->getOperand(0);
							Value* op4 = i2->getOperand(0);
				

							//Predicate code ICMP_UGT = 34; ICMP_SGT = 38
							if (inst->getPredicate() == 34 || inst->getPredicate() == 38){
								numOfValue = numOfValue + 2;
								errs() << "The correct state is :" << *op3 << " < " <<  *op4 << "\n";
								file << getValName(op3) << " " << getValName(op4) << " greater" << "\n"; 
							}

							//Predicate code ICMP_ULT = 36; ICMP_SLT = 40
							if (inst->getPredicate() == 36 || inst->getPredicate() == 40){
                            	numOfValue = numOfValue + 2;
                            	errs() << "The correct state is :" << *op3 << " > " <<  *op4 << "\n";
								file << getValName(op3) << " " << getValName(op4) << " lesser" << "\n";
                        	}
						}
						else
						{
							Value* op3 = i1->getOperand(1);
							Value* op4 = i2->getOperand(1);
							Instruction* i3 = static_cast<Instruction*>(i1->getOperand(1));
							Instruction* i4 = static_cast<Instruction*>(i2->getOperand(1));
							unsigned opcode3 = i3->getOpcode();
							unsigned opcode4 = i4->getOpcode();
							//errs() << *i3 << ":" << *i4 << "\n";
							if (opcode3 == llvm::Instruction::Load && opcode4 == llvm::Instruction::Load){
								errs() << "found load instructions" << "\n";
								//Predicate code ICMP_UGT = 34; ICMP_SGT = 38
								if (inst->getPredicate() == 34 || inst->getPredicate() == 38){
									numOfValue = numOfValue + 2;
									errs() << "The correct state is :" << *op3 << " > " <<  *op4 << "\n";
									file << getValName(op3) << " " << getValName(op4) << " greater" << "\n";
								}

								//Predicate code ICMP_ULT = 36; ICMP_SLT = 40
								if (inst->getPredicate() == 36 || inst->getPredicate() == 40){
									numOfValue = numOfValue + 2;
									errs() << "The correct state is :" << *op3 << " < " <<  *op4 << "\n";
									file << getValName(op3) << " " << getValName(op4) << " lesser" << "\n";
								}
							}
							else if (opcode3 == llvm::Instruction::Load && opcode4 != llvm::Instruction::Load){
								Value* op5 = i4->getOperand(1);
								Instruction* i5 = static_cast<Instruction*>(i4->getOperand(1));
								if (inst->getPredicate() == 34 || inst->getPredicate() == 38){
									numOfValue = numOfValue + 2;
									errs() << "The correct state is :" << *op3 << " >" <<  *op5 << "\n";
									file << getValName(op3) << " " << getValName(op5) << " greater" << "\n";
								}

								//Predicate code ICMP_ULT = 36; ICMP_SLT = 4
								if (inst->getPredicate() == 36 || inst->getPredicate() == 40){
									numOfValue = numOfValue + 2;
									errs() << "The correct state is :" << *op3 << " < " <<  *op5 << "\n";
									file << getValName(op3) << " " << getValName(op5) << " lesser" << "\n";
								}
							}
						}
					}
				}
			}
			return Pred;
		}
	}
	return nullptr;
}


bool TestPass::runOnModule(Module& m) {
	// Open output file (was previously opened at global scope with fragile static init)
	StringRef filename(name);
	llvm::raw_fd_ostream file(filename, EC, F_None);
	if (EC) {
		llvm::errs() << "Error opening file: " << EC.message() << "\n";
        return false;
	}

	//Read the common line file name from environment variable
	//Set by phase2.py before invoking this pass
	char *Filename = getenv("CONFD_COMMON_FILE");
	if (!Filename) {
		errs() << "Error: CONFD_COMMON_FILE environment variable not set\n";
		return false;
	}
	std::ifstream infile(Filename);
	std::string line;
	std::getline(infile, line);
	const char* string2 = line.c_str();

	//Reset global state for this run
	flag = 0;
	numOfValue = 0;
	S = StringRef();

	
    for(auto& F : m){
        for (auto& B : F) {
            for (auto& I : B) {
				//errs() << I << "\n";
				std::string str;
				llvm::raw_string_ostream ss(str);
				ss << I;
				const char* string1 = ss.str().c_str();

				//Searches for the common error line in each instruction
				// Normalize: trim leading whitespace from both, strip !dbg metadata from both
				std::string s1_norm(string1);
				size_t pos1 = s1_norm.find_first_not_of(" \t");
				if (pos1 != std::string::npos) s1_norm = s1_norm.substr(pos1);
				size_t dbg1 = s1_norm.find(", !dbg");
				if (dbg1 != std::string::npos) s1_norm = s1_norm.substr(0, dbg1);

				std::string s2_norm(string2);
				size_t pos2 = s2_norm.find_first_not_of(" \t");
				if (pos2 != std::string::npos) s2_norm = s2_norm.substr(pos2);
				size_t dbg2 = s2_norm.find(", !dbg");
				if (dbg2 != std::string::npos) s2_norm = s2_norm.substr(0, dbg2);

				if (s1_norm == s2_norm)
				{
					errs() << "it's a match" << "\n";
					//When the instruction is found, goes to predecessor Basic Block to find the involved parameter
					BasicBlock* B1 = predecessorBB(&B, file);
					errs() << numOfValue << "\n";
					if (numOfValue < 2){
						//Goes to predecessor Basic Block of the predecessor Basic Block to find another involved parameter
						BasicBlock* B2 = predecessorBB(B1, file);
					}
				}
			}
		}
	}
	return false;
}

}

//Registers the pass as 'test', the library name is 'libTestPass.so'
char TestPass::ID = 0;
static RegisterPass<TestPass> SCCReg("test", "Test Pass");
