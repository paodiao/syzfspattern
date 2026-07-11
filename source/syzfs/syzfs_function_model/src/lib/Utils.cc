#include <llvm/IR/DebugInfo.h>
#include <llvm/Pass.h>
#include <llvm/IR/Instructions.h>
#include "llvm/IR/Instruction.h"
#include <llvm/Support/Debug.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Constants.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Analysis/CallGraph.h>
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"  
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/BasicBlock.h" 
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include <llvm/IR/LegacyPassManager.h>
#include <map> 
#include <vector> 
#include <queue>
#include <fstream>
#include "llvm/IR/CFG.h" 
#include "llvm/Transforms/Utils/BasicBlockUtils.h" 
#include "llvm/IR/IRBuilder.h"

#include "Utils.h"
#include "Config.h"
#include "Common.h"

bool isSyscall(Function* F) {
	string FuncName = static_cast<string>(F->getName());
	if (FuncName.size() > 0) {
		if (startsWith(FuncName, "__do_sys_") || startsWith(FuncName, "__se_sys_")) {
			return true;
		}
		if (startsWith(FuncName, "__x64_sys_")) {
			return true;
		}
	}
	return false;
}

string getSyscallName(Function* F) {
	string FuncName = static_cast<string>(F->getName());
	if (FuncName.size() > 0) {
		if (startsWith(FuncName, "__do_sys_") || startsWith(FuncName, "__se_sys_")) {
			return FuncName.substr(9);
		}
		if (startsWith(FuncName, "__x64_sys_")) {
			return FuncName.substr(10);
		}
	}
	return "";
}

bool is_power_of_2(uint64_t n)
{
	return n != 0 && (n & (n - 1)) == 0;
}

std::vector<uint64_t> splitToPowersOfTwo(uint64_t num) {
    std::vector<uint64_t> result;
    
    uint64_t mask = 1;
    while (num) {
        if (num & 1) {
            result.push_back(mask);
        }
        num >>= 1;
        mask <<= 1;
    }
    
    return result;
}

std::vector<uint32_t> splitToPowersOfTwo32bits(uint32_t num) {
    std::vector<uint32_t> result;
    
    uint32_t mask = 1;
    while (num) {
        if (num & 1) {
            result.push_back(mask);
        }
        num >>= 1;
        mask <<= 1;
    }
    
    return result;
}

Instruction* getNextInstruction(Instruction* I) {
    // 获取当前指令所在的基块
    BasicBlock* BB = I->getParent();
    if (!BB) return nullptr; // 如果指令没有所属基本块，返回nullptr

    // 在基本块中查找当前指令的迭代器
    auto it = I->getIterator();
    ++it; // 移动到下一条指令
    if (it == BB->end()) {
        return nullptr; // 如果已经是最后一条指令，返回nullptr
    }
    return &(*it);
}

bool endsWith(std::string const & value, std::string const & ending)
{
    if (ending.size() > value.size()) return false;
    return std::equal(ending.rbegin(), ending.rend(), value.rbegin());
}

int startsWith(string s, string prefix) {
  return s.find(prefix) == 0?1:0;
}

std::ifstream& gotoLine(std::ifstream& file, unsigned int num){
    file.seekg(std::ios::beg);
    for(int i=0; i < num - 1; ++i){
        file.ignore(std::numeric_limits<std::streamsize>::max(),'\n');
    }
    return file;
}

void strip(string &str) {
    if  (str.length() != 0) {
      auto w = string(" ");
      auto n = string("\n");
      auto r = string("\t");
      auto t = string("\r");
      auto z = string("\x00");
      auto v = string(1 ,str.front()); 
      while((v == w) || (v==t) || (v==r) || (v==n) || (v==z)) {
          str.erase(str.begin());
          v = string(1 ,str.front());
      }
      v = string(1 , str.back()); 
      while((v ==w) || (v==t) || (v==r) || (v==n) || (v==z)) {
          str.erase(str.end() - 1 );
          v = string(1 , str.back());
      }
    }
  }

int getIntValue(Value* value) {
    auto constVal = dyn_cast<ConstantInt>(value);
    if (constVal) {
        return constVal->getZExtValue();
    } else {
        outs() << "[-] Non-constant int: " << *value << "\n";
        if (auto loadInst = dyn_cast<LoadInst>(value)) {
            auto addr = loadInst->getPointerOperand();
            outs() << "\t[-] Address: " << *addr << "\n";
            return getIntValue(addr);
        } else if (auto binaryInst = dyn_cast<BinaryOperator>(value)) {
            auto op1 = binaryInst->getOperand(0);
            auto op2 = binaryInst->getOperand(1);
            outs() << "\t[-] Op1: " << *op1 << "\n";
            outs() << "\t[-] Op2: " << *op2 << "\n";

        } else if (auto gv = dyn_cast<GlobalVariable>(value)) {
            auto initializer = gv->getInitializer();
            if (initializer) {
                return getIntValue(initializer);
            } else {
                outs() << "\t[-] No initializer for global variable: " << *value << "\n";   
            }
        }
        return -1;
    }
}

// from DIFUZE
string getDeviceString(Value *currVal) {
    const GEPOperator *gep = dyn_cast<GEPOperator>(currVal);
    const llvm::GlobalVariable *strGlobal = nullptr;
    if(gep != nullptr) {
        strGlobal = dyn_cast<GlobalVariable>(gep->getPointerOperand());
    }
    if (strGlobal != nullptr && strGlobal->hasInitializer()) {
        const Constant *currConst = strGlobal->getInitializer();
        const ConstantDataArray *currDArray = dyn_cast<ConstantDataArray>(currConst);
        string res = "";
        raw_string_ostream ss(res);
        if(currDArray != nullptr) {
            ss << currDArray->getAsCString();
        } else {
            ss << *currConst;
        }
        return ss.str();
    }
    if (auto currDArray = dyn_cast<ConstantDataArray>(currVal)) {
        string res = "";
        raw_string_ostream ss(res);
        ss << currDArray->getAsString();
        return ss.str();
    }
    return "?";
}

Value* getStructValue(Value* value) {
    auto handlerStructGV = dyn_cast<GlobalVariable>(value);
    if (handlerStructGV && handlerStructGV->hasInitializer()) {
        auto initializer = handlerStructGV->getInitializer();
        if (initializer) {
            auto handlerStruct = dyn_cast<ConstantStruct>(initializer);
            if (handlerStruct) {
                return dyn_cast<Value>(handlerStruct);
                outs() << "[+] Struct value: " << *handlerStruct << "\n";
            } else {
                outs() << "[-] Non-constant struct value: " << *(initializer) << "\n";
                outs() << "\t[-] Users: \n";
                for (auto user : handlerStructGV->users()) {
                    outs() << "\t\t" << *user << "\n";
                } 
            }
        } else {
            outs() << "[-] No initializer for struct: " << *value << "\n";
        }
    } else if (auto bitcastOp = dyn_cast<BitCastOperator>(value)) {
        outs() << "[-] BitCastOp: " << *bitcastOp << "\n";
        auto castVal = bitcastOp->getOperand(0);
        outs() << "\t[-] CastVal: " << *castVal << "\n";
        return getStructValue(castVal);
    } else {
        outs() << "[-] Local struct: " << *value << "\n";
        if (isa<PHINode>(value)) {
            auto phiVal = dyn_cast<PHINode>(value);
            // TODO: phi node 
            return getStructValue(phiVal->getIncomingValue(0));
        }
        if (isa<Argument>(value)) {
            outs() << "\t[-] Argument: " << *value << "\n";
        }
    }
    return nullptr;
}


vector<GetElementPtrInst*> getGepInstByStructName(Function* F, StringRef srcTypeName, StringRef resTypeName)
{
    vector<GetElementPtrInst*> res;
    for(inst_iterator iter = inst_begin(F); iter != inst_end(F); iter++)
    {
        Instruction* I = &*iter;
        if(I->getOpcode() == Instruction::GetElementPtr)
        {
            GetElementPtrInst* gepInst = dyn_cast<GetElementPtrInst>(I);
            if(!gepInst->getSourceElementType()->isStructTy())
            {
                continue;
            }
            if(gepInst->getSourceElementType()->getStructName() == srcTypeName)
            {
                if(!gepInst->getResultElementType()->isPointerTy())
                {
                    continue;
                }
                if(!gepInst->getResultElementType()->getPointerElementType()->isStructTy())
                    continue;
                if(gepInst->getResultElementType()->getPointerElementType()->getStructName() == resTypeName)
                    res.push_back(gepInst);

            }
        }
    }
    return res;
}

Function* getFunctionFromModules(StringRef funcName)
{
    Function* func = nullptr; 
   for(pair<Module*, StringRef> item : GlobalCtx.Modules)
    {
        Module* M = item.first;
        Function* tmp = M->getFunction(funcName);
        if(tmp != nullptr && !tmp->isDeclaration() && tmp->getInstructionCount() > 0)
        {
            func = tmp;
            break;
        }
    }
    return func;
}

int getBasicBlockIndex(BasicBlock* BB)
{
    Function* F = BB->getParent();
    int i = -1;
    for(auto iter = F->begin(); iter != F->end(); iter++)
    {
        i++;
        BasicBlock* bb = &*iter;
        if(bb == BB)
        {
            break;
        }
    }
    return i;
}

void outputBBInfo(BasicBlock* BB, raw_fd_ostream& outfile)
{
    outfile << "++++++++++++++++++++++++++++++++" << "\n";
    if(BB != nullptr)
    {
        Function* F = BB->getParent();
        Module* M = F->getParent();
        outfile << "src file name: " << M->getSourceFileName() << "\n";
        outfile << "function name: " << F->getName() << "\n";
        int idx = getBasicBlockIndex(BB);
        outfile << "basicblock id: " << idx << "\n";
    }
    outfile << "++++++++++++++++++++++++++++++++" << "\n";
}


// //要返回handler function和target block（block所在函数+block id），用来拼接到输出中
// void getOutputInfo(BasicBlock* BB)

string getValueAsOperand(Value* v){
    string result="";
    if(!v)
        return result;
// #ifdef DEBUG_CUSTOM
    llvm::raw_string_ostream output(result);
    v->printAsOperand(output);
// #endif
    return result;
}