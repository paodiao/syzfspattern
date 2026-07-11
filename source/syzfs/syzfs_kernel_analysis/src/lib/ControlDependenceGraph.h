#ifndef CONTROL_DEPENDENCE_GRAPH_H
#define CONTROL_DEPENDENCE_GRAPH_H

#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/ADT/BreadthFirstIterator.h"
#include "llvm/IR/CFG.h"
#include <vector>
#include <map>
#include <list>
#include <set>

using namespace llvm;

class ControlDependenceGraph {
public:
  // 控制依赖信息结构
  struct ControlDependenceInfo {
    BasicBlock *controller;  // 控制基本块
    bool condition;          // 控制条件 (true=真分支, false=假分支)
  };
  
  // 被控制的基本块信息结构
  struct DependentBlockInfo {
    BasicBlock *dependent;   // 被控制的基本块
    bool condition;          // 控制条件 (true=真分支, false=假分支)
  };

  // 构造函数：基于函数和后支配树构建控制依赖图
  ControlDependenceGraph(Function &F, PostDominatorTree &PDT) {
    buildControlDependenceGraph(F, PDT);
  }

  // 获取基本块的所有控制依赖
  std::vector<ControlDependenceInfo> getDependencies(BasicBlock *BB) {
    std::vector<ControlDependenceInfo> dependencies;
    auto range = cdg_map.equal_range(BB);
    for (auto it = range.first; it != range.second; ++it) {
      dependencies.push_back(it->second);
    }
    return dependencies;
  }

  // 获取控制特定基本块的所有控制器
  std::vector<BasicBlock*> getControllers(BasicBlock *BB) {
    std::vector<BasicBlock*> controllers;
    auto range = cdg_map.equal_range(BB);
    for (auto it = range.first; it != range.second; ++it) {
      controllers.push_back(it->second.controller);
    }
    return controllers;
  }

  // 获取某个控制器控制的所有基本块
  std::vector<DependentBlockInfo> getDependents(BasicBlock *controller) {
    std::vector<DependentBlockInfo> dependents;
  
    auto range = reverse_cdg_map.equal_range(controller);
    for (auto it = range.first; it != range.second; ++it) {
      dependents.push_back(it->second);
    }
  
    return dependents;
  }

  // 判断基本块是否控制依赖于另一个基本块
  bool isControlDependent(BasicBlock *dependent, BasicBlock *controller) {
    auto range = cdg_map.equal_range(dependent);
    for (auto it = range.first; it != range.second; ++it) {
      if (it->second.controller == controller) {
        return true;
      }
    }
    return false;
  }

  // 打印控制依赖图
  void print(raw_ostream &OS) {
    for (auto &entry : cdg_map) {
      BasicBlock *dependent = entry.first;
      ControlDependenceInfo info = entry.second;
      OS << dependent->getName() << " depends on " 
         << info.controller->getName() << " ("
         << (info.condition ? "T" : "F") << ")\n";
    }
  }

private:
  // 控制依赖图映射：被控制的基本块 -> 控制信息
  std::multimap<BasicBlock *, ControlDependenceInfo> cdg_map;
  // 反向
  std::multimap<BasicBlock *, DependentBlockInfo> reverse_cdg_map;


  // 构建控制依赖图的核心方法
  void buildControlDependenceGraph(Function &F, PostDominatorTree &PDT) {
    // 遍历所有基本块
    for (BasicBlock *BB : breadth_first(&F)) {
      const Instruction *TInst = BB->getTerminator();
      int branch_cnt = TInst->getNumSuccessors();
      
      // 只处理条件分支（有两个后继）
      if (branch_cnt != 2)
        continue;
        
      // 检查两个分支
      for (int i = 0; i < 2; i++) {
        const BasicBlock *BB_succ = TInst->getSuccessor(i);
        
        // 如果后继后支配当前块，则跳过（没有控制依赖）
        bool isPDom = PDT.dominates(BB_succ, BB);
        if (isPDom)
          continue;
        
        // 在后支配树中向上遍历，找到控制依赖的边界
        DomTreeNode *dtnode_end = PDT.getNode(BB)->getIDom();
        DomTreeNode *dtnode_iterator_BB_succ = PDT.getNode(BB_succ);
        
        while (dtnode_iterator_BB_succ != dtnode_end) {
          ControlDependenceInfo info;
          info.controller = BB;
          info.condition = (i == 0); // true for first successor, false for second
          
          // 记录控制依赖关系
          cdg_map.emplace(dtnode_iterator_BB_succ->getBlock(), info);

          // 同时记录反向映射
          DependentBlockInfo reverse_info;
          reverse_info.dependent = dtnode_iterator_BB_succ->getBlock();
          reverse_info.condition = info.condition;
          reverse_cdg_map.emplace(BB, reverse_info);
          
          // 向上遍历后支配树
          dtnode_iterator_BB_succ = dtnode_iterator_BB_succ->getIDom();
        }
      }
    }
  }
};

#endif // CONTROL_DEPENDENCE_GRAPH_H