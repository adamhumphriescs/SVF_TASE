//===- svf-ex.cpp -- A driver example of SVF-------------------------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013->  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===-----------------------------------------------------------------------===//

/*
 // A driver program of SVF including usages of SVF APIs
 //
 // Author: Yulei Sui,
 */

#include "SVF-LLVM/LLVMUtil.h"
#include "Graphs/SVFG.h"
#include "WPA/Andersen.h"
#include "llvm/IR/Metadata.h"
#include "SVF-LLVM/SVFIRBuilder.h"
#include "Util/Options.h"
#include "SVF-LLVM/SymbolTableBuilder.h"

using namespace llvm;
using namespace std;
using namespace SVF;

void addMD( Instruction* inst) {
  inst->setMetadata("tainted", MDNode::get(inst->getContext(), llvm::None));
}


Set<NodeID> traverseOnVFG_Sara(SVFG* vfg, Value* val) {
  auto *pag = SVFIR::getPAG();
  auto *svfVal = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(val);
  auto *pNode = pag->getGNode(pag->getValueNode(svfVal));
  const auto *vNode = vfg->getDefSVFGNode(pNode);

  Set<NodeID> visited;
  FIFOWorkList<const VFGNode*> worklist;
  Set<NodeID> icfgIDs;

  worklist.push(vNode);
  visited.insert(vNode->getId());
  icfgIDs.insert(vNode->getICFGNode()->getId());

  printf("\ntraversing VFG\n");
 
  /// Traverse along VFG
  while ( !worklist.empty() ) {
    const auto *vNode = worklist.pop();

    printf("checking vNode: %u\n", vNode->getICFGNode()->getId());
    
    for ( auto *edge : vNode->getOutEdges() ) {
      if ( edge->isDirectVFGEdge() ) {
        auto succID = edge->getDstID();
        auto *succNode = edge->getDstNode();
	auto s_icfgID = succNode->getICFGNode()->getId();

	printf("\tdst Node: %u\n", s_icfgID);
	
	if ( visited.find(succID) == visited.end() ) {
	  visited.insert(succID);
	  worklist.push(succNode);
	  icfgIDs.insert(s_icfgID);
	  printf("\tdst Node %u is new use\n", s_icfgID);
	}
      }
    }

    for ( auto *edge : vNode->getInEdges() ) {
      if ( edge->isDirectVFGEdge() ) {
        auto prevID = edge->getSrcID();
        auto *prevNode = edge->getSrcNode();
	auto p_icfgID = prevNode->getICFGNode()->getId();

	printf("\tsrc Node: %u\n", p_icfgID);
	
	if (visited.find(prevID) == visited.end() ) {
	  visited.insert(prevID);
	  worklist.push(prevNode);
	  icfgIDs.insert(p_icfgID);
	  printf("\tsrc Node %u is new use\n", p_icfgID);
	}
      }
    }
  }
    
  return icfgIDs;
}


Set<NodeID> SymVal_successors(const VFGNode* vNode, SVFG* vfg) {
  auto *pag = SVFIR::getPAG();
  
  Set<NodeID> visited;
  FIFOWorkList<const VFGNode*> worklist;
  Set<NodeID> icfgIDs;
    
  worklist.push(vNode);
  visited.insert(vNode->getId());
  icfgIDs.insert(vNode->getICFGNode()->getId());

  printf("\ntraversing successors\n");

  /// Traverse along VFG
  while (!worklist.empty()) {
    const auto *vNode = worklist.pop();

    printf("Searching %lu successors for Node %u, ICFG_ID: %u\n", vNode->getOutEdges().size(), vNode->getId(), vNode->getICFGNode()->getId());
    
    for ( auto *edge : vNode->getOutEdges() ) {
      bool setConstant = false;
	    
      auto *succNode = edge->getDstNode();
      auto succID = edge->getDstID();
      auto icfgID = succNode->getICFGNode()->getId();

      printf("SuccID: %u, icfgID: %u\n", succID, icfgID);
      
      //If a tainted variable gets overwritten with constant data, 
      //then taint it but do not traverse any further down this path.
      if ( auto *stmtNode = dyn_cast<StmtSVFGNode>(succNode) ) {   
	if ( SVFUtil::isa<StoreStmt>( stmtNode->getPAGEdge() ) ) {
	  const auto *val = stmtNode->getPAGEdge()->getSrcNode()->getValue();
	  auto *pNode = pag->getGNode(pag->getValueNode(val));

	  if( pNode->isConstDataOrAggDataButNotNullPtr() ) {
	    setConstant = true;
	    icfgIDs.insert(icfgID);
	    printf("successor node %u overwrites with constant data\n", icfgID);
	  }
	}
      }
	    
      if ( visited.find(succID) == visited.end() && !setConstant ) {
	visited.insert(succID);
	worklist.push(succNode);
	icfgIDs.insert(icfgID);
	printf("Adding successor %u to worklist\n", succID);
      } 
    }
  }
  return icfgIDs;
}


// given Set of nodes 'visited' and starting point vNode, search forward for the earliest Store statement,
// adding it to visited and return it
// if none found, return vNode
const VFGNode* verify_succ(const VFGNode* vNode, Set<NodeID> &visited) {
  printf("\nverifying %lu successors of node %u\n", vNode->getOutEdges().size(), vNode->getId());
  
  for ( auto *edge : vNode->getOutEdges() ) {
    auto succID = edge->getDstID();
    auto* succNode = edge->getDstNode();

    if ( edge->isDirectVFGEdge() && (visited.find(succID) == visited.end()) ) {
      if ( auto *stmtNode = dyn_cast<StmtSVFGNode>(succNode) ) {   
	if ( SVFUtil::isa<StoreStmt>(stmtNode->getPAGEdge()) ) {
	  printf("Store statement found in successors: node %u\n", succID);
	  visited.insert(succID);
	  return succNode;
	}
      }
    }  
  }
  return vNode;
}


// find all predecessors of vNode in the Value Flow Graph, store in visited
// return last node found
const VFGNode* iterate_predecessors(const VFGNode* vNode, Set<NodeID> &visited) {
  FIFOWorkList<const VFGNode*> worklist;
  worklist.push(vNode);

  printf("\nIterating predecessors of node %u, ICFG_ID: %u\n", vNode->getId(), vNode->getICFGNode()->getId());
  
  /// Traverse along VFG
  while ( !worklist.empty() ) {  
    vNode = worklist.pop();

    printf("checking %lu in-edges of node %u\n", vNode->getInEdges().size(), vNode->getId());
    
    for ( auto *edge : vNode->getInEdges() ) {
      auto prevID = edge->getSrcID();
      auto *prevNode = edge->getSrcNode();
      
      if ( ( visited.find(prevID) == visited.end() ) && edge->isDirectVFGEdge() && prevNode->getNodeKind() == VFGNode::ARet ) {
	printf("adding predecessor node from edge (%u -> %u) / (%u -> %u)\n", prevID, vNode->getId(), prevNode->getICFGNode()->getId(), vNode->getICFGNode()->getId());
	visited.insert(prevID);
	worklist.push(prevNode);
      }
    }    
  }
  return vNode;   
}


const VFGNode* find_defSymVal(Value* val, SVFG* vfg){
  auto *pag = SVFIR::getPAG();
  auto *svfVal = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(val);
  auto *pNode = pag->getGNode(pag->getValueNode(svfVal));

  printf("\nfind symval def\n");

  Set<NodeID> visited;
  const auto *vNode = vfg->getDefSVFGNode(pNode);
  
  const auto *temp = iterate_predecessors(vNode, visited);
  vNode = verify_succ(temp, visited);

  while ( temp != vNode ) {
    temp = iterate_predecessors(vNode, visited);
    vNode = verify_succ(temp, visited);
  }

  return vNode;
}


CallInst* find_callSite(Module* mM){
  for ( auto &Fn : mM->getFunctionList() ) {
    for ( auto &BB : Fn ) {
      for ( auto &Inst : BB ) {
	if ( isa<CallInst>(&Inst) ) {
	  std::string str;
	  llvm::raw_string_ostream ss(str);
	  ss << Inst;
		    
	  if ( str.find("make_byte_symbolic") != std::string::npos ){ 
	    return dyn_cast<CallInst>(&Inst);
	  }
	}
      }
    }
  }
  return nullptr;
}


void taint_instructions_sara (CallInst* cs, Value* val, ICFG* icfg,  Module* mM, Set<NodeID> icfgIDs, Function * Fn, bool &set , bool &beginTaint){ 
  Fn->setMetadata("taintedFun", MDNode::get(Fn->getContext(), llvm::None));
  
  printf("\n%lu ICFG IDs\n", icfgIDs.size());
  printf("\ntainting in fxn %s\n", std::string(Fn->getName()).c_str());
  
  for ( auto &BB : *Fn ) {    
    for ( auto &Inst : BB ) {

      // start tainting if we reach the make_byte_symbolic callsite
      if ( cs == dyn_cast<CallInst>(&Inst) ) {
	printf("Encountered MBS callsite, starting taint propogation\n");
	beginTaint = true;

      // regular callsite -> check instructions for the call
      } else if ( isa<CallInst>(&Inst) ) {

	auto *cInst = dyn_cast<CallInst>(&Inst);
	StringRef funName = cInst->getCalledFunction()->getName();

	printf("\ndropping into call %s\n", std::string(funName).c_str());
	taint_instructions_sara( cs, val, icfg, mM, icfgIDs, mM->getFunction(funName), set, beginTaint );
	printf("exiting callsite\n\n");
      }
	    
      const auto *svfInst = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(&Inst);
      auto id = icfg->getICFGNode(svfInst)->getId();

      printf("checking ICFG_ID: %u\n", id);

      // instr uses the tainted value
      if ( icfgIDs.find(id) != icfgIDs.end() && beginTaint ) {
	printf("tainting instruction\n");
	addMD(&Inst);

	// opcode 53 is a cmp where the next instr depends on the cmp
	// but svf doesn't link the two
	if ( Inst.getOpcode() == 53 ) {
	  set = true;
	}
      } else if ( set ) {
	printf("tainting instruction\n");
        addMD(&Inst);
	set = false;
      }
    }
  }
}

void taint_functions_sara (SVFG* vfg, ICFG* icfg, Module* mM) {
  // find callsite for fxn void make_byte_symbolic(void*)
  auto *cs = find_callSite(mM);
  if ( cs == nullptr ) {
    return;
  }
  
  auto *val = cs->getArgOperand(0);
  auto icfgIDs = SymVal_successors(find_defSymVal(val, vfg), vfg);
  auto *Fn =  mM->getFunction("main");
    
  if ( Fn == nullptr ) {
    Fn = mM->getFunction("begin_target_inner");   
  }
    
  bool beginTaint = false;
  bool set = false;

  taint_instructions_sara(cs, val, icfg, mM, icfgIDs, Fn, set, beginTaint);
}



int main(int argc, char ** argv) {
  auto moduleNameVec = OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis", "[options] <input-bitcode...>");
  auto *mset = LLVMModuleSet::getLLVMModuleSet();
  
  if ( Options::WriteAnder() == "ir_annotator" ) {
    mset->preProcessBCs(moduleNameVec);
  }

  auto *svfModule = LLVMModuleSet::buildSVFModule(moduleNameVec);

  /// Build Program Assignment Graph (SVFIR)
  SVFIRBuilder builder(svfModule);
  auto *pag = builder.build();

  /// Create Andersen's pointer analysis
  auto *ander = AndersenWaveDiff::createAndersenWaveDiff(pag);

  /// Call Graph
  auto* callgraph = ander->getPTACallGraph();

  /// ICFG
  auto* icfg = pag->getICFG();

  /// Value-Flow Graph (VFG)
  auto* vfg = new VFG(callgraph);

  /// Sparse value-flow graph (SVFG)
  SVFGBuilder svfBuilder(true);
  auto* svfg = svfBuilder.buildFullSVFG(ander);
  auto *mM = mset->getMainLLVMModule();
  taint_functions_sara(svfg, icfg, mM);

  mset->dumpModulesToFile(".svf.bc");
  
  delete vfg;

  AndersenWaveDiff::releaseAndersenWaveDiff();
  SVFIR::releaseSVFIR();
  SVF::LLVMModuleSet::releaseLLVMModuleSet();
  llvm::llvm_shutdown();
  return 0;
}

