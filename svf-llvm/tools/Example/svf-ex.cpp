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

using namespace llvm;
using namespace std;
using namespace SVF;

void addMD( Instruction* inst)
{
    std::string str = "tainted";
    inst->setMetadata(str, MDNode::get(inst->getContext(), llvm::None));
}

/*
void getMD(Instruction * inst)
{
    if (inst->getMetadata("tainted"))
    {
        cout << "yeaaah\n";
    }
    }*/
/*!
 * An example to query alias results of two LLVM values
 */
/*SVF::AliasResult aliasQuery(PointerAnalysis* pta, Value* v1, Value* v2)
{
    return pta->alias(v1,v2);
}
*/
/*!
 * An example to print points-to set of an LLVM value
 */
/*std::string printPts(PointerAnalysis* pta, Value* val)
{

    std::string str;
    raw_string_ostream rawstr(str);

    NodeID pNodeId = pta->getPAG()->getValueNode(val);
    const PointsTo& pts = pta->getPts(pNodeId);
    for (PointsTo::iterator ii = pts.begin(), ie = pts.end();
            ii != ie; ii++)
    {
        rawstr << " " << *ii << " ";
        PAGNode* targetObj = pta->getPAG()->getGNode(*ii);
        if(targetObj->hasValue())
        {
            rawstr << "(" <<*targetObj->getValue() << ")\t ";
        }
    }

    return rawstr.str();

    }*/


/*!
 * An example to query/collect all successor nodes from a ICFGNode (iNode) along control-flow graph (ICFG)
 */
void traverseOnICFG(ICFG* icfg, const Instruction* inst)
{
    const SVFInstruction* svfInst = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(inst);
    ICFGNode* iNode = icfg->getICFGNode(svfInst);
    FIFOWorkList<const ICFGNode*> worklist;
    Set<const ICFGNode*> visited;
    worklist.push(iNode);

    /// Traverse along VFG
    while (!worklist.empty())
    {
        const ICFGNode* vNode = worklist.pop();
        for (ICFGNode::const_iterator it = vNode->OutEdgeBegin(), eit =
                    vNode->OutEdgeEnd(); it != eit; ++it)
        {
            ICFGEdge* edge = *it;
            ICFGNode* succNode = edge->getDstNode();
            if (visited.find(succNode) == visited.end())
            {
                visited.insert(succNode);
                worklist.push(succNode);
            }
        }
    }
}

/*!
 * An example to query/collect all the uses of a definition of a value along value-flow graph (VFG)
 */
void traverseOnVFG(const SVFG* vfg, Value* val)
{
    SVFIR* pag = SVFIR::getPAG();

    SVFValue* svfVal = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(val);
    PAGNode* pNode = pag->getGNode(pag->getValueNode(svfVal));
    const VFGNode* vNode = vfg->getDefSVFGNode(pNode);
    FIFOWorkList<const VFGNode*> worklist;
    Set<const VFGNode*> visited;
    worklist.push(vNode);

    /// Traverse along VFG
    while (!worklist.empty())
    {
        const VFGNode* vNode = worklist.pop();
        for (VFGNode::const_iterator it = vNode->OutEdgeBegin(), eit =
                    vNode->OutEdgeEnd(); it != eit; ++it)
        {
            VFGEdge* edge = *it;
            VFGNode* succNode = edge->getDstNode();
            if (visited.find(succNode) == visited.end())
            {
                visited.insert(succNode);
                worklist.push(succNode);
            }
        }
    }

    /// Collect all LLVM Values
    for(Set<const VFGNode*>::const_iterator it = visited.begin(), eit = visited.end(); it!=eit; ++it)
    {
        // const VFGNode* node = *it;
        // //can only query VFGNode involving top-level pointers (starting with % or @ in LLVM IR)
        // PAGNode* pNode = vfg->getLHSTopLevPtr(node);
        // Value* val = pNode->getValue();
    }
}

/*!
 * An example to query/collect all the uses of a definition of a value along value-flow graph (VFG)
 */
Set<NodeID> traverseOnVFG_Sara(SVFG* vfg, Value* val)
{
     SVFIR* pag = SVFIR::getPAG();
     SVFValue* svfVal = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(val);
     printf("En el traverse\n");
    //outs() << *val << "\n";
    PAGNode* pNode = pag->getGNode(pag->getValueNode(svfVal));
    printf("PNODE\n");
    //outs()<< *(pNode->getValue()) << "\n";
    const VFGNode* vNode = vfg->getDefSVFGNode(pNode);
    Set<NodeID> visited;
    FIFOWorkList<const VFGNode*> worklist;
    //Set<const VFGNode*> visited;
    Set<NodeID> icfgIDs;
    worklist.push(vNode);
    visited.insert(vNode->getId());
    icfgIDs.insert(vNode->getICFGNode()->getId());

    /// Traverse along VFG
    while (!worklist.empty())
    {
        const VFGNode* vNode = worklist.pop();
       
        //outs()<< "VNODE"<< *(vNode->getValue()) <<" THE ICFGID " << vNode->getICFGNode()->getId() <<"\n";

        for (VFGNode::const_iterator it = vNode->OutEdgeBegin(), eit =
                    vNode->OutEdgeEnd(); it != eit; ++it)
        {
            VFGEdge* edge = *it;
            
            if (edge->isDirectVFGEdge())
            {
            NodeID succID = edge->getDstID();
            VFGNode* succNode = edge->getDstNode();
            NodeID s_icfgID = succNode->getICFGNode()->getId();
            
            //outs()<< "SUCCNODE"<<" THE ICFGID " << s_icfgID <<"\n";
            if (visited.find(succID) == visited.end())// || s_visited.find(succNode) == s_visited.end())
            {
                //visited.insert(succNode);
                visited.insert(succID);
                worklist.push(succNode);
               icfgIDs.insert(s_icfgID);
                //outs()<<"Inside the succ if else\n";   
            }
            }
            else{
                VFGNode* succNode = edge->getDstNode();
                outs()<< succNode->toString();
            }
        }
        for (VFGNode::const_iterator it = vNode->InEdgeBegin(), eit =
                    vNode->InEdgeEnd(); it != eit; ++it)
        {
            VFGEdge* edge = *it;
            
            if (edge->isDirectVFGEdge())
            {
            NodeID prevID = edge->getSrcID();
            VFGNode* prevNode = edge->getSrcNode();
            NodeID p_icfgID = prevNode->getICFGNode()->getId() ;
            //outs()<< "PREVNODE"<<" THE ICFGID " << p_icfgID <<"\n";
            if (visited.find(prevID) == visited.end() ) //|| p_visited.find(prevNode) == p_visited.end() )
            {
                visited.insert(prevID);
                worklist.push(prevNode);
                icfgIDs.insert(p_icfgID);
                //outs()<<"Inside the prev if else\n";   
            }
            }
            else{
                VFGNode* prevNode = edge->getSrcNode();
                outs()<< prevNode->toString();
            }
        }
    }
    return icfgIDs;
}

Set<NodeID> SymVal_succesors (const VFGNode* vNode, SVFG* vfg){
    SVFIR* pag = SVFIR::getPAG();
    outs()<<"En el symval successors\n";
    Set<NodeID> visited;
    FIFOWorkList<const VFGNode*> worklist;
    Set<NodeID> icfgIDs;
    worklist.push(vNode);
    visited.insert(vNode->getId());
    icfgIDs.insert(vNode->getICFGNode()->getId());

    /// Traverse along VFG
    while (!worklist.empty())
    {
        const VFGNode* vNode = worklist.pop();
        for (VFGNode::const_iterator it = vNode->OutEdgeBegin(), eit =
                    vNode->OutEdgeEnd(); it != eit; ++it)
        {
            bool constant = 1;
            const VFGEdge* edge = *it;
            NodeID succID = edge->getDstID();
            VFGNode* succNode = edge->getDstNode();
            NodeID icfgID = succNode->getICFGNode()->getId() ;
            
            outs()<< "succNode"<< succNode->toString() <<" and THE ICFGNode " << succNode->getICFGNode()->toString() <<"\n";
            
            //If a tainted variable gets overwritten with constant data, 
            //then taint it but do not traverse any further down this path.
            if (StmtSVFGNode* stmtNode = dyn_cast<StmtSVFGNode>(succNode)) {   
                if (SVFUtil::isa<StoreStmt>(stmtNode->getPAGEdge())){
                    const SVFInstruction* instr = stmtNode->getInst();
		    const SVFValue* val = dyn_cast<SVFCallInst>(instr)->getArgOperand(0);
                    PAGNode* pNode = pag->getGNode(pag->getValueNode(val));
		    //                    if (pNode->isConstantData())
		    if( pNode->isConstDataOrAggDataButNotNullPtr() )
                    {
                         constant = 0;
                         icfgIDs.insert(icfgID);
                         outs()<< "It is constant Data: "<< instr;
                    }  
                }
            }
            if (visited.find(succID) == visited.end() && constant) 
            {
                visited.insert(succID);
                worklist.push(succNode);
                icfgIDs.insert(icfgID);
                outs()<<"Inserting Node "<< succNode->toString() <<" \n";   
            } 
        }
    }
    return icfgIDs;
}

const VFGNode* verify_succ(const VFGNode* vNode, Set<NodeID> &visited)
{
    outs()<<"Printing vnode in verifysucc " <<vNode->toString()<< "\n";
    for (VFGNode::const_iterator it = vNode->OutEdgeBegin(), eit =
                vNode->OutEdgeEnd(); it != eit; ++it)
    {
        VFGEdge* edge = *it;
        NodeID succID = edge->getDstID();
        VFGNode* succNode = edge->getDstNode();
        outs()<<"Printing succNode in verifysucc" <<succNode->toString()<< "\n"; 
        if (edge->isDirectVFGEdge() && (visited.find(succID) == visited.end())){
            if (StmtSVFGNode* stmtNode = dyn_cast<StmtSVFGNode>(succNode)) {   
                if (SVFUtil::isa<StoreStmt>(stmtNode->getPAGEdge())){
                    visited.insert(succID);
                    outs()<<"Printing store succNode in verifysucc" <<succNode->toString()<< "\n"; 
                    return succNode;
                }
            }
        }  
    }
    return vNode;   
}
const VFGNode* iterate_predecessors(const VFGNode* vNode, Set<NodeID> &visited)
{
    
    FIFOWorkList<const VFGNode*> worklist;
    worklist.push(vNode);
    /// Traverse along VFG
    while (!worklist.empty())
    {  
        vNode = worklist.pop();
        outs()<<"Printing vnode in iterate" <<vNode->toString()<< "\n";
        for (VFGNode::const_iterator it = vNode->InEdgeBegin(), eit =
                    vNode->InEdgeEnd(); it != eit; ++it)
        {
            VFGEdge* edge = *it;
            NodeID prevID = edge->getSrcID();
            VFGNode* prevNode = edge->getSrcNode();
            if ((visited.find(prevID) == visited.end()) && edge->isDirectVFGEdge())
            {  
                visited.insert(prevID);
                worklist.push(prevNode);
                outs()<<"Printing pushed worklist " <<prevNode->toString()<< "\n"; 
            }
        }    
    }
    return vNode;   
}
const VFGNode* find_defSymVal (Value* val, SVFG* vfg){
    SVFIR* pag = SVFIR::getPAG();
    outs()<<"En el find defSymVal\n";
    SVFValue* svfVal = LLVMModuleSet::getLLVMModuleSet()->getSVFValue(val);
    PAGNode* pNode = pag->getGNode(pag->getValueNode(svfVal));
    const VFGNode* temp;
    Set<NodeID> visited;
    const VFGNode* vNode = vfg->getDefSVFGNode(pNode);
    temp = iterate_predecessors(vNode, visited);
    outs()<<"Printing temp node " <<temp->toString()<< "\n";
    vNode = verify_succ( temp, visited);
    outs()<<"Printing verification node " <<vNode->toString()<< "\n";
    while (temp != vNode)
    {
        temp = iterate_predecessors(vNode, visited);
        outs()<<"Printing while inside temp node " <<temp->toString()<< "\n";
        vNode = verify_succ(temp, visited);
        outs()<<"Printing while inside verification node " <<vNode->toString()<< "\n";
    }

    outs()<<"Printing first node " <<vNode->toString()<< "\n";
    return vNode;
}

CallInst* find_callSite(Module* mM){
    printf("en el find callsite\n");
    auto &FL = mM->getFunctionList();
    for (Function &Fn : FL){
        cout<< Fn.getName().data() << "\n";
        for (BasicBlock &BB : Fn){
            for (Instruction &Inst : BB)
            {
                if (isa<CallInst>(&Inst)) {
                    std::string str;
                    llvm::raw_string_ostream ss(str);
                    ss << Inst;
                    CallInst* cs;
                    outs()<< "\nhola"<<str <<"\n";
                    cs = dyn_cast<CallInst>(&Inst);
                    // Function *fun = cs->getCalledFunction();
                    if (str.find("make_byte_symbolic") != std::string::npos){ 
                        outs()<<"deberia pero no? \n";
                        
                        outs()<<"THIS IS THE CS HOPEFULLY   ****** " <<Inst <<"\n";
                        return cs;
                        //return dyn_cast<Value> (&Inst);
                    }
                }
            }
        }
    }
    return nullptr;

}

void taint_instructions_sara (CallInst* cs, Value* val, ICFG* icfg,  Module* mM, Set<NodeID> icfgIDs, Function * Fn, bool &set , bool &beginTaint){ 
    outs()<< "********************************* TAINTING INSIDE FUNCTION "<< Fn->getName() << " ************************************\n";
    std::string str1 = "taintedFun";
    Fn->setMetadata(str1, MDNode::get(Fn->getContext(), llvm::None));
    for (BasicBlock &BB : *Fn){
        for (Instruction &Inst : BB)
        {
            if (cs == dyn_cast<CallInst>(&Inst))
            {
                beginTaint = 1;
                outs()<<"Found make sym \n";
            }  
            else if (isa<CallInst>(&Inst))
            {
                CallInst* cInst;
                cInst = dyn_cast<CallInst>(&Inst);
                StringRef funName = cInst->getCalledFunction()->getName();
                // temp.push_back(mM->getFunction(funName));
                taint_instructions_sara ( cs, val, icfg, mM, icfgIDs, mM->getFunction(funName), set, beginTaint);
                outs()<< "********************************* RETURNING TO FUNCTION "<< Fn->getName() << " ************************************\n";
                //continue;
            }
            const SVFInstruction* svfInst = LLVMModuleSet::getLLVMModuleSet()->getSVFInstruction(&Inst);
            NodeID id = icfg->getICFGNode(svfInst)->getId();
            outs() << "BeginTaint "<< beginTaint << "In ID list? "<< (icfgIDs.find(id) != icfgIDs.end()) << "\n";

            if (icfgIDs.find(id) != icfgIDs.end() && beginTaint )
            {
                addMD(&Inst);
                
                if (Inst.getOpcode() == 53)
                {
                    outs() << "Set \n";
                    set = 1;
                }
                outs() << Inst << "and op "<< Inst.getOpcodeName() << "\n";
                //std::cout <<"ICFG ID of an INST"<< id << "\n";
                //addedMD.insert(id);
                //getMD(&Inst);
            }
            else if (set)
            {
                addMD(&Inst);
                set = 0;
                outs() << Inst << "and op "<< Inst.getOpcodeName() << "\n";
            }
        }
    }
}

void taint_functions_sara (SVFG* vfg, ICFG* icfg, Module* mM){
    CallInst* cs = find_callSite(mM);
    outs()<<"found callsite, getting callsite operand\n";
    Value* val = cs->getArgOperand(0);
    outs()<<"got callsite operand\n";
    Set<NodeID> icfgIDs = SymVal_succesors(find_defSymVal(val, vfg), vfg);
    // bool beginTaint = 0;
    Function *Fn =  mM->getFunction("main");
    if (Fn == nullptr)
    {
     Fn =  mM->getFunction("begin_target_inner");   
    }
    bool beginTaint = 0;
    bool set =0;
    //bool foundFunc = 1;
    outs()<< "********************************* checking if segfault "<< Fn->getName() << " ************************************\n";
    
    taint_instructions_sara(cs, val, icfg, mM, icfgIDs, Fn, set, beginTaint);

}

void taint_everything (Module* mM){
    printf("en el find callsite\n");
    auto &FL = mM->getFunctionList();
    for (Function &Fn : FL){
        for (BasicBlock &BB : Fn){
            for (Instruction &Inst : BB)
            {
                addMD(&Inst);
            }
        }
    }
}
int main(int argc, char ** argv)
{
    int arg_num = 0;
    char **arg_value = new char*[argc];
    std::vector<std::string> moduleNameVec;
    LLVMUtil::processArguments(argc, argv, arg_num, arg_value, moduleNameVec);
    cl::ParseCommandLineOptions(arg_num, arg_value,
                                "Whole Program Points-to Analysis\n");

    if (Options::WriteAnder() == "ir_annotator")
    {
        LLVMModuleSet::getLLVMModuleSet()->preProcessBCs(moduleNameVec);
    }

    SVFModule* svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(moduleNameVec);
    //    svfModule->buildSymbolTableInfo();

    /// Build Program Assignment Graph (SVFIR)
    SVFIRBuilder builder(svfModule);
    SVFIR* pag = builder.build();

    /// Create Andersen's pointer analysis
    Andersen* ander = AndersenWaveDiff::createAndersenWaveDiff(pag);

    /// Query aliases
    /// aliasQuery(ander,value1,value2);

    /// Print points-to information
    /// printPts(ander, value1);

    /// Call Graph
    PTACallGraph* callgraph = ander->getPTACallGraph();

    /// ICFG
    ICFG* icfg = pag->getICFG();
    //icfg->dump("icfg");

    /// Value-Flow Graph (VFG)
    VFG* vfg = new VFG(callgraph);

    /// Sparse value-flow graph (SVFG)
    SVFGBuilder svfBuilder(true);
    SVFG* svfg = svfBuilder.buildFullSVFG(ander);

    /// Collect uses of an LLVM Value
    
    Module * mM;
    mM = LLVMModuleSet::getLLVMModuleSet()->getMainLLVMModule();
    
    taint_functions_sara(svfg, icfg, mM);
    //taint_everything(mM);
    printf("finished\n");
    /// Collect all successor nodes on ICFG
    /// traverseOnICFG(icfg, value);

    // clean up memory
    delete vfg;
    delete svfg;
    AndersenWaveDiff::releaseAndersenWaveDiff();
    SVFIR::releaseSVFIR();

    LLVMModuleSet::getLLVMModuleSet()->dumpModulesToFile(".svf.bc");
    SVF::LLVMModuleSet::releaseLLVMModuleSet();

    llvm::llvm_shutdown();
    return 0;
}

