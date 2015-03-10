/*
 * sdn-context.cc
 *
 *  Created on: Nov 3, 2014
 *      Author: chen
 */

#include <iostream>
#include <deque>
#include <list>
#include "ol-context.h"
#include "sdn-graph.h"

NS_LOG_COMPONENT_DEFINE ("DPGraph");

Tuple::Tuple(ParseFunctor* tuple):
		tpName(tuple->fName->ToString())
{
	Variable* newVar = NULL;
	deque<ParseExpr*>::iterator it;
	ParseExprList *pargs = tuple->m_args;
	for (it = pargs->begin();it != pargs->end(); it++)
	{
		ParseVar* varPtr = dynamic_cast<ParseVar*>(*it);
		if (varPtr != NULL)
		{
			newVar = new Variable(varPtr, false);
			args.push_back(newVar);
		}
		else
		{
			NS_LOG_ERROR("Non-variable argument");
			//ERROR: Non-variable argument
		}
	}
}

Tuple::Tuple(string name, list<Variable::TypeCode> schema):
		tpName(name)
{
	list<Variable::TypeCode>::iterator it;
	for (it = schema.begin();it != schema.end();it++)
	{
		args.push_back(new Variable((*it), false));
	}
}

VarMap
Tuple::CreateVarMap(const Tuple* tp) const
{
	if (tp->GetName() != tpName)
	{
		NS_LOG_ERROR("Tuples of different relations cannot be mapped!");
		return VarMap();
	}

	if (tp->args.size() != args.size())
	{
		NS_LOG_ERROR("VarMap cannot be created due to unmatched argument size!");
		return VarMap();
	}

	VarMap vmap = VarMap();

	vector<Variable*>::const_iterator itf = args.begin();
	vector<Variable*>::const_iterator its = tp->args.begin();
	for (;itf != args.end();itf++, its++)
	{
		//TODO: Type checking?
		vmap.insert(VarMap::value_type((*itf),(*its)));
	}
	return vmap;
}

VarMap
Tuple::CreateVarMap(const PredicateInstance* pred) const
{
	VarMap vmap = VarMap();
	string predName = pred->GetName();
	if (predName != tpName)
	{
		NS_LOG_ERROR("Variable match cannot be created for different predicates!");
	}

	const vector<Term*>& predArgs = pred->GetArgs();
	if (args.size() != predArgs.size())
	{
		NS_LOG_ERROR("VarMap cannot be created due to unmatched argument size!");
		return vmap;
	}

	vector<Variable*>::const_iterator itf = args.begin();
	vector<Term*>::const_iterator its = predArgs.begin();
	Variable* predArg;
	for (;itf != args.end();itf++, its++)
	{
		predArg = dynamic_cast<Variable*>(*its);
		if (predArg == NULL)
		{
			NS_LOG_ERROR("Non-variable argument in the predicate!");
		}
		//TODO: Type checking?
		vmap.insert(VarMap::value_type(predArg,(*itf)));
	}
	return vmap;
}

list<Variable::TypeCode>
Tuple::GetSchema() const
{
	list<Variable::TypeCode> typeList = list<Variable::TypeCode>();

	vector<Variable*>::const_iterator it = args.begin();
	for (;it != args.end();it++)
	{
		typeList.push_back((*it)->GetVariableType());
	}

	return typeList;
}

void
Tuple::PrintTuple() const
{
	cout << tpName << "(";
	vector<Variable*>::const_iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		  if (it != args.begin())
		  {
			 cout << ",";
		  }
		  (*it)->PrintTerm();
	}
	cout << ")";
}

Tuple::~Tuple()
{
	vector<Variable*>::iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		delete (*it);
	}
}


//Implementation of RuleNode
RuleNode::RuleNode(string rName)
{
	ruleName = rName;
	cTemp = new ConstraintsTemplate();
}

void
RuleNode::UpdateUnif(Variable* v1, Variable* v2)
{
	Constraint* unification = new Constraint(Constraint::EQ, v1, v2);
	cTemp->AddConstraint(unification);
}

void
RuleNode::UpdateConstraint(Constraint* cPtr)
{
	cTemp->AddConstraint(cPtr);
}

void
RuleNode::PrintName() const
{
	cout << ruleName << endl;
}

void
RuleNode::PrintNode() const
{
	cout << "Rule ID: " << ruleName << endl;
	cout << "Constraints:" << endl;
	NS_LOG_DEBUG("To print template");
	cTemp->PrintTemplate();
	cout << endl;
	cout << "###### Simplified constraints ######" << endl;
	ConsList clist(1, cTemp);
	SimpConstraints simpCons(clist);
	simpCons.Print();
	cout << "####################################" << endl;
	NS_LOG_DEBUG("Template printed");
}

RuleNode::~RuleNode()
{
	delete cTemp;
}

TupleNode::TupleNode(ParseFunctor* tp)
{
	tuple = new Tuple(tp);
}

TupleNode::TupleNode(string tpName, vector<Variable*> args)
{
	tuple = new Tuple(tpName, args);
}

list<Variable::TypeCode>
TupleNode::GetSchema() const
{
	return tuple->GetSchema();
}

void
TupleNode::PrintName() const
{
	cout << tuple->GetName() << endl;
}

void
TupleNode::PrintNode() const
{
	tuple->PrintTuple();
}

TupleNode::~TupleNode()
{
	delete tuple;
}

MetaNode::MetaNode(string pName):
		predName(pName)
{
	headTuples = list<TupleNode*>();
	bodyTuples = list<TupleNode*>();
}

list<Variable::TypeCode>
MetaNode::GetSchema() const
{
	list<TupleNode*>::const_iterator it;

	if (headTuples.size() != 0)
	{
		it = headTuples.begin();
		return ((*it)->GetSchema());
	}
	else
	{
		if (bodyTuples.size() != 0)
		{
			it = bodyTuples.begin();
			return ((*it)->GetSchema());
		}
		else
		{
			NS_LOG_INFO("This MetaNode contains no TupleNode:" << predName);
			return list<Variable::TypeCode>();
		}
	}
}

void
MetaNode::AddHeadTuple(TupleNode* tnode)
{
	headTuples.push_back(tnode);
}

void
MetaNode::AddBodyTuple(TupleNode* tnode)
{
	bodyTuples.push_back(tnode);
}

void
MetaNode::PrintNode() const
{
	cout << predName << endl;
}

DPGraph::DPGraph(Ptr<OlContext> ctxt)
{
    NS_LOG_FUNCTION(this);
	OlContext::RuleList* rules = ctxt->GetRules();

	//Process rule by rule
	vector<OlContext::Rule*>::iterator it;
	for (it = rules->begin(); it != rules->end(); it++)
	{
		ProcessRule(*it);
	}
	NS_LOG_INFO("Dependency graph generated!");
}

const TupleListC&
DPGraph::GetBodyTuples(const RuleNode* rn) const
{
	return inEdgesRL.at(rn);
}

const TupleNode*
DPGraph::GetHeadTuple(const RuleNode* rn) const
{
	return outEdgeRL.at(rn);
}

void
DPGraph::ProcessRule(OlContext::Rule* r)
//Change return value if needed
{
    NS_LOG_FUNCTION(r->ruleID);
	map<string, Variable*> unifier;
	MetaNode* mNode = NULL;
	RuleNode* rNode = new RuleNode(r->ruleID);
	ruleNodes.push_back(rNode);

	//Process the head tuple
	//Assumption: head tuple does not have duplicate arguments
	TupleNode* hTuple = ProcessFunctor(r->head, unifier, rNode);
	string tName = hTuple->GetName();
	MetaList::const_iterator itm;
	for (itm = metaNodes.begin(); itm != metaNodes.end(); itm++)
	{
		if ((*itm)->GetName() == tName)
		{
			//Update the corresponding MetaNode
			(*itm)->AddHeadTuple(hTuple);
			mNode = (*itm);
			break;
		}
	}
	if (itm == metaNodes.end())
	{
		//Create a new MetaNode
		mNode = new MetaNode(tName);
		mNode->AddHeadTuple(hTuple);
		metaNodes.push_back(mNode);
	}

	outEdgeRL.insert(RHMap::value_type(rNode, hTuple));
	outEdgeRM.insert(RMHMap::value_type(rNode, mNode));

	//Process body terms
	list<ParseTerm*>::iterator it;
	ParseFunctor *functor = NULL;
	ParseAssign *assign = NULL;
	ParseSelect *select = NULL;
	for (it = r->terms.begin(); it != r->terms.end(); it++)
	{
	    //Process body tuples
		functor = dynamic_cast<ParseFunctor *>(*it);
		if (functor != NULL)
		{
		    NS_LOG_DEBUG("Processing Functor:\t" << (functor->fName->ToString()));
			TupleNode* bTuple = ProcessFunctor(functor, unifier, rNode);
			string bName = bTuple->GetName();
			MetaList::const_iterator itm;
			for (itm = metaNodes.begin(); itm != metaNodes.end(); itm++)
			{
				if ((*itm)->GetName() == bName)
				{
					//Update the corresponding MetaNode
					(*itm)->AddBodyTuple(bTuple);
					mNode = (*itm);
					break;
				}
			}
			if (itm == metaNodes.end())
			{
				//Create a new MetaNode
				mNode = new MetaNode(bName);
				mNode->AddBodyTuple(bTuple);
				metaNodes.push_back(mNode);
			}

			inEdgesRL[rNode].push_back(bTuple);
			inEdgesRM[rNode].push_back(mNode);
			continue;
		}

		//Process assignment
		assign = dynamic_cast<ParseAssign *>(*it);
		if (assign != NULL)
		{
			NS_LOG_DEBUG("Process Assignment");
			NS_LOG_DEBUG(assign->ToString());
			Constraint* consAssign = ProcessAssign(assign, unifier, rNode);
			rNode->UpdateConstraint(consAssign);
			continue;
		}

		//Process select
		select = dynamic_cast<ParseSelect *>(*it);
		if (select != NULL)
		{
			Constraint* consSelect = ProcessSelect(select, unifier, rNode);
			rNode->UpdateConstraint(consSelect);
			continue;
		}
	}
}

TupleNode*
DPGraph::ProcessFunctor(ParseFunctor* fct,
						map<string, Variable*>& unifier,
						RuleNode* rnode)
{
    NS_LOG_FUNCTION(this);
    Variable* newVar = NULL;
    vector<Variable*> varVec;

    string tpName = fct->fName->name;
	NS_LOG_DEBUG("Process tuple:" << tpName);

	//Create variable mapping between ParseVar and Variable
	ParseExprList* headArgs = fct->m_args;
	deque<ParseExpr*>::iterator itd = headArgs->begin();

	for (;itd != headArgs->end();itd++)
	{
		ParseVar* vPtr = dynamic_cast<ParseVar*>(*itd);
		newVar = ProcessParseVar(vPtr, unifier, rnode);
		varVec.push_back(newVar);
	}

	TupleNode* tnode = new TupleNode(tpName, varVec);
	tupleNodes.push_back(tnode);
	return tnode;
}

//Process ParseAssign
Constraint*
DPGraph::ProcessAssign(ParseAssign* assign,
					   map<string, Variable*>& unifier,
					   RuleNode* rnode)
{
	Term* leftE = ProcessExpr(assign->var, unifier, rnode);
	Term* rightE = ProcessExpr(assign->assign, unifier, rnode);
	return (new Constraint(Constraint::EQ, leftE, rightE));
}

Constraint*
DPGraph::ProcessSelect(ParseSelect* select,
					   map<string, Variable*>& unifier,
					   RuleNode* rnode)
{
	ParseBool* pBool = select->select;
	Constraint* cPtr = ProcessConstraint(pBool, unifier, rnode);
	return cPtr;
}

Term*
DPGraph::ProcessExpr(ParseExpr* pExpr,
					 map<string, Variable*>& unifier,
					 RuleNode* rnode)
{
	//Currently we do not process ParseBool in ParseExpr
	ParseVal* pVal = NULL;
	ParseVar* pVar = NULL;
	ParseMath* pMath = NULL;
	ParseFunction* pFunc = NULL;

	pVal = dynamic_cast<ParseVal*>(pExpr);
	if (pVal != NULL)
	{
		//pExpr points to ParseVal type
		return ProcessParseVal(pVal);
	}
	pVar = dynamic_cast<ParseVar*>(pExpr);
	if (pVar != NULL)
	{
		//pExpr points to ParseVar type
		return ProcessParseVar(pVar, unifier, rnode);
	}
	pMath = dynamic_cast<ParseMath*>(pExpr);
	if (pMath != NULL)
	{
		//pExpr points to ParseBool type
		return ProcessParseMath(pMath, unifier, rnode);
	}
	pFunc = dynamic_cast<ParseFunction*>(pExpr);
	if (pFunc != NULL)
	{
		//pExpr points to ParseFunction type
		return ProcessParseFunc(pFunc, unifier, rnode);
	}

	return NULL;
}

Value*
DPGraph::ProcessParseVal(ParseVal* value)
{
	ValuePtr vPtr = value->Value();
	ValInt32* intPtr = dynamic_cast<ValInt32*>(PeekPointer(vPtr));
	if (intPtr != NULL)
	{
		return (new IntVal(intPtr->GetInt32Value()));
	}

	ValDouble* dbPtr = dynamic_cast<ValDouble*>(PeekPointer(vPtr));
	if (dbPtr != NULL)
	{
		return (new DoubleVal(dbPtr->GetDoubleValue()));
	}

	ValStr* strPtr = dynamic_cast<ValStr*>(PeekPointer(vPtr));
	if (strPtr != NULL)
	{
		return (new StringVal(strPtr->ToString()));
	}

	return NULL;
}

Variable*
DPGraph::ProcessParseVar(ParseVar* pVar,
						 map<string, Variable*>& unifier,
						 RuleNode* rnode)
{
	Variable* newVar = new Variable(pVar, false);
	pair<map<string,Variable*>::iterator, bool> ret;
	ret = unifier.insert(pair<string,Variable*>(pVar->ToString(), newVar));
	if (ret.second == false)
	{
		//The ParseVar exists.
		//Add a constraint of equality between Variables
		rnode->UpdateUnif(ret.first->second,newVar);
	}

	return newVar;
}

UserFunction*
DPGraph::ProcessParseFunc(ParseFunction* pFunc,
						  map<string, Variable*>& unifier,
						  RuleNode* rnode)
{
	//Assumption: All terms in pFunc should be variables
	//TODO: return value undefined for UserFunction
	NS_LOG_WARN("Return value undetermined!");

	vector<Variable::TypeCode> tlist;
	vector<Term*> vlist;
	ParseVar* pVar = NULL;
	Variable* var = NULL;
	map<string, Variable*>::iterator itm;
	ParseExprList* funcArgs = pFunc->m_args;
	ParseExprList::iterator itp;
	for (itp = funcArgs->begin();itp != funcArgs->end();itp++)
	{
		pVar = dynamic_cast<ParseVar*>(*itp);
		if (pVar == NULL)
		{
			NS_LOG_ERROR("Non-variable found in function args!");
		}

		var = ProcessParseVar(pVar, unifier, rnode);
		tlist.push_back(var->GetVariableType());
		vlist.push_back(var);
	}

	string funcName = pFunc->Name();
	FunctionSchema* scm = new FunctionSchema(funcName, tlist, Variable::STRING);
	UserFunction* func = new UserFunction(scm, vlist);
	return func;
}

Constraint*
DPGraph::ProcessConstraint(ParseBool* pBool,
						   map<string, Variable*>& unifier,
						   RuleNode* rnode)
{
	Constraint::Operator op;
	if (pBool->oper == ParseBool::EQ)
	{
		op = Constraint::EQ;
	}
	else if (pBool->oper == ParseBool::NEQ)
	{
		op = Constraint::NEQ;
	}
	else if (pBool->oper == ParseBool::GT)
	{
		op = Constraint::GT;
	}
	else if (pBool->oper == ParseBool::LT)
	{
		op = Constraint::LT;
	}

	Term* leftE = ProcessExpr(pBool->lhs, unifier, rnode);
	Term* rightE = ProcessExpr(pBool->rhs, unifier, rnode);
	return (new Constraint(op, leftE, rightE));
}

Arithmetic*
DPGraph::ProcessParseMath(ParseMath* pMath,
						  map<string, Variable*>& unifier,
						  RuleNode* rnode)
{
	Arithmetic::ArithOp op;
	if (pMath->oper == ParseMath::PLUS)
	{
		op = Arithmetic::PLUS;
	}
	else if (pMath->oper == ParseMath::MINUS)
	{
		op = Arithmetic::MINUS;
	}
	else if (pMath->oper == ParseMath::TIMES)
	{
		op = Arithmetic::TIMES;
	}
	else if (pMath->oper == ParseMath::DIVIDE)
	{
		op = Arithmetic::DIVIDE;
	}

	Term* leftE = ProcessExpr(pMath->lhs, unifier, rnode);
	Term* rightE = ProcessExpr(pMath->rhs, unifier, rnode);
	return (new Arithmetic(op, leftE, rightE));
}

TupleNode*
DPGraph::FindTupleNode(ParseFunctor* tuple)
{
	string headName = tuple->fName->name;
	NS_LOG_DEBUG("Tuple name:" << headName << endl);
	//TODO:Hash function could be quick in detecting
	//if a tuple exists or not
	TupleList::iterator it;
	NS_LOG_DEBUG("Existing tuple names:");
	for (it = tupleNodes.begin();it != tupleNodes.end();it++)
	{
		string tname = (*it)->GetName();
		NS_LOG_DEBUG(tname << endl);
		if (tname == headName)
		{
			return (*it);
		}
	}
	return NULL;
}

void
DPGraph::PrintGraph() const
{
	cout << "Rule outgoing edges:" << endl;
	RHMap::const_iterator itr;
	for (itr = outEdgeRL.begin();itr != outEdgeRL.end();itr++)
	{
		//Print the rule node
		itr->first->PrintNode();
		cout << endl;

		//Print the head tuple
		cout << "Head tuple:";
		itr->second->PrintNode();
		cout << endl;
	}

	cout << "Rule incoming edges:" << endl;
	RBMap::const_iterator itt;
	for (itt = inEdgesRL.begin();itt != inEdgesRL.end();itt++)
	{
		//Print the name of the rule node
		itt->first->PrintName();
		cout << endl;

		//Print tuple nodes connected by the rule node
		TupleListC::const_iterator itrv;
		for (itrv = itt->second.begin(); itrv != itt->second.end(); itrv++)
		{
			(*itrv)->PrintNode();
			cout << endl;
		}
	}
}

DPGraph::~DPGraph()
{
	TupleList::iterator itr;
	for (itr = tupleNodes.begin();itr != tupleNodes.end();itr++)
	{
		delete (*itr);
	}

	MetaList::iterator itm;
	for (itm = metaNodes.begin();itm != metaNodes.end();itm++)
	{
		delete (*itm);
	}

	RuleList::iterator itt;
	for (itt = ruleNodes.begin();itt != ruleNodes.end();itt++)
	{
		delete (*itt);
	}
}

MiniGraph::MiniGraph(Ptr<DPGraph> dpgraph)
{
	outEdgeRM = dpgraph->outEdgeRM;
	inEdgesRM = dpgraph->inEdgesRM;

	MetaList::iterator itt;
	MetaList& mNodes = dpgraph->metaNodes;
	for (itt = mNodes.begin(); itt != mNodes.end(); itt++)
	{
		RuleListC rlist;
		outEdgesMT.insert(MTRMap::value_type((*itt),rlist));
		inEdgesMT.insert(MTRMap::value_type((*itt),rlist));
	}

	RMHMap::iterator itr;
	RMHMap& outE = dpgraph->outEdgeRM;
	for (itr = outE.begin(); itr != outE.end(); itr++)
	{
		inEdgesMT[itr->second].push_back(itr->first);
	}

	RMBMap::iterator itb;
	RMBMap& inE = dpgraph->inEdgesRM;
	for (itb = inE.begin(); itb != inE.end(); itb++)
	{
		MetaListC& tvec = itb->second;
		MetaListC::iterator itp;
		for (itp = tvec.begin(); itp != tvec.end(); itp++)
		{
			outEdgesMT[(*itp)].push_back(itb->first);
		}
	}
}

pair<RuleListC, RuleListC>
MiniGraph::TopoSort(const AnnotMap& invariants) const
{
	NS_LOG_INFO("Topological sorting");
	//Create a copy of the topology for processing
	RMHMap outEdgeRMCopy = outEdgeRM;
	RMBMap inEdgesRMCopy = inEdgesRM;
	MTRMap outEdgesMTCopy = outEdgesMT;
	MTRMap inEdgesMTCopy = inEdgesMT;

	//TupleList: a list of base tuples
	//RuleList: an ordered list of rules
	pair<RuleListC, RuleListC> topoOrder;
	int rNodeNum = outEdgeRMCopy.size();
	int rNodeCount = 0;	//Record how many rule nodes have been processed

	//ProcessQueue initialization
	deque<const Node*> processQueue;
	MTRMap::const_iterator itti;
	for (itti = inEdgesMTCopy.begin();itti != inEdgesMTCopy.end();itti++)
	{
		if (itti->second.size() == 0)
		{
			processQueue.push_back(itti->first);
		}
	}

	NS_LOG_DEBUG("Elements in Process Queue:" << processQueue.size());
	//Topological sorting
	while (rNodeCount < rNodeNum)
	{
		NS_LOG_DEBUG("Enter loop");
		NS_LOG_DEBUG("rNodeCount: " << rNodeCount);
		NS_LOG_DEBUG("rNodeNum: " << rNodeNum);
		NS_LOG_DEBUG("Size of processQueue: " << processQueue.size());
		//Non-recursive case
		if (processQueue.size() > 0)
		{
			const Node* curNode = processQueue.front();
			cout << endl;
			NS_LOG_INFO("Processing: ");
			curNode->PrintNode();
			cout << endl;
			processQueue.pop_front();
			//Process a meta node
			const MetaNode* mnode = dynamic_cast<const MetaNode*>(curNode);
			if (mnode != NULL)
			{
				//Delete the corresponding entry in inEdgesMTCopy
				inEdgesMTCopy.erase(mnode);
				RuleListC& rlist = outEdgesMTCopy[mnode];
				RuleListC::iterator itrl;
				for (itrl = rlist.begin();itrl != rlist.end();itrl++)
				{
					MetaListC& mlist = inEdgesRMCopy[(*itrl)];
					mlist.remove(mnode);
					if (mlist.size() == 0)
					{
						processQueue.push_back((*itrl));
					}
				}
				outEdgesMTCopy.erase(mnode);
			}

			//Process a rule node
			const RuleNode* rnode = dynamic_cast<const RuleNode*>(curNode);
			if (rnode != NULL)
			{
				//Store the topological order of the rule node
				topoOrder.first.push_back(rnode);
				//Delete the corresponding entry in inEdgesRMCopy
				inEdgesRMCopy.erase(rnode);
				const MetaNode* mtNode = outEdgeRMCopy[rnode];
				RuleListC& rl = inEdgesMTCopy[mtNode];
				rl.remove(rnode);
				if (rl.size() == 0)
				{
					processQueue.push_back(mtNode);
				}
				outEdgeRMCopy.erase(rnode);
				rNodeCount++;
			}
		}
		//Recursive case
		else
		{
			//TODO: Differentiate recursive rules with non-recursive ones
			MTRMap::iterator itm;
			for (itm = inEdgesMTCopy.begin(); itm != inEdgesMTCopy.end();itm++)
			{
				string tName = itm->first->GetName();
				AnnotMap::const_iterator ita = invariants.find(tName);
				if (ita != invariants.end())
				{
					NS_LOG_INFO("Processing Recursive Node: ");
					itm->first->PrintNode();
					//A tuple in a recursive loop
					processQueue.push_back(itm->first);

					RuleListC& rlist = itm->second;
					RuleListC::const_iterator itrc;
					for (itrc = rlist.begin(); itrc != rlist.end(); itrc++)
					{
						NS_LOG_INFO("Processing the incoming rule: ");
						(*itrc)->PrintNode();
						//Add all incoming rule nodes to topoOrder
						NS_LOG_DEBUG("Reach here??");
						topoOrder.second.push_back((*itrc));
						//Delete corresponding outbound edges from body tuples

						MetaListC& ml = inEdgesRMCopy[(*itrc)];
						MetaListC::const_iterator itml;
						NS_LOG_DEBUG("Reach here???");
						for (itml = ml.begin();itml != ml.end(); itml++)
						{
							MTRMap::iterator itmi = outEdgesMTCopy.find((*itml));
							if (itmi != outEdgesMTCopy.end())
							{
								itmi->second.remove((*itrc));
							}
						}
						inEdgesRMCopy.erase((*itrc));
						outEdgeRMCopy.erase((*itrc));
						rNodeCount++;
					}
					NS_LOG_DEBUG("Reach here?");
					break;
				}
			}
			inEdgesMTCopy.erase(itm);
		}
	}

	NS_LOG_INFO("Topological sorting completed!");

	return topoOrder;
}

MetaListC
MiniGraph::GetBaseTuples() const
{
	MetaListC mlist;

	MTRMap::const_iterator itti;
	for (itti = inEdgesMT.begin();itti != inEdgesMT.end();itti++)
	{
		if (itti->second.size() == 0)
		{
			//Record all base tuples
			mlist.push_back(itti->first);
		}
	}

	return mlist;
}

void
MiniGraph::PrintGraph() const
{
	cout << "------------------ Mini Graph --------------------" << endl;
	cout << "Rule node edges (outbound):" << endl;
	RMHMap::const_iterator itrh;
	for (itrh = outEdgeRM.begin();itrh != outEdgeRM.end();itrh++)
	{
		cout << "Rule head:";
		itrh->second->PrintNode();
		cout << endl;
		cout << "Rule name and constraints:" << endl;
		itrh->first->PrintNode();
		cout << endl;
	}
	cout << endl;

	cout << "Rule node edges (inbound):" << endl;
	RMBMap::const_iterator itrb;
	MetaListC::const_iterator ittv;
	for (itrb = inEdgesRM.begin();itrb != inEdgesRM.end();itrb++)
	{
		cout << "Rule name:" << endl;
		itrb->first->PrintName();
		cout << endl << endl;
		cout << "Rule bodies:" << endl;
		const MetaListC& mnodes = itrb->second;
		for (ittv = mnodes.begin();ittv != mnodes.end();ittv++)
		{
			cout << "\t";
			(*ittv)->PrintNode();
			cout << endl;
		}
		cout << endl;
	}
	cout << endl;

	cout << "Tuple node edges (outbound):" << endl;
	MTRMap::const_iterator itti;
	RuleListC::const_iterator itri;
	for (itti = outEdgesMT.begin();itti != outEdgesMT.end();itti++)
	{
		itti->first->PrintNode();
		cout << endl;
		const RuleListC& rnodes = itti->second;
		for (itri = rnodes.begin();itri != rnodes.end();itri++)
		{
			cout << "\t";
			(*itri)->PrintName();
			cout << endl;
		}
	}
	cout << endl;

	cout << "Tuple node edges (inbound):" << endl;
	for (itti = inEdgesMT.begin();itti != inEdgesMT.end();itti++)
	{
		itti->first->PrintNode();
		cout << endl;
		const RuleListC& rnodes = itti->second;
		for (itri = rnodes.begin();itri != rnodes.end();itri++)
		{
			cout << "\t";
			(*itri)->PrintName();
			cout << endl;
		}
	}
	cout << endl;
}
