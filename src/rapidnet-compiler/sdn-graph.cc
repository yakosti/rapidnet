/*
 * sdn-context.cc
 *
 *  Created on: Nov 3, 2014
 *      Author: chen
 */

#include <iostream>
#include <deque>
#include "sdn-graph.h"

NS_LOG_COMPONENT_DEFINE ("DPGraph");

//TODO: Do not assume all types are STRING
Tuple::Tuple(string name, int argNum):
		tpName(name)
{
	for (int i = 0;i < argNum;i++)
	{
		Variable* newVar = new Variable(Variable::STRING, false);
		args.push_back(newVar);
	}
}

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

void
Tuple::PrintTupleInst(VarMap& vmap) const
{
	cout << tpName << "(";
	vector<Variable*>::const_iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		  if (it != args.begin())
		  {
			 cout << ",";
		  }
		  Variable* instVar = vmap.at(*it);
		  instVar->PrintTerm();
	}
	cout << ")";
}


void
Tuple::PrintSimpTupleInst(VarMap& vmap, SimpConstraints& simpCons) const
{
	cout << tpName << "(";
	vector<Variable*>::const_iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		  if (it != args.begin())
		  {
			 cout << ",";
		  }
		  Variable* instVar = vmap.at(*it);
		  Variable* simpVar = simpCons.FindRootVar(instVar);
		  simpVar->PrintTerm();
	}
	cout << ")";
}

void
Tuple::PrintInstance(const map<Variable*, int>& valueMap, bool printVar)
{
	cout << tpName << "(";
	vector<Variable*>::iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		  if (it != args.begin())
		  {
			 cout << ",";
		  }

		  map<Variable*, int>::const_iterator itm;
		  itm = valueMap.find(*it);
		  int value = 0;
		  if (itm != valueMap.end())
		  {
			  value = itm->second;
		  }
		  cout << value;
	}
	cout << ")";
}

void
Tuple::PrintInstance(const map<Variable*, int>& valueMap, VarMap& vmap, bool printVar) const
{
	cout << tpName << "(";
	vector<Variable*>::const_iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		  if (it != args.begin())
		  {
			 cout << ",";
		  }

		  Variable* instVar = vmap.at(*it);
		  map<Variable*, int>::const_iterator itm;
		  itm = valueMap.find(instVar);
		  int value = 0;
		  if (itm != valueMap.end())
		  {
			  value = itm->second;
		  }
		  if (printVar == true)
		  {
			  cout << "(";
			  instVar->PrintTerm();
			  cout << ")";
		  }
		  cout << value;
	}
	cout << ")";
}

void
Tuple::PrintSimpInstance(const map<Variable*, int>& valueMap, VarMap& vmap,
					   SimpConstraints& simpCons, bool printVar) const
{
	cout << tpName << "(";
	vector<Variable*>::const_iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		  if (it != args.begin())
		  {
			 cout << ",";
		  }

		  Variable* instVar = vmap.at(*it);
     	  Variable* simpVar = simpCons.FindRootVar(instVar);
		  map<Variable*, int>::const_iterator itm;
		  itm = valueMap.find(simpVar);
		  int value = 0;
		  if (itm != valueMap.end())
		  {
			  value = itm->second;
		  }

		  if (printVar == true)
		  {
			  cout << "(";
			  simpVar->PrintTerm();
			  cout << ")";
		  }
		  cout << value;
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

//	ConsList clist(1, cTemp);
//	SimpConstraints simpCons(clist);
//	simpCons.Print();
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

int
TupleNode::GetArgLength() const
{
	return tuple->GetArgLength();
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

CircleNode::CircleNode(const Tuple* tp, const AnnotMap& invariant)
{
	string tpName = tp->GetName();
	int argSize = tp->GetArgLength();
	tuple = new Tuple(tpName, argSize);

	AnnotMap::const_iterator ita = invariant.find(tpName);
	if (ita != invariant.end())
	{
		const Annotation& annot = ita->second;
		PredicateInstance* pred = annot.first;
		Formula* form = annot.second;
		anntProp = form->Clone();
		VarMap vmap = tuple->CreateVarMap(pred);
		anntProp->VarReplace(vmap);
	}
	else
	{
		NS_LOG_ERROR("No invariant found for the tuple!");
	}
}

int
CircleNode::GetArgLength() const
{
	return tuple->GetArgLength();
}

void
CircleNode::PrintNode() const
{
	cout << endl;
	cout << "Circle Node:" << endl;
	tuple->PrintTuple();
	cout << endl;
	anntProp->Print();
	cout << endl;
}

CircleNode::~CircleNode()
{
	delete tuple;
	delete anntProp;
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
			cout << "This MetaNode contains no TupleNode:" << predName << endl;
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

NewMetaNode::NewMetaNode(string pName):
		predName(pName)
{
	headTuples = list<Node*>();
	bodyTuples = list<Node*>();
}

NewMetaNode::NewMetaNode(MetaNode*& mnode)
{
	predName = mnode->predName;
	headTuples = list<Node*>();
	bodyTuples = list<Node*>();
	list<TupleNode*>& headList = mnode->headTuples;
	list<TupleNode*>::iterator itl;
	for (itl = headList.begin();itl != headList.end();itl++)
	{
		headTuples.push_back(*itl);
	}

	list<TupleNode*>& bodyList = mnode->bodyTuples;
	for (itl = bodyList.begin();itl != bodyList.end();itl++)
	{
		bodyTuples.push_back(*itl);
	}
}

int
NewMetaNode::GetArgLength() const
{
	list<Node*>::const_iterator it;
	for (it = headTuples.begin();it != headTuples.end();it++)
	{
		return (*it)->GetArgLength();
	}

	for (it = bodyTuples.begin();it != bodyTuples.end();it++)
	{
		return (*it)->GetArgLength();
	}

	NS_LOG_ERROR("No instance found in this NewMetaNode!");
	return 0;
}

bool
NewMetaNode::IsCircleNode()
{
	//TODO: Eliminate type checking
	list<Node*>::iterator it = bodyTuples.begin();
	CircleNode* cnode = dynamic_cast<CircleNode*>(*it);
	return (cnode == NULL?false:true);
}

void
NewMetaNode::AddHeadTuple(Node* tnode)
{
	headTuples.push_back(tnode);
}

void
NewMetaNode::AddBodyTuple(Node* tnode)
{
	bodyTuples.push_back(tnode);
}

void
NewMetaNode::PrintNode() const
{
	cout << predName << endl;
}


DPGraph::DPGraph(Ptr<OlContext> ctxt)
{
    NS_LOG_FUNCTION(this);
	OlContext::RuleList* rules = ctxt->GetRules();

	//Process rule by rule
	vector<OlContext::Rule*>::iterator it;
	NS_LOG_DEBUG("Size of Rules: " << rules->size());
	for (it = rules->begin(); it != rules->end(); it++)
	{
		ProcessRule(*it);
	}
	cout << "Dependency graph generated!" << endl;
}

const TupleListC&
DPGraph::GetBodyTuples(RuleNode* rn) const
{
	return inEdgesRL.at(rn);
}

const TupleNode*
DPGraph::GetHeadTuple(RuleNode* rn) const
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
	//TODO: New variables can be created and folded into
	//Lists. So that's not captured in the head tuple
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

NewDPGraph::NewDPGraph(Ptr<DPGraph> dpgraph, const Invariant& inv)
{
	const AnnotMap& annotation = inv.GetInv();
	tupleNodes = dpgraph->tupleNodes;
	ruleNodes = dpgraph->ruleNodes;
	RHMap::iterator itr;
	RHMap& oldOutERL = dpgraph->outEdgeRL;
	for (itr = oldOutERL.begin();itr != oldOutERL.end();itr++)
	{
		outEdgeRL.insert(map<RuleNode*, Node*>::value_type(itr->first,
																	   itr->second));
	}

	map<TupleNode*, CircleNode*> nmap;
	RBMap::iterator itb;
	RBMap& oldInERL = dpgraph->inEdgesRL;
	for (itb = oldInERL.begin();itb != oldInERL.end();itb++)
	{
		list<Node*> nlist;
		RuleNode* rnode = itb->first;
		list<TupleNode*>& bodyList = itb->second;
		list<TupleNode*>::iterator itn;
		for (itn = bodyList.begin();itn != bodyList.end();itn++)
		{
			string bName = (*itn)->GetName();
			AnnotMap::const_iterator ita = annotation.find(bName);
			if (ita == annotation.end())
			{
				nlist.push_back(*itn);
			}
			else
			{
				TupleNode* tnode = dynamic_cast<TupleNode*>(*itn);
				assert(tnode != NULL);
				const Tuple* tp = tnode->GetTuple();
				CircleNode* cnode = new CircleNode(tp, annotation);
				const Tuple* ctuple = cnode->GetTuple();
				nmap.insert(map<TupleNode*, CircleNode*>::value_type(tnode, cnode));

				nlist.push_back(cnode);
				ConstraintsTemplate* ctemp = rnode->GetConsTemp();
				VarMap vmap = tp->CreateVarMap(ctuple);
				ctemp->ReplaceVar(vmap);

				circleNodes.push_back(cnode);
			}
		}

		inEdgesRL.insert(map<RuleNode*, list<Node*> >::value_type(rnode,
																  nlist));
	}

	//Copy metaNodes
	MetaList& mlist = dpgraph->metaNodes;
	map<string, pair<NewMetaNode*, NewMetaNode*> > metaMap;
	MetaList::iterator itmt;
	for (itmt = mlist.begin();itmt != mlist.end();itmt++)
	{
		string mName = (*itmt)->GetName();
		AnnotMap::const_iterator ita = annotation.find(mName);
		if (ita != annotation.end())
		{
			//Create a two MetaNodes for a recursive tuple
			NewMetaNode* headMeta = new NewMetaNode(mName);
			NewMetaNode* bodyMeta = new NewMetaNode(mName);

			list<TupleNode*>& headList = (*itmt)->headTuples;
			list<TupleNode*>::iterator itl;
			for (itl = headList.begin();itl != headList.end();itl++)
			{
				headMeta->AddHeadTuple(*itl);
			}

			list<TupleNode*>& tlist = (*itmt)->bodyTuples;
			for (itl = tlist.begin();itl != tlist.end();itl++)
			{
				CircleNode* cnode = nmap.at(*itl);
				bodyMeta->AddBodyTuple(cnode);
			}

			metaNodes.push_back(headMeta);
			metaNodes.push_back(bodyMeta);
			pair<NewMetaNode*, NewMetaNode*> metaPair(headMeta, bodyMeta);
			metaMap.insert(map<string, pair<NewMetaNode*, NewMetaNode*> >::
										value_type(mName, metaPair));
		}
		else
		{
			NewMetaNode* newMeta = new NewMetaNode(*itmt);
			metaNodes.push_back(newMeta);
		}
	}

	RMHMap::iterator itrh;
	RMHMap& oldOutERM = dpgraph->outEdgeRM;
	for (itrh = oldOutERM.begin();itrh != oldOutERM.end();itrh++)
	{
		RuleNode* rnode = itrh->first;
		MetaNode* mnode = itrh->second;
		string mName = mnode->GetName();
		NewMetaNode* newMeta = NULL;
		map<string, pair<NewMetaNode*, NewMetaNode*> >::iterator itp;
		itp = metaMap.find(mName);
		if (itp != metaMap.end())
		{
			outEdgeRM.insert(map<RuleNode*, NewMetaNode*>::
								value_type(rnode, itp->second.first));
		}
		else
		{
			list<NewMetaNode*>::iterator itl;
			for (itl = metaNodes.begin();itl != metaNodes.end();itl++)
			{
				string metaName = (*itl)->GetName();
				if (metaName == mName)
				{
					outEdgeRM.insert(map<RuleNode*, NewMetaNode*>::
										value_type(rnode, *itl));
					break;
				}
			}
		}

	}

	RMBMap::iterator itrb;
	RMBMap& oldInERM = dpgraph->inEdgesRM;
	for (itrb = oldInERM.begin();itrb != oldInERM.end();itrb++)
	{
		RuleNode* rnode = itrb->first;
		list<NewMetaNode*> nlist;
		list<MetaNode*>& mlist = itrb->second;
		list<MetaNode*>::iterator itm;
		for (itm = mlist.begin();itm != mlist.end();itm++)
		{
			string mName = (*itm)->GetName();
			map<string, pair<NewMetaNode*, NewMetaNode*> >::iterator itp;
			itp = metaMap.find(mName);
			if (itp != metaMap.end())
			{
				nlist.push_back(itp->second.second);
			}
			else
			{
				list<NewMetaNode*>::iterator itl;
				for (itl = metaNodes.begin();itl != metaNodes.end();itl++)
				{
					string metaName = (*itl)->GetName();
					if (metaName == mName)
					{
						nlist.push_back(*itl);
						break;
					}
				}
			}

		}

		inEdgesRM.insert(map<RuleNode*, list<NewMetaNode*> >::
									value_type(rnode, nlist));
	}
}

const list<Node*>&
NewDPGraph::GetBodies(RuleNode* rn) const
{
	return inEdgesRL.at(rn);
}

const Node*
NewDPGraph::GetHeadTuple(RuleNode* rn) const
{
	return outEdgeRL.at(rn);
}

void
NewDPGraph::Print()
{
	cout << endl;
	cout << "-------------- Print New Dependency Graph --------------" << endl;
	cout << "Rule outgoing edges:" << endl;
	map<RuleNode*, Node*>::const_iterator itr;
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
	map<RuleNode*, list<Node*> >::const_iterator itt;
	for (itt = inEdgesRL.begin();itt != inEdgesRL.end();itt++)
	{
		//Print the name of the rule node
		itt->first->PrintName();
		cout << endl;

		//Print tuple nodes connected by the rule node
		list<Node*>::const_iterator itrv;
		for (itrv = itt->second.begin(); itrv != itt->second.end(); itrv++)
		{
			(*itrv)->PrintNode();
			cout << endl;
		}
	}
	cout << "----------------------------------" << endl;
}

NewDPGraph::~NewDPGraph()
{
	list<CircleNode*>::iterator itc;
	for (itc = circleNodes.begin();itc != circleNodes.end();itc++)
	{
		delete (*itc);
	}

	list<NewMetaNode*>::iterator itn;
	for (itn = metaNodes.begin();itn != metaNodes.end();itn++)
	{
		delete (*itn);
	}
}

MiniGraph::MiniGraph(Ptr<NewDPGraph> newGraph, const Invariant& invariant)
{
	cout << "Constructing MiniGraph..." << endl;
	outEdgeRM = newGraph->outEdgeRM;
	inEdgesRM = newGraph->inEdgesRM;

	list<NewMetaNode*>::iterator itt;
	list<NewMetaNode*>& mNodes = newGraph->metaNodes;
	for (itt = mNodes.begin(); itt != mNodes.end(); itt++)
	{
		RuleListC rlist;
		outEdgesMT.insert(map<NewMetaNode*, RuleListC>::value_type((*itt),rlist));
		inEdgesMT.insert(map<NewMetaNode*, RuleListC>::value_type((*itt),rlist));
	}

	map<RuleNode*, NewMetaNode*>::iterator itr;
	map<RuleNode*, NewMetaNode*>& outE = newGraph->outEdgeRM;
	for (itr = outE.begin(); itr != outE.end(); itr++)
	{
		inEdgesMT[itr->second].push_back(itr->first);
	}

	map<RuleNode*, list<NewMetaNode*> >::iterator itb;
	map<RuleNode*, list<NewMetaNode*> >& inE = newGraph->inEdgesRM;
	for (itb = inE.begin(); itb != inE.end(); itb++)
	{
		list<NewMetaNode*>& tvec = itb->second;
		list<NewMetaNode*>::iterator itp;
		for (itp = tvec.begin(); itp != tvec.end(); itp++)
		{
			outEdgesMT[(*itp)].push_back(itb->first);
		}
	}
}

RuleListC
MiniGraph::TopoSort(const Invariant& inv) const
{
	cout << "Topological sorting..." << endl;
	const AnnotMap& invariants = inv.GetInv();
	//Create a copy of the topology for processing
	map<RuleNode*, NewMetaNode*> outEdgeRMCopy = outEdgeRM;
	map<RuleNode*, list<NewMetaNode*> > inEdgesRMCopy = inEdgesRM;
	map<NewMetaNode*, RuleListC> outEdgesMTCopy = outEdgesMT;
	map<NewMetaNode*, RuleListC> inEdgesMTCopy = inEdgesMT;

	//RuleList: an ordered list of rules
	RuleListC topoOrder;
	int rNodeNum = outEdgeRMCopy.size();
	int rNodeCount = 0;	//Record how many rule nodes have been processed

	//ProcessQueue initialization
	deque<Node*> processQueue;
	map<NewMetaNode*, RuleListC>::const_iterator itti;
	NS_LOG_DEBUG("Size of inEdgesMTCopy: " << inEdgesMTCopy.size());
	for (itti = inEdgesMTCopy.begin();itti != inEdgesMTCopy.end();itti++)
	{
		int ruleSize = itti->second.size();
		NS_LOG_DEBUG("MetaNode: " << itti->first->GetName());
		NS_LOG_DEBUG("Rule size: "<< ruleSize << endl);
		if (ruleSize == 0)
		{

			//Add base tuple TupleNode and CircleNode into the queue.
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
		if (processQueue.size() == 0)
		{
			NS_LOG_ERROR("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx");
			NS_LOG_ERROR("Loop still exists in the dependency graph!!!");
			NS_LOG_ERROR("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx");
			return topoOrder;
		}
		Node* curNode = processQueue.front();
		NS_LOG_DEBUG("Topo sorting: " << curNode->GetName());
		processQueue.pop_front();
		//Process a meta node
		NewMetaNode* mnode = dynamic_cast<NewMetaNode*>(curNode);
		if (mnode != NULL)
		{
			//Delete the corresponding entry in inEdgesMTCopy
			inEdgesMTCopy.erase(mnode);
			RuleListC& rlist = outEdgesMTCopy[mnode];
			RuleListC::iterator itrl;
			for (itrl = rlist.begin();itrl != rlist.end();itrl++)
			{
				list<NewMetaNode*>& mlist = inEdgesRMCopy[(*itrl)];
				mlist.remove(mnode);
				if (mlist.size() == 0)
				{
					processQueue.push_back((*itrl));
				}
			}
			outEdgesMTCopy.erase(mnode);
		}

		//Process a rule node
		RuleNode* rnode = dynamic_cast<RuleNode*>(curNode);
		if (rnode != NULL)
		{
			//Store the topological order of the rule node
			topoOrder.push_back(rnode);
			//Delete the corresponding entry in inEdgesRMCopy
			inEdgesRMCopy.erase(rnode);
			NewMetaNode* mtNode = outEdgeRMCopy[rnode];
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

	cout << "Topological sorting completed!" << endl;

	return topoOrder;
}

list<NewMetaNode*>
MiniGraph::GetBaseTuples() const
{
	list<NewMetaNode*> mlist;

	map<NewMetaNode*, RuleListC>::const_iterator itti;
	for (itti = inEdgesMT.begin();itti != inEdgesMT.end();itti++)
	{
		if (itti->second.size() == 0 && !(itti->first->IsCircleNode()))
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
	map<RuleNode*, NewMetaNode*>::const_iterator itrh;
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
	map<RuleNode*, list<NewMetaNode*> >::const_iterator itrb;
	list<NewMetaNode*>::const_iterator ittv;
	for (itrb = inEdgesRM.begin();itrb != inEdgesRM.end();itrb++)
	{
		cout << "Rule name:" << endl;
		itrb->first->PrintName();
		cout << endl << endl;
		cout << "Rule bodies:" << endl;
		const list<NewMetaNode*>& mnodes = itrb->second;
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
	map<NewMetaNode*, RuleListC>::const_iterator itti;
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
