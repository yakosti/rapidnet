/*
 * sdn-context.cc
 *
 *  Created on: Nov 3, 2014
 *      Author: chen
 */

#include <iostream>
#include <deque>
#include "ol-context.h"
#include "sdn-context.h"
#include "sdn-constraint.h"

Node::Node(string nodeName):
	name(nodeName){}

virtual void
Node::PrintNode()
{
	cout << name << endl;
}

void
RuleNode::UpdateUnif(const Variable* v1, const Variable* v2)
{
	Constraint* unification = new Constraint(Constraint::EQ, v1, v2);
	constraints.push_back(unification);
}

void
RuleNode::UpdateConstraint(const Constraint* cPtr)
{
	constraints.push_back(cPtr);
}

void
RuleNode::PrintNode()
{
	cout << "Head node:" << head->GetName() << endl;
	cout << "Body nodes:" << endl;
	vector<TupleNode*>::iterator itb;
	for (itb = bodies.begin(); itb != bodies.end(); itb++)
	{
		cout << (*itb)->GetName();
	}

	//TODO: Print out constraints
}

RuleNode::~RuleNode()
{
	vector<Constraint*>::iterator it;
	for (it = constraints.begin();it != constraints.end(); it++)
	{
		delete (*it);
	}
}

TupleNode::TupleNode(const ParseFunctor* tuple):
		Node(tuple->fName->ToString())
{
	deque<ParseExpr*>::iterator it;
	ParseExprList *pargs = tuple->m_args;
	for (it = pargs->begin();it != pargs->end(); it++)
	{
		args.push_back(new Variable(*it));
	}
}

void
TupleNode::PrintNode()
{
	cout << name << "(";
	vector<Variable*>::iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		//TODO: Print out variables
	}
}

void
TupleNode::~TupleNode()
{
	vector<Variable*>::iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		delete (*it);
	}
}

DPGraph::DPGraph(const OlContext* ctxt)
{
	OlContext::RuleList* rules = ctxt->GetRules();

	//Process rule by rule
	vector<OlContext::Rule*>::iterator it;
	for (it = rules->begin(); it != rules->end(); it++)
	{
		ProcessRule(*it);
	}
	PrintGraph();
}

DPGraph::~DPGraph()
{
	vector<TupleNode*>::iterator itt;
	for (itt = tnodeList.begin();itt != tnodeList.end();itt++)
	{
		delete (*itt);
	}
	vector<RuleNode*>::iterator itr;
	for (itr = rnodeList.begin();itr != rnodeList.end();itr++)
	{
		delete (*itr);
	}
}

void
DPGraph::ProcessRule(const OlContext::Rule* r)
//Change return value if needed
{
	map<string, Variable*> unifier;
	RuleNode* rnode = new RuleNode();

	//Process head tuple
	//Assumption: head tuple does not have duplicate arguments
	ProcessFunctor(r->head, rnode);

	//Process body terms
	list<ParseTerm*>::iterator it;
	ParseFunctor *functor = NULL;
	ParseAssign *assign = NULL;
	ParseSelect *select = NULL;
	for (it = r->terms.begin(); it != r->terms.end(); it++)
	{
		functor = dynamic_cast<ParseFunctor *>(*it);
		assign = dynamic_cast<ParseAssign *>(*it);
		select = dynamic_cast<ParseSelect *>(*it);
		if (functor != NULL)
		{
			ProcessFunctor(functor);
			break;
		}

		if (assign != NULL)
		{
			ProcessAssign(assign);
			break;
		}

		if (select != NULL)
		{

			break;
		}
	}
}

void
DPGraph::ProcessFunctor(const ParseFunctor* fct, RuleNode* rnode)
{
	//Find corresponding TupleNode. Create one if nothing is found
	TupleNode* tnode = FindTupleNode(fct);
	if (tnode == NULL)
	{
		tnode = new TupleNode(fct);
		tnodeList.push_back(tnode);
	}

	//Process arguments of the tuple
	ParseExprList* headArgs = fct->m_args;
	deque<ParseExpr*>::iterator itd = headArgs.begin();
	vector<Variable*>& tArgs = tnode->GetArgs();
	vector<Variable*>::iterator itv = tArgs.begin();
	for (;itd != headArgs.end();itd++,itv++)
	{
		ParseVar* vPtr = dynamic_cast<ParseVar*>(*itd);
		pair<map<string,Variable*>::iterator, bool> ret;
		ret = unifier.insert(pair<string, Variable*>(vPtr->ToString(),
													(*itv)));
		if (ret.second == false)
		{
			//Update unification in rnode
			rnode->UpdateUnif(ret.first->second,(*itv));
		}
	}
}

//Process ParseAssign
void
DPGraph::ProcessAssign(const ParseAssign* assign,
					   const map<string, Variable*>& unifier,
					   RuleNode* rnode)
{
	map<string, Variable*>::iterator it;
	it = unifier.find(assign->var->ToString());
	if (it == unifier.end())
	{
		//ERROR: Variable in assignment does not appear in any functor
		return;
	}

	//Assumption: Right operator of assignment is value
	ParseVal* pValue = dynamic_cast<ParseVal*>(assign->assign);
	if (pValue == NULL)
	{
		//ERROR: Not a ParseVal
		return;
	}
	Expression* vPtr = ProcessParseVal(pValue);
	Constraint* cPtr = Constraint(Constraint::EQ, it->second, vPtr);
	rnode->UpdateConstraint(cPtr);
}

void
DPGraph::ProcessSelect(const ParseSelect* select,
					   const map<string, Variable*>& unifier,
					   RuleNode* rnode)
{
	ParseBool* pBool = select->select;
	Constraint* cPtr = ProcessParseBool(pBool, unifier);
	rnode->UpdateConstraint(cPtr);
}

const Expression*
DPGraph::ProcessExpr(const ParseExpr* pExpr,
					 const map<string, Variable*>&, unifier)
{
	ParseVal* pVal = NULL;
	ParseVar* pVar = NULL;
	ParseBool* pBool = NULL;
	ParseMath* pMath = NULL;

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
		return ProcessParseVar(pVar, );
	}
	pBool = dynamic_cast<ParseBool*>(pExpr);
	if (pBool != NULL)
	{
		//pExpr points to ParseBool type
		return ProcessParseBool(pBool);
	}
	pMath = dynamic_cast<ParseMath*>(pExpr);
	if (pMath != NULL)
	{
		//pExpr points to ParseBool type
		return ProcessParseMath(pMath);
	}
}

const Expression*
DPGraph::ProcessParseVal(const ParseVal* value,
						 const map<string, Variable*>)
{
	ValuePtr vPtr = value->Value();
	ValInt32* intPtr = dynamic_cast<ValInt32*>(vPtr);
	if (intPtr != NULL)
	{
		return (new IntVal(intPtr));
	}

	ValDouble* dbPtr = dynamic_cast<ValDouble*>(vPtr);
	if (dbPtr != NULL)
	{
		return (new DoubleVal(dbPtr));
	}
}

const Expression*
DPGraph::ProcessParseVar(const ParseVar* pVar,
						 const map<string, Variable*>& unifier)
{
	map<string, Variable*>::iterator it;
	it = unifier.find(pVar->ToString());
	if (it == unifier.end())
	{
		return NULL;
	}
	else
	{
		return it->second;
	}
}

const Constraint*
DPGraph::ProcessParseBool(const ParseBool* pBool,
						  const map<string, Variable*>& unifier)
{
	Constraint::Operator op;
	if (pBool->oper == ParseBool::EQ)
	{
		op = Constraint::EQ;
	}
	else if (pBool->oper == ParseBool::NEQ)
	{
		op = Constraint::NEG;
	}
	else if (pBool->oper == ParseBool::GT)
	{
		op = Constraint::GT;
	}
	else if (pBool->oper == ParseBool::LT)
	{
		op = Constraint::LT;
	}

	Expression* leftE = ProcessExpr(lhs, unifier);
	Expression* rightE = ProcessExpr(rhs, unifier);
	return Constraint(op, leftE, rightE);
}

const Expression*
DPGraph::ProcessParseMath(const ParseMath* pMath,
						  const map<string, Variable*>& unifier)
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

	Expression* leftE = ProcessParseExpr(lhs, unifier);
	Expression* rightE = ProcessParseExpr(rhs, unifier);
	return Arithmetic(op, leftE, rightE);
}

const TupleNode*
DPGraph::FindTupleNode(const ParseFunctor* tuple)
{
	string headName = tuple->fName->name;
	//TODO:Hash function could be quick in detecting
	//if a relation exists or not
	vector<TupleNode*>::iterator it;
	for (it = tnodeList.begin();it != tnodeList.end();it++)
	{
		tname = (*it)->GetName();
		if (tname == headName)
		{
			return (*it);
		}
	}
	return NULL;
}

void
DPGraph::PrintGraph()
{
	cout << "Tuple nodes:" << endl;
	vector<TupleNode*>::iterator itt;
	for (itt = tnodeList.begin();itt != tnodeList.end();itt++)
	{
		(*itt)->PrintNode();
	}

	cout << "Rule nodes:" << endl;
	vector<RuleNode*>::iterator itr;
	for (itr = rnodeList.begin();itr != rnodeList.end();itr++)
	{
		(*itr)->PrintNode();
	}
}
