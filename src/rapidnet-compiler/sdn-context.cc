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

void
Node::PrintNode()
{
	cout << name << endl;
}

void
RuleNode::UpdateUnif(Variable* v1, Variable* v2)
{
	Constraint* unification = new Constraint(Constraint::EQ, v1, v2);
	constraints.push_back(unification);
}

void
RuleNode::UpdateConstraint(Constraint* cPtr)
{
	constraints.push_back(cPtr);
}

void
RuleNode::PrintNode()
{
	cout << "Rule ID: " << name << endl;
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

TupleNode::TupleNode(ParseFunctor* tuple):
		Node(tuple->fName->ToString())
{
	deque<ParseExpr*>::iterator it;
	ParseExprList *pargs = tuple->m_args;
	for (it = pargs->begin();it != pargs->end(); it++)
	{
		ParseVar* varPtr = dynamic_cast<ParseVar*>(*it);
		if (varPtr != NULL)
		{
			ValuePtr vPtr = varPtr->value;
			ParsedValue::TypeCode tp = vPtr->GetTypeCode();
			if (tp == ParsedValue::STR)
			{
				args.push_back(new Variable(Variable::STRING));
				break;
			}
			if (tp == ParsedValue::DOUBLE)
			{
				args.push_back(new Variable(Variable::DOUBLE));
				break;
			}
			if (tp == ParsedValue::INT32)
			{
				args.push_back(new Variable(Variable::INT));
				break;
			}
		}
		else
		{
			//ERROR: Non-variable argument
		}
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

TupleNode::~TupleNode()
{
	vector<Variable*>::iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		delete (*it);
	}
}

DPGraph::DPGraph(Ptr<OlContext> ctxt)
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
DPGraph::ProcessRule(OlContext::Rule* r)
//Change return value if needed
{
	map<string, Variable*> unifier;
	RuleNode* rnode = new RuleNode(r->ruleID);

	//Process head tuple
	//Assumption: head tuple does not have duplicate arguments
	ProcessFunctor(r->head, unifier, rnode);

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
			ProcessFunctor(functor, unifier, rnode);
			break;
		}

		if (assign != NULL)
		{
			ProcessAssign(assign, unifier, rnode);
			break;
		}

		if (select != NULL)
		{

			break;
		}
	}
}

void
DPGraph::ProcessFunctor(ParseFunctor* fct,
						map<string, Variable*>& unifier,
						RuleNode* rnode)
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
	deque<ParseExpr*>::iterator itd = headArgs->begin();
	vector<Variable*>& tArgs = tnode->GetArgs();
	vector<Variable*>::iterator itv = tArgs.begin();
	for (;itd != headArgs->end();itd++,itv++)
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
DPGraph::ProcessAssign(ParseAssign* assign,
					   map<string, Variable*>& unifier,
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
	Constraint* cPtr = new Constraint(Constraint::EQ, it->second, vPtr);
	rnode->UpdateConstraint(cPtr);
}

void
DPGraph::ProcessSelect(ParseSelect* select,
					   map<string, Variable*>& unifier,
					   RuleNode* rnode)
{
	ParseBool* pBool = select->select;
	Constraint* cPtr = ProcessParseBool(pBool, unifier);
	rnode->UpdateConstraint(cPtr);
}

Expression*
DPGraph::ProcessExpr(ParseExpr* pExpr,
					 map<string, Variable*>& unifier)
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
		return ProcessParseVar(pVar, unifier);
	}
	pBool = dynamic_cast<ParseBool*>(pExpr);
	if (pBool != NULL)
	{
		//pExpr points to ParseBool type
		return ProcessParseBool(pBool, unifier);
	}
	pMath = dynamic_cast<ParseMath*>(pExpr);
	if (pMath != NULL)
	{
		//pExpr points to ParseBool type
		return ProcessParseMath(pMath, unifier);
	}

	return NULL;
}

Expression*
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

	return NULL;
}

Expression*
DPGraph::ProcessParseVar(ParseVar* pVar,
						 map<string, Variable*>& unifier)
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

Constraint*
DPGraph::ProcessParseBool(ParseBool* pBool,
						  map<string, Variable*>& unifier)
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

	Expression* leftE = ProcessExpr(pBool->lhs, unifier);
	Expression* rightE = ProcessExpr(pBool->rhs, unifier);
	return (new Constraint(op, leftE, rightE));
}

Expression*
DPGraph::ProcessParseMath(ParseMath* pMath,
						  map<string, Variable*>& unifier)
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

	Expression* leftE = ProcessExpr(pMath->lhs, unifier);
	Expression* rightE = ProcessExpr(pMath->rhs, unifier);
	return (new Arithmetic(op, leftE, rightE));
}

TupleNode*
DPGraph::FindTupleNode(ParseFunctor* tuple)
{
	string headName = tuple->fName->name;
	//TODO:Hash function could be quick in detecting
	//if a relation exists or not
	vector<TupleNode*>::iterator it;
	for (it = tnodeList.begin();it != tnodeList.end();it++)
	{
		string tname = (*it)->GetName();
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
