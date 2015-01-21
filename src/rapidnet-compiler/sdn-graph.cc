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

NS_LOG_COMPONENT_DEFINE ("SdnContext");

Relation::Relation(ParseFunctor* tuple):
		relName(tuple->fName->ToString())
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
			if (tp == ParsedValue::STR || tp == ParsedValue::IP_ADDR)
			{
  			    args.push_back(new Variable(Variable::STRING, true));
				continue;
			}
			if (tp == ParsedValue::DOUBLE)
			{
			    args.push_back(new Variable(Variable::DOUBLE, true));
				continue;
			}
			if (tp == ParsedValue::INT32)
			{
			    args.push_back(new Variable(Variable::INT, true));
				continue;
			}
			if (tp == ParsedValue::LIST)
			{
			    args.push_back(new Variable(Variable::LIST, true));
				continue;
			}
		}
		else
		{
			NS_LOG_ERROR("Non-variable argument");
			//ERROR: Non-variable argument
		}
	}
}

void
Relation::PrintRelation() const
{
	cout << relName << "(";
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

Relation::~Relation()
{
	vector<Variable*>::iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		delete (*it);
	}
}

//Implementation of ConstraintsTemplate
void
ConstraintsTemplate::AddConstraint(Constraint* cst)
{
	constraints.push_back(cst);
}

ConstraintsTemplate::~ConstraintsTemplate()
{
	ConstraintList::iterator it;
	for (it = constraints.begin(); it != constraints.end(); it++)
	{
		delete (*it);
	}
}

void
ConstraintsTemplate::PrintTemplate() const
{
	ConstraintList::const_iterator itc;
	for (itc = constraints.begin(); itc != constraints.end(); itc++)
	{
	  cout << "\t";
	  (*itc)->PrintConstraint();
	  cout << endl;
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
}

RuleNode::~RuleNode()
{
	delete cTemp;
}

TupleNode::TupleNode(ParseFunctor* tp)
{
	rel = new Relation(tp);
}

void
TupleNode::Instantiate(VarMap& vmap) const
{
	const vector<Variable*>& args = rel->GetArgs();
	vector<Variable*>::const_iterator itv;
	for (itv = args.begin();itv != args.end();itv++)
	{
		Variable* var = new Variable((*itv)->GetVariableType(), false);
		vmap.insert(VarMap::value_type((*itv), var));
	}
}

void
TupleNode::PrintName() const
{
	cout << rel->GetName() << endl;
}

void
TupleNode::PrintNode() const
{
	rel->PrintRelation();
}

TupleNode::~TupleNode()
{
	delete rel;
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
	NS_LOG_DEBUG("DPGraph construction over!");
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
	RuleNode* rnode = new RuleNode(r->ruleID);
	ruleNodes.push_back(rnode);

	//Process the head tuple
	//Assumption: head tuple does not have duplicate arguments
	TupleNode* hTuple = ProcessFunctor(r->head, unifier, rnode);
	outEdgeRL.insert(RHMap::value_type(rnode, hTuple));

	//Process body terms
	list<ParseTerm*>::iterator it;
	ParseFunctor *functor = NULL;
	ParseAssign *assign = NULL;
	ParseSelect *select = NULL;
	for (it = r->terms.begin(); it != r->terms.end(); it++)
	{
	    NS_LOG_DEBUG("See how many times I run");
		functor = dynamic_cast<ParseFunctor *>(*it);
		if (functor != NULL)
		{
		    NS_LOG_DEBUG("Processing Functor:\t" << (functor->fName->ToString()));
			TupleNode* bTuple = ProcessFunctor(functor, unifier, rnode);
			inEdgesRL[rnode].push_back(bTuple);
			continue;
		}

		//Process assignment
		assign = dynamic_cast<ParseAssign *>(*it);
		if (assign != NULL)
		{
			ProcessAssign(assign, unifier, rnode);
			continue;
		}

		//Process select
		select = dynamic_cast<ParseSelect *>(*it);
		if (select != NULL)
		{
			ProcessSelect(select, unifier, rnode);
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
	//Find corresponding TupleNode. Create one if nothing is found
	TupleNode* tnode = FindTupleNode(fct);
	if (tnode == NULL)
	{
		tnode = new TupleNode(fct);
		tupleNodes.push_back(tnode);
		NS_LOG_DEBUG("\n Create a new tuple node:");
		//tnode->PrintNode();
	}

	//Process arguments of the tuple
	ParseExprList* headArgs = fct->m_args;
	deque<ParseExpr*>::iterator itd = headArgs->begin();
	const vector<Variable*>& tArgs = tnode->GetArgs();
	vector<Variable*>::const_iterator itv = tArgs.begin();

	for (;itd != headArgs->end();itd++,itv++)
	{
		ParseVar* vPtr = dynamic_cast<ParseVar*>(*itd);
		pair<map<string,Variable*>::iterator, bool> ret;
		ret = unifier.insert(pair<string,Variable*>(vPtr->ToString(), (*itv)));
		if (ret.second == false)
		{
			//Update unification in rnode
			rnode->UpdateUnif(ret.first->second,(*itv));
		}
	}
    NS_LOG_DEBUG("Reach here?");
	return tnode;
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
	Term* vPtr = ProcessParseVal(pValue);
	Constraint* cPtr = new Constraint(Constraint::EQ, it->second, vPtr);
	rnode->UpdateConstraint(cPtr);
}

void
DPGraph::ProcessSelect(ParseSelect* select,
					   map<string, Variable*>& unifier,
					   RuleNode* rnode)
{
	ParseBool* pBool = select->select;
	Constraint* cPtr = ProcessConstraint(pBool, unifier);
	rnode->UpdateConstraint(cPtr);
}

Term*
DPGraph::ProcessExpr(ParseExpr* pExpr,
					 map<string, Variable*>& unifier)
{
	//Currently we do not process ParseBool in ParseExpr
	ParseVal* pVal = NULL;
	ParseVar* pVar = NULL;
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
	pMath = dynamic_cast<ParseMath*>(pExpr);
	if (pMath != NULL)
	{
		//pExpr points to ParseBool type
		return ProcessParseMath(pMath, unifier);
	}

	return NULL;
}

Term*
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

Term*
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

Term*
DPGraph::ProcessParseFunc(ParseFunction* pFunc,
						  map<string, Variable*>& unifier)
{

}

Constraint*
DPGraph::ProcessConstraint(ParseBool* pBool,
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

	Term* leftE = ProcessExpr(pBool->lhs, unifier);
	Term* rightE = ProcessExpr(pBool->rhs, unifier);
	return (new Constraint(op, leftE, rightE));
}

Term*
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

	Term* leftE = ProcessExpr(pMath->lhs, unifier);
	Term* rightE = ProcessExpr(pMath->rhs, unifier);
	return (new Arithmetic(op, leftE, rightE));
}

TupleNode*
DPGraph::FindTupleNode(ParseFunctor* tuple)
{
	string headName = tuple->fName->name;
	NS_LOG_DEBUG("Tuple name:" << headName << endl);
	//TODO:Hash function could be quick in detecting
	//if a relation exists or not
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

	RuleList::iterator itt;
	for (itt = ruleNodes.begin();itt != ruleNodes.end();itt++)
	{
		delete (*itt);
	}
}

MiniGraph::MiniGraph(Ptr<DPGraph> dpgraph)
{
	outEdgeRL = dpgraph->outEdgeRL;
	inEdgesRL = dpgraph->inEdgesRL;

	TupleList::iterator itt;
	TupleList& tnodes = dpgraph->tupleNodes;
	for (itt = tnodes.begin(); itt != tnodes.end(); itt++)
	{
		RuleListC rlist;
		outEdgesTP.insert(TRMap::value_type((*itt),rlist));
		inEdgesTP.insert(TRMap::value_type((*itt),rlist));
	}

	RHMap::iterator itr;
	RHMap& outE = dpgraph->outEdgeRL;
	for (itr = outE.begin(); itr != outE.end(); itr++)
	{
		inEdgesTP[itr->second].push_back(itr->first);
	}

	RBMap::iterator itb;
	RBMap& inE = dpgraph->inEdgesRL;
	for (itb = inE.begin(); itb != inE.end(); itb++)
	{
		TupleListC& tvec = itb->second;
		TupleListC::iterator itp;
		for (itp = tvec.begin(); itp != tvec.end(); itp++)
		{
			outEdgesTP[(*itp)].push_back(itb->first);
		}
	}
}

pair<TupleListC, RuleListC>
MiniGraph::TopoSort()
{
	//TupleList: a list of base tuples
	//RuleList: an ordered list of rules
	pair<TupleListC, RuleListC> topoOrder;

	//Topological sort
	deque<const Node*> processQueue;
	TRMap::const_iterator itti;
	for (itti = inEdgesTP.begin();itti != inEdgesTP.end();itti++)
	{
		if (itti->second.size() == 0)
		{
			//Record all base tuples
			topoOrder.first.push_back(itti->first);
			processQueue.push_back(itti->first);
		}
	}

	while (processQueue.size() > 0)
	{
		const Node* curNode = processQueue.front();
		processQueue.pop_front();
		//Process a tuple node
		const TupleNode* tnode = dynamic_cast<const TupleNode*>(curNode);
		if (tnode != NULL)
		{
			//Delete the corresponding entry in inEdgesTP
			inEdgesTP.erase(tnode);
			RuleListC& rlist = outEdgesTP[tnode];
			RuleListC::iterator itrl;
			for (itrl = rlist.begin();itrl != rlist.end();itrl++)
			{
				TupleListC& tlist = inEdgesRL[(*itrl)];
				tlist.remove(tnode);
				if (tlist.size() == 0)
				{
					processQueue.push_back((*itrl));
				}
			}
		}

		const RuleNode* rnode = dynamic_cast<const RuleNode*>(curNode);
		if (rnode != NULL)
		{
			//Store the topological order of the rule node
			topoOrder.second.push_back(rnode);
			//Delete the corresponding entry in inEdgesRL
			inEdgesRL.erase(rnode);
			const TupleNode* tn = outEdgeRL[rnode];
			RuleListC& rl = inEdgesTP[tn];
			rl.remove(rnode);
			if (rl.size() == 0)
			{
				processQueue.push_back(tn);
			}
		}
	}

	return topoOrder;
}

void
MiniGraph::PrintGraph() const
{
	cout << "Rule node edges (outbound):" << endl;
	RHMap::const_iterator itrh;
	for (itrh = outEdgeRL.begin();itrh != outEdgeRL.end();itrh++)
	{
		cout << "Rule name and constraints:" << endl;
		itrh->first->PrintNode();
		cout << endl;
		cout << "Rule head:";
		itrh->second->PrintName();
		cout << endl;
	}
	cout << endl;

	cout << "Rule node edges (inbound):" << endl;
	RBMap::const_iterator itrb;
	TupleListC::const_iterator ittv;
	for (itrb = inEdgesRL.begin();itrb != inEdgesRL.end();itrb++)
	{
		cout << "Rule name:" << endl;
		itrb->first->PrintName();
		cout << endl << endl;
		cout << "Rule bodies:" << endl;
		const TupleListC& tnodes = itrb->second;
		for (ittv = tnodes.begin();ittv != tnodes.end();ittv++)
		{
			cout << "\t";
			(*ittv)->PrintNode();
			cout << endl;
		}
		cout << endl;
	}
	cout << endl;

	cout << "Tuple node edges (outbound):" << endl;
	TRMap::const_iterator itti;
	RuleListC::const_iterator itri;
	for (itti = outEdgesTP.begin();itti != outEdgesTP.end();itti++)
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
	for (itti = inEdgesTP.begin();itti != inEdgesTP.end();itti++)
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
