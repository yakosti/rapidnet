/*
 * sdn-constraint.cc
 *
 *  Created on: Nov 8, 2014
 *      Author: chen
 */

#include "sdn-derivation.h"

NS_LOG_COMPONENT_DEFINE ("Dpool");

DerivNode::DerivNode(const Tuple* tp)
{
	head = new Tuple(tp->GetName(),tp->GetSchema());
	ruleName = "";
	ruleConstraints = NULL;
	bodyDerivs = DerivNodeList();
	bodyAnnotations = DerivAnnoList();
	allConstraints = ConsList();
	allInvs = FormList();
}

DerivNode::DerivNode(string tpName, list<Variable::TypeCode>& tlist)
{
	head = new Tuple(tpName,tlist);
	ruleName = "";
	ruleConstraints = NULL;
	bodyDerivs = DerivNodeList();
	bodyAnnotations = DerivAnnoList();
	allConstraints = ConsList();
	allInvs = FormList();
}

void
DerivNode::AddRuleName(string rName)
{
	ruleName = rName;
}

void
DerivNode::AddChildDerivNode(DerivNode* dnode)
{
	bodyDerivs.push_back(dnode);
}

void
DerivNode::UpdateConstraint(ConstraintsTemplate* ctp)
{
	ruleConstraints = ctp;
}

void
DerivNode::PrintHead() const
{
	head->PrintTuple();
}

void
DerivNode::PrintDerivNode() const
{
	cout << "Derivation Node:" << endl;
	cout << "Head:";
	head->PrintTuple();
	cout << endl;
	cout << "Rule name:" << ruleName;
	cout << endl;
	cout << "Body tuples:" << endl;
	DerivNodeList::const_iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->PrintHead();
		cout << endl;
	}
	DerivAnnoList::const_iterator ita;
	for (ita = bodyAnnotations.begin();ita != bodyAnnotations.end();ita++)
	{
		(*ita)->PrintHead();
		cout << endl;
	}
	if (ruleConstraints != NULL)
	{
		cout << "Constraints:" << endl;
		ruleConstraints->PrintTemplate();
	}
}

void
DerivNode::PrintDerivation() const
{
	PrintDerivNode();

	DerivNodeList::const_iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->PrintDerivation();
		cout << endl;
	}
	DerivAnnoList::const_iterator ita;
	for (ita = bodyAnnotations.begin();ita != bodyAnnotations.end();ita++)
	{
		(*ita)->PrintDerivation();
		cout << endl;
	}
}

DerivNode::~DerivNode()
{
	delete head;
	delete ruleConstraints;
}

RecurNode::RecurNode(const Tuple* tp):
		DerivNode(tp)
{
	invariant = NULL;
}

void
RecurNode::AddInvariant(Formula* inv)
{
	invariant = inv;
}

void
RecurNode::PrintDerivNode() const
{
	DerivNode::PrintDerivNode();

	cout << "User-annotated formula:" << endl;
	invariant->Print();
	cout << endl;
}

RecurNode::~RecurNode()
{
	delete head;
	delete ruleConstraints;
	DerivNodeList::iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		delete(*itd);
	}
}

Dpool::Dpool(const Ptr<DPGraph> dpgraph, const AnnotMap& invariants)
{
	//Perform topological sorting on the dependency graph
	NS_LOG_INFO("Topological sorting");
	const TupleNode* head = NULL;
	Ptr<MiniGraph> mGraph (new MiniGraph(dpgraph));
	pair<RuleListC, RuleListC> topoOrder = mGraph->TopoSort(invariants);
	MetaListC btlist = mGraph->GetBaseTuples();

	//Create a key in derivations for each tuple node in dpgraph
	NS_LOG_INFO("Creating Dpool...");
	const TupleList& tnlist = dpgraph->GetTupleList();
	TupleList::const_iterator itn;
	DerivNodeList dlist = DerivNodeList();
	for (itn = tnlist.begin();itn != tnlist.end();itn++)
	{
		string headName = (*itn)->GetName();
		derivations.insert(DerivMap::value_type(headName, dlist));
	}

	//Process base tuples
	//TODO: Handle cases where base tuples have annotations
	NS_LOG_INFO("Process base tuples...");
	NS_LOG_DEBUG("Size of MetaList:" << btlist.size());
	MetaListC::const_iterator itti;
	for (itti = btlist.begin();itti != btlist.end();itti++)
	{
		list<Variable::TypeCode> tlist = (*itti)->GetSchema();
		string tpName = (*itti)->GetName();
		DerivNode* dNode = new DerivNode(tpName, tlist);
		UpdateDerivNode(tpName, dNode);
	}

	//Process rule nodes that cause loops
	//Add the invariant of the head to the created RecurNode
	NS_LOG_INFO("Process rules that cause loops...");
	RuleListC& loopList = topoOrder.second;
	RuleListC::const_iterator itl;
	for (itl = loopList.begin();itl != loopList.end();itl++)
	{
		head = dpgraph->GetHeadTuple((*itl));
		const Tuple* headTuple = head->GetTuple();
		RecurNode* rnode = new RecurNode(headTuple);

		string ruleName = (*itl)->GetName();
		rnode->AddRuleName(ruleName);

		//Add the annotation to the node
		string tpName = headTuple->GetName();
		const Annotation* inv = invariants.at(tpName);
		Formula* newInv = inv->second->Clone();
		const Tuple* tpr = rnode->GetHeadTuple();
		VarMap vmapInv = inv->first->CreateVarMap(tpr);
		newInv->VarReplace(vmapInv);
		rnode->AddInvariant(newInv);

		//Add child DerivNodes and unify variables in constraints
		VarMap vmapTuple = headTuple->CreateVarMap(rnode->GetHeadTuple());
		const TupleListC bodyList = dpgraph->GetBodyTuples(*itl);
		const Tuple* tNode = NULL;
		DerivNode* newNode = NULL;
		TupleListC::const_iterator itt;
		for (itt = bodyList.begin();itt != bodyList.end();itt++)
		{
			tNode = (*itt)->GetTuple();
			newNode = new DerivNode(tNode);
			VarMap newMap = tNode->CreateVarMap(newNode->GetHeadTuple());
			vmapTuple.insert(newMap.begin(), newMap.end());
			rnode->AddChildDerivNode(newNode);
		}

		//Replace variables in rule constraints
		const ConstraintsTemplate* ruleCons = (*itl)->GetConsTemp();
		ConstraintsTemplate* newCons = new ConstraintsTemplate(*ruleCons);
		newCons->ReplaceVar(vmapTuple);
		rnode->UpdateConstraint(newCons);

		UpdateDerivNode(head->GetName(), rnode);
	}

	//Process rule nodes based on topological order
	NS_LOG_INFO("Process rules based on topological sorting...");
	RuleListC& rlist = topoOrder.first;
	RuleListC::const_iterator itr;
	for (itr = rlist.begin();itr != rlist.end();itr++)
	{
		NS_LOG_DEBUG("Process a rule...");
		//Record all possible derivations of body tuples
		vector<DerivNodeList::const_iterator> itv;
		const TupleListC& tblist = dpgraph->GetBodyTuples((*itr));

		head = dpgraph->GetHeadTuple((*itr));
		const Tuple* hdTuple = head->GetTuple();
		Tuple* headInst = new Tuple(hdTuple->GetName(), hdTuple->GetSchema());
		VarMap unifMap = hdTuple->CreateVarMap(headInst);

		//Recursively create DerivNode
		ProcessRuleNode(headInst, (*itr), tblist, tblist.begin(), itv, unifMap);
	}
}

void
Dpool::ProcessRuleNode(Tuple* head,
				   	   const RuleNode* rnode,
					   const TupleListC& bodyList,
					   TupleListC::const_iterator curPos,
					   vector<DerivNodeList::const_iterator> bodyDerivs,
					   VarMap vmap)
{
	if (curPos == bodyList.end())
	{
		NS_LOG_DEBUG("Create a DerivNode after the recursion is done.");
		//All possible derivations of body tuples
		CreateDerivNode(head, rnode, bodyList, bodyDerivs, vmap);
		return;
	}

	const DerivNodeList& dlist = derivations.at((*curPos)->GetName());
	TupleListC::const_iterator curBody = curPos;
	NS_LOG_DEBUG("Size of dlist:" << dlist.size());
	curPos++;
	DerivNodeList::const_iterator itd;
	for (itd = dlist.begin();itd != dlist.end();itd++)
	{
		//Record the derivation of body tuples
		bodyDerivs.push_back(itd);

		//Create variable mapping
		const Tuple* bodyTuple = (*curBody)->GetTuple();
		VarMap newMap = bodyTuple->CreateVarMap((*itd)->GetHeadTuple());
		vmap.insert(newMap.begin(), newMap.end());
		ProcessRuleNode(head, rnode, bodyList, curPos, bodyDerivs, vmap);
	}
}

void
Dpool::CreateDerivNode(Tuple* head,
		 	 	 	   const RuleNode* rnode,
					   const TupleListC& bodyList,
					   vector<DerivNodeList::const_iterator>& bodyDerivs,
					   VarMap& vmap)
{
	cout << "Create a DerivNode:" << endl;
	cout << "head:";
	head->PrintTuple();
	cout << endl;
	cout << "rule:";
	rnode->PrintName();
	cout << endl;

	DerivNodeList dblist;
	DerivAnnoList dalist;
	ConsList cslist;
	FormList flist;

	//Process the rule
	vector<DerivNodeList::const_iterator>::iterator it;
	NS_LOG_DEBUG("Size of bodyDerivs: " << bodyDerivs.size());
	for (it = bodyDerivs.begin();it != bodyDerivs.end();it++)
	{
		//Determine if the DerivNode is RecurNode
		const RecurNode* rNode = dynamic_cast<const RecurNode*>(**it);
		if (rNode != NULL)
		{
			dalist.push_back(rNode);
			flist.push_back(rNode->GetInv());
		}
		else
		{
			//Add pointer to the corresponding DerivNode of the body tuple
			dblist.push_back(**it);

			//Add references to cumulative constraints
			const ConsList& clist = (**it)->GetCumuConsts();
			cslist.insert(cslist.end(), clist.begin(), clist.end());
			cslist.push_back((**it)->GetConstraints());
		}
	}

	//Replace variables in rule constraints
	const ConstraintsTemplate* ruleCons = rnode->GetConsTemp();
	ConstraintsTemplate* newCons = new ConstraintsTemplate(*ruleCons);
	newCons->ReplaceVar(vmap);

	DerivNode* dnode = new DerivNode(head, rnode->GetName(),
									 newCons, dblist, dalist,
									 cslist, flist);
	UpdateDerivNode(head->GetName(), dnode);
}

void
Dpool::UpdateDerivNode(string tpName, DerivNode* dnode)
{
	derivations[tpName].push_back(dnode);
}

void
Dpool::PrintDpool() const
{
	cout << "Derivation Pool" << endl;
	DerivMap::const_iterator itd;
	for (itd = derivations.begin();itd != derivations.end();itd++)
	{
		cout << itd->first << endl;
		const DerivNodeList& dlist = itd->second;
		DerivNodeList::const_iterator itn;
		int count = 1;
		NS_LOG_DEBUG("size of Dpool:" << dlist.size());
		for (itn = dlist.begin();itn != dlist.end();itn++, count++)
		{
			cout << "The " << count << "th derivation" << endl;
			(*itn)->PrintDerivNode();
			cout << endl;
		}
		cout << endl;
	}
}

void
Dpool::PrintDeriv(string tpName) const
{
	cout << "Derivations of relation:" << tpName << endl;
	DerivNodeList dlist = derivations.at(tpName);
	DerivNodeList::const_iterator itc;
	for (itc = dlist.begin(); itc != dlist.end(); itc++)
	{
		(*itc)->PrintDerivation();
		cout << endl << endl;
	}
}

void
Dpool::PrintAllDeriv() const
{
	cout << "----------------- All Derivations --------------" << endl;
	DerivMap::const_iterator it;
	for (it = derivations.begin();it != derivations.end();it++)
	{
		cout << "---------------- " << it->first << " ---------------" << endl;
		DerivNodeList::const_iterator itc;
		for (itc = it->second.begin(); itc != it->second.end(); itc++)
		{
			(*itc)->PrintDerivation();
			cout << endl << endl;
			cout << "************" << endl;
		}
	}
}

Dpool::~Dpool()
{
	//Destruct instances of TupleD and DerivNode
	DerivMap::iterator itd;
	for (itd = derivations.begin();itd != derivations.end();itd++)
	{
		//Destruct instances of DerivNode
		DerivNodeList::iterator itl;
		DerivNodeList& dlist = itd->second;
		for (itl = dlist.begin();itl != dlist.end();itl++)
		{
			delete (*itl);
		}
	}
}
