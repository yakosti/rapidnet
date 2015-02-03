/*
 * sdn-constraint.cc
 *
 *  Created on: Nov 8, 2014
 *      Author: chen
 */

#include "sdn-derivation.h"

NS_LOG_COMPONENT_DEFINE ("Dpool");

CpoolEntry::CpoolEntry(const CpoolEntry& ce)
{
	clist = ce.clist;
	vmap = ce.vmap;
}

CpoolEntryInst*
CpoolEntry::GetConstraints() const
{
	CpoolEntryInst* cinst = new CpoolEntryInst();
	ConstraintList::const_iterator it;
	for (it = clist.begin(); it != clist.end(); it++)
	{
		Constraint* cst = new Constraint(**it);
		cst->ReplaceVar(vmap);
		cinst->AddConstraint(cst);
	}
	return cinst;
}

void
CpoolEntry::PrintEntry()
{
	cout << "CpoolEntry:" << endl;
	CpoolEntryInst* cinst = GetConstraints();
	cinst->PrintInst();
}

void
CpoolEntryInst::AddConstraint(Constraint* cst)
{
	instList.push_back(cst);
}

void
CpoolEntryInst::PrintInst() const
{
	ConstraintList::const_iterator it;
	for (it = instList.begin(); it != instList.end(); it++)
	{
		(*it)->PrintConstraint();
		cout << endl;
	}
}

CpoolEntryInst::~CpoolEntryInst()
{
	ConstraintList::iterator it;
	for (it = instList.begin(); it != instList.end(); it++)
	{
		delete (*it);
	}
}

Cpool::Cpool()
{
	constraints = list<CpoolEntry>();
}

Cpool::Cpool(const Cpool& cp)
{
	constraints = cp.constraints;
}

void
Cpool::AddConstraint(const CpoolEntry& ce)
{
	constraints.push_back(ce);
}

void
Cpool::Append(const Cpool& cp)
{
	const list<CpoolEntry>& cpcs = cp.constraints;
	constraints.insert(constraints.end(), cpcs.begin(), cpcs.end());
}

void
Cpool::PrintCpool()
{
	cout << "Cpool:" << endl;
	list<CpoolEntry>::iterator it;
	for (it = constraints.begin();it != constraints.end();it++)
	{
		(*it).PrintEntry();
		cout << endl;
	}
}

DerivNode::DerivNode(const TupleNode* h)
{
	head = h;
	rl = NULL;
	bodyDerivs = DerivBodyList();
	bodyCons = Cpool();
}

void
DerivNode::PrintHeadName()
{
	head->PrintName();
}

void
DerivNode::PrintDerivNode()
{
	cout << "Derivation Node:" << endl;
	cout << "Head:";
	head->PrintName();
	cout << endl;
	cout << "Rule name:";
	if (rl != NULL)
	{
		rl->PrintName();
	}
	else
	{
		cout << "No rule";
	}
	cout << endl;
	cout << "Body derivations:" << endl;
	DerivBodyList::iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->PrintDerivBody();
		cout << endl;
	}
	cout << "Children's constraints:" << endl;
	bodyCons.PrintCpool();
}

DerivNode::~DerivNode()
{
	DerivBodyList::iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		delete (*itd);
	}
}

void
DerivBody::PrintDerivBody()
{
	cout << "DerivBody:" << endl;
	cout << "Body tuple:";
	next->PrintHeadName();
	cout << endl;
	cout << "Unifications:" << endl;
	ConstraintList::iterator it;
	for (it = unifications.begin();it != unifications.end();it++)
	{
		(*it)->PrintConstraint();
		cout << endl;
	}
	cout << "Instantiation:" << endl;
	VarMap::iterator itv;
	for (itv = unifLabel.begin();itv != unifLabel.end();itv++)
	{
		itv->first->PrintTerm();
		cout << ":";
		itv->second->PrintTerm();
		cout << endl;
	}
}

DerivBody::~DerivBody()
{
	VarMap::iterator itv;
	for (itv = unifLabel.begin();itv != unifLabel.end();itv++)
	{
		//Destruct the variables for unification
		delete itv->second;
	}

	ConstraintList::iterator itc;
	for (itc = unifications.begin();itc != unifications.end();itc++)
	{
		delete (*itc);
	}
}

/*Dpool::Dpool(Ptr<DPGraph> dpgraph, const Annotation& invariants)
{
	//Perform topological sorting on the dependency graph
	NS_LOG_INFO("Topological sorting");
	Ptr<MiniGraph> mGraph (new MiniGraph(dpgraph));
	pair<MetaListC, RuleListC> topoOrder = mGraph->TopoSort(invariants);

	//Create a key in derivations for each tuple node in dpgraph
	const TupleList& tnlist = dpgraph->GetTupleList();
	TupleList::const_iterator itn;
	for (itn = tnlist.begin();itn != tnlist.end();itn++)
	{
		DerivNodeList dlist = DerivNodeList();
		const TupleNode* ctp = (*itn);
		derivations.insert(DerivMap::value_type(ctp, dlist));
	}

	//Process base tuples
	TupleListC& btlist = topoOrder.first;
	TupleListC::const_iterator itti;
	for (itti = btlist.begin();itti != btlist.end();itti++)
	{
		derivations[(*itti)].push_back(new DerivNode((*itti)));
	}

	//Process rule nodes based on topological order
	NS_LOG_INFO("Process rules based on topological sorting");
	const RuleListC& rlist = topoOrder.second;
	RuleListC::const_iterator itr;
	for (itr = rlist.begin();itr != rlist.end();itr++)
	{
		NS_LOG_DEBUG("Process a rule...");
		//Record all possible derivations of body tuples
		vector<DerivNodeList::const_iterator> itv;
		const TupleNode* head = dpgraph->GetHeadTuple((*itr));
		const TupleListC& tblist = dpgraph->GetBodyTuples((*itr));
		TupleListC::const_iterator itc = tblist.begin();

		//Recursively create DerivNode
		ProcessRuleNode(head, (*itr), tblist, itc, itv);
	}
}*/

void
Dpool::ProcessRuleNode(const TupleNode* head,
				   	   const RuleNode* rnode,
					   const TupleListC& bodyList,
					   TupleListC::const_iterator curPos,
					   vector<DerivNodeList::const_iterator> bodyDerivs)
{
	if (curPos == bodyList.end())
	{
		NS_LOG_DEBUG("Create a DerivNode after the recursion is done.");
		//All possible derivations of body tuples
		CreateDerivNode(head, rnode, bodyList, bodyDerivs);
		return;
	}

	const DerivNodeList& dlist = derivations[(*curPos)];
	curPos++;
	DerivNodeList::const_iterator itd;
	for (itd = dlist.begin();itd != dlist.end();itd++)
	{
		bodyDerivs.push_back(itd);
		ProcessRuleNode(head, rnode, bodyList, curPos, bodyDerivs);
	}
}

void
Dpool::CreateDerivNode(const TupleNode* head,
		 	 	 	   const RuleNode* rnode,
					   const TupleListC& bodyList,
					   vector<DerivNodeList::const_iterator>& bodyDerivs)
{
	cout << "Create a DerivNode: head->";
	head->PrintName();
	cout << ";rule->";
	rnode->PrintName();
	cout << endl;

	DerivBodyList elist;
	Cpool clist;	//Constraint pool of the DerivNode

	//Process rule bodies:
	//Create rule instantiation, unify tuples and collect constraints
	vector<DerivNodeList::const_iterator>::iterator it;
	for (it = bodyDerivs.begin();it != bodyDerivs.end();it++)
	{
		ConstraintList unif = ConstraintList();
		//Process a DerivNode and its derivation

		//Instantiation and unification of the rule in the DerivNode
		VarMap instantiation;
		(**it)->GetHeadNode()->Instantiate(instantiation);
		//Create unification for the header
		VarMap::const_iterator itv;
		for (itv = instantiation.begin(); itv != instantiation.end(); itv++)
		{
			Constraint* cst = new Constraint(Constraint::EQ, itv->first, itv->second);
			unif.push_back(cst);
		}

		const DerivBodyList& dlist = (**it)->GetDerivBodies();
		DerivBodyList::const_iterator itd;
		for (itd = dlist.begin();itd != dlist.end();itd++)
		{
			const TupleNode* tn = (*itd)->GetChild()->GetHeadNode();
			//Instantiation of body tuples
			tn->Instantiate(instantiation);
		}

		//Add new unification between the head of the child rule
		//and the corresponding body tuple in the current rule

		//Create the DerivBody
		DerivBody* bodyTuple = new DerivBody((**it), unif, instantiation);
		elist.push_back(bodyTuple);

		//NS_LOG_DEBUG("Collect constraints...");
		//Collect constraints
		//Copy the constraints from child DerivNode
		clist.Append((**it)->GetConstraints());
		//(2) Add the child rule's constraints
		const RuleNode* rn = (**it)->GetRuleNode();
		if (rn != NULL)
		{
			const ConstraintList& cst = (**it)->GetRuleNode()->GetConstraints();
			CpoolEntry entry = CpoolEntry(cst, instantiation);
			clist.AddConstraint(entry);
		}
		//(3) Add the old unifications of the child rule with new unifications
		const DerivBodyList& dblist = (**it)->GetDerivBodies();
		DerivBodyList::const_iterator itb;
		for (itb = dblist.begin();itb != dblist.end();itb++)
		{
			const ConstraintList& uniList = (*itb)->GetUnif();
			clist.AddConstraint(CpoolEntry(uniList, instantiation));
		}
	}

	DerivNode* dnode = new DerivNode(head, rnode, elist, clist);
	UpdateDerivNode(head, dnode);
}

void
Dpool::UpdateDerivNode(const TupleNode* tnode, DerivNode* dnode)
{
	derivations[tnode].push_back(dnode);
}

Derivation*
Dpool::GetDerivation(const DerivNode* dnode)
{
	Derivation* deriv = new Derivation();
	VarMap vmap = VarMap();

	//Get derivations of body tuples
	const DerivBodyList& dlist = dnode->GetDerivBodies();
	DerivBodyList::const_iterator it;
	for (it = dlist.begin(); it != dlist.end(); it++)
	{
		GetDerivInst(deriv, (*it)->GetChild(), (*it)->GetMap());
	}
	//Get the last derivation of the head tuple
	DerivInst* dinst = new DerivInst(dnode, VarMap());
	deriv->AddDerivInst(dinst);

	return deriv;
}

const DerivNodeList&
Dpool::GetDerivNodes(const TupleNode* tnode)
{
	return derivations.at(tnode);
}

void
Dpool::GetDerivInst(Derivation* deriv, const DerivNode* dnode, const VarMap& vmap)
{
	const DerivBodyList& dlist = dnode->GetDerivBodies();
	DerivBodyList::const_iterator it;
	for (it = dlist.begin(); it != dlist.end(); it++)
	{
		GetDerivInst(deriv, (*it)->GetChild(), (*it)->GetMap());
	}

	//Insert an instance of the rule in the current DerivNode
	DerivInst* dinst = new DerivInst(dnode, vmap);
	deriv->AddDerivInst(dinst);
}

void
Dpool::PrintDpool() const
{
	cout << "Derivation Pool" << endl;
	DerivMap::const_iterator itd;
	for (itd = derivations.begin();itd != derivations.end();itd++)
	{
		itd->first->PrintNode();
		cout << endl;
		const DerivNodeList& dlist = itd->second;
		DerivNodeList::const_iterator itn;
		int count = 1;
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
Dpool::PrintDerivs()
{
	cout << "Derivations" << endl;
	DerivMap::const_iterator itd;
	for (itd = derivations.begin(); itd != derivations.end(); itd++)
	{
		itd->first->PrintNode();
		DerivNodeList::const_iterator itc;
		const DerivNodeList& dlist = itd->second;
		for (itc = dlist.begin(); itc != dlist.end(); itc++)
		{
			//TODO: Decouple GetDerivation from printDerivs
			Derivation* deriv = GetDerivation((*itc));
			cout << endl;
			deriv->PrintDeriv();
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

DerivTuple::DerivTuple(const TupleNode* tp, const VarMap& vmap)
{
	name = tp->GetName();

	vector<Variable*>::const_iterator itv;
	const vector<Variable*>& tpArgs = tp->GetArgs();
	VarMap::const_iterator itm;
	for (itv = tpArgs.begin(); itv != tpArgs.end(); itv++)
	{
		itm = vmap.find((*itv));
		if (itm != vmap.end())
		{
			args.push_back(itm->second);
		}
		else
		{
			args.push_back(*itv);
		}
	}
}

void
DerivTuple::PrintTuple() const
{
	cout << name << "(";
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

DerivInst::DerivInst(const DerivNode* dnode, const VarMap& vmap)
{
	bodies = list<DerivTuple*>();
	constraints = new CpoolEntryInst();
	ConstraintList::const_iterator itc;
	//The head tuple
	head = new DerivTuple(dnode->GetHeadNode(), vmap);

	const RuleNode* rl = dnode->GetRuleNode();
	if (rl != NULL)
	{
		ruleName = rl->GetName();

		//Body tuples and unifications
		const DerivBodyList& dlist = dnode->GetDerivBodies();
		DerivBodyList::const_iterator itd;
		for (itd = dlist.begin(); itd != dlist.end(); itd++)
		{
			//Body tuples
			const DerivNode* child = (*itd)->GetChild();
			const TupleNode* tn = child->GetHeadNode();
			DerivTuple* dtuple = new DerivTuple(tn, (*itd)->GetMap());
			bodies.push_back(dtuple);

			//Unifications
			const ConstraintList& uniList = (*itd)->GetUnif();
			for (itc = uniList.begin(); itc != uniList.end(); itc++)
			{
				Constraint* cst = new Constraint((**itc));
				cst->ReplaceVar(vmap);
				constraints->AddConstraint(cst);
			}
		}

		const ConstraintList& clist = rl->GetConstraints();
		for (itc = clist.begin(); itc != clist.end(); itc++)
		{
			Constraint* cst = new Constraint((**itc));
			cst->ReplaceVar(vmap);
			constraints->AddConstraint(cst);
		}
	}
	else
	{
		ruleName = "";
	}
}

void
DerivInst::PrintInst() const
{
	cout << ruleName << " ";
	head->PrintTuple();
	cout << ":-" << endl;
	list<DerivTuple*>::const_iterator it;
	for (it = bodies.begin(); it != bodies.end(); it++)
	{
		(*it)->PrintTuple();
		cout << endl;
	}

	constraints->PrintInst();
}

DerivInst::~DerivInst()
{
	delete head;
	delete constraints;
	list<DerivTuple*>::iterator it;
	for (it = bodies.begin(); it != bodies.end(); it++)
	{
		delete (*it);
	}
}

Derivation::Derivation()
{
	deriv = list<DerivInst*>();
}

void
Derivation::AddDerivInst(DerivInst* dinst)
{
	deriv.push_back(dinst);
}

void
Derivation::PrintDeriv() const
{
	list<DerivInst*>::const_iterator itd;
	for (itd = deriv.begin(); itd != deriv.end(); itd++)
	{
		(*itd)->PrintInst();
		cout << endl << endl;
	}
}

Derivation::~Derivation()
{
	list<DerivInst*>::iterator it;
	for (it = deriv.begin(); it != deriv.end(); it++)
	{
		delete (*it);
	}
}
