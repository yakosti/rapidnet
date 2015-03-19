/*
 * sdn-constraint.cc
 *
 *  Created on: Nov 8, 2014
 *      Author: chen
 */

#include "sdn-derivation.h"

NS_LOG_COMPONENT_DEFINE ("Dpool");

DpoolNode::DpoolNode(string tpName, int argSize)
{
	head = new Tuple(tpName, argSize);
}

DpoolNode::DpoolNode(const Tuple* tp)
{
	string tpName = tp->GetName();
	int argSize = tp->GetArgLength();
	head = new Tuple(tpName, argSize);
}

DpoolNode::DpoolNode(const PredicateInstance* pred)
{
	string predName = pred->GetName();
	int argSize = pred->GetArgs().size();
	head = new Tuple(predName, argSize);
}

void
DpoolNode::PrintHead() const
{
	head->PrintTuple();
}

void
DpoolNode::PrintHeadInst(const map<Variable*, int>& valueMap) const
{
	head->PrintInstance(valueMap);
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
DerivNode::UpdateCumuCons(ConsList& clist)
{
	allConstraints = clist;
}

void
DerivNode::ReplaceVar(VarMap& vmap)
{
	ruleConstraints->ReplaceVar(vmap);
}

Obligation
DerivNode::GetAllObligs() const
{
	return Obligation(allConstraints, allInvs);
}

void
DerivNode::FindSubTuple(const list<PredicateInstance*>& plist,
					    map<string, list<const Tuple*> >& tlist) const
{
	//Assume tlist has been initialized according to plist
	string tpName = head->GetName();
	map<string, list<const Tuple*> >::iterator itm;
	itm = tlist.find(tpName);
	if (itm != tlist.end())
	{
		//The tuple needs to be registered
		itm->second.push_back(head);
	}

	DpoolNodeList::const_iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->FindSubTuple(plist, tlist);
	}
}

void
DerivNode::PrintCumuCons() const
{
	cout << endl;
	cout << "============ Cumulative Simplified Constraints ===========" << endl;
	SimpConstraints simp(allConstraints);
	simp.Print();
	cout << "=======================";
	cout << endl;
}

void
DerivNode::PrintDerivNode() const
{
	cout << endl;
	cout << "$$$$$$$$$$$$ Derivation Node $$$$$$$$$$$" << endl;
	cout << "Head:";
	head->PrintTuple();
	cout << endl;
	cout << "Rule name:" << ruleName;
	cout << endl;
	cout << "Body tuples:" << endl;
	NS_LOG_DEBUG("Number of bodies: " << bodyDerivs.size());
	DpoolNodeList::const_iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->PrintHead();
		cout << endl;
	}
	if (ruleConstraints != NULL)
	{
		cout << "Constraints:" << endl;
		ruleConstraints->PrintTemplate();
		cout << endl;
		ConsList clist(1, ruleConstraints);
		SimpConstraints simpCons(clist);
		simpCons.Print();
	}

	PrintCumuCons();
	cout << "$$$$$$$$$$$$$$$$$$$$$$$$$" << endl;
}

void
DerivNode::PrintInstance(const map<Variable*, int>& valueMap) const
{
	cout << endl;
	cout << "%%%%%%%%%%%%%% Derivation Instance %%%%%%%%%%%%%" << endl;
	cout << "Head:";
	head->PrintInstance(valueMap);
	cout << endl;
	cout << "Rule name:" << ruleName;
	cout << endl;
	cout << "Body tuples:" << endl;
	NS_LOG_DEBUG("Number of bodies: " << bodyDerivs.size());
	DpoolNodeList::const_iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->PrintHeadInst(valueMap);
		cout << endl;
	}
	if (ruleConstraints != NULL)
	{
		cout << "Constraints:" << endl;
		ruleConstraints->PrintInstance(valueMap);
		cout << endl;
	}
	cout << "%%%%%%%%%%%%%%%%%%%%%%%%%%%" << endl;
}

void
DerivNode::PrintDerivation() const
{
	PrintDerivNode();
	PrintCumuCons();

	DpoolNodeList::const_iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->PrintDerivation();
		cout << endl;
	}
}

void
DerivNode::PrintExecution(map<Variable*, int>& valueMap) const
{
	PrintInstance(valueMap);

	DpoolNodeList::const_iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->PrintExecution(valueMap);
		cout << endl;
	}
}

DerivNode::~DerivNode()
{
	delete head;
	delete ruleConstraints;
}

BaseNode::BaseNode(const PredicateInstance* pred, const ConstraintsTemplate& ctemp):
		DpoolNode(pred)
{
	cts = new ConstraintsTemplate(ctemp);
	VarMap vmap = head->CreateVarMap(pred);
	cts->ReplaceVar(vmap);
}

BaseNode::BaseNode(const Tuple* tp):
		DpoolNode(tp)
{
	cts = NULL;
}

BaseNode::BaseNode(string tpName, int argSize):
		DpoolNode(tpName, argSize)
{
	cts = NULL;
}

void
BaseNode::FindSubTuple(const list<PredicateInstance*>& plist,
				  	   map<string, list<const Tuple*> >& tlist) const
{
	//Assume tlist has been initialized according to plist
	string tpName = head->GetName();
	map<string, list<const Tuple*> >::iterator itm;
	itm = tlist.find(tpName);
	if (itm != tlist.end())
	{
		//The tuple needs to be registered
		itm->second.push_back(head);
	}
}

void
BaseNode::PrintCumuCons() const
{
	cout << endl;
	cout << "+++++++ BaseNode Constraints ++++++" << endl;
	if (cts != NULL)
	{
		cts->PrintTemplate();
	}
	cout << "++++++++++++++++++++++++" << endl;
}

void
BaseNode::PrintDerivNode() const
{
	cout << endl;
	cout << "******* Base Node ********" << endl;
	cout << "Head: ";
	head->PrintTuple();
	cout << endl;
	if (cts != NULL)
	{
		cts->PrintTemplate();
	}
	cout << endl;
}

void
BaseNode::PrintInstance(const map<Variable*, int>& valueMap) const
{
	cout << endl;
	cout << "@@@@@@@@@@ Base Instance @@@@@@@@@" << endl;
	cout << "Head instance: " << endl;
	head->PrintInstance(valueMap);
	cout << endl;
	if (cts != NULL)
	{
		cts->PrintInstance(valueMap);
	}
	cout << "@@@@@@@@@@@@@@@@@@@@@" << endl;
}

void
BaseNode::PrintDerivation() const
{
	PrintDerivNode();
}

void
BaseNode::PrintExecution(map<Variable*, int>& valueMap) const
{
	PrintInstance(valueMap);
}

BaseNode::~BaseNode()
{
	delete head;
	delete cts;
}

PropNode::PropNode(const PredicateInstance* pred, Formula* fm = NULL):
		DpoolNode(pred)
{
	if (fm != NULL)
	{
		prop = fm->Clone();
		VarMap vmap = head->CreateVarMap(pred);
		prop->VarReplace(vmap);
	}
	else
	{
		prop = NULL;
	}
}

void
PropNode::AddInvariant(Formula* inv)
{
	prop = inv;
}

void
PropNode::FindSubTuple(const list<PredicateInstance*>& plist,
					   map<string, list<const Tuple*> >& tlist) const
{
	//Assume tlist has been initialized according to plist
	string tpName = head->GetName();
	map<string, list<const Tuple*> >::iterator itm;
	itm = tlist.find(tpName);
	if (itm != tlist.end())
	{
		//The tuple needs to be registered
		itm->second.push_back(head);
	}
}

void
PropNode::PrintCumuCons() const
{
	cout << endl;
	cout << "+++++++ PropNode Constraints ++++++" << endl;
	prop->Print();
	cout << "++++++++++++++++++++++++" << endl;
}

void
PropNode::PrintDerivNode() const
{
	cout << endl;
	cout << "++++++++++++ Recursive Node +++++++++++" << endl;
	DpoolNode::PrintDerivNode();

	cout << "User-annotated formula:" << endl;
	prop->Print();
	cout << endl;
	cout << "+++++++++++++++++++++++";
	cout << endl;
}

void
PropNode::PrintInstance(const map<Variable*, int>& valueMap) const
{
	cout << endl;
	cout << "++++++++++++ Recursive Instance +++++++++++" << endl;
	cout << "Head:";
	head->PrintInstance(valueMap);
	cout << endl;

	cout << "User-annotated formula:" << endl;
	prop->Print();
	cout << "+++++++++++++++++++++++";
	cout << endl;
}

void
PropNode::PrintDerivation() const
{
	PrintDerivNode();
}

void
PropNode::PrintExecution(map<Variable*, int>& valueMap) const
{
	PrintInstance(valueMap);
}

PropNode::~PropNode()
{
	delete head;
	delete prop;
}

Dpool::Dpool(const Ptr<NewDPGraph> newGraph,
			 const Ptr<MiniGraph> miniGraph,
			 const BaseProperty& baseProp,
			 const Invariant& inv)
{
	NS_LOG_INFO("Creating Dpool...");
	const AnnotMap& invariants = inv.GetInv();
	const ConsAnnotMap& baseAnnot = baseProp.GetProp();
	const Node* head = NULL;
	RuleListC topoOrder = miniGraph->TopoSort(inv);
	list<NewMetaNode*> metaList = miniGraph->GetBaseTuples();

	//Create a BaseNode for each base tuple
	NS_LOG_INFO("Process base tuples...");
	baseMap = BaseMap();
	list<NewMetaNode*>::iterator itml;
	for (itml = metaList.begin();itml != metaList.end();itml++)
	{
		NS_LOG_DEBUG("Base tuple...");
		string nodeName = (*itml)->GetName();
		ConsAnnotMap::const_iterator itc = baseAnnot.find(nodeName);
		if (itc != baseAnnot.end())
		{
			//Process a base tuple with annotation
			const ConsAnnot& propPair = itc->second;
			PredicateInstance* basePred = propPair.first;
			ConstraintsTemplate* baseCons = propPair.second;
			BaseNode* bnode = new BaseNode(basePred, *baseCons);
			BaseNodeList blist(1, bnode);
			baseMap.insert(BaseMap::value_type(nodeName, blist));
		}
		else
		{
			NS_LOG_DEBUG("No annot case");
			int argSize = (*itml)->GetArgLength();
			NS_LOG_DEBUG("Tuple length: " << argSize);
			BaseNode* newNode = new BaseNode(nodeName, argSize);
			BaseNodeList blist(1, newNode);
			baseMap.insert(BaseMap::value_type(nodeName, blist));
		}
	}

	//Create a PropNode for each recursive tuple
	NS_LOG_INFO("Create circle nodes...");
	recurMap = PropMap();
	AnnotMap::const_iterator ita;
	for (ita = invariants.begin();ita != invariants.end();ita++)
	{
		string tpName = ita->first;
		const Annotation& recurAnnot = ita->second;
		PredicateInstance* pred = recurAnnot.first;
		Formula* form = recurAnnot.second;
		PropNode* pnode = new PropNode(pred, form);
		PropNodeList plist(1, pnode);
		recurMap.insert(PropMap::value_type(tpName, plist));
	}

	//Process rule nodes based on topological order
	NS_LOG_INFO("Process rules based on topological sorting...");
	RuleListC::const_iterator itr;
	for (itr = topoOrder.begin();itr != topoOrder.end();itr++)
	{
		NS_LOG_DEBUG("Process a rule...");
		//Record all possible derivations of body tuples
		vector<DpoolNode*> itv;
		const list<Node*>& tblist = newGraph->GetBodies((*itr));

		head = newGraph->GetHeadTuple((*itr));
		const Tuple* hdTuple = head->GetTuple();
		VarMap unifMap = VarMap();

		//Recursively create DerivNode
		ProcessRuleNode(hdTuple, (*itr), tblist, tblist.begin(), itv, unifMap);
	}
	NS_LOG_INFO("Dpool Constructed!");
}

void
Dpool::ProcessRuleNode(const Tuple* ruleHead,
				   	   RuleNode* rnode,
					   const list<Node*>& bodyList,
					   list<Node*>::const_iterator curPos,
					   vector<DpoolNode*> bodyDerivs,
					   VarMap vmap)
{
	NS_LOG_DEBUG("Size of bodyList: " << bodyList.size());
	if (curPos == bodyList.end())
	{
		//All possible derivations of body tuples
		CreateDerivNode(ruleHead, rnode, bodyDerivs, vmap);
		return;
	}

	//Find out whether the tuple being searched is
	//a BaseNode, PropNode, or DerivNode
	string tpName = (*curPos)->GetName();
	const Tuple* bodyTuple = (*curPos)->GetTuple();
	assert(bodyTuple != NULL);
	curPos++;
	BaseMap::iterator itb = baseMap.find(tpName);
	if (itb != baseMap.end())
	{
		//Process BaseNode
		BaseNodeList& blist = itb->second;
		BaseNodeList::iterator itbl;
		for (itbl = blist.begin();itbl != blist.end();itbl++)
		{
			bodyDerivs.push_back(*itbl);

			const Tuple* tp = (*itbl)->GetHead();
			VarMap newMap = bodyTuple->CreateVarMap(tp);
			vmap.insert(newMap.begin(), newMap.end());
			ProcessRuleNode(ruleHead, rnode, bodyList, curPos, bodyDerivs, vmap);

			bodyDerivs.pop_back();
		}
	}
	else
	{
		//Process PropNode
		PropMap::iterator itp = recurMap.find(tpName);
		if (itp != recurMap.end())
		{
			PropNodeList& plist = itp->second;
			PropNodeList::iterator itpl;
			for (itpl = plist.begin();itpl != plist.end();itpl++)
			{
				bodyDerivs.push_back(*itpl);

				const Tuple* tp = (*itpl)->GetHead();
				VarMap newMap = bodyTuple->CreateVarMap(tp);
				vmap.insert(newMap.begin(), newMap.end());
				ProcessRuleNode(ruleHead, rnode, bodyList, curPos, bodyDerivs, vmap);

				bodyDerivs.pop_back();
			}
		}
		else
		{
			//Process DerivNode
			DerivMap::iterator itd = derivations.find(tpName);
			if (itd == derivations.end())
			{
				NS_LOG_ERROR("Body derivations not found!");
			}
			DerivNodeList& dlist = itd->second;
			DerivNodeList::iterator itdl;
			for (itdl = dlist.begin();itdl != dlist.end();itdl++)
			{
				//Record the derivation of body tuples
				bodyDerivs.push_back(*itdl);

				//Create variable mapping
				const Tuple* tp = (*itdl)->GetHead();
				VarMap newMap = bodyTuple->CreateVarMap(tp);
				vmap.insert(newMap.begin(), newMap.end());
				ProcessRuleNode(ruleHead, rnode, bodyList, curPos, bodyDerivs, vmap);

				bodyDerivs.pop_back();
			}
		}
	}
}

void
Dpool::CreateDerivNode(const Tuple* ruleHead,
		 	 	 	   RuleNode* rnode,
					   vector<DpoolNode*>& bodyDerivs,
					   VarMap& vmap)
{
	NS_LOG_DEBUG("Create a DerivNode:");
	NS_LOG_DEBUG("Head: ");
	ruleHead->PrintTuple();
	NS_LOG_DEBUG("Rule:");
	rnode->PrintName();
	cout << endl;

	DpoolNodeList dblist;
	ConsList cslist;
	FormList flist;

	//Replace variables in rule constraints
	const ConstraintsTemplate* ruleCons = rnode->GetConsTemp();
	ConstraintsTemplate* newCons = new ConstraintsTemplate(*ruleCons);

	//Process the rule
	vector<DpoolNode*>::iterator it;
	for (it = bodyDerivs.begin();it != bodyDerivs.end();it++)
	{
		//Collect cumulative constraints and formulas
		//TODO: Replace case study here with inheritance
		DerivNode* dnode = dynamic_cast<DerivNode*>(*it);
		if (dnode != NULL)
		{
			dblist.push_back(dnode);

			//Add references to cumulative constraints
			const ConsList& clist = (dnode)->GetCumuConsts();
			cslist.insert(cslist.end(), clist.begin(), clist.end());
			continue;
		}

		BaseNode* bnode = dynamic_cast<BaseNode*>(*it);
		if (bnode != NULL)
		{
			dblist.push_back(bnode);

			const ConstraintsTemplate* cts = bnode->GetCons();
			if (cts != NULL)
			{
				cslist.push_back(cts);
			}
			continue;
		}

		PropNode* pnode = dynamic_cast<PropNode*>(*it);
		if (pnode != NULL)
		{
			dblist.push_back(pnode);

			Formula* form = pnode->GetInv();
			if (form != NULL)
			{
				flist.push_back(form);
			}
			continue;
		}
	}
	//Add local constraints into cumulative constraint list
	if (newCons != NULL)
	{
		cslist.push_back(newCons);
	}

	DerivNode* dnode = new DerivNode(ruleHead, rnode->GetName(),
									 newCons, dblist, cslist, flist);

	const Tuple* htp = dnode->GetHead();
	VarMap headMap = ruleHead->CreateVarMap(htp);
	vmap.insert(headMap.begin(), headMap.end());
	dnode->ReplaceVar(vmap);

	UpdateDerivNode(ruleHead->GetName(), dnode);
}

void
Dpool::UpdateDerivNode(string tpName, DerivNode* dnode)
{
	derivations[tpName].push_back(dnode);
}

bool
Dpool::VerifyInvariants(const Invariant& inv) const
{
	Formula* proofObl = NULL;
	const AnnotMap& invariant = inv.GetInv();
	AnnotMap::const_iterator ita;
	//Check each invariant in the annotation
	for (ita = invariant.begin();ita != invariant.end();ita++)
	{
		string tpName = ita->first;
		const Annotation& annot = ita->second;
		PredicateInstance* predInst = annot.first;
		int predArgSize = predInst->GetArgs().size();
		//All headers should be unified to the unifTuple
		Tuple unifTuple = Tuple(tpName, predArgSize);

		//Unify variables in the invariant
		Formula* tupleInv = annot.second->Clone();
		VarMap invMap = unifTuple.CreateVarMap(predInst);
		tupleInv->VarReplace(invMap);

		//Check soundness and completeness
		//Invariant <=> Constraints1 \/ Constraints2 \/ ... \/ Constraintsn
		const DerivNodeList& dlist = derivations.at(tpName);
		DerivNodeList::const_iterator itd;
		Formula* disjForm = NULL;
		for (itd = dlist.begin();itd != dlist.end();itd++)
		{
			//Enumerate all possible derivations, including recursive ones
			Formula* conjForm = NULL;
			const Tuple* head = (*itd)->GetHead();
			VarMap vmap = head->CreateVarMap(&unifTuple);

			const ConsList& clist = (*itd)->GetCumuConsts();
			ConsList::const_iterator itc;
			for (itc = clist.begin();itc != clist.end();itc++)
			{
				const ConstraintList& ctsList = (*itc)->GetConstraints();
				ConstraintList::const_iterator itct;
				for (itct = ctsList.begin();itct != ctsList.end();itct++)
				{
					Constraint* cons = new Constraint(**itct);
					if (conjForm == NULL)
					{
						conjForm = cons;
					}
					else
					{
						conjForm = new Connective(Connective::AND, conjForm, cons);
					}
				}
			}

			FormList& flist = (*itd)->GetInvariants();
			FormList::iterator itf;
			for (itf = flist.begin();itf != flist.end();itf++)
			{
				Formula* newForm = (*itf)->Clone();
				newForm->VarReplace(vmap);
				if (conjForm == NULL)
				{
					conjForm = newForm;
				}
				else
				{
					conjForm = new Connective(Connective::AND, conjForm, newForm);
				}
			}

			//Create the disjunctive formula of C1 \/ C2...\/ Cn
			if (disjForm == NULL)
			{
				disjForm = conjForm;
			}
			else
			{
				disjForm = new Connective(Connective::OR, disjForm, conjForm);
			}
		}

		Formula* soundForm = new Connective(Connective::IMPLY, disjForm, tupleInv);
		//TODO: Verify soundForm
		Formula* completeForm = new Connective(Connective::IMPLY, tupleInv, disjForm);
		//TODO: Verify completeForm
	}

	//TODO: What's the return value here?
	return true;
}

const DerivNodeList&
Dpool::GetDerivList(string tpName) const
{
	return derivations.at(tpName);
}


void
Dpool::PrintDpool() const
{
	cout << endl;
	cout << "############### Print Derivation Pool ##############" << endl;
	cout << "####### Derived Nodes ########" << endl;
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
	cout << "######## Base Nodes #######" << endl;

	BaseMap::const_iterator itb;
	for (itb = baseMap.begin();itb != baseMap.end();itb++)
	{
		cout << itb->first;
		const BaseNodeList& blist = itb->second;
		BaseNodeList::const_iterator itbl;
		for (itbl = blist.begin();itbl != blist.end();itbl++)
		{
			(*itbl)->PrintDerivNode();
			cout << endl;
		}
		cout << endl;
	}

	cout << "######## Circle Nodes #######" << endl;
	PropMap::const_iterator itp;
	for (itp = recurMap.begin();itp != recurMap.end();itp++)
	{
		cout << itp->first;
		const PropNodeList& plist = itp->second;
		PropNodeList::const_iterator itpl;
		for (itpl = plist.begin();itpl != plist.end();itpl++)
		{
			(*itpl)->PrintDerivNode();
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
	cout << "----------------------" << endl;
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
