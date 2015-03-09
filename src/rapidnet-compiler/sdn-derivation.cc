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

	DerivNodeList::const_iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->FindSubTuple(plist, tlist);
	}

	DerivAnnoList::const_iterator ita;
	for (ita = bodyAnnotations.begin();ita != bodyAnnotations.end();ita++)
	{
		(*ita)->FindSubTuple(plist, tlist);
	}
}

void
DerivNode::PrintHead() const
{
	head->PrintTuple();
}

void
DerivNode::PrintCumuCons() const
{
	cout << endl;
	cout << "============ Simplified Cumulative Constraints ===========" << endl;
	SimpConstraints simp(allConstraints);
	simp.Print();
	cout << "=======================";
	cout << endl;
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
	NS_LOG_DEBUG("Number of bodies: " << bodyDerivs.size());
	NS_LOG_DEBUG("Number of anno bodies: " << bodyAnnotations.size());
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
		cout << endl;
		cout << "###### Simplified constraints ######" << endl;
		ConsList clist(1, ruleConstraints);
		SimpConstraints simpCons(clist);
		simpCons.Print();
		cout << "####################################" << endl;
	}
}

void
DerivNode::PrintDerivation() const
{
	PrintDerivNode();
	PrintCumuCons();

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
	cout << "Recursive Node:" << endl;
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
	NS_LOG_DEBUG("Size of bodyList: " << bodyList.size());
	if (curPos == bodyList.end())
	{
		NS_LOG_DEBUG("Create a DerivNode after the recursion is done.");
		NS_LOG_DEBUG("Head: " << head->GetName());
		NS_LOG_DEBUG("Size of bodyDerivs: " << bodyDerivs.size());
		//All possible derivations of body tuples
		CreateDerivNode(head, rnode, bodyDerivs, vmap);
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

		bodyDerivs.pop_back();
	}
}

void
Dpool::CreateDerivNode(Tuple* head,
		 	 	 	   const RuleNode* rnode,
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

	//Replace variables in rule constraints
	const ConstraintsTemplate* ruleCons = rnode->GetConsTemp();
	ConstraintsTemplate* newCons = new ConstraintsTemplate(*ruleCons);
	newCons->ReplaceVar(vmap);

	//Process the rule
	vector<DerivNodeList::const_iterator>::iterator it;
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
		}
	}
	//Add local constraints into cumulative constraint list
	if (newCons != NULL)
	{
		cslist.push_back(newCons);
	}

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

bool
Dpool::VerifyInvariants(const AnnotMap& invariant) const
{
	AnnotMap::const_iterator ita;
	for (ita = invariant.begin();ita != invariant.end();ita++)
	{
		string tpName = ita->first;
		const Annotation* annot = ita->second;
		Tuple* tp = annot->first;
		Formula* tupleInv = annot->second;

		const DerivNodeList& dlist = derivations.at(tpName);
		DerivNodeList::const_iterator itd;
		for (itd = dlist.begin();itd != dlist.end();itd++)
		{
			const RecurNode* rnode = dynamic_cast<const RecurNode*>(*itd);
			if (rnode == NULL)
			{
				//Base case
				//Unify the head tuple
				const Tuple* head = (*itd)->GetHeadTuple();
				VarMap vmap = tp->CreateVarMap(head);
				Formula* newInv = tupleInv->Clone();
				newInv->VarReplace(vmap);

				const ConstraintsTemplate* cst = (*itd)->GetConstraints();
				//Translate cst into assertions in CVC4
				//Query newInv
				//Return false if false

				delete newInv;
			}
			else
			{
				//Recursive case
				const DerivNodeList& bodyList = (*itd)->GetBodyDerivs();
				vector<const ConstraintsTemplate*> clist;
				vector<Formula*> flist;
				VarMap vmap;
				const ConstraintsTemplate* cts = (*itd)->GetConstraints();
				bool recurFlag = VerifyRecurInv(bodyList.begin(), bodyList.end(), clist,
												flist, invariant, tpName, vmap, cts);

				//TODO: Any alternative to garbage collection?
				vector<Formula*>::iterator itf;
				for (itf = flist.begin();itf != flist.end();itf++)
				{
					delete (*itf);
				}

				if (recurFlag == false)
				{
					return false;
				}
			}
		}
	}

	return true;
}

bool
Dpool::VerifyRecurInv(DerivNodeList::const_iterator curPos,
					  DerivNodeList::const_iterator endItr,
					  vector<const ConstraintsTemplate*> clist,
					  vector<Formula*>& flist,
					  const AnnotMap& annot,
					  string veriTuple,
					  const VarMap& vmap,
					  const ConstraintsTemplate* ruleCons) const
{
	if (curPos == endItr)
	{
		//Assert clist
		//Unify ruleCons
		//Query veriTuple's formula after Variable mapping

	}

	//TODO: Unify the head tuples
	bool veriResult = false;
	const Tuple* bodyTuple = (*curPos)->GetHeadTuple();
	string bodyName = bodyTuple->GetName();
	curPos++;
	AnnotMap::const_iterator ita = annot.find(bodyName);
	if (ita == annot.end())
	{
		//Non-recursive body
		const DerivNodeList& dlist = derivations.at(bodyName);
		DerivNodeList::const_iterator itd;
		for (itd = dlist.begin();itd != dlist.end();itd++)
		{
			const Tuple* head = (*itd)->GetHeadTuple();
			VarMap headMap = bodyTuple->CreateVarMap(head);
			headMap.insert(vmap.begin(), vmap.end());
			clist.push_back((*itd)->GetConstraints());
			veriResult = VerifyRecurInv(curPos, endItr, clist, flist, annot,
										veriTuple, headMap, ruleCons);
			if (veriResult == false)
			{
				return false;
			}
			clist.pop_back();
		}
	}
	else
	{
		//A recursive body
		//Use invariant instead of all its derivations
		Annotation* bodyInv = ita->second;
		Tuple* tupleInv = bodyInv->first;
		Formula* formInv = bodyInv->second;

		VarMap formMap = tupleInv->CreateVarMap(bodyTuple);
		Formula* newInv = formInv->Clone();
		newInv->VarReplace(formMap);
		flist.push_back(newInv);
		veriResult = VerifyRecurInv(curPos, endItr, clist, flist, annot,
				 	 	 	 	 	veriTuple, vmap, ruleCons);
		if (veriResult == false)
		{
			return false;
		}
	}

	return true;
}

const DerivNodeList&
Dpool::GetDerivList(string tpName) const
{
	return derivations.at(tpName);
}

bool
Dpool::CheckProperty(const Property& prop)
{
	//Process universally quantified predicates
	const list<PredicateInstance*>& plist = prop.GetUniPred();
	list<PredicateInstance*>::const_iterator itc = plist.begin();
	DerivNodeList dlist = DerivNodeList();
	return CheckRecurUniv(prop, plist, itc, dlist);
}

bool
Dpool::CheckRecurUniv(const Property& prop,
					  const list<PredicateInstance*>& plist,
					  list<PredicateInstance*>::const_iterator itc,
					  DerivNodeList dlist)
{
	if (itc == plist.end())
	{
		return CheckExistProp(prop, dlist);
	}

	string predName = (*itc)->GetName();
	DerivNodeList& headList = derivations.at(predName);
	itc++;
	DerivNodeList::iterator itd;
	for (itd = headList.begin();itd != headList.end();itd++)
	{
		dlist.push_back(*itd);
		bool result = CheckRecurUniv(prop, plist, itc, dlist);
		//One false branch makes the whole checking false
		if (result == false)
		{
			//Generate counter-example
			return false;
		}
		dlist.pop_back();
	}

	return true;
}

//TODO: Separate the verification of universally
//quantified constraints from CheckExistProp
bool
Dpool::CheckExistProp(const Property& prop,
					  const DerivNodeList& dlist)
{
	//First check if the assumption holds or not
	VarMap vmap;
	ConsList cslist;
	FormList flist;
	list<SimpConstraints*> slist;

	const list<PredicateInstance*>& plist = prop.GetUniPred();
	DerivNodeList::const_iterator itd = dlist.begin();
	list<PredicateInstance*>::const_iterator itp = plist.begin();
	for (;itd != dlist.end();itd++, itp++)
	{
		//Create variable mapping between predicate and the head tuple
		const Tuple* head = (*itd)->GetHeadTuple();
		VarMap headMap = head->CreateVarMap(*itp);
		vmap.insert(headMap.begin(), headMap.end());

		//Record simplified constraints
		const ConsList& clist = (*itd)->GetCumuConsts();
		SimpConstraints* newSimp = new SimpConstraints(clist);
		slist.push_back(newSimp);

		//Collect constraints
		const ConstraintsTemplate& newCtemp = newSimp->GetConstraints();
		cslist.push_back(&newCtemp);

		//Collect invariants
		const FormList& tupleFlist = (*itd)->GetInvariants();
		flist.insert(flist.end(), tupleFlist.begin(), tupleFlist.end());
	}
	const ConstraintsTemplate* cTemp = prop.GetUniCons();
	ConstraintsTemplate uniCons(*cTemp);
	uniCons.ReplaceVar(vmap);
	cslist.push_back(&uniCons);
	//Check satisfiability of cslist + flist.
	//If it is unsat, then return true;
	//Otherwise, keep going.

	//Check if assumption /\ not conclusion is sat

	//First find existentially quantified tuples from derivations
	//of universally quantified tuples
	map<string, list<const Tuple*> > tlist;
	list<const Tuple*> ctlist;
	for (itp = plist.begin();itp != plist.end();itp++)
	{
		//tlist initialization
		string pName = (*itp)->GetName();
		tlist.insert(map<string, list<const Tuple*> >::value_type(
													pName, ctlist));
	}

	DerivNodeList::const_iterator itdc;
	for (itdc = dlist.begin();itdc != dlist.end();itdc++)
	{
		(*itdc)->FindSubTuple(plist, tlist);
	}

	//Check all possible combinations
	map<string, list<const Tuple*> >::const_iterator itmc = tlist.begin();
	list<const Tuple*> tplist;
	bool res = CheckRecurExist(prop, tlist, itmc, tplist, cslist, flist);

	//If the set of tuples are the instances in existential
	//quantification, then they provide instantiation of
	//existentially quantified variables.

	//Release memory allocated to slist;
	list<SimpConstraints*>::iterator itl;
	for (itl = slist.begin();itl != slist.end();itl++)
	{
		delete (*itl);
	}

	return res;
}

bool
Dpool::CheckRecurExist(const Property& prop,
					   map<string, list<const Tuple*> >& tlist,
					   map<string, list<const Tuple*> >::const_iterator itm,
					   list<const Tuple*> tplist,
					   ConsList& clist,
					   const FormList& flist)
{
	if (itm == tlist.end())
	{
		return CheckWholeProp(prop, tplist, clist, flist);
	}

	const list<const Tuple*>& headList = itm->second;
	itm++;
	list<const Tuple*>::const_iterator itp;
	for (itp = headList.begin();itp != headList.end();itp++)
	{
		tplist.push_back(*itp);
		bool res = CheckRecurExist(prop, tlist, itm,
								   tplist, clist, flist);
		if (res == true)
		{
			//Generate a counter-example
			return true;
		}

		tplist.pop_back();
	}

	return false;
}

bool
Dpool::CheckWholeProp(const Property& prop,
					  list<const Tuple*> tplist,
					  ConsList& clist,
					  const FormList& flist)
{
	VarMap vmap;
	const list<PredicateInstance*>& plist = prop.GetUniPred();
	list<const Tuple*>::const_iterator itt;
	list<PredicateInstance*>::const_iterator itp;
	for (itt = tplist.begin();itt != tplist.end();itt++)
	{
		string tpName = (*itt)->GetName();
		for (itp = plist.begin();itp != plist.end();itp++)
		{
			string pName = (*itp)->GetName();
			if (tpName == pName)
			{
				//Create variable mapping for existentially
				//quantified predicates
				VarMap newMap = (*itt)->CreateVarMap(*itp);
				vmap.insert(newMap.begin(), newMap.end());
				break;
			}
		}
	}

	const ConstraintsTemplate* csTemp = prop.GetExistCons();
	ConstraintsTemplate* newTemp = csTemp->Revert();
	newTemp->ReplaceVar(vmap);
	clist.push_back(newTemp);

	//Check clist + flist is sat?
	//If sat, return false
	//If unsat, return true

	delete newTemp;
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
