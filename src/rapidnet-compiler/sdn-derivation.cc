/*
 * sdn-constraint.cc
 *
 *  Created on: Nov 8, 2014
 *      Author: chen
 */

#include "sdn-derivation.h"

NS_LOG_COMPONENT_DEFINE ("Dpool");

DpoolInstNode::DpoolInstNode()
{
	dnode = NULL;
	headMap = VarMap();
	ruleMap = VarMap();
	bodyList = list<DpoolInstNode*>();
}

DpoolInstNode::~DpoolInstNode()
{
	VarMap::iterator itvm;
	for (itvm = headMap.begin();itvm != headMap.end();itvm++)
	{
		delete itvm->second;
	}
	for (itvm = ruleMap.begin();itvm != ruleMap.end();itvm++)
	{
		delete itvm->second;
	}

	list<DpoolInstNode*>::iterator itdp;
	for (itdp = bodyList.begin();itdp != bodyList.end();itdp++)
	{
		delete (*itdp);
	}
}


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

VarMap
DpoolNode::CreateHeadInst()
{
	VarMap vmap;
	const vector<Variable*> headArgs = head->GetArgs();
	vector<Variable*>::const_iterator itvv;
	for (itvv = headArgs.begin();itvv != headArgs.end();itvv++)
	{
		Variable* newVar = new Variable(Variable::STRING, false);
		vmap.insert(VarMap::value_type(*itvv, newVar));
	}

	return vmap;
}

void
DpoolNode::CreateDerivInst(VarMap& vmap)
{
	const vector<Variable*> varVec = head->GetArgs();
	vector<Variable*>::const_iterator itv;
	for (itv = varVec.begin();itv < varVec.end();itv++)
	{
		Variable* newVar = new Variable(Variable::STRING, false);
		vmap.insert(VarMap::value_type(*itv, newVar));
	}
}

void
DpoolNode::PrintHead() const
{
	head->PrintTuple();
}

void
DpoolNode::PrintHeadInst(const map<Variable*, int>& valueMap, bool printVar) const
{
	head->PrintInstance(valueMap, printVar);
}

void
DpoolNode::PrintHeadInst(const map<Variable*, int>& valueMap, VarMap& vmap, bool printVar) const
{
	head->PrintInstance(valueMap, vmap, printVar);
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
DerivNode::ReplaceVar(VarMap& vmap)
{
	ruleConstraints->ReplaceVar(vmap);
}

void
DerivNode::FindSubTuple(const list<PredicateInstance*>& plist,
					    ExQuanTuple& tlist,
						const DerivNode* desigHead) const
{
	//Assume tlist has been initialized according to plist
	string tpName = head->GetName();
	NS_LOG_DEBUG("Find tuple: " << tpName);
	ExQuanTuple::iterator itm;
	itm = tlist.find(tpName);
	if (itm != tlist.end())
	{
		//The tuple needs to be registered
		TupleLineage newLineage = TupleLineage(head, desigHead);
		itm->second.push_back(newLineage);
	}

	DpoolNodeList::const_iterator itd;
	NS_LOG_DEBUG("Size of dpool:" << bodyDerivs.size());
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->FindSubTuple(plist, tlist, desigHead);
	}
}

void
DerivNode::FindSubTuple(const list<PredicateInstance*>& plist,
				  	  	DpoolTupleMap& tlist,
						DpoolInstNode* instNode) const
{
	//Assume tlist has been initialized according to plist
	string tpName = head->GetName();
	NS_LOG_DEBUG("Find tuple: " << tpName);
	DpoolTupleMap::iterator itm;
	itm = tlist.find(tpName);
	if (itm != tlist.end())
	{
		//The tuple needs to be registered
		DpoolTupleInst newLineage = DpoolTupleInst(this, instNode);
		itm->second.push_back(newLineage);
	}

	DpoolNodeList::const_iterator itd;
	NS_LOG_DEBUG("Size of dpool:" << bodyDerivs.size());
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		const DpoolNode* bodyNode = (*itd);
		list<DpoolInstNode*>& blist = instNode->bodyList;
		list<DpoolInstNode*>::iterator itInst = blist.begin();
		for (itInst = blist.begin();itInst != blist.end();itInst++)
		{
			if (bodyNode == (*itInst)->dnode)
			{
				(*itd)->FindSubTuple(plist, tlist, *itInst);
				break;
			}
		}
	}
}

void
DerivNode::FindBaseTuple(ExQuanTuple& tlist,
						const DerivNode* desigHead) const
{
	string tpName = head->GetName();
	NS_LOG_DEBUG("Reach tuple: " << tpName);

	DpoolNodeList::const_iterator itd;
	NS_LOG_DEBUG("Size of dpool:" << bodyDerivs.size());
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->FindBaseTuple(tlist, desigHead);
	}
}

void
DerivNode::FindBaseTuple(DpoolInstNode* dInst, DpoolTupleMap& bmap)
{
	if (dInst->dnode != this)
	{
		NS_LOG_ERROR("Instantiation failure: incorrect DpoolInstNode");
		return;
	}

	DpoolNodeList::iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		const DpoolNode* bodyNode = (*itd);
		list<DpoolInstNode*>& blist = dInst->bodyList;
		list<DpoolInstNode*>::iterator itInst = blist.begin();
		for (itInst = blist.begin();itInst != blist.end();itInst++)
		{
			if (bodyNode == (*itInst)->dnode)
			{
				(*itd)->FindBaseTuple(*itInst, bmap);
				break;
			}
		}
	}
}

VarMap
DerivNode::CreateBodyInst(list<Variable*>& varList)
{
	VarMap vmap;
	ruleConstraints->FindFreeVar(varList, vmap);

	return vmap;
}

void
DerivNode::CreateDerivInst(VarMap& vmap)
{
	DpoolNode::CreateDerivInst(vmap);
	ruleConstraints->CreateVarInst(vmap);

	DpoolNodeList::iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->CreateDerivInst(vmap);
	}
}


DpoolInstNode*
DerivNode::CreateDerivInst()
{
	DpoolInstNode* instNode = new DpoolInstNode();
	instNode->dnode = this;
	VarMap headMap = this->CreateHeadInst();
	instNode->headMap = headMap;

	list<Variable*> varList;

	const vector<Variable*> headArgs = head->GetArgs();
	vector<Variable*>::const_iterator itvv;
	for (itvv = headArgs.begin();itvv != headArgs.end();itvv++)
	{
		varList.push_back(*itvv);
	}

	DpoolNodeList::iterator itdp;
	for (itdp = bodyDerivs.begin();itdp != bodyDerivs.end();itdp++)
	{
		DpoolInstNode* bodyInst = (*itdp)->CreateDerivInst();
		instNode->bodyList.push_back(bodyInst);

		const Tuple* bodyHead = (*itdp)->GetHead();
		const vector<Variable*> bodyArgs = bodyHead->GetArgs();
		vector<Variable*>::const_iterator itvb;
		for (itvb = bodyArgs.begin();itvb != bodyArgs.end();itvb++)
		{
			varList.push_back(*itvb);
		}
	}

	instNode->ruleMap = this->CreateBodyInst(varList);

	return instNode;
}

DpoolNode*
DerivNode::DeepCopy()
{
//	//Copy Constraints
//	ConstraintsTemplate* newConsTemp = new ConstraintsTemplate(*ruleConstraints);
//
//	//Copy bodyDerivs
//	DpoolNodeList newBodies;
//	ConsList newClist;
//	FormList newFlist;
//	list<Variable*> headVars;
//
//	DpoolNodeList::iterator itdn;
//	for (itdn = bodyDerivs.begin();itdn != bodyDerivs.end();itdn++)
//	{
//		//Create a copy for each body tuple
//		DpoolNode* newBody = (*itdn)->DeepCopy();
//
//		DerivNode* dnode = dynamic_cast<DerivNode*>(*itdn);
//		if (dnode != NULL)
//		{
//			//Add references to cumulative constraints
//			const ConsList& clist = (dnode)->GetCumuConsts();
//			newClist.insert(newClist.end(), clist.begin(), clist.end());
//			const FormList& flist = (dnode)->GetInvariants();
//			newFlist.insert(newFlist.end(), flist.begin(), flist.end());
//
//			continue;
//		}
//
//		BaseNode* bnode = dynamic_cast<BaseNode*>(*itdn);
//		if (bnode != NULL)
//		{
//			const ConstraintsTemplate* cts = bnode->GetCons();
//			if (cts != NULL)
//			{
//				newClist.push_back(cts);
//			}
//			continue;
//		}
//
//		PropNode* pnode = dynamic_cast<PropNode*>(*itdn);
//		if (pnode != NULL)
//		{
//			Formula* form = pnode->GetInv();
//			if (form != NULL)
//			{
//				newFlist.push_back(form);
//			}
//			continue;
//		}
//
//		//Collect variables in the head
//		const vector<Variable*> argVec = (*itdn)->GetHead()->GetArgs();
//		vector<Variable*>::const_iterator itvv;
//		for (itvv = argVec.begin();itvv != argVec.end();itvv++)
//		{
//			headVars.push_back(*itvv);
//		}
//	}
//	newClist.push_back(ruleConstraints);
//
//	DerivNode* newDnode = new DerivNode(head, ruleName, newConsTemp, newBodies,
//										newClist, newFlist);
//	const Tuple* newHead = newDnode->GetHead();
//	const vector<Variable*> headVec = (*itdn)->GetHead()->GetArgs();
//	vector<Variable*>::const_iterator itvh;
//	for (itvh = headVec.begin();itvh != headVec.end();itvh++)
//	{
//		headVars.push_back(*itvh);
//	}
//	VarMap headMap = head->CreateVarMap(newHead);
//	newDnode->ruleConstraints->ReplaceVar(headMap);
//
//	//Collect free variables in the constraints
//	VarMap freeMap = VarMap();
//	newDnode->ruleConstraints->FindFreeVar(headVars, freeMap);
//	VarMap::iterator itvm;
//	for (itvm = freeMap.begin();itvm != freeMap.end();itvm++)
//	{
//		freeVars.push_back(itvm->second);
//	}
//
//	return newDnode;
}

void
DerivNode::CollectConsInst(DpoolInstNode* dInst, ConsList& clist, FormList& flist)
{
	if (dInst->dnode != this)
	{
		NS_LOG_ERROR("Instantiation failure: incorrect DpoolInstNode");
		return;
	}

	VarMap vmap = dInst->headMap;
	list<DpoolInstNode*>::iterator itld;
	list<DpoolInstNode*>& blist = dInst->bodyList;
	for (itld = blist.begin();itld != blist.end();itld++)
	{
		vmap.insert((*itld)->headMap.begin(),(*itld)->headMap.end());
	}
	vmap.insert(dInst->ruleMap.begin(),dInst->ruleMap.end());

	ConstraintsTemplate* newCons = new ConstraintsTemplate(*ruleConstraints);
	newCons->ReplaceVar(vmap);
	clist.push_back(newCons);

	DpoolNodeList::iterator itbd;
	list<DpoolInstNode*>::iterator itInst = blist.begin();
	for (itbd = bodyDerivs.begin();itbd != bodyDerivs.end();itbd++, itInst++)
	{
		(*itbd)->CollectConsInst(*itInst, clist, flist);
	}
}

void
DerivNode::PrintCumuCons() const
{
//	cout << endl;
//	cout << "============ Cumulative Simplified Constraints ===========" << endl;
//	SimpConstraints simp(allConstraints);
//	simp.Print();
//	cout << "=======================";
//	cout << endl;
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
//		ConsList clist(1, ruleConstraints);
//		SimpConstraints simpCons(clist);
//		simpCons.Print();
	}

	cout << "$$$$$$$$$$$$$$$$$$$$$$$$$" << endl;
}

void
DerivNode::PrintInstance(const map<Variable*, int>& valueMap, bool printVar) const
{
	cout << endl;
	cout << "%%%%%%%%%%%%%% Derivation Instance %%%%%%%%%%%%%" << endl;
	cout << "Head:";
	head->PrintInstance(valueMap, printVar);
	cout << endl;
	cout << "Rule name:" << ruleName;
	cout << endl;
	cout << "Body tuples:" << endl;
	DpoolNodeList::const_iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->PrintHeadInst(valueMap, printVar);
		cout << endl;
	}
	if (ruleConstraints != NULL)
	{
		cout << "Constraints:" << endl;
		ruleConstraints->PrintInstance(valueMap, printVar);
		cout << endl;
	}
	cout << "%%%%%%%%%%%%%%%%%%%%%%%%%%%" << endl;
}

void
DerivNode::PrintInstance(const map<Variable*, int>& valueMap, VarMap& vmap, bool printVar) const
{
	cout << endl;
	cout << "%%%%%%%%%%%%%% Derivation Instance %%%%%%%%%%%%%" << endl;
	cout << "Head:";
	head->PrintInstance(valueMap, vmap, printVar);
	cout << endl;
	cout << "Rule name:" << ruleName;
	cout << endl;
	cout << "Body tuples:" << endl;
	DpoolNodeList::const_iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->PrintHeadInst(valueMap, vmap, printVar);
		cout << endl;
	}
	if (ruleConstraints != NULL)
	{
		cout << "Constraints:" << endl;
		ruleConstraints->PrintInstance(valueMap, vmap, printVar);
		cout << endl;
	}
	cout << "%%%%%%%%%%%%%%%%%%%%%%%%%%%" << endl;
}

void
DerivNode::PrintInstance(const map<Variable*, int>& valueMap,
						 DpoolInstNode* instNode,
						 bool printVar) const
{
	cout << endl;
	cout << "%%%%%%%%%%%%%% Derivation Instance %%%%%%%%%%%%%" << endl;
	cout << "Head:";
	VarMap headMap = instNode->headMap;
	head->PrintInstance(valueMap, headMap, printVar);
	cout << endl;
	cout << "Rule name:" << ruleName << endl;
	cout << "Rule constraints:" << endl;
	VarMap ruleMap = instNode->ruleMap;
	VarMap completeMap = headMap;
	completeMap.insert(ruleMap.begin(), ruleMap.end());

	cout << "Body tuples:" << endl;
	DpoolNodeList::const_iterator itd;
	list<DpoolInstNode*>::iterator itld = instNode->bodyList.begin();
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++, itld++)
	{
		const DpoolNode* bodyNode = (*itd);
		VarMap& bodyHeadMap = (*itld)->headMap;
		completeMap.insert(bodyHeadMap.begin(), bodyHeadMap.end());
		(*itd)->PrintHeadInst(valueMap, bodyHeadMap, printVar);
		cout << endl;
	}

	if (ruleConstraints != NULL)
	{
		cout << "Constraints:" << endl;
		ruleConstraints->PrintInstance(valueMap, completeMap, printVar);
		cout << endl;
	}
	cout << endl;

	cout << "%%%%%%%%%%%%%%%%%%%%%%%%%%%" << endl;
}

void
DerivNode::PrintDerivation() const
{
	PrintDerivNode();
	//PrintCumuCons();

	DpoolNodeList::const_iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->PrintDerivation();
		cout << endl;
	}
}

void
DerivNode::PrintDerivInst(DpoolInstNode* instNode)
{
	cout << endl;
	cout << "$$$$$$$$$$$$ Derivation Node Instance $$$$$$$$$$$" << endl;
	cout << "Head:";
	VarMap& headMap = instNode->headMap;
	head->PrintTupleInst(headMap);
	cout << endl;
	cout << "Rule name:" << ruleName;
	VarMap completeMap = headMap;
	VarMap& ruleMap = instNode->ruleMap;
	completeMap.insert(ruleMap.begin(), ruleMap.end());

	cout << endl;
	cout << "Body tuples:" << endl;
	DpoolNodeList::const_iterator itd;
	list<DpoolInstNode*>& instList = instNode->bodyList;
	list<DpoolInstNode*>::iterator itld = instList.begin();
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++, itld++)
	{
		const DpoolNode* bodyNode = (*itd);
		if (bodyNode == (*itld)->dnode)
		{
			const Tuple* bodyHead = bodyNode->GetHead();
			VarMap& bodyMap = (*itld)->headMap;
			bodyHead->PrintTupleInst(bodyMap);
			completeMap.insert(bodyMap.begin(), bodyMap.end());
		}
		else
		{
			NS_LOG_ERROR("DpoolInstNode does not match!");
		}
		cout << endl;
	}

	cout << endl;
	cout << "Rule body:" << endl;
	if (ruleConstraints != NULL)
	{
		ruleConstraints->PrintTempInst(completeMap);
	}

	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		const DpoolNode* bodyNode = (*itd);
		list<DpoolInstNode*>::iterator itld;
		for (itld = instNode->bodyList.begin();itld != instNode->bodyList.end();itld++)
		{
			if (bodyNode == (*itld)->dnode)
			{
				(*itd)->PrintDerivInst(*itld);
				cout << endl;
				break;
			}
		}
		cout << endl;
	}

	cout << "$$$$$$$$$$$$$$$$$$$$$$$$$" << endl;
}


void
DerivNode::PrintSimpDerivInst(DpoolInstNode* instNode, SimpConstraints& simpCons)
{
	cout << endl;
	cout << "$$$$$$$$$$$$ Simplified Derivation Node $$$$$$$$$$$" << endl;
	cout << "Head:";
	VarMap& headMap = instNode->headMap;
	head->PrintSimpTupleInst(headMap, simpCons);
	cout << endl;
	cout << "Rule name:" << ruleName;
	VarMap completeMap = headMap;
	VarMap& ruleMap = instNode->ruleMap;
	completeMap.insert(ruleMap.begin(), ruleMap.end());

	cout << endl;
	cout << "Body tuples:" << endl;
	DpoolNodeList::const_iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		const DpoolNode* bodyNode = (*itd);
		list<DpoolInstNode*>::iterator itld;
		for (itld = instNode->bodyList.begin();itld != instNode->bodyList.end();itld++)
		{
			if (bodyNode == (*itld)->dnode)
			{
				const Tuple* bodyHead = bodyNode->GetHead();
				VarMap& bodyMap = (*itld)->headMap;
				bodyHead->PrintSimpTupleInst(bodyMap, simpCons);
				completeMap.insert(bodyMap.begin(), bodyMap.end());
				break;
			}
		}
		cout << endl;
	}

	cout << "Rule body:" << endl;
	if (ruleConstraints != NULL)
	{
		ruleConstraints->PrintSimpTempInst(completeMap, simpCons);
	}

	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		const DpoolNode* bodyNode = (*itd);
		list<DpoolInstNode*>::iterator itld;
		for (itld = instNode->bodyList.begin();itld != instNode->bodyList.end();itld++)
		{
			if (bodyNode == (*itld)->dnode)
			{
				(*itd)->PrintSimpDerivInst(*itld, simpCons);
				cout << endl;
				break;
			}
		}
		cout << endl;
	}

	cout << "$$$$$$$$$$$$$$$$$$$$$$$$$" << endl;
}

void
DerivNode::PrintExecution(map<Variable*, int>& valueMap, bool printVar) const
{
	cout << endl;
	cout << "~~~~~~~~~~~~~~~ Execution Trace ~~~~~~~~~~~~~~" << endl;
	PrintInstance(valueMap, printVar);

	DpoolNodeList::const_iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->PrintExecution(valueMap, printVar);
		cout << endl;
	}
	cout << "~~~~~~~~~~~~~~~~~~~~~~~~~~~~" << endl;
}

void
DerivNode::PrintExecInst(map<Variable*, int>& valueMap, VarMap& vmap, bool printVar) const
{
	cout << endl;
	cout << "~~~~~~~~~~~~~~~ Execution Trace ~~~~~~~~~~~~~~" << endl;
	PrintInstance(valueMap, vmap, printVar);

	DpoolNodeList::const_iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		(*itd)->PrintExecInst(valueMap, vmap, printVar);
		cout << endl;
	}
	cout << "~~~~~~~~~~~~~~~~~~~~~~~~~~~~" << endl;
}

void
DerivNode::PrintExecInst(map<Variable*, int>& valueMap,
						 DpoolInstNode* instNode,
						 bool printVar) const
{
	cout << endl;
	cout << "~~~~~~~~~~~~~~~ Execution Trace ~~~~~~~~~~~~~~" << endl;
	PrintInstance(valueMap, instNode, printVar);

	DpoolNodeList::const_iterator itd;
	for (itd = bodyDerivs.begin();itd != bodyDerivs.end();itd++)
	{
		const DpoolNode* bodyNode = (*itd);
		list<DpoolInstNode*>::iterator itld;
		for (itld = instNode->bodyList.begin();itld != instNode->bodyList.end();itld++)
		{
			if (bodyNode == (*itld)->dnode)
			{
				(*itd)->PrintExecInst(valueMap, *itld, printVar);
				break;
			}
		}

		cout << endl;
	}
	cout << "~~~~~~~~~~~~~~~~~~~~~~~~~~~~" << endl;
}

DerivNode::~DerivNode()
{
	delete head;
	delete ruleConstraints;
	list<Variable*>::iterator itl;
	for (itl = freeVars.begin();itl != freeVars.end();itl++)
	{
		delete (*itl);
	}
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
BaseNode::UpdateCons(ConstraintsTemplate* newConTemp)
{
	cts = newConTemp;
}

void
BaseNode::FindSubTuple(const list<PredicateInstance*>& plist,
				  	   ExQuanTuple& tlist,
					   const DerivNode* desigHead) const
{
	//Assume tlist has been initialized according to plist
	string tpName = head->GetName();
	NS_LOG_DEBUG("Find tuple: " << tpName);
	ExQuanTuple::iterator itm;
	itm = tlist.find(tpName);
	if (itm != tlist.end())
	{
		//The tuple needs to be registered
		TupleLineage newLineage = TupleLineage(head, desigHead);
		itm->second.push_back(newLineage);
	}
}

void
BaseNode::FindSubTuple(const list<PredicateInstance*>& plist,
				  	   DpoolTupleMap& tlist,
						DpoolInstNode* instNode) const
{
	//Assume tlist has been initialized according to plist
	string tpName = head->GetName();
	NS_LOG_DEBUG("Find tuple: " << tpName);
	DpoolTupleMap::iterator itm;
	itm = tlist.find(tpName);
	if (itm != tlist.end())
	{
		//The tuple needs to be registered
		DpoolTupleInst newLineage = DpoolTupleInst(this, instNode);
		itm->second.push_back(newLineage);
	}
}

void
BaseNode::FindBaseTuple(ExQuanTuple& tlist,
					   const DerivNode* desigHead) const
{
	string tpName = head->GetName();
	NS_LOG_DEBUG("Find base tuple: " << tpName);
	ExQuanTuple::iterator itm;

	pair<ExQuanTuple::iterator, bool> ret;
	list<TupleLineage> emptyBaseList;
	ret = tlist.insert(ExQuanTuple::value_type(tpName, emptyBaseList));

	TupleLineage newLineage = TupleLineage(head, desigHead);
	ret.first->second.push_back(newLineage);
}

void
BaseNode::FindBaseTuple(DpoolInstNode* dInst, DpoolTupleMap& bmap)
{
	if (dInst->dnode != this)
	{
		NS_LOG_ERROR("Instantiation failure: incorrect DpoolInstNode");
		return;
	}

	string tpName = head->GetName();
	pair<DpoolTupleMap::iterator, bool> ret;
	list<DpoolTupleInst> emptyBaseList;
	ret = bmap.insert(DpoolTupleMap::value_type(tpName, emptyBaseList));

	DpoolTupleInst newPair = DpoolTupleInst(this, dInst);
	ret.first->second.push_back(newPair);
}

DpoolNode*
BaseNode::DeepCopy()
{
	//Copy Constraints
	ConstraintsTemplate* newConsTemp = new ConstraintsTemplate(*cts);

	BaseNode* newBase = new BaseNode(head);
	newBase->UpdateCons(newConsTemp);
	const Tuple* newHead = newBase->GetHead();
	VarMap headMap = head->CreateVarMap(newHead);
	newBase->cts->ReplaceVar(headMap);

	//Collect free variables in the constraints
	VarMap freeMap = VarMap();
	list<Variable*> headVars;
	const vector<Variable*> headVec = head->GetArgs();
	vector<Variable*>::const_iterator itvv;
	for (itvv = headVec.begin();itvv != headVec.end();itvv++)
	{
		headVars.push_back(*itvv);
	}

	newBase->cts->FindFreeVar(headVars, freeMap);
	VarMap::iterator itvm;
	for (itvm = freeMap.begin();itvm != freeMap.end();itvm++)
	{
		freeVars.push_back(itvm->second);
	}

	return newBase;
}


DpoolInstNode*
BaseNode::CreateDerivInst()
{
	DpoolInstNode* instNode = new DpoolInstNode();
	instNode->dnode = this;
	VarMap headMap = this->CreateHeadInst();
	instNode->headMap = headMap;

	list<Variable*> varList;

	const vector<Variable*> headArgs = head->GetArgs();
	vector<Variable*>::const_iterator itvv;
	for (itvv = headArgs.begin();itvv != headArgs.end();itvv++)
	{
		varList.push_back(*itvv);
	}

	instNode->ruleMap = this->CreateBodyInst(varList);

	return instNode;
}

VarMap
BaseNode::CreateBodyInst(list<Variable*>& varList)
{
	VarMap vmap;
	cts->FindFreeVar(varList, vmap);

	return vmap;
}

void
BaseNode::CollectConsInst(DpoolInstNode* dInst, ConsList& clist, FormList& flist)
{
	if (dInst->dnode != this)
	{
		NS_LOG_ERROR("Instantiation failure: incorrect DpoolInstNode");
		return;
	}

	VarMap vmap = dInst->headMap;
	vmap.insert(dInst->ruleMap.begin(),dInst->ruleMap.end());

	ConstraintsTemplate* newCons = new ConstraintsTemplate(*cts);
	newCons->ReplaceVar(vmap);
	clist.push_back(newCons);
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
BaseNode::PrintDerivInst(DpoolInstNode* instNode)
{
	cout << endl;
	cout << "******* Base Node Instance ********" << endl;
	cout << "Head: ";
	VarMap& headMap = instNode->headMap;
	head->PrintTupleInst(headMap);
	cout << endl;
	VarMap completeMap = headMap;
	VarMap& ruleMap = instNode->ruleMap;
	completeMap.insert(ruleMap.begin(), ruleMap.end());
	if (cts != NULL)
	{
		cts->PrintTempInst(completeMap);
	}
	cout << endl;
}


void
BaseNode::PrintSimpDerivInst(DpoolInstNode* instNode, SimpConstraints& simpCons)
{
	cout << endl;
	cout << "******* Simplified Base Node ********" << endl;
	cout << "Head: ";
	VarMap& headMap = instNode->headMap;
	head->PrintSimpTupleInst(headMap, simpCons);
	cout << endl;
	VarMap completeMap = headMap;
	VarMap& ruleMap = instNode->ruleMap;
	completeMap.insert(ruleMap.begin(), ruleMap.end());
	if (cts != NULL)
	{
		cts->PrintSimpTempInst(completeMap, simpCons);
	}
	cout << endl;
}

void
BaseNode::PrintInstance(const map<Variable*, int>& valueMap, bool printVar) const
{
	cout << endl;
	cout << "@@@@@@@@@@ Base Instance @@@@@@@@@" << endl;
	cout << "Head instance: " << endl;
	head->PrintInstance(valueMap, printVar);
	cout << endl;
	if (cts != NULL)
	{
		cts->PrintInstance(valueMap, printVar);
	}
	cout << "@@@@@@@@@@@@@@@@@@@@@" << endl;
}

void
BaseNode::PrintInstance(const map<Variable*, int>& valueMap, VarMap& vmap, bool printVar) const
{
	cout << endl;
	cout << "@@@@@@@@@@ Base Instance @@@@@@@@@" << endl;
	cout << "Head instance: " << endl;
	head->PrintInstance(valueMap, vmap, printVar);
	cout << endl;
	if (cts != NULL)
	{
		cts->PrintInstance(valueMap, vmap, printVar);
	}
	cout << "@@@@@@@@@@@@@@@@@@@@@" << endl;
}

void
BaseNode::PrintInstance(const map<Variable*, int>& valueMap,
						 DpoolInstNode* instNode,
						 bool printVar) const
{
	cout << endl;
	cout << "@@@@@@@@@@ Base Instance @@@@@@@@@" << endl;
	cout << "Head instance: " << endl;
	VarMap& headMap = instNode->headMap;
	head->PrintInstance(valueMap, headMap, printVar);
	VarMap& ruleMap = instNode->ruleMap;
	VarMap completeMap = headMap;
	completeMap.insert(ruleMap.begin(),ruleMap.end());
	cout << endl;
	if (cts != NULL)
	{
		cts->PrintInstance(valueMap, completeMap, printVar);
	}
	cout << "@@@@@@@@@@@@@@@@@@@@@" << endl;
}


void
BaseNode::PrintDerivation() const
{
	PrintDerivNode();
}

void
BaseNode::PrintExecution(map<Variable*, int>& valueMap, bool printVar) const
{
	PrintInstance(valueMap, printVar);
}

void
BaseNode::PrintExecInst(map<Variable*, int>& valueMap, VarMap& vmap, bool printVar) const
{
	PrintInstance(valueMap, vmap, printVar);
}

void
BaseNode::PrintExecInst(map<Variable*, int>& valueMap,
						DpoolInstNode* instNode,
						bool printVar) const
{
	PrintInstance(valueMap, instNode, printVar);
}


BaseNode::~BaseNode()
{
	delete head;
	delete cts;
	list<Variable*>::iterator itl;
	for (itl = freeVars.begin();itl != freeVars.end();itl++)
	{
		delete (*itl);
	}
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

PropNode::PropNode(const Tuple* tp):
		DpoolNode(tp)
{
	prop = NULL;
}

void
PropNode::AddInvariant(Formula* inv)
{
	prop = inv;
}

void
PropNode::FindSubTuple(const list<PredicateInstance*>& plist,
					   ExQuanTuple& tlist,
					   const DerivNode* desigHead) const
{
	//Assume tlist has been initialized according to plist
	string tpName = head->GetName();
	NS_LOG_DEBUG("Find tuple: " << tpName);
	ExQuanTuple::iterator itm;
	itm = tlist.find(tpName);
	if (itm != tlist.end())
	{
		//The tuple needs to be registered
		TupleLineage newLineage = TupleLineage(head, desigHead);
		itm->second.push_back(newLineage);
	}
}

void
PropNode::FindSubTuple(const list<PredicateInstance*>& plist,
				  	   DpoolTupleMap& tlist,
					   DpoolInstNode* instNode) const
{
	//Assume tlist has been initialized according to plist
	string tpName = head->GetName();
	NS_LOG_DEBUG("Find tuple: " << tpName);
	DpoolTupleMap::iterator itm;
	itm = tlist.find(tpName);
	if (itm != tlist.end())
	{
		//The tuple needs to be registered
		DpoolTupleInst newLineage = DpoolTupleInst(this, instNode);
		itm->second.push_back(newLineage);
	}
}

DpoolNode*
PropNode::DeepCopy()
{
	//Copy formula
	Formula* newForm = prop->Clone();

	//Create a new PropNode
	PropNode* newProp = new PropNode(head);
	const Tuple* newHead = newProp->GetHead();
	VarMap headMap = head->CreateVarMap(newHead);
	newForm->VarReplace(headMap);
	newProp->AddInvariant(newForm);

	return newProp;
}

VarMap
PropNode::CreateBodyInst(list<Variable*>& varList)
{
	VarMap vmap;
	prop->FindFreeVar(varList, vmap);

	return vmap;
}

DpoolInstNode*
PropNode::CreateDerivInst()
{
	DpoolInstNode* instNode = new DpoolInstNode();
	instNode->dnode = this;
	VarMap headMap = this->CreateHeadInst();
	instNode->headMap = headMap;

	list<Variable*> varList;

	const vector<Variable*> headArgs = head->GetArgs();
	vector<Variable*>::const_iterator itvv;
	for (itvv = headArgs.begin();itvv != headArgs.end();itvv++)
	{
		varList.push_back(*itvv);
	}

	instNode->ruleMap = this->CreateBodyInst(varList);

	return instNode;
}

void
PropNode::CollectConsInst(DpoolInstNode* dInst, ConsList& clist, FormList& flist)
{
	if (dInst->dnode != this)
	{
		NS_LOG_ERROR("Instantiation failure: incorrect DpoolInstNode");
		return;
	}

	VarMap vmap = dInst->headMap;
	vmap.insert(dInst->ruleMap.begin(),dInst->ruleMap.end());

	Formula* newForm = prop->Clone();
	newForm->VarReplace(vmap);
	flist.push_back(newForm);
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
	DpoolNode::PrintHead();
	cout << endl;

	cout << "User-annotated formula:" << endl;
	prop->Print();
	cout << endl;
	cout << "+++++++++++++++++++++++";
	cout << endl;
}

void
PropNode::PrintDerivInst(DpoolInstNode* instNode)
{
	cout << endl;
	cout << "******* Prop Node Instance ********" << endl;
	cout << "Head: ";
	VarMap& headMap = instNode->headMap;
	head->PrintTupleInst(headMap);
	cout << endl;
	VarMap completeMap = headMap;
	VarMap& ruleMap = instNode->ruleMap;
	completeMap.insert(ruleMap.begin(), ruleMap.end());
	if (prop != NULL)
	{
		prop->PrintInst(completeMap);
	}
	cout << endl;
}

void
PropNode::PrintSimpDerivInst(DpoolInstNode* instNode, SimpConstraints& simpCons)
{
	cout << endl;
	cout << "******* Simplified Prop Node ********" << endl;
	cout << "Head: ";
	VarMap& headMap = instNode->headMap;
	head->PrintSimpTupleInst(headMap, simpCons);
	cout << endl;
	VarMap completeMap = headMap;
	VarMap& ruleMap = instNode->ruleMap;
	completeMap.insert(ruleMap.begin(), ruleMap.end());
	if (prop != NULL)
	{
		prop->PrintSimpInst(completeMap, simpCons);
	}
	cout << endl;
}

void
PropNode::PrintInstance(const map<Variable*, int>& valueMap, bool printVar) const
{
	cout << endl;
	cout << "++++++++++++ Recursive Instance +++++++++++" << endl;
	cout << "Head:";
	head->PrintInstance(valueMap, printVar);
	cout << endl;

	cout << "User-annotated formula:" << endl;
	prop->Print();
	cout << "+++++++++++++++++++++++";
	cout << endl;
}

void
PropNode::PrintInstance(const map<Variable*, int>& valueMap, VarMap& vmap, bool printVar) const
{
	cout << endl;
	cout << "++++++++++++ Recursive Instance +++++++++++" << endl;
	cout << "Head:";
	head->PrintInstance(valueMap, vmap, printVar);
	cout << endl;

	cout << "User-annotated formula:" << endl;
	Formula* newForm = prop->Clone();
	newForm->VarReplace(vmap);
	newForm->Print();
	cout << "+++++++++++++++++++++++";
	cout << endl;
	delete newForm;
}

void
PropNode::PrintInstance(const map<Variable*, int>& valueMap,
						DpoolInstNode* instNode,
						bool printVar) const
{
	cout << endl;
	cout << "++++++++++++ Recursive Instance +++++++++++" << endl;
	cout << "Head:";
	VarMap& headMap = instNode->headMap;
	head->PrintInstance(valueMap, headMap, printVar);
	cout << endl;

	cout << "User-annotated formula:" << endl;
	VarMap& ruleMap = instNode->ruleMap;
	VarMap completeMap = headMap;
	completeMap.insert(ruleMap.begin(),ruleMap.end());
	Formula* newForm = prop->Clone();
	newForm->VarReplace(completeMap);
	newForm->Print();
	cout << "+++++++++++++++++++++++";
	cout << endl;
	delete newForm;
}

void
PropNode::PrintDerivation() const
{
	PrintDerivNode();
}

void
PropNode::PrintExecution(map<Variable*, int>& valueMap, bool printVar) const
{
	PrintInstance(valueMap, printVar);
}

void
PropNode::PrintExecInst(map<Variable*, int>& valueMap, VarMap& vmap, bool printVar) const
{
	PrintInstance(valueMap, vmap, printVar);
}

void
PropNode::PrintExecInst(map<Variable*, int>& valueMap,
						DpoolInstNode* instNode,
						bool printVar) const
{
	PrintInstance(valueMap, instNode, printVar);
}

PropNode::~PropNode()
{
	delete head;
	delete prop;
	list<Variable*>::iterator itl;
	for (itl = freeVars.begin();itl != freeVars.end();itl++)
	{
		delete (*itl);
	}
}

Dpool::Dpool(const Ptr<NewDPGraph> newGraph,
			 const Ptr<MiniGraph> miniGraph,
			 const BaseProperty& baseProp,
			 const Invariant& inv)
{
	cout << "Creating Dpool..." << endl;
	const AnnotMap& invariants = inv.GetInv();
	const ConsAnnotMap& baseAnnot = baseProp.GetProp();
	const Node* head = NULL;
	RuleListC topoOrder = miniGraph->TopoSort(inv);
	list<NewMetaNode*> metaList = miniGraph->GetBaseTuples();

	//Create a BaseNode for each base tuple
	cout << "Process base tuples..." << endl;
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
			BaseNode* newNode = new BaseNode(nodeName, argSize);
			BaseNodeList blist(1, newNode);
			baseMap.insert(BaseMap::value_type(nodeName, blist));
		}
	}

	//Create a PropNode for each recursive tuple
	cout << "Create circle nodes..." << endl;
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
	cout << "Process rules based on topological sorting..." << endl;
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
	cout << "Dpool Constructed!" << endl;
}

void
Dpool::ProcessRuleNode(const Tuple* ruleHead,
				   	   RuleNode* rnode,
					   const list<Node*>& bodyList,
					   list<Node*>::const_iterator curPos,
					   vector<DpoolNode*> bodyDerivs,
					   VarMap vmap)
{
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

	//Replace variables in rule constraints
	const ConstraintsTemplate* ruleCons = rnode->GetConsTemp();
	ConstraintsTemplate* newCons = new ConstraintsTemplate(*ruleCons);

	//Process the rule
	vector<DpoolNode*>::iterator it;
	for (it = bodyDerivs.begin();it != bodyDerivs.end();it++)
	{
		//TODO: DeepCopy creates state explosion problem
		//DpoolNode* instDnode = (*it)->DeepCopy();
		DpoolNode* bodyDnode = (*it);

		//Collect cumulative constraints and formulas
		//TODO: Replace case study here with inheritance
		DerivNode* dnode = dynamic_cast<DerivNode*>(bodyDnode);
		if (dnode != NULL)
		{
			dblist.push_back(dnode);
			continue;
		}

		BaseNode* bnode = dynamic_cast<BaseNode*>(bodyDnode);
		if (bnode != NULL)
		{
			dblist.push_back(bnode);
			continue;
		}

		PropNode* pnode = dynamic_cast<PropNode*>(bodyDnode);
		if (pnode != NULL)
		{
			dblist.push_back(pnode);
			continue;
		}
	}

	string ruleName = rnode->GetName();
	DerivNode* dnode = new DerivNode(ruleHead, ruleName, newCons, dblist);

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

//TODO: There are potential memory leak problems with VerifyInvariants
void
Dpool::VerifyInvariants(const Invariant& inv) const
{
//	NS_LOG_FUNCTION("Verifying Invariants...");
//	const AnnotMap& invariant = inv.GetInv();
//	AnnotMap::const_iterator ita;
//
//	//Check each invariant in the annotation
//	for (ita = invariant.begin();ita != invariant.end();ita++)
//	{
//		//Soundness: (C1 => C) /\ (C2 => C) /\ ... /\ (Ci => C)
//		//Completeness: (C => C1) \/ (C => C2) \/ ... \/ (C => Ci)
//		bool soundFlag = true;
//		bool completeFlag = false;
//
//		string tpName = ita->first;
//		const Annotation& annot = ita->second;
//		PredicateInstance* predInst = annot.first;
//		int predArgSize = predInst->GetArgs().size();
//		//All headers should be unified to the unifTuple
//		Tuple unifTuple = Tuple(tpName, predArgSize);
//		NS_LOG_DEBUG("Unification tuple:");
//		unifTuple.PrintTuple();
//		cout << endl;
//
//		//Unify variables in the invariant
//		Formula* tupleInv = annot.second->Clone();
//		VarMap invMap = unifTuple.CreateVarMap(predInst);
//		tupleInv->VarReplace(invMap);
//		NS_LOG_DEBUG("Original Invariant Property:");
//		unifTuple.PrintTuple();
//		cout << endl;
//		tupleInv->Print();
//		cout << endl;
//
//		const DerivNodeList& dlist = derivations.at(tpName);
//		DerivNodeList::const_iterator itd;
//		//Collect constraints and invariants from all derivations
//		for (itd = dlist.begin();itd != dlist.end();itd++)
//		{
//			NS_LOG_DEBUG("Print derivations");
//			(*itd)->PrintDerivation();
//			cout << endl;
//
//			Formula* localInv = tupleInv->Clone();
//			const Tuple* head = (*itd)->GetHead();
//			VarMap vmap = head->CreateVarMap(&unifTuple);
//
//			list<ConstraintsTemplate*> newclist = list<ConstraintsTemplate*>();
//			const ConsList& clist = (*itd)->GetCumuConsts();
//			ConsList::const_iterator itcl;
//			for (itcl = clist.begin();itcl != clist.end();itcl++)
//			{
//				ConstraintsTemplate* consTemp = new ConstraintsTemplate(**itcl);
//				consTemp->ReplaceVar(vmap);
//				newclist.push_back(consTemp);
//			}
//
//			FormList newflist = FormList();
//			FormList& flist = (*itd)->GetInvariants();
//			FormList::iterator itf;
//			for (itf = flist.begin();itf != flist.end();itf++)
//			{
//				Formula* newForm = (*itf)->Clone();
//				newForm->VarReplace(vmap);
//				newflist.push_back(newForm);
//			}
//
//			//Simplify constraints
//			SimpConstraints simpCons = SimpConstraints(newclist);
//			NS_LOG_DEBUG("Print simplified constraints:");
//			simpCons.Print();
//			cout << endl;
//
//			//Replace variables in Formulas of derivations
//			for (itf = newflist.begin();itf != newflist.end();itf++)
//			{
//				(*itf)->VarReplace(simpCons);
//			}
//
//			//Replace variables in the invariant
//			localInv->VarReplace(simpCons);
//
//			//Create proof obligation for invariant checking
//			Formula* conjForm = NULL;
//
//			//Add constraints
//			const ConstraintsTemplate& simpTemp = simpCons.GetConstraints();
//			const ConstraintList& cslist = simpTemp.GetConstraints();
//			ConstraintList::const_iterator itcs;
//			for (itcs = cslist.begin();itcs != cslist.end();itcs++)
//			{
//				Constraint* cons = new Constraint(**itcs);
//				if (conjForm == NULL)
//				{
//					conjForm = cons;
//				}
//				else
//				{
//					conjForm = new Connective(Connective::AND, conjForm, cons);
//				}
//			}
//
//			//Add formulas
//			for (itf = newflist.begin();itf != newflist.end();itf++)
//			{
//				Formula* newForm = (*itf)->Clone();
//				if (conjForm == NULL)
//				{
//					conjForm = newForm;
//				}
//				else
//				{
//					conjForm = new Connective(Connective::AND, conjForm, newForm);
//				}
//			}
//
//			//Check:
//			//(1) Completeness: C => Ci
//			if (completeFlag == false)
//			{
//				Formula* completeForm = new Connective(Connective::IMPLY, localInv, conjForm);
//				Formula* negCompleteForm = new Connective(Connective::NOT, completeForm, NULL);
//				FormList cflist = FormList(1, negCompleteForm);
//				map<Variable*, int> completeAssign = check_sat_generalized(cflist);
//				if (completeAssign.size() > 0)
//				{
//					cout << "This part of completeness does not hold!" << endl;
//				}
//				else
//				{
//					cout << "Completeness holds!" << endl;
//					completeFlag = true;
//				}
//
//				completeForm->NullifyMem();
//				delete negCompleteForm;
//			}
//
//			//(2) Soundness: Ci => C;
//			if (soundFlag == true)
//			{
//				Formula* soundForm = new Connective(Connective::IMPLY, conjForm, localInv);
//				Formula* negSoundForm = new Connective(Connective::NOT, soundForm, NULL);
//				FormList sflist = FormList(1, negSoundForm);
//				map<Variable*, int> soundAssign = check_sat_generalized(sflist);
//				if (soundAssign.size() > 0)
//				{
//					cout << "Soundness does not hold!" << endl;
//					soundFlag = false;
//				}
//				else
//				{
//					cout << "This part of soundness holds!" << endl;
//				}
//
//				soundForm->NullifyMem();
//				delete negSoundForm;
//			}
//
//			list<ConstraintsTemplate*>::iterator itnew;
//			cout << "newclist size: " << newclist.size() << endl;
//			for (itnew = newclist.begin();itnew != newclist.end();itnew++)
//			{
//				delete (*itnew);
//			}
//
//			delete localInv;
//			delete conjForm;
//
//
//			if (soundFlag == false && completeFlag == true)
//			{
//				cout << "Soundness & Completeness neither holds!");
//				delete tupleInv;
//				return;
//			}
//		}
//
//		if (soundFlag == true)
//		{
//			cout << "Soundness holds");
//		}
//
//		if (completeFlag == true)
//		{
//			cout << "Completeness holds");
//		}
//
//		delete tupleInv;
//	}
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
		int count = 1;
		for (itc = it->second.begin(); itc != it->second.end(); itc++, count++)
		{
			cout << endl;
			cout << "~~~~~~~~ The " << count << "th derivation" << endl;
			(*itc)->PrintDerivation();
			cout << endl << endl;
			cout << "~~~~~~~~~" << endl;
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
