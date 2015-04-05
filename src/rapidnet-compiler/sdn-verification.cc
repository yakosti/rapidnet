/*
 * sdn-verification.cc
 *
 *  Created on: Mar 22, 2015
 *      Author: chen
 */

#include "sdn-verification.h"

NS_LOG_COMPONENT_DEFINE ("Verification");

/*
 * Property verification
 */

//TODO: We assume now that universally quantified tuples
//and existentially quantified tuples in Property do not
//have duplicates

//Propagate assignment from representative variables
//to all variables in the equivalent class
map<Variable*, int>
PropAssignment(SimpConstraints& simpCons, map<Variable*, int> assignment)
{
	NS_LOG_FUNCTION("Propagate assignments...");
	map<Variable*, int> fullAssign;
	const map<Variable*, list<Variable*> >& equiClass = simpCons.GetEquiClass();
	map<Variable*, list<Variable*> >::const_iterator ite;
	for (ite = equiClass.begin();ite != equiClass.end();ite++)
	{
		Variable* repre = ite->first;
		map<Variable*, int>::const_iterator itm = assignment.find(repre);
		int value = 0;
		if (itm != assignment.end())
		{
			value = itm->second;
		}
		list<Variable*>::const_iterator itv;
		for (itv = ite->second.begin();itv != ite->second.end();itv++)
		{
			fullAssign.insert(map<Variable*,int>::value_type(*itv, value));
		}
	}

	return fullAssign;
}

//Counter-example generation
void GenCounterExp(map<Variable*, int> assignment,
				   list<pair<const DpoolNode*, SimpConstraints&> >& dlist,
				   map<const DpoolNode*, DpoolInstNode*>& instMap)
{
	NS_LOG_FUNCTION("Generate counter example...");
	cout << endl;
	cout << "==================== Generate Counter Example ==================" << endl;
	//Print execution of all DerivNodes
	list<pair<const DpoolNode*, SimpConstraints&> >::iterator itd;
	for (itd = dlist.begin();itd != dlist.end();itd++)
	{
		const DpoolNode* dnode = (*itd).first;
		string headName = dnode->GetHead()->GetName();
		SimpConstraints& simpCons = (*itd).second;
//		NS_LOG_DEBUG("SimpCons: ");
//		simpCons.Print();
//		map<Variable*, int>::iterator assItr;
//		for (assItr = assignment.begin();assItr != assignment.end();assItr++)
//		{
//			cout << "Variable: ";
//			assItr->first->PrintTerm();
//			cout << ":" << assItr->second << endl;
//		}

		map<Variable*, int> valueMap = PropAssignment(simpCons, assignment);

//		cout << endl;
//		map<Variable*, int>::iterator itmv;
//		for (itmv = valueMap.begin();itmv != valueMap.end();itmv++)
//		{
//			itmv->first->PrintTerm();
//			cout << ":" << itmv->second;
//			cout << endl;
//		}
//		cout << endl;

		map<const DpoolNode*, DpoolInstNode*>::iterator itInst = instMap.find(dnode);
		if (itInst == instMap.end())
		{
			NS_LOG_ERROR("Variable mapping not found!");
		}

		cout << "************* Execution Trace of " << headName;
		bool printVar = false;
		cout << " *************" << endl;
		DpoolInstNode* instNode = itInst->second;
		//dnode->PrintExecInst(valueMap, instNode, true);
		dnode->PrintSimpExecInst(valueMap, instNode, simpCons, true);
		cout << "*******************************" << endl;
	}

	cout << "===================================" << endl;
}

//TODO: documentation
//assignment: counter-example instances
//return value: [true: constraints sat|false: constraints unsat]
bool CheckWholeProp(const Property& prop,
					list<DpoolTupleInst>& tplist,
				    ConsList& clist,
					FormList& flist,
					map<Variable*, int>& assignment,
					list<SimpConstraints*>& slist)
{
	NS_LOG_FUNCTION("Check combined predicates...");
	VarMap headMap;

	//Create variable mapping for existentially quantified predicates
	const list<PredicateInstance*>& plist = prop.GetExistPred();
	list<DpoolTupleInst>::const_iterator itt;
	list<PredicateInstance*>::const_iterator itp;

	for (itt = tplist.begin();itt != tplist.end();itt++)
	{
		const DpoolNode* dnode = (*itt).first;
		const Tuple* headTp = dnode->GetHead();
		string tpName = headTp->GetName();
		for (itp = plist.begin();itp != plist.end();itp++)
		{
			string pName = (*itp)->GetName();
			if (tpName == pName)
			{
				DpoolInstNode* instNode = (*itt).second;
				VarMap& instMap = instNode->headMap;
				const vector<Term*> predArgs = (*itp)->GetArgs();
				const vector<Variable*> args = headTp->GetArgs();
				cout << "size of pred" << predArgs.size() << endl;
				cout << "size of tuple" << args.size() << endl;
				vector<Variable*>::const_iterator itvv;
				vector<Term*>::const_iterator itp = predArgs.begin();
				for (itvv = args.begin();itvv != args.end();itvv++, itp++)
				{
					Variable* varInst = instMap.at(*itvv);
					Variable* predVar = dynamic_cast<Variable*>(*itp);
					if (predVar == NULL)
					{
						NS_LOG_ERROR("A non-variable argument in the predicate!");
					}
					headMap.insert(VarMap::value_type(predVar, varInst));

				}

				break;
			}
		}
	}

	//Add existentially quantified constraints
	const ConstraintsTemplate* csTemp = prop.GetExistCons();
	ConstraintsTemplate* newTemp = csTemp->Revert();
	newTemp->ReplaceVar(headMap);

	//Unify variables with universally quantified predicates
	list<SimpConstraints*>::iterator its;
	for (its = slist.begin();its != slist.end();its++)
	{
		newTemp->ReplaceVar(**its);
	}

	//Separate cases by determining if there are
	//existentially quantified variables in properties
	const list<Variable*>& existVars = prop.GetExistVars();
	if (existVars.size() > 0)
	{
		//Create a universally quantified formula
		list<Variable*>::const_iterator itev;
		vector<Variable*> quanVars;
		for (itev = existVars.begin();itev != existVars.end();itev++)
		{
			quanVars.push_back(*itev);
		}
		Formula* univForm = new Quantifier(Quantifier::FORALL, quanVars, newTemp);
		flist.push_back(univForm);
	}
	else
	{
		clist.push_back(newTemp);
	}

	//Check clist + flist is sat?
	assignment = check_sat(clist, flist);
	delete newTemp;
	if (assignment.size() > 0)
	{
		return true;
	}
	else
	{
		return false;
	}
}

//Return value: [true: an unsat element, meaning its negation is valid|
//				 false: all sat, its negation invalid]
bool CheckRecurExist(const Property& prop,
					 DpoolTupleMap& tlist,
					 DpoolTupleMap::const_iterator itm,
					 list<DpoolTupleInst> tplist,
					 ConsList& clist,
					 FormList& flist,
					 map<Variable*, int>& assignment,
					 list<SimpConstraints*> slist,
					 map<const DpoolNode*, DpoolInstNode*>& dvmap)
{
	NS_LOG_FUNCTION("Check existentially quantified predicates...");
	if (itm == tlist.end())
	{
		return CheckWholeProp(prop, tplist, clist, flist, assignment, slist);
	}

	const list<DpoolTupleInst>& headList = itm->second;
	itm++;
	list<DpoolTupleInst>::const_iterator itp;
	for (itp = headList.begin();itp != headList.end();itp++)
	{
		tplist.push_back(*itp);
		bool res = CheckRecurExist(prop, tlist, itm, tplist,
								   clist, flist, assignment, slist, dvmap);
		if (res == false)
		{
			return true;
		}

		tplist.pop_back();
	}

	return false;
}


//TODO: Separate the verification of universally
//quantified constraints from CheckExistProp
bool CheckExistProp(const Property& prop,
					const DpoolNodeList& dlist,
					BaseRelProperty& brp)
{
	NS_LOG_FUNCTION("Check universally quantified properties...");
	//First if the assumption holds or not
	VarMap headMap;
	ConsList cslist;
	FormList flist;
	list<SimpConstraints*> slist;
	map<Variable*, int> assignment = map<Variable*, int>();
	bool veriResult = false;

	map<const DpoolNode*, DpoolInstNode*> dInstMap;

	DpoolNodeList::const_iterator itd;
	for (itd = dlist.begin();itd != dlist.end();itd++)
	{
		//Create derivation instances
		NS_LOG_DEBUG("Dnode:");
		(*itd)->PrintDerivation();
		VarMap instMap = VarMap();
		DpoolInstNode* instNode = (*itd)->CreateDerivInst();

//		cout << "****************** Check Derivation Instance ******************" << endl;
//		(*itd)->PrintDerivInst(instNode);
//		cout << "******************************************************" << endl;
		dInstMap.insert(map<const DpoolNode*, DpoolInstNode*>::value_type(*itd, instNode));

		//Create constraint instances
		ConsList copyclist = ConsList();
		(*itd)->CollectConsInst(instNode, copyclist, flist);

		//Record simplified constraint instances
		SimpConstraints* newSimp = new SimpConstraints(copyclist);
		slist.push_back(newSimp);

		//Collect simplified constraint instances
		const ConstraintsTemplate& newCtemp = newSimp->GetConstraints();
//		cout << "@@@@@@@@@@@@@@@  Simplified Constraints Instances @@@@@@@@@@@@@@" << endl;
//		newCtemp.PrintTemplate();
//		cout << "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@" << endl;
		//newCtemp.PrintTemplate();
		cslist.push_back(&newCtemp);

		//Deallocate memory of copyclist
		ConsList::iterator itcp;
		for (itcp = copyclist.begin();itcp != copyclist.end();itcp++)
		{
			delete (*itcp);
		}
	}

	//Add special base tuple requirements
	DpoolTupleMap baseCollection;
	DpoolNodeList::const_iterator itdc;
	for (itdc = dlist.begin();itdc != dlist.end();itdc++)
	{
		string tpName = (*itdc)->GetHead()->GetName();
		cout << "Search base predicates in: " << tpName << endl;
		const DpoolNode* dnode = *itdc;
		DpoolInstNode* instNode = dInstMap.at(dnode);
		(*itdc)->FindBaseTuple(instNode, baseCollection);
	}

	NS_LOG_DEBUG("Base tuples of derivations collected.");

	//Process base relational properties one by one
	list<BaseRel*>& brlist = brp.GetPropSet();
	list<BaseRel*>::iterator itb;
	for (itb = brlist.begin();itb != brlist.end();itb++)
	{
		list<PredicateInstance*>& basePreds = (*itb)->basePreds;
		list<PredicateInstance*>::iterator itpd = basePreds.begin();
		list<DpoolTupleInst> lineageList = list<DpoolTupleInst>();
		CheckRecurBase(**itb, itpd, lineageList, baseCollection, flist);
	}

	NS_LOG_DEBUG("Base relational properties processing finished.");

	//Replace variables in flist with representative variables
	FormList::iterator itf;
	for (itf = flist.begin();itf != flist.end();itf++)
	{
		list<SimpConstraints*>::iterator itsp;
		for (itsp = slist.begin();itsp != slist.end();itsp++)
		{
			(*itf)->VarReplace(**itsp);
		}
	}

	//Create variable unification for universally quantified predicates
	const list<PredicateInstance*>& plist = prop.GetUniPred();
	list<PredicateInstance*>::const_iterator itp = plist.begin();
	for (itd = dlist.begin();itd != dlist.end();itd++, itp++)
	{
		//(*itd)->PrintDerivNode();

		map<const DpoolNode*, DpoolInstNode*>::iterator itmd = dInstMap.find(*itd);
		if (itmd == dInstMap.end())
		{
			NS_LOG_ERROR("Variable mapping not found!");
		}
		VarMap& derivInstMap = itmd->second->headMap;

		//Create variable mapping between predicate and the head tuple instance
		const Tuple* head = (*itd)->GetHead();
		const vector<Variable*> args = head->GetArgs();
		vector<Variable*>::const_iterator itvv;
		const vector<Term*> predArgs = (*itp)->GetArgs();
		vector<Term*>::const_iterator itpa = predArgs.begin();
		for (itvv = args.begin();itvv != args.end();itvv++,itpa++)
		{
			Variable* instVar = derivInstMap.at(*itvv);
			Variable* predVar = dynamic_cast<Variable*>(*itpa);
			if (predVar == NULL)
			{
				NS_LOG_ERROR("An non-variable argument in the predicate.");
			}
			headMap.insert(VarMap::value_type(predVar, instVar));
		}
	}

	//Collect universally quantified constraints
	const ConstraintsTemplate* cTemp = prop.GetUniCons();
	ConstraintsTemplate* uniCons = new ConstraintsTemplate(*cTemp);
	uniCons->ReplaceVar(headMap);

	//Replace variables with representative ones of the equivalent class
	list<SimpConstraints*>::iterator its;
	for (its = slist.begin();its != slist.end();its++)
	{
		uniCons->ReplaceVar(**its);
	}

	cslist.push_back(uniCons);

//	cout << "cslist contents:" << endl;
//	for (ConsList::iterator itc = cslist.begin();itc != cslist.end();itc++)
//	{
//		(*itc)->PrintTemplate();
//	}

	//Check satisfiability of cslist + flist.
	cout << "Check satisfiability of the assumption:" << endl;

	//Check if there is at least one Constraint or Formula
	ConsList::iterator itcp;
	bool EmptyAssump = true;
	for (itcp = cslist.begin();itcp != cslist.end();itcp++)
	{
		if (!(*itcp)->IsEmpty())
		{
			EmptyAssump = false;
			break;
		}
	}
	if (EmptyAssump == true && flist.size() > 0)
	{
		EmptyAssump = false;
	}

	map<Variable*, int> assumpValue;
	if (EmptyAssump == false)
	{
		NS_LOG_DEBUG("The property contains assumption.");
		assumpValue = check_sat(cslist, flist);
		if (assumpValue.size() == 0)
		{
			//Assumption is not satisfiable
			cout << "Assumption of the property is unsatisfiable "
					"for this derivation branch." << endl;

			//Print the derivation that is being checked
//			DerivNodeList::const_iterator itpr = dlist.begin();
//			list<SimpConstraints*>::iterator its = slist.begin();
//			for (;itpr != dlist.end();itpr++, its++)
//			{
//				cout << "Print an instance of simplified derivation:";
//				DpoolInstNode* instNode = dInstMap.at(*itpr);
//				(*itpr)->PrintSimpDerivInst(instNode, **its);
//				cout << endl;
//			}

			//Release memory allocated to slist;
			list<SimpConstraints*>::iterator itl;
			for (itl = slist.begin();itl != slist.end();itl++)
			{
				delete (*itl);
			}

			FormList::iterator itfl;
			for (itfl = flist.begin();itfl != flist.end();itfl++)
			{
				delete (*itfl);
			}

			delete uniCons;

			//TODO: See how interleaved design leads to chaos
			//Deallocate memory of free variables
			map<const DpoolNode*, DpoolInstNode*>::iterator itm;
			for (itm = dInstMap.begin();itm != dInstMap.end();itm++)
			{
				delete itm->second;
			}

			return true;
		}
	}


	//Check if assumption /\ not conclusion is sat

	//First find existentially quantified tuples from derivations
	//of universally quantified tuples
	const list<PredicateInstance*>& existPlist = prop.GetExistPred();
	//TODO: Separate checking process for the case where
	//existentially quantified predicates does not exist
	if (existPlist.size() == 0)
	{
		cout << "No existentially quantified predicates." << endl;
		//Proof the case where there is no
		//existentially quantified predicate
		const ConstraintsTemplate* csTemp = prop.GetExistCons();
		NS_LOG_DEBUG("Existentially quantified constraints:");
		csTemp->PrintTemplate();

		ConstraintsTemplate* newTemp = csTemp->Revert();
		newTemp->ReplaceVar(headMap);

		list<SimpConstraints*>::iterator its;
		for (its = slist.begin();its != slist.end();its++)
		{
			newTemp->ReplaceVar(**its);
		}

		NS_LOG_DEBUG("Constraints after unification:");
		newTemp->PrintTemplate();

		cslist.push_back(newTemp);
//		cout << "cslist contents:" << endl;
//		for (ConsList::iterator itc = cslist.begin();itc != cslist.end();itc++)
//		{
//			(*itc)->PrintTemplate();
//		}

		//Check cslist + flist is sat?
		assignment = check_sat(cslist, flist);
		delete newTemp;

		if (assignment.size() > 0)
		{
			//Generate counter-example
			list<pair<const DpoolNode*, SimpConstraints&> > pairList;
			list<SimpConstraints*>::iterator itsl = slist.begin();
			DpoolNodeList::const_iterator itd = dlist.begin();
			for (;itd != dlist.end();itd++, itsl++)
			{
				pair<const DpoolNode*, SimpConstraints&> newPair(*itd, **itsl);
				pairList.push_back(newPair);
			}
			GenCounterExp(assignment, pairList, dInstMap);
			veriResult = false;
		}
		else
		{
			veriResult = true;
		}
	}
	else
	{
		cout << "Process existential quantified tuples." << endl;
		//Initialization for collection of existentially quantified predicates
		DpoolTupleMap exTupleList;
		list<DpoolTupleInst> emptyList;
		for (itp = existPlist.begin();itp != existPlist.end();itp++)
		{
			//initialization
			string pName = (*itp)->GetName();
			exTupleList.insert(DpoolTupleMap::value_type(pName, emptyList));
		}

		//Collect existentially quantified predicates from all derivations
		DpoolNodeList::const_iterator itdc;
		for (itdc = dlist.begin();itdc != dlist.end();itdc++)
		{
			string tpName = (*itdc)->GetHead()->GetName();
			NS_LOG_DEBUG("Search existentially quantified predicates in: " << tpName);
			const DpoolNode* dnode = (*itdc);
			DpoolInstNode* instNode = dInstMap.at(dnode);
			(*itdc)->FindSubTuple(existPlist, exTupleList, instNode);
		}

		DpoolTupleMap::iterator itmp;
		for (itmp = exTupleList.begin();itmp != exTupleList.end();itmp++)
		{
			list<DpoolTupleInst>& tplist = itmp->second;
			if (tplist.size() == 0)
			{
				cout << "No matching for existentially "
						    "quantified predicate: " << itmp->first << endl;
				//Generate counter examples for universally quantified predicates
				//TODO: The following copy of code can be used as a function
				list<pair<const DpoolNode*, SimpConstraints&> > pairList;
				list<SimpConstraints*>::iterator itsl = slist.begin();
				DpoolNodeList::const_iterator itd = dlist.begin();
				for (;itd != dlist.end();itd++, itsl++)
				{
					pair<const DpoolNode*, SimpConstraints&> newPair(*itd, **itsl);
					pairList.push_back(newPair);
				}

				GenCounterExp(assumpValue, pairList, dInstMap);
				return false;
			}
		}

		//Check all possible combinations
		DpoolTupleMap::const_iterator itmc = exTupleList.begin();
		list<DpoolTupleInst> tplist;
		bool res = CheckRecurExist(prop, exTupleList, itmc, tplist,
								   cslist, flist, assignment, slist, dInstMap);
		if (res == false)
		{
			//Generate counter examples for universally quantified predicates
			//TODO: The following copy of code can be used as a function
			list<pair<const DpoolNode*, SimpConstraints&> > pairList;
			list<SimpConstraints*>::iterator itsl = slist.begin();
			DpoolNodeList::const_iterator itd = dlist.begin();
			for (;itd != dlist.end();itd++, itsl++)
			{
				pair<const DpoolNode*, SimpConstraints&> newPair(*itd, **itsl);
				pairList.push_back(newPair);
			}

			GenCounterExp(assignment, pairList, dInstMap);
		}

		//If the set of tuples are the instances in existential
		//quantification, then they provide instantiation of
		//existentially quantified variables.

		veriResult = res;
	}

	//Release memory allocated to slist;
	list<SimpConstraints*>::iterator itl;
	for (itl = slist.begin();itl != slist.end();itl++)
	{
		(*itl)->Print();
		delete (*itl);
	}

	FormList::iterator itfl;
	for (itfl = flist.begin();itfl != flist.end();itfl++)
	{
		delete (*itfl);
	}

	delete uniCons;

	//TODO: See how interleaved design leads to chaos
	//Deallocate memory of free variables
	map<const DpoolNode*, DpoolInstNode*>::iterator itm;
	for (itm = dInstMap.begin();itm != dInstMap.end();itm++)
	{
		delete itm->second;
	}

	return veriResult;
}

//Return value: [true: property holds|false: property does not hold]
bool CheckRecurUniv(const Dpool& dpool,
					const Property& prop,
					const list<PredicateInstance*>& plist,
					list<PredicateInstance*>::const_iterator itc,
					DpoolNodeList dlist,
					BaseRelProperty& brp)
{
	NS_LOG_FUNCTION("Enumerate universally quantified predicates...");
	if (itc == plist.end())
	{
		bool res = CheckExistProp(prop, dlist, brp);
		return res;
	}

	bool resFlag = true;
	string predName = (*itc)->GetName();
	itc++;
	NS_LOG_DEBUG("Pred name:" << predName);
	const DerivMap& dmap = dpool.GetDerivation();
	DerivMap::const_iterator itdm = dmap.find(predName);
	if (itdm == dmap.end())
	{
		//A base tuple
		const BaseMap& bmap = dpool.GetBases();

		BaseMap::const_iterator itbm;
		for (itbm = bmap.begin();itbm != bmap.end();itbm++)
		{
			cout << itbm->first << endl;
		}

		const BaseNodeList& blist = bmap.at(predName);
		BaseNodeList::const_iterator itb;
		for (itb = blist.begin();itb != blist.end();itb++)
		{
			string baseName = (*itb)->GetHead()->GetName();
			if (baseName == predName)
			{
				dlist.push_back(*itb);
				bool result = CheckRecurUniv(dpool, prop, plist, itc, dlist, brp);
				if (result == false)
				{
					resFlag = false;
				}
				break;
			}
		}
	}
	else
	{
		const DerivNodeList& headList = itdm->second;
		DerivNodeList::const_iterator itd;
		for (itd = headList.begin();itd != headList.end();itd++)
		{
			dlist.push_back(*itd);
			bool result = CheckRecurUniv(dpool, prop, plist, itc, dlist, brp);
			//One false branch makes the whole checking false
			if (result == false)
			{
				resFlag = false;
			}
			dlist.pop_back();
		}
	}

	return resFlag;
}

//TODO: Add property checking for base tuples
bool CheckProperty(const Dpool& dpool,
				   const Property& prop,
				   BaseRelProperty& brp)
{
	//TODO: Unify invariant checking and property checking
	cout << "----------------- Check property ----------------" << endl;
	//Process universally quantified predicates
	const list<PredicateInstance*>& plist = prop.GetUniPred();
	list<PredicateInstance*>::const_iterator itc = plist.begin();
	DpoolNodeList dlist = DpoolNodeList();
	bool res = CheckRecurUniv(dpool, prop, plist, itc, dlist, brp);
	return res;
}

