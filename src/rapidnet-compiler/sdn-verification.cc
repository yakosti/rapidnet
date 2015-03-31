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
				   list<pair<const DerivNode*, SimpConstraints&> >& dlist,
				   map<const DerivNode*, VarMap>& instMap)
{
	NS_LOG_FUNCTION("Generate counter example...");
	cout << endl;
	cout << "==================== Generate Counter Example ==================" << endl;
	//Print execution of all DerivNodes
	list<pair<const DerivNode*, SimpConstraints&> >::iterator itd;
	for (itd = dlist.begin();itd != dlist.end();itd++)
	{
		const DerivNode* dnode = (*itd).first;
		string headName = dnode->GetHead()->GetName();
		SimpConstraints& simpCons = (*itd).second;
		NS_LOG_DEBUG("SimpCons: ");
		simpCons.Print();
		map<Variable*, int>::iterator assItr;
		for (assItr = assignment.begin();assItr != assignment.end();assItr++)
		{
			cout << "Variable: ";
			assItr->first->PrintTerm();
			cout << ":" << assItr->second << endl;
		}

		map<Variable*, int> valueMap = PropAssignment(simpCons, assignment);
		map<const DerivNode*, VarMap>::iterator itInst = instMap.find((*itd).first);
		if (itInst == instMap.end())
		{
			NS_LOG_ERROR("Variable mapping not found!");
		}
		cout << "************* Execution Trace of " << headName;
		cout << " *************" << endl;
		dnode->PrintExecInst(valueMap, itInst->second);
		cout << "*******************************" << endl;
	}

	cout << "===================================" << endl;
}

//TODO: documentation
//assignment: counter-example instances
//return value: [true: constraints sat|false: constraints unsat]
bool CheckWholeProp(const Property& prop,
					list<TupleLineage>& tplist,
				    ConsList& clist,
					FormList& flist,
					map<Variable*, int>& assignment,
					list<SimpConstraints*>& slist,
					map<const DerivNode*, VarMap>& dvmap)
{
	NS_LOG_FUNCTION("Check combined predicates...");
	VarMap headMap;

	//Create variable mapping for existentially quantified predicates
	const list<PredicateInstance*>& plist = prop.GetExistPred();
	list<TupleLineage>::const_iterator itt;
	list<PredicateInstance*>::const_iterator itp;
	for (itt = tplist.begin();itt != tplist.end();itt++)
	{
		const Tuple* exTuple = (*itt).first;
		const DerivNode* desigHead = (*itt).second;
		string tpName = exTuple->GetName();
		for (itp = plist.begin();itp != plist.end();itp++)
		{
			string pName = (*itp)->GetName();
			if (tpName == pName)
			{
				VarMap& instMap = dvmap.at(desigHead);
				const vector<Term*> predArgs = (*itp)->GetArgs();

				const vector<Variable*> args = exTuple->GetArgs();
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
					 ExQuanTuple& tlist,
					 ExQuanTuple::const_iterator itm,
					 list<TupleLineage> tplist,
					 ConsList& clist,
					 FormList& flist,
					 map<Variable*, int>& assignment,
					 list<SimpConstraints*> slist,
					 map<const DerivNode*, VarMap>& dvmap)
{
	NS_LOG_FUNCTION("Check existentially quantified predicates...");
	if (itm == tlist.end())
	{
		return CheckWholeProp(prop, tplist, clist, flist, assignment, slist, dvmap);
	}

	const list<TupleLineage>& headList = itm->second;
	itm++;
	list<TupleLineage>::const_iterator itp;
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
					const DerivNodeList& dlist)
{
	NS_LOG_FUNCTION("Check universally quantified properties...");
	//First if the assumption holds or not
	VarMap headMap;
	ConsList cslist;
	FormList flist;
	list<SimpConstraints*> slist;
	map<Variable*, int> assignment = map<Variable*, int>();
	bool veriResult = false;

	map<const DerivNode*, VarMap> dInstMap = map<const DerivNode*, VarMap>();

	DerivNodeList::const_iterator itd;
	for (itd = dlist.begin();itd != dlist.end();itd++)
	{
		//Create derivation instances
		NS_LOG_DEBUG("Dnode:");
		(*itd)->PrintDerivation();
		VarMap instMap = VarMap();
		(*itd)->CreateDerivInst(instMap);
		dInstMap.insert(map<const DerivNode*, VarMap>::value_type(*itd, instMap));

		NS_LOG_DEBUG("Print instantiated variables:");
		VarMap::iterator ittest;
		for (ittest = instMap.begin();ittest != instMap.end();ittest++)
		{
			ittest->first->PrintTerm();
			cout << ":";
			ittest->second->PrintTerm();
			cout << endl;
		}

		//Create constraint instances
		const ConsList& clist = (*itd)->GetCumuConsts();
		ConsList copyclist = ConsList();
		ConsList::const_iterator itcp;
		for (itcp = clist.begin();itcp != clist.end();itcp++)
		{
			ConstraintsTemplate* copyTemp = new ConstraintsTemplate(**itcp);
			//Create instance constraints of the execution
			copyTemp->ReplaceVar(instMap);
			copyclist.push_back(copyTemp);
		}

		//Record simplified constraint instances
		SimpConstraints* newSimp = new SimpConstraints(copyclist);
		slist.push_back(newSimp);

		//Collect simplified constraint instances
		const ConstraintsTemplate& newCtemp = newSimp->GetConstraints();
		//newCtemp.PrintTemplate();
		cslist.push_back(&newCtemp);

		//Collect invariants
		const FormList& tupleFlist = (*itd)->GetInvariants();
		FormList::const_iterator itfl;
		for (itfl = tupleFlist.begin();itfl != tupleFlist.end();itfl++)
		{
			Formula* newForm = (*itfl)->Clone();
			newForm->VarReplace(instMap);
			flist.push_back(newForm);
		}

		NS_LOG_DEBUG("Delete here?");
		//Deallocate memory of copyclist
		for (itcp = copyclist.begin();itcp != copyclist.end();itcp++)
		{
			delete (*itcp);
		}
		NS_LOG_DEBUG("Delete here??");
	}


	const list<PredicateInstance*>& plist = prop.GetUniPred();
	list<PredicateInstance*>::const_iterator itp = plist.begin();
	for (itd = dlist.begin();itd != dlist.end();itd++, itp++)
	{
		//(*itd)->PrintDerivNode();

		map<const DerivNode*, VarMap>::iterator itmd = dInstMap.find(*itd);
		if (itmd == dInstMap.end())
		{
			NS_LOG_ERROR("Variable mapping not found!");
		}
		VarMap& derivInstMap = itmd->second;

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
				NS_LOG_ERROR("An non-varaible argument in the predicate.");
			}
			headMap.insert(VarMap::value_type(predVar, instVar));
		}
	}

	NS_LOG_DEBUG("Print mapping from predicate variables to variable instances:");
	VarMap::iterator itvh;
	for (itvh = headMap.begin();itvh != headMap.end();itvh++)
	{
		itvh->first->PrintTerm();
		cout << ":";
		itvh->second->PrintTerm();
		cout << endl;
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
	NS_LOG_INFO("Check satisfiability of the assumption:");

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
			NS_LOG_INFO("Assumption of the property is unsatisfiable "
					"for this derivation branch.");

			//Deallocate memory of free variables
			map<const DerivNode*, VarMap>::iterator itm;
			for (itm = dInstMap.begin();itm != dInstMap.end();itm++)
			{
				VarMap& instMap = itm->second;
				VarMap::iterator itvm;
				for (itvm = instMap.begin();itvm != instMap.end();itvm++)
				{
					delete itvm->second;
				}
			}

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
		NS_LOG_INFO("No existentially quantified predicates.");
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
			list<pair<const DerivNode*, SimpConstraints&> > pairList;
			list<SimpConstraints*>::iterator itsl = slist.begin();
			DerivNodeList::const_iterator itd = dlist.begin();
			for (;itd != dlist.end();itd++, itsl++)
			{
				pair<const DerivNode*, SimpConstraints&> newPair(*itd, **itsl);
				pairList.push_back(newPair);
			}
			//GenCounterExp(assignment, pairList, dInstMap);
			veriResult = false;
		}
		else
		{
			veriResult = true;
		}
	}
	else
	{
		NS_LOG_INFO("Process existential quantified tuples.");
		//Initialization for collection of existentially quantified predicates
		ExQuanTuple exTupleList;
		list<TupleLineage> emptyList;
		for (itp = existPlist.begin();itp != existPlist.end();itp++)
		{
			//initialization
			string pName = (*itp)->GetName();
			exTupleList.insert(ExQuanTuple::value_type(pName, emptyList));
		}

		//Collect existentially quantified predicates from all derivations
		DerivNodeList::const_iterator itdc;
		for (itdc = dlist.begin();itdc != dlist.end();itdc++)
		{
			string tpName = (*itdc)->GetHead()->GetName();
			NS_LOG_DEBUG("Search existentially quantified predicates in: " << tpName);
			(*itdc)->FindSubTuple(existPlist, exTupleList, *itdc);
		}

		ExQuanTuple::iterator itmp;
		for (itmp = exTupleList.begin();itmp != exTupleList.end();itmp++)
		{
			list<TupleLineage>& tplist = itmp->second;
			if (tplist.size() == 0)
			{
				NS_LOG_INFO("No matching for existentially "
						    "quantified predicate: " << itmp->first);
				//Generate counter examples for universally quantified predicates
				//TODO: The following copy of code can be used as a function
				list<pair<const DerivNode*, SimpConstraints&> > pairList;
				list<SimpConstraints*>::iterator itsl = slist.begin();
				DerivNodeList::const_iterator itd = dlist.begin();
				for (;itd != dlist.end();itd++, itsl++)
				{
					pair<const DerivNode*, SimpConstraints&> newPair(*itd, **itsl);
					pairList.push_back(newPair);
				}

				//GenCounterExp(assumpValue, pairList,  dInstMap);
				return false;
			}
		}

		//Check all possible combinations
		ExQuanTuple::const_iterator itmc = exTupleList.begin();
		list<TupleLineage> tplist;
		bool res = CheckRecurExist(prop, exTupleList, itmc, tplist,
								   cslist, flist, assignment, slist, dInstMap);
		if (res == false)
		{
			//Generate counter examples for universally quantified predicates
			//TODO: The following copy of code can be used as a function
			list<pair<const DerivNode*, SimpConstraints&> > pairList;
			list<SimpConstraints*>::iterator itsl = slist.begin();
			DerivNodeList::const_iterator itd = dlist.begin();
			for (;itd != dlist.end();itd++, itsl++)
			{
				pair<const DerivNode*, SimpConstraints&> newPair(*itd, **itsl);
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

	NS_LOG_DEBUG("Reach here?");

	FormList::iterator itfl;
	for (itfl = flist.begin();itfl != flist.end();itfl++)
	{
		delete (*itfl);
	}

	delete uniCons;

	NS_LOG_DEBUG("Reach here??");

	//TODO: See how interleaved design leads to chaos
	//Deallocate memory of free variables
	map<const DerivNode*, VarMap>::iterator itm;
	for (itm = dInstMap.begin();itm != dInstMap.end();itm++)
	{
		VarMap& instMap = itm->second;
		VarMap::iterator itvm;
		for (itvm = instMap.begin();itvm != instMap.end();itvm++)
		{
			delete itvm->second;
		}
	}

	NS_LOG_DEBUG("Reach here???");

	return veriResult;
}

//Return value: [true: property holds|false: property does not hold]
bool CheckRecurUniv(const DerivMap& dmap,
					const Property& prop,
					const list<PredicateInstance*>& plist,
					list<PredicateInstance*>::const_iterator itc,
					DerivNodeList dlist)
{
	NS_LOG_FUNCTION("Enumerate universally quantified predicates...");
	if (itc == plist.end())
	{
		bool res = CheckExistProp(prop, dlist);
		NS_LOG_DEBUG("Reach here???");
		return res;
	}

	string predName = (*itc)->GetName();
	NS_LOG_DEBUG("Pred name:" << predName);
	const DerivNodeList& headList = dmap.at(predName);
	itc++;
	DerivNodeList::const_iterator itd;
	for (itd = headList.begin();itd != headList.end();itd++)
	{
		dlist.push_back(*itd);
		bool result = CheckRecurUniv(dmap, prop, plist, itc, dlist);
		//One false branch makes the whole checking false
		if (result == false)
		{
			return false;
		}
		dlist.pop_back();
	}

	return true;
}

//TODO: Add property checking for base tuples
bool CheckProperty(const Dpool& dpool,
				   const Property& prop)
{
	//TODO: Unify invariant checking and property checking
	cout << "----------------- Check property ----------------" << endl;
	//Process universally quantified predicates
	const list<PredicateInstance*>& plist = prop.GetUniPred();
	list<PredicateInstance*>::const_iterator itc = plist.begin();
	DerivNodeList dlist = DerivNodeList();
	const DerivMap& dmap = dpool.GetDerivation();
	return CheckRecurUniv(dmap, prop, plist, itc, dlist);
}

