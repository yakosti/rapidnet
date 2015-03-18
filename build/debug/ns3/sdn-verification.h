/*
 * sdn-verification.h
 *
 *  Created on: Mar 10, 2015
 *      Author: chen
 */

#ifndef SDN_VERIFICATION_H_
#define SDN_VERIFICATION_H_

#include "ns3/log.h"

#include "sdn-derivation.h"
#include "sdn-parse-smtlib.h"

NS_LOG_COMPONENT_DEFINE ("RapidNetDPGraph");

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
	map<Variable*, int> fullAssign;
	const map<Variable*, list<Variable*> >& equiClass = simpCons.GetEquiClass();
	map<Variable*, list<Variable*> >::const_iterator ite;
	for (ite = equiClass.begin();ite != equiClass.end();ite++)
	{
		Variable* repre = ite->first;
		int value = assignment.at(repre);
		list<Variable*>::const_iterator itv;
		for (itv = ite->second.begin();itv != ite->second.end();itv++)
		{
			fullAssign.insert(map<Variable*,int>::value_type(repre, value));
		}
	}

	return fullAssign;
}

//Counter-example generation
void GenCounterExp(map<Variable*, int> assignment,
				   list<pair<const DerivNode&, SimpConstraints&> >& dlist)
{
	//Print execution of all DerivNodes
	list<pair<const DerivNode&, SimpConstraints&> >::iterator itd;
	for (itd = dlist.begin();itd != dlist.end();itd++)
	{
		const DerivNode& dnode = (*itd).first;
		string headName = dnode.GetHead()->GetName();
		SimpConstraints& simpCons = (*itd).second;
		map<Variable*, int> valueMap = PropAssignment(simpCons, assignment);
		cout << "************* Execution Trace of " << headName;
		cout << " *************" << endl;
		dnode.PrintExecution(valueMap);
		cout << "*******************************" << endl;
	}
}

//TODO: documentation
//assignment: counter-example instances
//return value: [true: constraints sat|false: constraints unsat]
bool CheckWholeProp(const Property& prop,
					list<const Tuple*> tplist,
				    ConsList& clist,
					const FormList& flist,
					map<Variable*, int>& assignment,
					list<SimpConstraints*> slist)
{
	NS_LOG_FUNCTION("Check combined predicates...");
	VarMap vmap;
	const list<PredicateInstance*>& plist = prop.GetExistPred();
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
	list<SimpConstraints*>::iterator its;
	for (its = slist.begin();its != slist.end();its++)
	{
		newTemp->ReplaceVar(**its);
	}

	clist.push_back(newTemp);

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
					 map<string, list<const Tuple*> >& tlist,
					 map<string, list<const Tuple*> >::const_iterator itm,
					 list<const Tuple*> tplist,
					 ConsList& clist,
					 const FormList& flist,
					 map<Variable*, int>& assignment,
					 list<SimpConstraints*> slist)
{
	NS_LOG_FUNCTION("Check existentially quantified predicates...");
	if (itm == tlist.end())
	{
		return CheckWholeProp(prop, tplist, clist, flist, assignment, slist);
	}

	const list<const Tuple*>& headList = itm->second;
	itm++;
	list<const Tuple*>::const_iterator itp;
	for (itp = headList.begin();itp != headList.end();itp++)
	{
		tplist.push_back(*itp);
		bool res = CheckRecurExist(prop, tlist, itm, tplist,
								   clist, flist, assignment, slist);
		if (res == false)
		{
			//TODO:Generate a counter-example
			return true;
		}

		tplist.pop_back();
	}

	return false;
}


//TODO: Separate the verification of universally
//quantified constraints from CheckExistProp
bool CheckExistProp(const Property& prop,
					const DerivNodeList& dlist,
					map<Variable*, int>& assignment)
{
	NS_LOG_FUNCTION("Check universally quantified properties...");
	//First if the assumption holds or not
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
		const Tuple* head = (*itd)->GetHead();
		VarMap headMap = head->CreateVarMap(*itp);
		vmap.insert(headMap.begin(), headMap.end());

		//Record simplified constraints
		const ConsList& clist = (*itd)->GetCumuConsts();
		SimpConstraints* newSimp = new SimpConstraints(clist);
		NS_LOG_DEBUG("Test SimpConstraints:");
		newSimp->Print();
		slist.push_back(newSimp);

		//Collect simplified constraints
		const ConstraintsTemplate& newCtemp = newSimp->GetConstraints();
		//newCtemp.PrintTemplate();
		cslist.push_back(&newCtemp);

		//Collect invariants
		const FormList& tupleFlist = (*itd)->GetInvariants();
		flist.insert(flist.end(), tupleFlist.begin(), tupleFlist.end());
	}
	//Collect universally quantified constraints
	const ConstraintsTemplate* cTemp = prop.GetUniCons();
	ConstraintsTemplate uniCons(*cTemp);
	uniCons.ReplaceVar(vmap);
	//Replace variables with representative ones of the equivalent class
	list<SimpConstraints*>::iterator its;
	for (its = slist.begin();its != slist.end();its++)
	{
		uniCons.ReplaceVar(**its);
	}
	cslist.push_back(&uniCons);

//	cout << "cslist contents:" << endl;
//	for (ConsList::iterator itc = cslist.begin();itc != cslist.end();itc++)
//	{
//		(*itc)->PrintTemplate();
//	}

	//Check satisfiability of cslist + flist.
	NS_LOG_INFO("Check satisfiability of the assumption.");
	map<Variable*, int> assumpValue = check_sat(cslist, flist);
	if (assumpValue.size() == 0)
	{
		//Assumption is not satisfiable
		NS_LOG_INFO("Assumption of the property does not satisfy.");
		return true;
	}

	//Check if assumption /\ not conclusion is sat

	//First find existentially quantified tuples from derivations
	//of universally quantified tuples
	const list<PredicateInstance*>& existPlist = prop.GetExistPred();
	//TODO: Separate checking process for the case where
	//existentially quantified predicates does not exist
	if (existPlist.size() == 0)
	{
		//Proof the case where there is no
		//existentially quantified predicate
		const ConstraintsTemplate* csTemp = prop.GetExistCons();
		ConstraintsTemplate* newTemp = csTemp->Revert();
		newTemp->ReplaceVar(vmap);
		list<SimpConstraints*>::iterator its;
		for (its = slist.begin();its != slist.end();its++)
		{
			newTemp->ReplaceVar(**its);
		}

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
			return false;
		}
		else
		{
			return true;
		}
	}
	else
	{
		map<string, list<const Tuple*> > tlist;
		list<const Tuple*> ctlist;
		for (itp = existPlist.begin();itp != existPlist.end();itp++)
		{
			//tlist initialization
			string pName = (*itp)->GetName();
			tlist.insert(map<string, list<const Tuple*> >::value_type(
														pName, ctlist));
		}

		DerivNodeList::const_iterator itdc;
		for (itdc = dlist.begin();itdc != dlist.end();itdc++)
		{
//			(*itdc)->FindSubTuple(existPlist, tlist);
		}

		//Check all possible combinations
		map<string, list<const Tuple*> >::const_iterator itmc = tlist.begin();
		list<const Tuple*> tplist;
		bool res = CheckRecurExist(prop, tlist, itmc, tplist,
								   cslist, flist, assignment, slist);

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
}

//Return value: [true: property holds|false: property does not hold]
bool CheckRecurUniv(const DerivMap& dmap,
					const Property& prop,
					const list<PredicateInstance*>& plist,
					list<PredicateInstance*>::const_iterator itc,
					DerivNodeList dlist,
					map<Variable*, int>& assignment)
{
	NS_LOG_FUNCTION("Enumerate universally quantified predicates...");
	if (itc == plist.end())
	{
		return CheckExistProp(prop, dlist, assignment);
	}

	string predName = (*itc)->GetName();
	NS_LOG_DEBUG("Pred name:" << predName);
	const DerivNodeList& headList = dmap.at(predName);
	itc++;
	DerivNodeList::const_iterator itd;
	for (itd = headList.begin();itd != headList.end();itd++)
	{
		dlist.push_back(*itd);
		bool result = CheckRecurUniv(dmap, prop, plist, itc,
									 dlist, assignment);
		//One false branch makes the whole checking false
		if (result == false)
		{
			return false;
		}
		dlist.pop_back();
	}

	return true;
}


bool CheckProperty(const Dpool& dpool,
				   const Property& prop,
				   map<Variable*, int>& assignment)
{
	cout << "----------------- Check property ----------------" << endl;
	//Process universally quantified predicates
	assignment = map<Variable*, int>();
	const list<PredicateInstance*>& plist = prop.GetUniPred();
	list<PredicateInstance*>::const_iterator itc = plist.begin();
	DerivNodeList dlist = DerivNodeList();
	const DerivMap& dmap = dpool.GetDerivation();
	return CheckRecurUniv(dmap, prop, plist, itc, dlist, assignment);
}

#endif /* SDN_VERIFICATION_H_ */
