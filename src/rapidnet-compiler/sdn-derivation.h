/*
 * sdn-constraint.h
 *
 *
 *  Created on: Nov 7, 2014
 *      Author: cchen
 */

#ifndef SDN_DERIVATION_H_
#define SDN_DERIVATION_H_

#include <iostream>
#include <string>
#include <vector>
#include "sdn-formula.h"
#include "sdn-graph.h"
#include "sdn-property.h"
//#include "parser-util.h"

using namespace std;

class DerivNode;
class DerivBody;
class RecurNode;

typedef list<const ConstraintsTemplate*> ConsList;
typedef list<const Formula*> FormList;
typedef list<const DerivNode*> DerivNodeList;
typedef map<string, DerivNodeList> DerivMap;
typedef list<const RecurNode*> DerivAnnoList;

typedef pair<const ConsList&, const FormList&> Obligation;

//TODO: Create a class called BaseNode for base tuples.
//DerivNode points to a derivation of a body tuple
class DerivNode
{
public:
	DerivNode(const Tuple*);

	DerivNode(string tpName, list<Variable::TypeCode>&);

	DerivNode(Tuple* tn, string rn,
			  ConstraintsTemplate* consTemp,
			  DerivNodeList dlist, DerivAnnoList dblist,
			  ConsList clist, FormList flist):
		head(tn),ruleName(rn),ruleConstraints(consTemp),
		bodyDerivs(dlist),bodyAnnotations(dblist),
		allConstraints(clist), allInvs(flist){}

	void AddRuleName(string);

	void AddChildDerivNode(DerivNode*);

	void UpdateConstraint(ConstraintsTemplate*);

	const Tuple* GetHeadTuple() const{return head;}

	const ConsList& GetCumuConsts() const{return allConstraints;}

	const FormList& GetInvariants() const{return allInvs;}

	//Obtain all constraints and invariants that should be satisfied
	//to make execution possible
	Obligation GetAllObligs() const;

	const ConstraintsTemplate* GetConstraints() const{return ruleConstraints;}

	const DerivNodeList& GetBodyDerivs() const{return bodyDerivs;}

	void FindSubTuple(const list<PredicateInstance*>&,
					  map<string, list<const Tuple*> >&) const;

	void PrintHead() const;

	void PrintHeadInst(const map<Variable*, int>&) const;

	void PrintCumuCons() const;

	//Just print the current DerivNode
	virtual void PrintDerivNode() const;

	virtual void PrintInstance(const map<Variable*, int>&) const;

	//Print the whole derivation represented by the DerivNode
	void PrintDerivation() const;

	//Print a real execution corresponding to the derivation
	void PrintExecution(map<Variable*, int>) const;

	virtual ~DerivNode();

protected:
	Tuple* head;
	string ruleName;
	ConstraintsTemplate* ruleConstraints;
	DerivNodeList bodyDerivs; //Points body tuples that have derivations
	DerivAnnoList bodyAnnotations; //Points body tuples that have annotations

	ConsList allConstraints; //Cumulative constraints of a derivation
	FormList allInvs; //Cumulative invariants of a derivation
};

class RecurNode: public DerivNode
{
public:
	RecurNode(const Tuple*);

	void AddInvariant(Formula*);

	const Formula* GetInv() const {return invariant;}

	void PrintDerivNode() const;

	void PrintInstance(const map<Variable*, int>&) const;

	~RecurNode();
private:
	//TODO: See if invariant can be merged into Constraints
	Formula* invariant;
};

class DerivInst;
class Derivation;

class Dpool: public RefCountBase
{
public:
	Dpool(const Ptr<DPGraph>, const AnnotMap&);

	void ProcessRuleNode(Tuple*,
		   	   	   	   	 const RuleNode*,
						 const TupleListC&,
						 TupleListC::const_iterator,
						 vector<DerivNodeList::const_iterator>,
						 VarMap vmap);

	void CreateDerivNode(Tuple*,
	 	 	   	   	   	 const RuleNode*,
						 vector<DerivNodeList::const_iterator>&,
						 VarMap& vmap);

	void UpdateDerivNode(string tpName, DerivNode* dnode);

	bool VerifyInvariants(const AnnotMap&) const;

	//TODO: to be tested with z3
	bool VerifyRecurInv(DerivNodeList::const_iterator,
						DerivNodeList::const_iterator,
						vector<const ConstraintsTemplate*>,
						vector<Formula*>&,
						const AnnotMap&,
						string veriTuple,
						const VarMap& vmap,
						const ConstraintsTemplate*) const;

	const DerivNodeList& GetDerivList(string tpName) const;

	//TODO: We assume now that universally quantified tuples
	//and existentially quantified tuples in Property do not
	//have duplicates
	bool CheckProperty(const Property&);

	bool CheckRecurUniv(const Property&,
						const list<PredicateInstance*>&,
						list<PredicateInstance*>::const_iterator,
						DerivNodeList);

	bool CheckExistProp(const Property&, const DerivNodeList&);

	bool CheckRecurExist(const Property&,
						 map<string, list<const Tuple*> >&,
						 map<string, list<const Tuple*> >::const_iterator,
						 const list<const Tuple*>,
						 ConsList&,
						 const FormList&);

	bool CheckWholeProp(const Property&,
						list<const Tuple*>,
			 	 	 	ConsList&,
						const FormList&);

	void PrintDpool() const;

	void PrintDeriv(string) const;

	void PrintAllDeriv() const;

	~Dpool();
private:
	DerivMap derivations;
};

#endif /* SDN_DERIVATION_H_ */
