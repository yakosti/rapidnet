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

class Dpool;
class DerivNode;
class DpoolNode;
class BaseNode;
class PropNode;

typedef list<const ConstraintsTemplate*> ConsList;
typedef list<const Formula*> FormList;
typedef list<DerivNode*> DerivNodeList;
typedef list<BaseNode*> BaseNodeList;
typedef list<PropNode*> PropNodeList;
typedef list<DpoolNode*> DpoolNodeList;
typedef map<string, DerivNodeList> DerivMap;
typedef map<string, BaseNodeList> BaseMap;
typedef map<string, PropNodeList> PropMap;

typedef pair<const ConsList&, const FormList&> Obligation;

class DpoolNode
{
public:
	DpoolNode(string tpName, int argSize);

	DpoolNode(const Tuple*);

	DpoolNode(const PredicateInstance*);

	const Tuple* GetHead() const {return head;}

	void PrintHead() const;

	void PrintHeadInst(const map<Variable*, int>&) const;

	virtual void PrintCumuCons() const{}

	//Just print the current DerivNode
	virtual void PrintDerivNode() const{}

	virtual void PrintInstance(const map<Variable*, int>&) const{}

	//Print the whole derivation represented by the DerivNode
	virtual void PrintDerivation() const{}

	//Print a real execution corresponding to the derivation
	virtual void PrintExecution(map<Variable*, int>&) const{}

	virtual ~DpoolNode(){}

protected:
	Tuple* head;
};

//DerivNode points to a derivation of a body tuple
class DerivNode: public DpoolNode
{
public:
	DerivNode(Tuple* tn, string rn, ConstraintsTemplate* consTemp,
			  DpoolNodeList& dlist, ConsList& clist, FormList& flist):
				  DpoolNode(tn), ruleName(rn),ruleConstraints(consTemp),
				  bodyDerivs(dlist), allConstraints(clist), allInvs(flist){}

	void AddRuleName(string);

	void AddChildDerivNode(DerivNode*);

	void UpdateConstraint(ConstraintsTemplate*);

	void UpdateCumuCons(ConsList&);

	const ConsList& GetCumuConsts() const{return allConstraints;}

	const FormList& GetInvariants() const{return allInvs;}

	//Obtain all constraints and invariants that should be satisfied
	//to make execution possible
	Obligation GetAllObligs() const;

	const ConstraintsTemplate* GetConstraints() const{return ruleConstraints;}

	const DpoolNodeList& GetBodyDerivs() const{return bodyDerivs;}

//	void FindSubTuple(const list<PredicateInstance*>&,
//					  map<string, list<const Tuple*> >&) const;

	void PrintHead() const;

	void PrintHeadInst(const map<Variable*, int>&) const;

	void PrintCumuCons() const;

	//Just print the current DerivNode
	void PrintDerivNode() const;

	void PrintInstance(const map<Variable*, int>&) const;

	//Print the whole derivation represented by the DerivNode
	void PrintDerivation() const;

	//Print a real execution corresponding to the derivation
	void PrintExecution(map<Variable*, int>&) const;

	virtual ~DerivNode();

protected:
	string ruleName;
	ConstraintsTemplate* ruleConstraints;
	DpoolNodeList bodyDerivs;

	ConsList allConstraints; //Cumulative constraints of a derivation
	FormList allInvs; //Cumulative invariants of a derivation
};

class BaseNode: public DpoolNode
{
public:
	BaseNode(const PredicateInstance*, const ConstraintsTemplate&);

	BaseNode(const Tuple*);

	BaseNode(string, int);

	const ConstraintsTemplate* GetCons() const{return cts;}

	void PrintCumuCons() const;

	void PrintDerivNode() const;

	void PrintInstance(const map<Variable*, int>&) const;

	void PrintDerivation() const;

	void PrintExecution(map<Variable*, int>&) const;

	~BaseNode();
private:
	ConstraintsTemplate* cts;
};

class PropNode: public DpoolNode
{
public:
	PropNode(const PredicateInstance*, Formula*);

	void AddInvariant(Formula*);

	const Formula* GetInv() const {return prop;}

	void PrintCumuCons() const;

	void PrintDerivNode() const;

	void PrintInstance(const map<Variable*, int>&) const;

	void PrintDerivation() const;

	void PrintExecution(map<Variable*, int>&) const;

	~PropNode();
private:
	Formula* prop;
};

class DerivInst;
class Derivation;

class Dpool: public RefCountBase
{
public:
	Dpool(const Ptr<NewDPGraph>, const Ptr<MiniGraph>,
		  const BaseProperty&, const Invariant&);

	void ProcessRuleNode(Tuple*,
		   	   	   	   	 RuleNode*,
						 const list<Node*>&,
						 list<Node*>::const_iterator,
						 vector<DpoolNode*>,
						 VarMap vmap);

	void CreateDerivNode(Tuple*,
	 	 	   	   	   	 RuleNode*,
						 vector<DpoolNode*>&,
						 VarMap& vmap);

	void UpdateDerivNode(string tpName, DerivNode* dnode);

	bool VerifyInvariants(const Invariant&) const;

	//TODO: to be tested with z3
	bool VerifyRecurInv(DerivNodeList::const_iterator,
						DerivNodeList::const_iterator,
						vector<const ConstraintsTemplate*>,
						vector<Formula*>&,
						const AnnotMap&,
						string veriTuple,
						const VarMap& vmap,
						const ConstraintsTemplate*) const;

	const DerivMap& GetDerivation() const{return derivations;}

	const DerivNodeList& GetDerivList(string tpName) const;

	void PrintDpool() const;

	void PrintDeriv(string) const;

	void PrintAllDeriv() const;

	~Dpool();
private:
	DerivMap derivations;
	BaseMap baseMap;
	PropMap recurMap;
};

#endif /* SDN_DERIVATION_H_ */
