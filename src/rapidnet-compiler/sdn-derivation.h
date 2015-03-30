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
#include "sdn-parse-smtlib.h"

using namespace std;

class Dpool;
class DerivNode;
class DpoolNode;
class BaseNode;
class PropNode;

typedef list<DerivNode*> DerivNodeList;
typedef list<BaseNode*> BaseNodeList;
typedef list<PropNode*> PropNodeList;
typedef list<DpoolNode*> DpoolNodeList;
typedef map<string, DerivNodeList> DerivMap;
typedef map<string, BaseNodeList> BaseMap;
typedef map<string, PropNodeList> PropMap;

typedef pair<const Tuple*, const DerivNode*> TupleLineage;
typedef map<string, list<TupleLineage> > ExQuanTuple;


typedef pair<const ConsList&, const FormList&> Obligation;

class DpoolNode
{
public:
	DpoolNode(string tpName, int argSize);

	DpoolNode(const Tuple*);

	DpoolNode(const PredicateInstance*);

	const Tuple* GetHead() const {return head;}

	void FindSubTuple(const list<PredicateInstance*>& plist,
					  ExQuanTuple& tlist,
					  const DerivNode* desigHead) const{}

	//TODO: Don't let the user do the garbage collection
	virtual void CreateDerivInst(VarMap&);

	void PrintHead() const;

	void PrintHeadInst(const map<Variable*, int>&) const;

	void PrintHeadInst(const map<Variable*, int>&, VarMap&) const;

	virtual void PrintCumuCons() const{}

	//Just print the current DerivNode
	virtual void PrintDerivNode() const{}

	virtual void PrintInstance(const map<Variable*, int>&) const{}

	virtual void PrintInstance(const map<Variable*, int>&, VarMap&) const{}

	//Print the whole derivation represented by the DerivNode
	virtual void PrintDerivation() const{}

	//Print a real execution corresponding to the derivation
	virtual void PrintExecution(map<Variable*, int>&) const{}

	virtual void PrintExecInst(map<Variable*, int>&, VarMap&) const{}

	virtual ~DpoolNode(){}

protected:
	Tuple* head;
};

//DerivNode points to a derivation of a body tuple
class DerivNode: public DpoolNode
{
public:
	DerivNode(const Tuple* tn, string rn, ConstraintsTemplate* consTemp,
			  DpoolNodeList& dlist, ConsList& clist, FormList& flist):
				  DpoolNode(tn), ruleName(rn),ruleConstraints(consTemp),
				  bodyDerivs(dlist), allConstraints(clist), allInvs(flist){}

	void AddRuleName(string);

	void AddChildDerivNode(DerivNode*);

	void UpdateConstraint(ConstraintsTemplate*);

	void UpdateCumuCons(ConsList&);

	void ReplaceVar(VarMap& vmap);

	const ConsList& GetCumuConsts() const{return allConstraints;}

	FormList& GetInvariants() {return allInvs;}

	//Obtain all constraints and invariants that should be satisfied
	//to make execution possible
	Obligation GetAllObligs() const;

	const ConstraintsTemplate* GetConstraints() const{return ruleConstraints;}

	const DpoolNodeList& GetBodyDerivs() const{return bodyDerivs;}

	void FindSubTuple(const list<PredicateInstance*>&,
					  ExQuanTuple&,
					  const DerivNode*) const;

	void CreateDerivInst(VarMap&);

	void PrintHead() const;

	void PrintCumuCons() const;

	//Just print the current DerivNode
	void PrintDerivNode() const;

	void PrintInstance(const map<Variable*, int>&) const;

	void PrintInstance(const map<Variable*, int>&, VarMap&) const;

	//Print the whole derivation represented by the DerivNode
	void PrintDerivation() const;

	//Print a real execution corresponding to the derivation
	void PrintExecution(map<Variable*, int>&) const;

	//From derivation to instances to execution traces
	void PrintExecInst(map<Variable*, int>&, VarMap&) const;

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

	void FindSubTuple(const list<PredicateInstance*>&,
					  ExQuanTuple&,
					  const DerivNode*) const;

	void PrintCumuCons() const;

	void PrintDerivNode() const;

	void PrintInstance(const map<Variable*, int>&) const;

	void PrintInstance(const map<Variable*, int>&, VarMap&) const;

	void PrintDerivation() const;

	void PrintExecution(map<Variable*, int>&) const;

	void PrintExecInst(map<Variable*, int>&, VarMap&) const;

	~BaseNode();
private:
	ConstraintsTemplate* cts;
};

class PropNode: public DpoolNode
{
public:
	PropNode(const PredicateInstance*, Formula*);

	void AddInvariant(Formula*);

	Formula* GetInv() {return prop;}

	void FindSubTuple(const list<PredicateInstance*>&,
					  ExQuanTuple&,
					  const DerivNode*) const;

	void PrintCumuCons() const;

	void PrintDerivNode() const;

	void PrintInstance(const map<Variable*, int>&) const;

	void PrintInstance(const map<Variable*, int>&, VarMap&) const;

	void PrintDerivation() const;

	void PrintExecution(map<Variable*, int>&) const;

	void PrintExecInst(map<Variable*, int>&, VarMap&) const;

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

	void ProcessRuleNode(const Tuple*,
		   	   	   	   	 RuleNode*,
						 const list<Node*>&,
						 list<Node*>::const_iterator,
						 vector<DpoolNode*>,
						 VarMap vmap);

	void CreateDerivNode(const Tuple*,
	 	 	   	   	   	 RuleNode*,
						 vector<DpoolNode*>&,
						 VarMap& vmap);

	void UpdateDerivNode(string tpName, DerivNode* dnode);

	void VerifyInvariants(const Invariant&) const;

	const DerivMap& GetDerivation() const{return derivations;}

	const DerivNodeList& GetDerivList(string tpName) const;

	void CreateDerivInst(const DpoolNode&, VarMap&);

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
