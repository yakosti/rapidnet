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

class DpoolInstNode;
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
//TODO: Change name of ExQuanTuple, because we also use this for base tuples found
typedef map<string, list<TupleLineage> > ExQuanTuple;

typedef pair<const DpoolNode*, DpoolInstNode*> DpoolTupleInst;
typedef map<string, list<DpoolTupleInst> > DpoolTupleMap;


typedef pair<const ConsList&, const FormList&> Obligation;

//Provide instantiation for a derivation
class DpoolInstNode
{
public:
	DpoolInstNode();

	~DpoolInstNode();

public:
	const DpoolNode* dnode;//const: we need to pass "this" to dnode
	VarMap headMap;
	VarMap ruleMap;
	list<DpoolInstNode*> bodyList;
};

class DpoolNode
{
public:
	DpoolNode(string tpName, int argSize);

	DpoolNode(const Tuple*);

	DpoolNode(const PredicateInstance*);

	const Tuple* GetHead() const {return head;}

	virtual void FindSubTuple(const list<PredicateInstance*>& plist,
					  	  	  ExQuanTuple& tlist,
							  const DerivNode* desigHead) const{}

	virtual void FindSubTuple(const list<PredicateInstance*>& plist,
						  	  DpoolTupleMap& tlist,
							  DpoolInstNode*) const{}

	virtual void FindBaseTuple(ExQuanTuple&, const DerivNode*) const{}

	virtual void FindBaseTuple(DpoolInstNode*, DpoolTupleMap&){}

	VarMap CreateHeadInst();

	virtual VarMap CreateBodyInst(list<Variable*>&){return VarMap();}

	//TODO: Don't let the user do the garbage collection
	virtual void CreateDerivInst(VarMap&);

	virtual DpoolInstNode* CreateDerivInst(){}

	virtual DpoolNode* DeepCopy(){return NULL;}

	virtual void CollectConsInst(DpoolInstNode*, ConsList&, FormList&){}

	void PrintHead() const;

	void PrintHeadInst(const map<Variable*, int>&, bool printVar) const;

	void PrintHeadInst(const map<Variable*, int>&, VarMap&, bool printVar) const;

	void PrintSimpHeadInst(const map<Variable*, int>&, VarMap&,
						   SimpConstraints&, bool printVar) const;

	virtual void PrintCumuCons() const{}

	//Just print the current DerivNode
	virtual void PrintDerivNode() const{}

	virtual void PrintInstance(const map<Variable*, int>&, bool) const{}

	virtual void PrintInstance(const map<Variable*, int>&, VarMap&, bool) const{}

	virtual void PrintInstance(const map<Variable*, int>&, DpoolInstNode*, bool) const{}

	virtual void PrintSimpInstance(const map<Variable*, int>&, DpoolInstNode*,
							   	   SimpConstraints&, bool) const{}

	//Print the whole derivation represented by the DerivNode
	virtual void PrintDerivation() const{}

	virtual void PrintDerivInst(DpoolInstNode*){}

	virtual void PrintSimpDerivInst(DpoolInstNode*, SimpConstraints&){}

	//Print a real execution corresponding to the derivation
	virtual void PrintExecution(map<Variable*, int>&, bool printVar) const{}

	virtual void PrintExecInst(map<Variable*, int>&, VarMap&, bool) const{}

	virtual void PrintExecInst(map<Variable*, int>&, DpoolInstNode*, bool) const{}

	virtual void PrintSimpExecInst(map<Variable*, int>&, DpoolInstNode*,
								   SimpConstraints&, bool) const{}

	virtual ~DpoolNode(){}

protected:
	Tuple* head;
	list<Variable*> freeVars;
};

//DerivNode points to a derivation of a body tuple
class DerivNode: public DpoolNode
{
	//TODO: Free variables could exist in ruleConstraints
	//They need deallocation

public:
	DerivNode(const Tuple* tn, string rn,
			  ConstraintsTemplate* consTemp,DpoolNodeList& dlist):
				  DpoolNode(tn), ruleName(rn),ruleConstraints(consTemp),
				  bodyDerivs(dlist){}

	void AddRuleName(string);

	void AddChildDerivNode(DerivNode*);

	void UpdateConstraint(ConstraintsTemplate*);

	void UpdateCumuCons(ConsList&);

	void ReplaceVar(VarMap& vmap);

	//Obtain all constraints and invariants that should be satisfied
	//to make execution possible
	Obligation GetAllObligs() const;

	const ConstraintsTemplate* GetConstraints() const{return ruleConstraints;}

	const DpoolNodeList& GetBodyDerivs() const{return bodyDerivs;}

	void FindSubTuple(const list<PredicateInstance*>&,
					  ExQuanTuple&,
					  const DerivNode*) const;

	void FindSubTuple(const list<PredicateInstance*>&,
					  DpoolTupleMap&,
					  DpoolInstNode*) const;

	void FindBaseTuple(ExQuanTuple&,
					   const DerivNode*) const;

	void FindBaseTuple(DpoolInstNode*, DpoolTupleMap&);

	VarMap CreateBodyInst(list<Variable*>&);

	void CreateDerivInst(VarMap&);

	DpoolInstNode* CreateDerivInst();

	DpoolNode* DeepCopy();

	void CollectConsInst(DpoolInstNode*, ConsList&, FormList&);

	void PrintHead() const;

	void PrintCumuCons() const;

	//Just print the current DerivNode
	void PrintDerivNode() const;

	void PrintInstance(const map<Variable*, int>&, bool) const;

	void PrintInstance(const map<Variable*, int>&, VarMap&, bool) const;

	void PrintInstance(const map<Variable*, int>&, DpoolInstNode*, bool) const;

	void PrintSimpInstance(const map<Variable*, int>&, DpoolInstNode*,
						   SimpConstraints&, bool) const;

	//Print the whole derivation represented by the DerivNode
	void PrintDerivation() const;

	void PrintDerivInst(DpoolInstNode*);

	//Print the instantiation of a derivation in a simplified form
	void PrintSimpDerivInst(DpoolInstNode*, SimpConstraints&);

	//Print a real execution corresponding to the derivation
	void PrintExecution(map<Variable*, int>&, bool printVar) const;

	//From derivation to instances to execution traces
	void PrintExecInst(map<Variable*, int>&, VarMap&, bool) const;

	void PrintExecInst(map<Variable*, int>&, DpoolInstNode*, bool) const;

	void PrintSimpExecInst(map<Variable*, int>&, DpoolInstNode*,
						   SimpConstraints&, bool) const;

	virtual ~DerivNode();

protected:
	string ruleName;
	ConstraintsTemplate* ruleConstraints;
	DpoolNodeList bodyDerivs;
};

class BaseNode: public DpoolNode
{
public:
	BaseNode(const PredicateInstance*, const ConstraintsTemplate&);

	BaseNode(const Tuple*);

	BaseNode(string, int);

	void UpdateCons(ConstraintsTemplate*);

	const ConstraintsTemplate* GetCons() const{return cts;}

	void FindSubTuple(const list<PredicateInstance*>&,
					  ExQuanTuple&,
					  const DerivNode*) const;

	void FindSubTuple(const list<PredicateInstance*>&,
						  DpoolTupleMap&,
						  DpoolInstNode*) const;

	void FindBaseTuple(ExQuanTuple&,
						 const DerivNode*) const;

	void FindBaseTuple(DpoolInstNode*, DpoolTupleMap&);

	DpoolNode* DeepCopy();

	DpoolInstNode* CreateDerivInst();

	VarMap CreateBodyInst(list<Variable*>&);

	void CollectConsInst(DpoolInstNode*, ConsList&, FormList&);

	void PrintCumuCons() const;

	void PrintDerivNode() const;

	void PrintDerivInst(DpoolInstNode*);

	void PrintSimpDerivInst(DpoolInstNode*, SimpConstraints&);

	void PrintInstance(const map<Variable*, int>&, bool) const;

	void PrintInstance(const map<Variable*, int>&, VarMap&, bool) const;

	void PrintInstance(const map<Variable*, int>&, DpoolInstNode*, bool) const;

	void PrintSimpInstance(const map<Variable*, int>&, DpoolInstNode*,
							   SimpConstraints&, bool) const;

	void PrintDerivation() const;

	void PrintExecution(map<Variable*, int>&, bool printVar) const;

	void PrintExecInst(map<Variable*, int>&, VarMap&, bool) const;

	void PrintExecInst(map<Variable*, int>&, DpoolInstNode*, bool) const;

	void PrintSimpExecInst(map<Variable*, int>&, DpoolInstNode*,
							   SimpConstraints&, bool) const;

	~BaseNode();
private:
	ConstraintsTemplate* cts;
};

class PropNode: public DpoolNode
{
public:
	PropNode(const PredicateInstance*, Formula*);

	PropNode(const Tuple*);

	void AddInvariant(Formula*);

	Formula* GetInv() {return prop;}

	void FindSubTuple(const list<PredicateInstance*>&,
					  ExQuanTuple&,
					  const DerivNode*) const;

	void FindSubTuple(const list<PredicateInstance*>&,
					  DpoolTupleMap&,
					  DpoolInstNode*) const;

	DpoolNode* DeepCopy();

	DpoolInstNode* CreateDerivInst();

	VarMap CreateBodyInst(list<Variable*>&);

	void CollectConsInst(DpoolInstNode*, ConsList&, FormList&);

	void PrintCumuCons() const;

	void PrintDerivNode() const;

	void PrintDerivInst(DpoolInstNode*);

	void PrintSimpDerivInst(DpoolInstNode*, SimpConstraints&);

	void PrintInstance(const map<Variable*, int>&, bool) const;

	void PrintInstance(const map<Variable*, int>&, VarMap&, bool) const;

	void PrintInstance(const map<Variable*, int>&, DpoolInstNode*, bool) const;

	void PrintSimpInstance(const map<Variable*, int>&, DpoolInstNode*,
								   SimpConstraints&, bool) const;

	void PrintDerivation() const;

	void PrintExecution(map<Variable*, int>&, bool printVar) const;

	void PrintExecInst(map<Variable*, int>&, VarMap&, bool) const;

	void PrintExecInst(map<Variable*, int>&, DpoolInstNode*, bool) const;

	void PrintSimpExecInst(map<Variable*, int>&, DpoolInstNode*,
						   SimpConstraints&, bool) const;

	~PropNode();
private:
	//TODO: Create a new copy for variables in prop.
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

	void VerifyInvariants(const Invariant&, BaseRelProperty&) const;

	const DerivMap& GetDerivation() const{return derivations;}

	const BaseMap& GetBases() const{return baseMap;}

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


void
ConstructBaseObl(BaseRel&,
				 list<DpoolTupleInst>&,
				 FormList&);

void
CheckRecurBase(BaseRel&,
			   list<PredicateInstance*>::iterator,
			   list<DpoolTupleInst>,
			   DpoolTupleMap&,
			   FormList&);


#endif /* SDN_DERIVATION_H_ */
