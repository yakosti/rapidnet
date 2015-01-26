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
//#include "parser-util.h"

using namespace std;

class DerivNode;
class DerivBody;

typedef list<DerivNode*> DerivNodeList;
typedef map<const TupleNode*, DerivNodeList> DerivMap;
typedef list<DerivBody*> DerivBodyList;

/*
 * Components of derivation pool
 */
class CpoolEntryInst
{
public:
	void AddConstraint(Constraint*);

	void PrintInst() const;

	~CpoolEntryInst();
private:
	ConstraintList instList;
};

class CpoolEntry
{
public:
	CpoolEntry(const CpoolEntry&);		//Shallow copy

	CpoolEntry(const ConstraintList& cl, const VarMap& vm):
		clist(cl),vmap(vm){}

	CpoolEntryInst* GetConstraints() const;

	void PrintEntry();

private:
	ConstraintList clist;
	VarMap vmap;
};

class Cpool
{
public:
	Cpool();

	Cpool(const Cpool&);	//Shallow copy

	void AddConstraint(const CpoolEntry&);

	void Append(const Cpool&);

	void PrintCpool();

private:
	list<CpoolEntry> constraints;
};

/*A node in the derivation tree*/
class DerivNode
{
public:
	DerivNode(const TupleNode*);

	DerivNode(const TupleNode* tn, const RuleNode* rn,
			  const DerivBodyList& dl, const Cpool& cp):
		head(tn),rl(rn),bodyDerivs(dl),bodyCons(cp){}

	const TupleNode* GetHeadNode() const{return head;}

	const RuleNode* GetRuleNode() const{return rl;}

	const DerivBodyList& GetDerivBodies() const{return bodyDerivs;}

	const Cpool& GetConstraints() const{return bodyCons;}

	void PrintHeadName();

	void PrintDerivNode();

	~DerivNode();
private:
	const TupleNode* head;
	const RuleNode* rl;
	DerivBodyList bodyDerivs;
	Cpool bodyCons;
};

/*An edge and unification in the derivation tree*/
class DerivBody
{
public:
	DerivBody(DerivNode* nt, ConstraintList& unif, VarMap& uf):
		next(nt),unifications(unif),unifLabel(uf){}

	const ConstraintList& GetUnif() const{return unifications;}

	const DerivNode* GetChild() const {return next;}

	const VarMap& GetMap() const {return unifLabel;}

	void PrintDerivBody();

	~DerivBody();
private:
	DerivNode* next;
	ConstraintList unifications;
	VarMap unifLabel;	//Unification to create constraint instances
};

class DerivInst;
class Derivation;

class Dpool: public RefCountBase
{
public:
	//Dpool(Ptr<DPGraph>, const Annotation&);

	void ProcessRuleNode(const TupleNode*,
		   	   	   	   	 const RuleNode*,
						 const TupleListC&,
						 TupleListC::const_iterator,
						 vector<DerivNodeList::const_iterator>);

	void CreateDerivNode(const TupleNode*,
	 	 	   	   	   	 const RuleNode*,
						 const TupleListC&,
						 vector<DerivNodeList::const_iterator>&);

	void UpdateDerivNode(const TupleNode*, DerivNode*);

	Derivation* GetDerivation(const DerivNode*);

	const DerivNodeList& GetDerivNodes(const TupleNode*);

	void GetDerivInst(Derivation*, const DerivNode*, const VarMap&);

	void PrintDpool() const;

	void PrintDerivs();

	~Dpool();
private:
	DerivMap derivations;
};

/*
 * Real instances of a derivation
 */

/*A real instance of a tuple*/
class DerivTuple
{
public:
	DerivTuple(const TupleNode*, const VarMap&);

	void PrintTuple() const;

private:
	string name;
	vector<Variable*> args;
};

/*An instance of DerivInst represents a real rule application*/
class DerivInst
{
public:
	DerivInst(const DerivNode*, const VarMap&);

	void PrintInst() const;

	~DerivInst();

private:
	string ruleName;
	DerivTuple* head;
	list<DerivTuple*> bodies;
	CpoolEntryInst* constraints;
};

/*A real derivation of a tuple*/
class Derivation
{
public:
	Derivation();

	void AddDerivInst(DerivInst*);

	void PrintDeriv() const;

	~Derivation();
private:
	list<DerivInst*> deriv;
};

#endif /* SDN_DERIVATION_H_ */
