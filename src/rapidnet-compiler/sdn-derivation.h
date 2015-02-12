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
class RecurNode;

typedef list<const ConstraintsTemplate*> ConsList;
typedef list<const Formula*> FormList;
typedef list<const DerivNode*> DerivNodeList;
typedef map<string, DerivNodeList> DerivMap;
typedef list<const RecurNode*> DerivAnnoList;

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

	const ConstraintsTemplate* GetConstraints() const{return ruleConstraints;}

	void PrintHead() const;

	//Just print the current DerivNode
	virtual void PrintDerivNode() const;

	//Print the whole derivation represented by the DerivNode
	void PrintDerivation() const;

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
						 const TupleListC&,
						 vector<DerivNodeList::const_iterator>&,
						 VarMap& vmap);

	void UpdateDerivNode(string tpName, DerivNode* dnode);

	void PrintDpool() const;

	void PrintDeriv(string) const;

	void PrintAllDeriv() const;

	~Dpool();
private:
	DerivMap derivations;
};

#endif /* SDN_DERIVATION_H_ */
