 /*
 * sdn-context.h
 *
 *  Created on: Oct 20, 2014
 *      Author: chen
 */

#ifndef SDNCONTEXT_H_
#define SDNCONTEXT_H_

#include<vector>
#include<map>
#include<list>
#include<sstream>
#include<string>

#include "ns3/ref-count-base.h"
#include "ns3/ptr.h"

#include "sdn-formula.h"
#include "ol-context.h"
#include "parser-util.h"

using namespace std;
using namespace ns3;
using namespace rapidnet_compiler;

typedef list<Constraint*> ConstraintList;

/*
 * Class relation represents the schema of tuples in NDLog program
 */
class Relation
{
public:
	Relation(ParseFunctor*);

	int GetArgLength() const {return args.size();}

	//TODO: Can GetArgs function be removed?
	const vector<Variable*>& GetArgs() const {return args;}

	string GetName() const {return relName;}

	void PrintRelation() const;

	~Relation();

private:
	string relName;
	vector<Variable*> args;
};

/*
 * Class ConstraintsTemplate represents the schema of constraints in NDLog program
 */
class ConstraintsTemplate
{
public:
	void AddConstraint(Constraint*);

	const ConstraintList& GetConstraints() const {return constraints;}

	void PrintTemplate() const;

	~ConstraintsTemplate();

private:
	ConstraintList constraints;
};

/*
 * Components of Dependency graph
 */
class Node
{
public:
	virtual void PrintNode() const =0;

	virtual ~Node(){}
};

class RuleNode: public Node
{
public:
	RuleNode(string rName);

	const ConstraintList& GetConstraints() const {return cTemp->GetConstraints();}

	void UpdateUnif(Variable*, Variable*);

	void UpdateConstraint(Constraint*);

	string GetName() const {return ruleName;}

	void PrintName() const;

	void PrintNode() const;

	~RuleNode();

private:
	string ruleName;
	ConstraintsTemplate* cTemp;
};

class TupleNode: public Node
{
public:
	TupleNode(ParseFunctor*);

	int GetArgLength() const {return rel->GetArgLength();}

	const vector<Variable*>& GetArgs() const {return rel->GetArgs();}

	void Instantiate(VarMap&) const;

	string GetName() const {return rel->GetName();}

	void PrintName() const;

	void PrintNode() const;

	~TupleNode();

private:
	Relation* rel;
};

typedef list<TupleNode*> TupleList;
typedef list<RuleNode*> RuleList;
typedef list<const TupleNode*> TupleListC;
typedef list<const RuleNode*> RuleListC;
typedef map<const RuleNode*, TupleListC> RBMap;//Mapping from the rule node to bodies
typedef map<const RuleNode*, const TupleNode*> RHMap;//Mapping from the rule node to the head
typedef map<const TupleNode*, RuleListC> TRMap;

class DPGraph: public RefCountBase
{
	friend class MiniGraph;

public:
	//Rule format: head :- body1, body2,...bodyn, cstraint1, cstraint2...
	DPGraph(Ptr<OlContext>);

	const TupleList& GetTupleList() const {return tupleNodes;}

	const TupleListC& GetBodyTuples(const RuleNode*) const;

	const TupleNode* GetHeadTuple(const RuleNode*) const;

	void ProcessRule(OlContext::Rule*);

	TupleNode* ProcessFunctor(ParseFunctor*,
							  map<string, Variable*>&,
							  RuleNode*);

	void ProcessAssign(ParseAssign*,
					   map<string, Variable*>&,
					   RuleNode*);

	void ProcessSelect(ParseSelect*,
					   map<string, Variable*>&,
					   RuleNode*);

	Term* ProcessExpr(ParseExpr*,
					  map<string, Variable*>&);

	Term* ProcessParseVal(ParseVal*);

	Term* ProcessParseVar(ParseVar*,
						  map<string, Variable*>&);

	Term* ProcessParseFunc(ParseFunction*,
						   map<string, Variable*>&);

	Constraint* ProcessConstraint(ParseBool*,
								  map<string, Variable*>&);

	Term* ProcessParseMath(ParseMath*,
						   map<string, Variable*>&);

	TupleNode* FindTupleNode(ParseFunctor*);

	void PrintGraph() const;

	~DPGraph();

private:
	TupleList tupleNodes;
	RuleList ruleNodes;
	RHMap outEdgeRL;	//Edges from a rule node to its head tuple
	RBMap inEdgesRL;	//Edges from a rule node to its body tuples
};

class MiniGraph: public RefCountBase
{
public:
	MiniGraph(Ptr<DPGraph>);

	//Topological sort on the dependency graph
	pair<TupleListC, RuleListC> TopoSort();

	void PrintGraph() const;

private:
	RHMap outEdgeRL;
	RBMap inEdgesRL;
	TRMap outEdgesTP;
	TRMap inEdgesTP;
};

#endif /* SDNCONTEXT_H_ */
