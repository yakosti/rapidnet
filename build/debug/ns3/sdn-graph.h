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
 * Class tuple represents the schema of tuples in NDLog program
 */
class Tuple
{
public:
	Tuple(ParseFunctor*);

	Tuple(string, list<Variable::TypeCode>);

	Tuple(string name, vector<Variable*> vargs):
		tpName(name),args(vargs){}

	VarMap CreateVarMap(const Tuple*) const;

	int GetArgLength() const {return args.size();}

	//TODO: Can GetArgs function be removed?
	const vector<Variable*>& GetArgs() const {return args;}

	list<Variable::TypeCode> GetSchema() const;

	string GetName() const {return tpName;}

	void PrintTuple() const;

	~Tuple();

private:
	string tpName;
	vector<Variable*> args;
};

/*
 * Class ConstraintsTemplate represents the schema of constraints in NDLog program
 */
class ConstraintsTemplate
{
public:
	ConstraintsTemplate();

	ConstraintsTemplate(const ConstraintsTemplate&);

	void AddConstraint(Constraint*);

	void ReplaceVar(VarMap&);

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

	const ConstraintsTemplate* GetConsTemp() const {return cTemp;}

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

	TupleNode(string, vector<Variable*>);

	int GetArgLength() const {return tuple->GetArgLength();}

	const Tuple* GetTuple() const {return tuple;}

	const vector<Variable*>& GetArgs() const {return tuple->GetArgs();}

	list<Variable::TypeCode> GetSchema() const;

	string GetName() const {return tuple->GetName();}

	void PrintName() const;

	void PrintNode() const;

	~TupleNode();

private:
	Tuple* tuple;
};

/*
 * MetaNode: a logical node that wraps TupleNodes of the same predicate
 */
class MetaNode: public Node
{
public:
	MetaNode(string);

	list<Variable::TypeCode> GetSchema() const;

	string GetName() const {return predName;}

	void AddHeadTuple(TupleNode*);

	void AddBodyTuple(TupleNode*);

	void PrintNode() const;

public:
	string predName;	//Name of the predicate
	list<TupleNode*> headTuples;
	list<TupleNode*> bodyTuples;
};

typedef list<TupleNode*> TupleList;
typedef list<RuleNode*> RuleList;
typedef list<MetaNode*> MetaList;
typedef list<const TupleNode*> TupleListC;
typedef list<const RuleNode*> RuleListC;
typedef list<const MetaNode*> MetaListC;
typedef map<const RuleNode*, TupleListC> RBMap;//Mapping from the rule node to bodies
typedef map<const RuleNode*, MetaListC> RMBMap;//Mapping from the rule node to bodies
typedef map<const RuleNode*, const TupleNode*> RHMap;//Mapping from the rule node to the head
typedef map<const RuleNode*, const MetaNode*> RMHMap;//Mapping from the rule node to the head
typedef map<const TupleNode*, RuleListC> TRMap;
typedef map<const MetaNode*, RuleListC> MTRMap;

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

	Constraint* ProcessAssign(ParseAssign*,
					   map<string, Variable*>&,
					   RuleNode*);

	Constraint* ProcessSelect(ParseSelect*,
					   map<string, Variable*>&,
					   RuleNode*);

	//In Process* functions, the argument of RuleNode*
	//is added for update of variable unification.
	Term* ProcessExpr(ParseExpr*,
					  map<string, Variable*>&,
					  RuleNode* rnode);

	Value* ProcessParseVal(ParseVal*);

	Variable* ProcessParseVar(ParseVar*,
						  map<string, Variable*>&,
						  RuleNode*);

	UserFunction* ProcessParseFunc(ParseFunction*,
						   map<string, Variable*>&,
						   RuleNode*);

	Constraint* ProcessConstraint(ParseBool*,
								  map<string, Variable*>&,
								  RuleNode*);

	Arithmetic* ProcessParseMath(ParseMath*,
						   map<string, Variable*>&,
						   RuleNode*);

	TupleNode* FindTupleNode(ParseFunctor*);

	void PrintGraph() const;

	~DPGraph();

private:
	TupleList tupleNodes; //TODO: tupleNodes has duplicate tuples
	MetaList metaNodes;	//TODO: Create a class for MetaList
	RuleList ruleNodes;
	RHMap outEdgeRL;	//Edges from a rule node to its head tuple
	RBMap inEdgesRL;	//Edges from a rule node to its body tuples
	RMHMap outEdgeRM;	//Edges from a rule node to its head metanode
	RMBMap inEdgesRM;	//Edges from a rule node to its body metanodes
};

typedef pair<Tuple*, Formula*> Annotation;
typedef map<string, Annotation*> AnnotMap;

class MiniGraph: public RefCountBase
{
public:
	MiniGraph(Ptr<DPGraph>);

	//Topological sorting on the dependency graph
	//in order to obtain an ordered list of rule nodes for processing.
	pair<RuleListC, RuleListC> TopoSort(const AnnotMap&) const;

	MetaListC GetBaseTuples() const;

	void PrintGraph() const;

private:
	RMHMap outEdgeRM;	//Outbound edges of rules to head tuples
	RMBMap inEdgesRM;	//Inbound edges of rules from body tuples
	MTRMap outEdgesMT;	//Outbound edges of body tuples to rules
	MTRMap inEdgesMT;	//Inbound edges of head tuples from rules
};

#endif /* SDNCONTEXT_H_ */
