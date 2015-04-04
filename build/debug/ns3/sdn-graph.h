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
#include "sdn-property.h"
#include "ol-context.h"
#include "parser-util.h"

using namespace std;
using namespace ns3;
using namespace rapidnet_compiler;

class CircleNode;

/*
 * Class tuple represents the schema of tuples in NDLog program
 */
class Tuple
{
public:
	Tuple(string, int);

	Tuple(ParseFunctor*);

	Tuple(string, list<Variable::TypeCode>);

	Tuple(string name, vector<Variable*> vargs):
		tpName(name),args(vargs){}

	//Self mapped to argument tuple
	VarMap CreateVarMap(const Tuple*) const;


	//Predicate mapped to self
	VarMap CreateVarMap(const PredicateInstance*) const;

	int GetArgLength() const {return args.size();}

	//TODO: Can GetArgs function be removed?
	//TODO: Variable* in the vector is still changeble
	const vector<Variable*>& GetArgs() const {return args;}

	list<Variable::TypeCode> GetSchema() const;

	string GetName() const {return tpName;}

	void PrintTuple() const;

	void PrintTupleInst(VarMap&) const;

	void PrintSimpTupleInst(VarMap&, SimpConstraints&) const;

	void PrintInstance(const map<Variable*, int>&, bool printVar);

	void PrintInstance(const map<Variable*, int>&, VarMap&, bool printVar) const;

	void PrintSimpInstance(const map<Variable*, int>&, VarMap&,
							SimpConstraints&, bool printVar) const;

	~Tuple();

private:
	string tpName;
	vector<Variable*> args;
};



/*
 * Components of Dependency graph
 */
class Node
{
public:
	virtual string GetName() const =0;

	virtual const Tuple* GetTuple() const {return NULL;}

	virtual int GetArgLength() const{return 0;}

	virtual void PrintNode() const =0;

	virtual ~Node(){}
};

class RuleNode: public Node
{
public:
	RuleNode(string rName);

	const ConstraintList& GetConstraints() const {return cTemp->GetConstraints();}

	ConstraintsTemplate* GetConsTemp() {return cTemp;}

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

	int GetArgLength() const;

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

class CircleNode: public Node
{
public:
	CircleNode(const Tuple*, const AnnotMap&);

	string GetName() const {return tuple->GetName();}

	const Tuple* GetTuple() const {return tuple;}

	int GetArgLength() const;

	virtual void PrintNode() const;

	~CircleNode();
private:
	Tuple* tuple;
	//TODO: Add formula* to class Node
	Formula* anntProp;
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

class NewMetaNode: public Node
{
public:
	NewMetaNode(string);

	NewMetaNode(MetaNode*&);

	string GetName() const {return predName;}

	int GetArgLength() const;

	bool IsCircleNode();

	void AddHeadTuple(Node*);

	void AddBodyTuple(Node*);

	void PrintNode() const;

public:
	string predName;
	list<Node*> headTuples;
	list<Node*> bodyTuples;	//Allow CircleNode
};

//TODO: Convert TupleListC back to const
typedef list<TupleNode*> TupleList;
typedef list<RuleNode*> RuleList;
typedef list<MetaNode*> MetaList;
typedef list<TupleNode*> TupleListC;
typedef list<RuleNode*> RuleListC;
typedef list<MetaNode*> MetaListC;
typedef map<RuleNode*, TupleListC> RBMap;//Mapping from the rule node to bodies
typedef map<RuleNode*, MetaListC> RMBMap;//Mapping from the rule node to bodies
typedef map<RuleNode*, TupleNode*> RHMap;//Mapping from the rule node to the head
typedef map<RuleNode*, MetaNode*> RMHMap;//Mapping from the rule node to the head
typedef map<TupleNode*, RuleListC> TRMap;
typedef map<MetaNode*, RuleListC> MTRMap;

class DPGraph: public RefCountBase
{
	friend class NewDPGraph;

public:
	//Rule format: head :- body1, body2,...bodyn, cstraint1, cstraint2...
	DPGraph(Ptr<OlContext>);

	const TupleList& GetTupleList() const {return tupleNodes;}

	const TupleListC& GetBodyTuples(RuleNode*) const;

	const TupleNode* GetHeadTuple(RuleNode*) const;

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


//TODO: NewDPGraph will destroy the old DPGraph
class NewDPGraph: public RefCountBase
{
	friend class MiniGraph;

public:
	NewDPGraph(Ptr<DPGraph>, const Invariant&);

	const list<Node*>& GetBodies(RuleNode*) const;

	const Node* GetHeadTuple(RuleNode*) const;

	void Print();

	~NewDPGraph();

private:
	TupleList tupleNodes;
	list<CircleNode*> circleNodes;
	list<NewMetaNode*> metaNodes;
	RuleList ruleNodes;
	map<RuleNode*, Node*> outEdgeRL;
	map<RuleNode*, list<Node*> > inEdgesRL;
	map<RuleNode*, NewMetaNode*> outEdgeRM;
	map<RuleNode*, list<NewMetaNode*> > inEdgesRM;
};

class MiniGraph: public RefCountBase
{
public:
	MiniGraph(Ptr<NewDPGraph>, const Invariant&);

	//Topological sorting on the dependency graph
	//in order to obtain an ordered list of rule nodes for processing.
	RuleListC TopoSort(const Invariant&) const;

	list<NewMetaNode*> GetBaseTuples() const;

	void PrintGraph() const;

private:
	map<RuleNode*, NewMetaNode*> outEdgeRM;	//Outbound edges of rules to head tuples
	map<RuleNode*, list<NewMetaNode*> > inEdgesRM;	//Inbound edges of rules from body tuples
	map<NewMetaNode*, RuleListC> outEdgesMT;	//Outbound edges of body tuples to rules
	map<NewMetaNode*, RuleListC> inEdgesMT;	//Inbound edges of head tuples from rules
};

#endif /* SDNCONTEXT_H_ */
