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

/*
 * Components of Dependency graph
 */
class Node
{
public:
	Node(string nName):name(nName){}

	void PrintName();

	virtual void PrintNode(){}

	string GetName(){return name;}

	virtual ~Node(){}

protected:
	string name;
};

class TupleNode: public Node
{
public:
	TupleNode(ParseFunctor*);

	int GetArgLength(){return args.size();}

	vector<Variable*>& GetArgs(){return args;}

	void PrintNode();

	~TupleNode();

private:
	vector<Variable*> args;
};

class RuleNode: public Node
{
public:
	RuleNode(string rName):Node(rName){}

	const vector<Constraint*>& GetConstraints(){return constraints;}

	void UpdateUnif(Variable*, Variable*);

	void UpdateConstraint(Constraint*);

	void PrintNode();

	~RuleNode();

private:
	vector<Constraint*> constraints;
};

typedef list<TupleNode*> TupleList;
typedef list<RuleNode*> RuleList;
typedef map<RuleNode*, TupleList> RBMap;//Mapping from the rule node to bodies
typedef map<RuleNode*, TupleNode*> RHMap;//Mapping from the rule node to the head
typedef map<TupleNode*, RuleList> TRMap;

class DPGraph: public RefCountBase
{
	friend class MiniGraph;

public:
	//Rule format: head :- body1, body2,...bodyn, cstraint1, cstraint2...
	DPGraph(Ptr<OlContext>);

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

	void PrintGraph();

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
	pair<TupleList, RuleList> TopoSort();

	void PrintGraph();

private:
	RHMap outEdgeRL;
	RBMap inEdgesRL;
	TRMap outEdgesTP;
	TRMap inEdgesTP;
};

#endif /* SDNCONTEXT_H_ */
