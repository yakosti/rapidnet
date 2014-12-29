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

typedef vector<TupleNode*> TupleVec;
typedef vector<RuleNode*> RuleVec;
typedef map<RuleNode*, TupleVec> RBMap;//Mapping from the rule node to bodies
typedef map<RuleNode*, TupleNode*> RHMap;//Mapping from the rule node to the head

class DPGraph: public RefCountBase
{
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
	TupleVec tupleNodes;
	RuleVec ruleNodes;
	RHMap outEdgeRL;	//Edges from a rule node to its head tuple
	RBMap inEdgesRL;	//Edges from a rule node to its body tuples
};

#endif /* SDNCONTEXT_H_ */
