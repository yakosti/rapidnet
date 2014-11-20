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
#include<sstream>
#include<string>

#include "ns3/ref-count-base.h"
#include "ns3/ptr.h"

#include "sdn-constraint.h"
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
	Node(string);

	virtual void PrintNode(){}

	string GetName(){return name;}

	virtual ~Node(){}

protected:
	string name;
};

class TupleNode: public Node
{
public:
	TupleNode(const ParseFunctor*);

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
	vector<Constraint*>& GetConstraints(){return constraints;}

	void UpdateUnif(const Variable*, const Variable*);

	void UpdateConstraint(const Constraint*);

	void PrintNode();

	~RuleNode();
private:
	TupleNode* head;			//Outbound edge
	vector<TupleNode*> bodies;	//Inbound edges
	vector<const Constraint*> constraints;
};

class DPGraph: public RefCountBase
{
public:
	//Rule format: head :- body1, body2,...bodyn, cstraint1, cstraint2...
	DPGraph(const OlContext*);

	~DPGraph(){}

	void ProcessRule(const OlContext::Rule*);

	void ProcessFunctor(const ParseFunctor*, RuleNode*);

	void ProcessAssign(const ParseAssign*,
					   const map<string, Variable*>&,
					   RuleNode*);

	void ProcessSelect(const ParseSelect*,
					   const map<string, Variable*>&,
					   RuleNode*);

	const Expression* ProcessExpr(const ParseExpr*,
								  const map<string, Variable*>&);

	const Expression* ProcessParseVal(const ParseVal*,
									  const map<string, Variable*>&);

	const Expression* ProcessParseVar(const ParseVar*,
									  const map<string, Variable*>&);

	const Constraint* ProcessParseBool(const ParseBool*,
								 	   const map<string, Variable*>&);

	const Expression* ProcessParseMath(const ParseMath*,
									   const map<string, Variable*>&);

	const TupleNode* FindTupleNode(const ParseFunctor*);

	void PrintGraph();

private:
	vector<RuleNode*> rnodeList;
	vector<TupleNode*> tnodeList;
};

#endif /* SDNCONTEXT_H_ */
