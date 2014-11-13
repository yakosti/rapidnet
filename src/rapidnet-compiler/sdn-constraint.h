/*
 * sdn-constraint.h
 *
 *  Created on: Nov 7, 2014
 *      Author: cchen
 */

#ifndef SDN_CONSTRAINT_H_
#define SDN_CONSTRAINT_H_

#include<string>
#include<vector>

#include "parse-util.h"

using namespace std;

namespace ns3{
namespace rapidnet_sdn_veri{

class Formula;

/*
 * Expression
 */
class Expression
{
public:
	virtual ~Expression(){}
};

class Term: public Expression
{
public:
	virtual ~Term(){}
};

class Variable: public Term
{
public:
	Variable(ParseExpr*);

	enum TypeCode
		  {
		      STRING,
		      INT,
		      DOUBLE,
		  };

private:
	string name;
	TypeCode varType;
	static int varCount;
};

class UserFunction: public Term
{
private:
	string fName;
	vector<Variable*> args;
};

//See if template can be used here
class Value: public Expression
{
public:
	virtual ~Value(){}
};

class IntVal: public Value
{
public:
	IntVal(ValInt32*);

private:
	int value;
};

class DoubleVal: public Value
{
public:
	DoubleVal(ValDouble*);

private:
	double value;
};

class Arithmetic: public Expression
{
public:
	enum ArithType
	{
		PLUS,
		MINUS,
		TIME,
		DIVIDE
	};
private:
	Expression* leftE;
	Expression* rightE;
};

class Constraint: public Formula
{
public:
	Constraint(Operator, Expression*, Expression*);

	~Constraint();

	enum Operator
	{
		EQUAL,
		GREATERTHAN,
		SMALLERTHAN,
		UNEQUAL
	};
private:
	Operator op;
	Expression* leftE;
	Expression* rightE;
};

/*
 * Components of Constraint pool
 */
//class Rule;						//struct Rule in ol-context.h
//
//class TupleInst: public RefCountBase
//{
//public:
//	TupleInst(const TupleNode*);
//private:
//	string name;
//	vector<Variable*> args;
//};
//
//class RuleInst: public RefCountBase
//{
//public:
//	RuleInst(const RuleNode, const vector<TupleInst*>&);
//private:
//	string ruleID;
//	TupleInst* head;
//	TupleInst* event;
//	vector<TupleInst*> bodies;
//	vector<Constraint*> constraints;
//	vector<RuleInst*> inboundRules;
//	//Vector of rules that derive bodies
//};

/*Execution tree*/
class Derivation: public RefCountBase{};

typedef vector<constraint> ConstraintList;
typedef pair<Derivation, ConstraintList> ConstraintPair;
typedef vector<ConstraintPair> ConstraintPairList;
typedef map<TupleInst, ConstraintPairList> ConstraintPool;

class Cpool: public RefCountBase
{
private:
	 ConstraintPool pool;
};
}	// namespace ns3
}	// namespace rapidnet_sdn_veri

#endif /* SDN_CONSTRAINT_H_ */
