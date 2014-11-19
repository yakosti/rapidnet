/*
 * sdn-constraint.h
 *
 *  Created on: Nov 7, 2014
 *      Author: cchen
 */

#ifndef SDN_CONSTRAINT_H_
#define SDN_CONSTRAINT_H_

#include <string>
#include <vector>
#include "parser-util.h"

using namespace std;

/*
 * Components of constraint pool
 */

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
	enum TypeCode
	{
		STRING,
		INT,
		DOUBLE
	};

	Variable(TypeCode);

	static int varCount;

private:
	string name;
	TypeCode varType;
};

int Variable::varCount = 0;

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
	//IntVal(ValInt32*);
	IntVal(int v):value(v){}

private:
	int value;
};

class DoubleVal: public Value
{
public:
	//DoubleVal(ValDouble*);

	DoubleVal(double v):value(v){}

private:
	double value;
};

class Arithmetic: public Expression
{
public:
	enum ArithOp
	{
		PLUS,
		MINUS,
		TIMES,
		DIVIDE
	};

	Arithmetic(ArithOp opt, Expression* exprL, Expression* exprR):
		op(opt), leftE(exprL), rightE(exprR){}

private:
	ArithOp op;
	Expression* leftE;
	Expression* rightE;
};

class Constraint
{
public:
	enum Operator
	{
		EQ,		//Equal to
		NEQ,	//Unequal to
		GT,		//Greater than
		LT,		//Smaller than
	};

	Constraint(Operator opt, Expression* exprL, Expression* exprR):
		op(opt),leftE(exprL),rightE(exprR){}

	~Constraint();

private:
	Operator op;
	Expression* leftE;
	Expression* rightE;
};

/*Execution tree*/
class Derivation;

typedef vector<Constraint*> ConstraintList;
//typedef pair<Derivation, ConstraintList> ConstraintPair;
//typedef vector<ConstraintPair> ConstraintPairList;
//typedef map<TupleInst, ConstraintPairList> ConstraintPool;

class Cpool
{
private:
	//ConstraintPool pool;
	ConstraintList pool;
};

#endif /* SDN_CONSTRAINT_H_ */
