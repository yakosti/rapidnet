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
	//Variable(TypeCode);

	enum TypeCode
		  {
		      STRING,
		      INT,
		      DOUBLE,
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
	Arithmetic(Expression* exprL, Expression* exprR):
		leftE(exprL), rightE(exprR){}

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



class Constraint
{
public:
	Constraint(Operator opt, Expression* exprL, Expression* exprR):
		Op(opt),leftE(exprL),rightE(exprR){}

	~Constraint();

	enum Operator
		{
			EQ,		//Equal to
			UEQ,	//Unequal to
			GT,		//Greater than
			ST,		//Smaller than
		};


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
