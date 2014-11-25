/*
 * sdn-formula.h
 *
 *  Created on: Nov 18, 2014
 *      Author: Chen
 */

#ifndef SDN_FORMULA_H_
#define SDN_FORMULA_H_

#include <vector>
#include <string>
#include <iostream>
#include <sstream>

using namespace std;

/*
 * Term
 */
class Term
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

	void PrintVar();

	static int varCount;

private:
	string name;
	TypeCode varType;
};

class UserFunction: public Term
{
private:
	string fName;
	vector<Variable*> args;
};

//See if template can be used here
class Value: public Term
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

class Arithmetic: public Term
{
public:
	enum ArithOp
	{
		PLUS,
		MINUS,
		TIMES,
		DIVIDE
	};

	Arithmetic(ArithOp opt, Term* exprL, Term* exprR):
		op(opt), leftE(exprL), rightE(exprR){}

private:
	ArithOp op;
	Term* leftE;
	Term* rightE;
};

/*
 * Parse tree for formula
 */
class Formula;

class Connective: public Formula
{
public:
	enum ConnType
	{
		IMPLY,
		OR,
		AND
	};
private:
	Formula* leftF;
	Formula* rightF;
};

class Quantifier: public Formula
{
private:
	vector<Variable*> boundVars;
	Formula* quantifiedF;
};

class Forall: public Quantifier{};
class Exist: public Quantifier{};

class Predicate: public Formula
{
private:
	string name;
	vector<Term*> args;
};

class Constraint: public Formula
{
public:
	enum Operator
	{
		EQ,		//Equal to
		NEQ,	//Unequal to
		GT,		//Greater than
		LT,		//Smaller than
	};

	Constraint(Operator opt, Term* exprL, Term* exprR):
		op(opt),leftE(exprL),rightE(exprR){}

	~Constraint();

private:
	Operator op;
	Term* leftE;
	Term* rightE;
};

#endif /* SDN_FORMULA_H_ */
