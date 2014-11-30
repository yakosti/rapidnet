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
 * ******************************************************************************** *
 *                                                                                  *
 *                               Parse tree for Term                                *
 *                                                                                  *
 * ******************************************************************************** *
 */


/*
 * Term
 */
class Term
{
public:
	virtual ~Term(){}

	virtual int GetValue() { //dummy return
		return 0;
	}
};


int varCount = 0;

class Variable: public Term
{
public:
	enum TypeCode
	{
		BOOL,
		INT,
		DOUBLE,
		STRING
	};

	Variable(TypeCode t):varType(t){
		varCount = varCount+1;
		name =  "variable"+std::to_string(varCount);
	}

	virtual ~Variable(){}

	TypeCode GetVariableType() {
		return varType;
	}

	string GetVariableName() {
		return name;
	}

private:
	string name;
	TypeCode varType;
};

class UserFunction: public Term
{
public:
	UserFunction(){}

	virtual ~UserFunction(){}

private:
	string fName;
	vector<Variable*> args;
};

//See if template can be used here
// these are CONSTANTS
class Value: public Term
{
public:
	virtual ~Value(){}
};

class IntVal: public Value
{
public:
	IntVal(int v):value(v){}

	virtual ~IntVal(){}

	int GetIntValue() {
		return value;
	}

private:
	int value;
};

class DoubleVal: public Value
{
public:
	DoubleVal(double v):value(v){}

	~DoubleVal(){}

	double GetDoubleValue() {
		return value;
	}

private:
	double value;
};

class StringVal: public Value
{
public:
	StringVal(string v):value(v){}

	~StringVal(){}

	string GetStringValue() {
		return value;
	}

private:
	string value;
};

class BoolVal: public Value
{
public:
	BoolVal(double v):value(v){}

	~BoolVal(){}

	bool GetBoolValue() {
		return value;
	}

private:
	bool value;
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

	ArithOp GetArithOp() {
		return op;
	}

	Term* GetLeftE() {
		return leftE;
	}

	Term* GetRightE() {
		return rightE;
	}

private:
	ArithOp op;
	Term* leftE;
	Term* rightE;
};

/* 
 * ******************************************************************************** *
 *                                                                                  *
 *                               Parse tree for Term                                *
 *                                                                                  *
 * ******************************************************************************** *
 */











/* 
 * ******************************************************************************** *
 *                                                                                  *
 *                               Parse tree for formula                             *
 *                                                                                  *
 * ******************************************************************************** *
 */

class Formula 
{
public:
	Formula(){}

	virtual ~Formula(){}

};






class Connective: public Formula
{
public:
	enum ConnType
	{
		IMPLY,
		OR,
		AND
	};

	Connective(ConnType ct, Formula* formL, Formula* formR):
		conntype(ct), leftF(formL), rightF(formR){}

	virtual ~Connective(){}

	virtual ConnType GetConnType() {
		return conntype;
	}

	virtual Formula* GetLeftF() {
		return leftF;
	}

	virtual Formula* GetRightF() {
		return rightF;
	}

private:
	ConnType conntype;
	Formula* leftF;
	Formula* rightF;
};







class Quantifier: public Formula
{
public:
	enum QuanType {
		FORALL,
		EXISTS
	};

	Quantifier(QuanType q, vector<Variable*> b, Formula* f):
		quantype(q),boundVar(b),quantifiedF(f){}

	virtual ~Quantifier(){}


	virtual vector<Variable*> GetBoundVariables() {
		return boundVar;
	}

	virtual QuanType GetQuantifierType() {
		return quantype;
	}


	virtual Formula* GetQuantifierFormula() {
		return quantifiedF;
	}

private:
	QuanType quantype;
	vector<Variable*> boundVar;
	Formula* quantifiedF;
};





class PredicateF: public Formula
{
public:
	PredicateF(string n, vector<Term*> a):
		name(n),args(a){}

	virtual ~PredicateF(){}

	virtual string GetPredicateName() {
		return name;
	}

	virtual vector<Term*> GetPredicateArgs() {
		return args;
	}

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

	~Constraint(){}

	Operator GetOperator() {
		return op;
	}

	Term* GetLeftE() {
		return leftE;
	}

	Term* GetRightE() {
		return rightE;
	}

private:
	Operator op;
	Term* leftE;
	Term* rightE;
};

/* 
 * ******************************************************************************** *
 *                                                                                  *
 *                               Parse tree for formula                             *
 *                                                                                  *
 * ******************************************************************************** *
 */

#endif /* SDN_FORMULA_H_ */



/* END OF FILE */