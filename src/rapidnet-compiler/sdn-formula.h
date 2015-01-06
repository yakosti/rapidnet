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

	virtual int GetValue();
	
	virtual void PrintTerm();
};




class Variable: public Term
{
public:
	enum TypeCode
	{
		BOOL,
		INT,
		DOUBLE,
		STRING,
		LIST
	};

	/*
	 * t: BOOL/INT/DOUBLE/STRING type
	 * b: free or bound variable?
	 */
	Variable(TypeCode t, bool b);

	virtual ~Variable(){}

	TypeCode GetVariableType();
	
	string GetVariableName();

	bool GetFreeOrBound();

	void PrintTerm();

private:
	string name;
	TypeCode varType;
	bool isbound;
	static int varCount;
};



class FunctionSchema
{
public:
	FunctionSchema(string n, vector<Variable::TypeCode>& d, Variable::TypeCode r);

	virtual ~FunctionSchema();

	string GetName();

	vector<Variable::TypeCode>& GetDomainTypes();

	Variable::TypeCode GetRangeType();

	void PrintSchema();

private:
	string name;
	vector<Variable::TypeCode> domain;
	Variable::TypeCode range;
};


// CVC4: mkFunctionType
class UserFunction: public Term
{
public:
	UserFunction(FunctionSchema* s, vector<Term*>& a);

	virtual ~UserFunction();

	FunctionSchema* GetSchema();

	vector<Term*>& GetArgs();

	void PrintTerm();

private:
	FunctionSchema* schema;
	vector<Term*> args;
};





//See if template can be used here
// these are CONSTANTS
class Value: public Term
{
public:
	virtual ~Value(){}

    virtual void PrintTerm(){}
};





class IntVal: public Value
{
public:
	IntVal(int v);

	virtual ~IntVal();

	int GetIntValue();

	void PrintTerm();

private:
	int value;
};






class DoubleVal: public Value
{
public:
	DoubleVal(double v);

	virtual ~DoubleVal();

	double GetDoubleValue();

	void PrintTerm();	

private:
	double value;
};




class StringVal: public Value
{
public:
	StringVal(string v);

	virtual ~StringVal();

	string GetStringValue();

	void PrintTerm();	

private:
	string value;
};




class BoolVal: public Value
{
public:
	BoolVal(double v);

	~BoolVal();

	bool GetBoolValue();

	void PrintTerm();

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

	Arithmetic(ArithOp opt, Term* exprL, Term* exprR);

	ArithOp GetArithOp();

	Term* GetLeftE();

	Term* GetRightE();

	void PrintTerm();

	void PrintOp();

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

	Connective(ConnType ct, Formula* formL, Formula* formR);

	virtual ~Connective();

	virtual ConnType GetConnType();

	virtual Formula* GetLeftF();

	virtual Formula* GetRightF();

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

	Quantifier(QuanType q, vector<Variable*>& b, Formula* f);

	virtual ~Quantifier();

	virtual vector<Variable*>& GetBoundVariables();

	virtual QuanType GetQuantifierType();

	virtual Formula* GetQuantifierFormula();

private:
	QuanType quantype;
	vector<Variable*> boundVarList;
	Formula* fml;
};




class PredicateSchema
{
public:
	PredicateSchema(string n, vector<Variable::TypeCode>& t);

	virtual ~PredicateSchema();

	string GetName();

	vector<Variable::TypeCode>& GetTypes();

private:
	string name;
	vector<Variable::TypeCode> types;
};




class PredicateInstance: public Formula
{
public:
	PredicateInstance(PredicateSchema* s, vector<Term*>& a);

	virtual ~PredicateInstance();

	PredicateSchema* GetSchema();

	vector<Term*>& GetArgs();

private:
	PredicateSchema* schema;
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

	Constraint(Operator opt, Term* exprL, Term* exprR);

	~Constraint();

	Operator GetOperator();

	Term* GetLeftE();

	Term* GetRightE();

	void PrintConstraint();

	void PrintOp();

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





