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
#include <map>
#include <iostream>
#include <sstream>

#include "ns3/log.h"

using namespace std;

class Variable;

//TODO: change VarMap into a class
typedef map<Variable*, Variable*> VarMap;


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

	int GetValue();
	
	virtual Term* Clone() {return NULL;}

	virtual void ReplaceVar(const VarMap&){}

	virtual void PrintTerm() =0;
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

	~Variable(){}

	TypeCode GetVariableType();
	
	string GetVariableName();

	bool GetFreeOrBound();

	Variable* Clone() {return this;}

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

	FunctionSchema(const FunctionSchema&);

	~FunctionSchema();

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

	UserFunction(const UserFunction&);

	FunctionSchema* GetSchema();

	vector<Term*>& GetArgs();

	UserFunction* Clone();

	void ReplaceVar(const VarMap&);

	void PrintTerm();

	~UserFunction();

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

	virtual Value* Clone() {return NULL;}

    void PrintTerm(){}
};





class IntVal: public Value
{
public:
	IntVal(int v);

	IntVal(const IntVal&);

	int GetIntValue();

	IntVal* Clone();

	void PrintTerm();

private:
	int value;
};






class DoubleVal: public Value
{
public:
	DoubleVal(double v);

	DoubleVal(const DoubleVal&);

	double GetDoubleValue();

	DoubleVal* Clone();

	void PrintTerm();	

private:
	double value;
};




class StringVal: public Value
{
public:
	StringVal(string v);

	StringVal(const StringVal&);

	string GetStringValue();

	StringVal* Clone();

	void PrintTerm();	

private:
	string value;
};




class BoolVal: public Value
{
public:
	BoolVal(double v);

	BoolVal(const BoolVal&);

	bool GetBoolValue();

	BoolVal* Clone();

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

	Arithmetic(const Arithmetic&);

	ArithOp GetArithOp();

	Term* GetLeftE();

	Term* GetRightE();

	Arithmetic* Clone();

	void ReplaceVar(const VarMap&);

	void PrintTerm();

	void PrintOp();

	~Arithmetic();

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

	virtual Formula* Clone() =0;

	virtual void Print() const =0;

	virtual void VarReplace(const VarMap&) =0;

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

	Connective(const Connective&);

	void VarReplace(const VarMap&);

	Connective* Clone();

	ConnType GetConnType();

	Formula* GetLeftF();

	Formula* GetRightF();

	void Print() const;

	~Connective();

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

	Quantifier(QuanType q, const vector<Variable*>& b, Formula* f);

	Quantifier(const Quantifier&);

	void VarReplace(const VarMap&);

	Quantifier* Clone();

	vector<Variable*>& GetBoundVariables();

	QuanType GetQuantifierType();

	Formula* GetQuantifierFormula();

	void Print() const;

	~Quantifier();

private:
	QuanType quantype;
	vector<Variable*> boundVarList;
	Formula* fml;
};




class PredicateSchema
{
public:
	PredicateSchema(string n, vector<Variable::TypeCode>& t);

	PredicateSchema(const PredicateSchema&);

	string GetName();

	vector<Variable::TypeCode>& GetTypes();

	void Print() const;

private:
	string name;
	vector<Variable::TypeCode> types;
};




class PredicateInstance: public Formula
{
public:
	PredicateInstance(PredicateSchema* s, vector<Term*>& a);

	PredicateInstance(const PredicateInstance&);

	void VarReplace(const VarMap&);

	PredicateInstance* Clone();

	PredicateSchema* GetSchema();

	vector<Term*>& GetArgs();

	void Print() const;

	~PredicateInstance();

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

	Constraint(const Constraint&);

	~Constraint();

	Constraint* Clone();

	Operator GetOperator();

	Term* GetLeftE();

	Term* GetRightE();

	void VarReplace(const VarMap&);

	void Print() const;

	void PrintOp() const;

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





