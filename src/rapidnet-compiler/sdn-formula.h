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
	
	virtual void PrintTerm(){}
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
	Variable(TypeCode t, bool b):varType(t),isbound(b),varCount(0) {
        Variable::varCount = Variable::varCount + 1;
		ostringstream countStream;
		countStream << Variable::varCount;  
		name =  "variable"+ countStream.str();
	}

	virtual ~Variable(){}

	TypeCode GetVariableType() {
		return varType;
	}

	string GetVariableName() {
		return name;
	}

	bool GetFreeOrBound() {
		return isbound;
	}

	void PrintTerm() {
		cout << name;
	}

private:
	string name;
	TypeCode varType;
	bool isbound;
	int varCount;
};



class FunctionSchema
{
public:
	FunctionSchema(string n, vector<Variable::TypeCode> d, Variable::TypeCode r):
		name(n),domain(d),range(r){}

	virtual ~FunctionSchema(){}

	string GetName() {
		return name;
	}

	vector<Variable::TypeCode>& GetDomainTypes () {
		return domain;
	}

	Variable::TypeCode GetRangeType() {
		return range;
	}

	void PrintSchema() {
		cout << name;	
	}

private:
	string name;
	vector<Variable::TypeCode> domain;
	Variable::TypeCode range;
};


// CVC4: mkFunctionType
class UserFunction: public Term
{
public:
	UserFunction(FunctionSchema* s, vector<Term*> a):
		schema(s),args(a){}

	virtual ~UserFunction(){}

	FunctionSchema* GetSchema() {
		return schema;
	}

	vector<Term*>& GetArgs() {
		return args;
	}

	void PrintTerm() {
		schema->PrintSchema();
		cout << "(";
		vector<Term*>::iterator it;
		for (it = args.begin(); it != args.end(); it++) {
		    if (it != args.begin()) {
		      	cout << ",";
		    }
		    (*it)->PrintTerm();
		}
		cout << ")";
	}

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
	IntVal(int v):value(v){}

	virtual ~IntVal(){}

	int GetIntValue() {
		return value;
	}

	void PrintTerm() {
		cout << value;
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

	void PrintTerm() {
		cout << value;
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

	void PrintTerm() {
		cout << value;
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

	void PrintTerm() {
		cout << value;
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

	void PrintTerm() {
		leftE->PrintTerm();
  		PrintOp();
  		rightE->PrintTerm();
	}

	void PrintOp() {
		switch(op) {
			case Arithmetic::PLUS:
			    cout << "+";
			    break;
			case Arithmetic::MINUS:
			    cout << "-";
			    break;
			case Arithmetic::TIMES:
			    cout << "*";
			    break;
			case Arithmetic::DIVIDE:
			    cout << "/";
			    break;
		}  
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
		quantype(q),boundVarList(b),fml(f){}

	virtual ~Quantifier(){}


	virtual vector<Variable*>& GetBoundVariables() {
		return boundVarList;
	}

	virtual QuanType GetQuantifierType() {
		return quantype;
	}


	virtual Formula* GetQuantifierFormula() {
		return fml;
	}

private:
	QuanType quantype;
	vector<Variable*> boundVarList;
	Formula* fml;
};




class PredicateSchema
{
public:
	PredicateSchema(string n, vector<Variable::TypeCode> t):
		name(n),types(t){}

	virtual ~PredicateSchema(){}

	string GetName() {
		return name;
	}

	vector<Variable::TypeCode>& GetTypes () {
		return types;
	}

private:
	string name;
	vector<Variable::TypeCode> types;
};




class PredicateInstance: public Formula
{
public:
	PredicateInstance(PredicateSchema* s, vector<Term*> a):
		schema(s),args(a){}

	virtual ~PredicateInstance(){}

	PredicateSchema* GetSchema() {
		return schema;
	}

	vector<Term*>& GetArgs() {
		return args;
	}

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

	Constraint(Operator opt, Term* exprL, Term* exprR):
		op(opt),leftE(exprL),rightE(exprR){}

	~Constraint() {}

	Operator GetOperator() {
		return op;
	}

	Term* GetLeftE() {
		return leftE;
	}

	Term* GetRightE() {
		return rightE;
	}

	void PrintConstraint() {
		leftE->PrintTerm();
		PrintOp();
		rightE->PrintTerm();
	}

	void PrintOp() {
		switch(op){
		case Constraint::EQ:
		    cout << "=";
		    break;
		case Constraint::NEQ:
		    cout << "!=";
		    break;
		case Constraint::GT:
		    cout << ">";
		    break;
		case Constraint::LT:
		    cout << "<";
		    break;
		}
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





