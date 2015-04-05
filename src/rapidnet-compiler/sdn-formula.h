/*
 * sdn-formula.h
 *
 *  Created on: Nov 18, 2014
 *      Author: Chen
 * 
 * TODO: CHANGE THESE TO CONST FUNCTIONS, SAFER AS OTHER PEOPLE CANNOT CHANGE THE CODE
 * CHEN CHEN AND LAY KUAN, MARCH 10, 2015
 */

#ifndef SDN_FORMULA_H_
#define SDN_FORMULA_H_

#include <vector>
#include <list>
#include <string>
#include <map>
#include <iostream>
#include <sstream>

#include "ns3/log.h"
#include "parser-util.h"
#include "sdn-auxiliary.h"

using namespace std;
using namespace ns3;
using namespace rapidnet_compiler;

class Variable;
class ConstraintsTemplate;
class SimpConstraints;

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

	virtual void GetVars(vector<Variable*>& vlist){}

	virtual void ReplaceVar(const VarMap&){}

	void VarReplace(UnionFindSet,
					const map<Variable*, int>,
					const map<int, Variable*>){}

	virtual void CreateVarInst(VarMap&){}

	void FindReplaceFreeVar(list<Variable*>&, VarMap&){}

	virtual void PrintTerm() =0;

	virtual void PrintInst(VarMap&){}

	virtual void PrintSimpInst(VarMap&, SimpConstraints&){}

	virtual void PrintInstance(const map<Variable*, int>&, bool) const =0;

	virtual void PrintInstance(const map<Variable*, int>&, VarMap&, bool) const{}

	virtual void PrintSimpInstance(const map<Variable*, int>&, VarMap&,
			                       SimpConstraints&, bool) const{}
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

	Variable(TypeCode, bool);

	Variable(ParseVar*, bool);

	void CreateNewVar();

	TypeCode GetVariableType();
	
	string GetVariableName();

	void GetVars(vector<Variable*>&);

	bool GetFreeOrBound();

	Variable* Clone() {return this;}

	void PrintTerm();

	virtual void PrintInstance(const map<Variable*, int>&, bool) const{}

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

	void PrintName() const;

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

	void GetVars(vector<Variable*>&);

	void VarReplace(const VarMap&);

	void VarReplace(UnionFindSet,
					const map<Variable*, int>,
					const map<int, Variable*>);

	virtual void CreateVarInst(VarMap&);

	void FindReplaceFreeVar(list<Variable*>&, VarMap&);

	void PrintInst(VarMap&);

	void PrintSimpInst(VarMap&, SimpConstraints&);

	void PrintTerm();

	void PrintInstance(const map<Variable*, int>&, bool) const;

	void PrintInstance(const map<Variable*, int>&, VarMap&, bool) const;

	void PrintSimpInstance(const map<Variable*, int>&, VarMap&,
				           SimpConstraints&, bool) const;

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

	void GetVars(vector<const Variable*>&) const{}

    void PrintTerm(){}

    void PrintInst(VarMap&){}

    void PrintSimpInst(VarMap&, SimpConstraints&){}

    virtual void PrintInstance(const map<Variable*, int>&, bool) const{}

    virtual void PrintInstance(const map<Variable*, int>&, VarMap&, bool) const{}

    virtual void PrintSimpInstance(const map<Variable*, int>&, VarMap&,
    				           	   SimpConstraints&, bool) const{}
};





class IntVal: public Value
{
public:
	IntVal(int v);

	IntVal(const IntVal&);

	int GetIntValue();

	IntVal* Clone();

	void PrintTerm();

	void PrintInst(VarMap&){cout << value;}

	void PrintSimpInst(VarMap&, SimpConstraints&){cout << value;}

	void PrintInstance(const map<Variable*, int>&, bool) const;

	void PrintInstance(const map<Variable*, int>&, VarMap&, bool) const;

	void PrintSimpInstance(const map<Variable*, int>&, VarMap&,
					           SimpConstraints&, bool) const{cout << value;}

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

	void PrintInst(VarMap&){cout << value;}

	void PrintSimpInst(VarMap&, SimpConstraints&){cout << value;}

	void PrintInstance(const map<Variable*, int>&, bool) const;

	void PrintInstance(const map<Variable*, int>&, VarMap&, bool) const;

	void PrintSimpInstance(const map<Variable*, int>&, VarMap&,
						   SimpConstraints&, bool) const{cout << value;}

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

	void PrintInst(VarMap&){cout << value;}

	void PrintSimpInst(VarMap&, SimpConstraints&){cout << value;}

	void PrintInstance(const map<Variable*, int>&, bool) const;

	void PrintInstance(const map<Variable*, int>&, VarMap&, bool) const;

	void PrintSimpInstance(const map<Variable*, int>&, VarMap&,
						   SimpConstraints&, bool) const{cout << value;}

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

	void PrintInst(VarMap&){cout << value;}

	void PrintSimpInst(VarMap&, SimpConstraints&){cout << value;}

	void PrintInstance(const map<Variable*, int>&, bool) const;

	void PrintInstance(const map<Variable*, int>&, VarMap&, bool) const;

	void PrintSimpInstance(const map<Variable*, int>&, VarMap&,
						   SimpConstraints&, bool) const{cout << value;}

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

	void VarReplace(UnionFindSet,
					const map<Variable*, int>,
					const map<int, Variable*>);

	virtual void CreateVarInst(VarMap&);

	void FindReplaceFreeVar(list<Variable*>&, VarMap&);

	void GetVars(vector<Variable*>&);

	void PrintTerm();

	void PrintInst(VarMap&);

	void PrintSimpInst(VarMap&, SimpConstraints&);

	void PrintInstance(const map<Variable*, int>&, bool) const;

	void PrintInstance(const map<Variable*, int>&, VarMap&, bool) const;

	void PrintSimpInstance(const map<Variable*, int>&, VarMap&,
						   SimpConstraints&, bool) const;

	void PrintOp() const;

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

	virtual Formula* Clone(){return new Formula();}

	virtual void Print() const{}

	void PrintInst(VarMap&){}

	virtual void PrintSimpInst(VarMap&, SimpConstraints&){}

	virtual void PrintSimpInstance(const map<Variable*, int>&, VarMap&,
						   	   	   SimpConstraints&, bool) const{}

	virtual void VarReplace(const VarMap&){}

	virtual void VarReplace(SimpConstraints& simp)
		{cout << "Default variable replacement.";}

	virtual void FindFreeVar(list<Variable*>&, VarMap&){}

	//TODO: This function is not good practice
	virtual void ArgSwap(){}

	//ERROR: Aweful idea
	virtual void NullifyMem(){}

	virtual ~Formula(){}
};

class True: public Formula
{
public:
	True(){}

	True(const True&){}

	True* Clone();

	void Print() const{cout << "True";}

	void PrintInst(VarMap& vmap){cout << "True";}

	void PrintSimpInst(VarMap& vmap, SimpConstraints& simpCons){cout << "True";}

	void PrintSimpInstance(const map<Variable*, int>&, VarMap&,
						   SimpConstraints&, bool) const{cout << "True";}
};

class False: public Formula{};

/*
 * Negation is UNARY, thus is always stored on formL
 * formR for negation is ALWAYS null
 */
class Connective: public Formula
{
public:
	enum ConnType
	{
		IMPLY,
		OR,
		AND,
		NOT,
	};

	Connective(ConnType ct, Formula* formL, Formula* formR);

	Connective(const Connective&);

	void VarReplace(const VarMap&);

	void VarReplace(SimpConstraints&);

	void ArgSwap();

	void FindFreeVar(list<Variable*>&, VarMap&);

	//ERROR: Aweful function
	void NullifyMem();

	Connective* Clone();

	ConnType GetConnType();

	Formula* GetLeftF();

	Formula* GetRightF();

	void Print() const;

	void PrintInst(VarMap&);

	void PrintSimpInst(VarMap&, SimpConstraints&);

	void PrintSimpInstance(const map<Variable*, int>&, VarMap&,
						   SimpConstraints&, bool) const;

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

	Quantifier(QuanType, const vector<Variable*>&, Formula*);

	Quantifier(QuanType, const vector<Variable*>&, const ConstraintsTemplate*);

	Quantifier(const Quantifier&);

	void VarReplace(const VarMap&);

	void VarReplace(SimpConstraints&);

	void FindFreeVar(list<Variable*>&, VarMap&);

	Quantifier* Clone();

	vector<Variable*>& GetBoundVariables();

	QuanType GetQuantifierType();

	Formula* GetQuantifierFormula();

	void Print() const;

	void PrintInst(VarMap&);

	void PrintSimpInst(VarMap&, SimpConstraints&);

	void PrintSimpInstance(const map<Variable*, int>&, VarMap&,
						   SimpConstraints&, bool) const;

	~Quantifier();

private:
	QuanType quantype;
	vector<Variable*> boundVarList;
	Formula* fml;
};




class PredicateSchema
{
public:
	PredicateSchema(string, int);

	PredicateSchema(string, vector<Variable::TypeCode>&);

	PredicateSchema(const PredicateSchema&);

	string GetName() const;

	const vector<Variable::TypeCode>& GetTypes() const;

	void Print() const;

private:
	string name;
	vector<Variable::TypeCode> types;
};



class PredicateInstance: public Formula
{
public:
	PredicateInstance(PredicateSchema*, vector<Term*>&);

	PredicateInstance(const PredicateInstance&);

	void VarReplace(const VarMap&);

	PredicateInstance* Clone();

	string GetName() const;

	const PredicateSchema* GetSchema() const;

	const vector<Term*>& GetArgs() const;

	void Print() const;

	void PrintInst(VarMap&);

	void PrintSimpInst(VarMap&, SimpConstraints&);

	void PrintSimpInstance(const map<Variable*, int>&, VarMap&,
						   SimpConstraints&, bool) const;

	~PredicateInstance();

private:
	PredicateSchema* schema;
	vector<Term*> args;
};

class SimpConstraints;

//TODO: variables in Constraint is now required to be independent

//TODO: Unification of variables in invariants and
//representative variables in equivalent classes
class Constraint: public Formula
{
public:
	enum Operator
	{
		EQ,		//Equal to
		NEQ,	//Unequal to
		GT,		//Greater than
		GE,		//Greater than or equal to
		LT,		//Smaller than
		LE,		//Less than or equal to
	};

	Constraint(Operator opt, Term* exprL, Term* exprR);

	Constraint(const Constraint&);

	~Constraint();

	Constraint* Clone();

	Constraint* Revert() const;

	Operator GetOperator();

	Term* GetLeftE();

	Term* GetRightE();

	bool IsEquiv() const;

	bool IsUnif();

	//TODO: This member function should be const
	void GetVars(vector<Variable*>&);

	void VarReplace(const VarMap&);

	void VarReplace(UnionFindSet,
					const map<Variable*, int>,
					const map<int, Variable*>);

	//TODO: make SimpConstraints const
	void VarReplace(SimpConstraints&);

	virtual void CreateVarInst(VarMap&);

	void FindFreeVar(list<Variable*>&, VarMap&);

	void Print() const;

	void PrintInst(VarMap&);

	void PrintSimpInst(VarMap&, SimpConstraints&);

	void PrintInstance(const map<Variable*, int>&, bool) const;

	void PrintInstance(const map<Variable*, int>&, VarMap&, bool) const;

	void PrintSimpInstance(const map<Variable*, int>&, VarMap&,
						   SimpConstraints&, bool) const;

	void PrintOp() const;

private:
	Operator op;
	Term* leftE;
	Term* rightE;
};

typedef list<Constraint*> ConstraintList;

/*
 * Class ConstraintsTemplate represents a set of constraints in NDLog program
 */
class ConstraintsTemplate
{
public:
	ConstraintsTemplate();

	ConstraintsTemplate(const ConstraintsTemplate&);

	void AddConstraint(Constraint*);

	void ReplaceVar(VarMap&);

	void ReplaceVar(SimpConstraints&);

	void RemoveUnif();

	ConstraintsTemplate* Revert() const;

	const ConstraintList& GetConstraints() const {return constraints;}

	bool IsEmpty() const;

	void CreateVarInst(VarMap&);

	void FindFreeVar(list<Variable*>&, VarMap&);

	void PrintTemplate() const;

	void PrintTempInst(VarMap&);

	void PrintSimpTempInst(VarMap&, SimpConstraints&);

	void PrintInstance(const map<Variable*, int>&, bool) const;

	void PrintInstance(const map<Variable*, int>&, VarMap&, bool) const;

	void PrintSimpInstance(const map<Variable*, int>&, VarMap&,
						   SimpConstraints&, bool) const;

	~ConstraintsTemplate();

private:
	ConstraintList constraints;
};

typedef list<const ConstraintsTemplate*> ConsList;
typedef list<Formula*> FormList;

class SimpConstraints
{
public:
	SimpConstraints();

	SimpConstraints(const ConsList&);

	SimpConstraints(const list<ConstraintsTemplate*>&);

	void Initialize(const ConsList&);

	void CreateEquiClass();

	Variable* FindRootVar(Variable*);

	const map<Variable*, list<Variable*> >& GetEquiClass() {return equiClass;}

	const ConstraintsTemplate& GetConstraints() const{return cts;}

	UnionFindSet& GetUnionFindSet() {return varSet;}

	const map<Variable*, int>& GetVarTable() {return varTable;}

	const map<int, Variable*>& GetRevTable() {return varRevTable;}

	void Print();

private:
	ConstraintsTemplate cts;
	map<Variable*, int> varTable;
	map<int, Variable*> varRevTable;
	UnionFindSet varSet;

	map<Variable*, list<Variable*> > equiClass;
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





