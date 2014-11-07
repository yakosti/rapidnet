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

namespace ns3{
namespace rapidnet_sdn_veri{

class Formula;

/*
 * Expression
 */
class Expression;

class Term: public Expression{};
class Variable: public Term
{
public:
	Variable();
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
class Value: public Expression{};

class IntVal: public Value
{
private:
	int value;
};

class DoubleVal: public Value
{
private:
	double value;
};

class BoolVal: public Value
{
private:
	bool value;
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

class constraint: public Formula
{
public:
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
}	// namespace ns3
}	// namespace rapidnet_sdn_veri

#endif /* SDN_CONSTRAINT_H_ */
