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
#include <sdn-constraint.h>

using namespace std;

/*
 * Parse tree for formula
 */
class Formula;

class LogicConnective: public Formula
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

class LogicForall: public Quantifier{};
class LogicExist: public Quantifier{};

class LogicPredicate: public Formula
{
private:
	string name;
	vector<Term*> args;
};

#endif /* SDN_FORMULA_H_ */
