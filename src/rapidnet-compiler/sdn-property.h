/*
 * property.h
 *
 *  Created on: Mar 5, 2015
 *      Author: chen
 */

#ifndef SDN_PROPERTY_H_
#define SDN_PROPERTY_H_

#include<list>
#include<iostream>
#include<fstream>

#include "sdn-formula.h"

using namespace std;

class Property
{
public:

	//Hardcode property inputList
	Property();

	void ProcessUniCons(const map<string, Variable*>&);

	void ProcessExistCons(const map<string, Variable*>&);

	vector<Term*> ParseArgs(const string, map<string, Variable*>&);

	void ProcessUniPred(const string, map<string, Variable*>&);

	void ProcessExistPred(const string, map<string, Variable*>&);

	PredicateInstance* ParsePred(const string, map<string, Variable*>&);

	void ParseExistVars(string, map<string, Variable*>);

	void Print() const;

	//ConstraintsTemplate* ParseCons(string, map<string, Variable*>);

	~Property();

private:
	list<Variable*> uniVars;
	list<PredicateInstance*> univPredList;
	ConstraintsTemplate* univConsList;
	list<Variable*> existVars;
	list<PredicateInstance*> existPredList;
	ConstraintsTemplate* existConsList;
};



#endif /* SDN_PROPERTY_H_ */
