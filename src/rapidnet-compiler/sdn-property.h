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

//TODO: Current Property does not support quantifiers in constraints
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

	const list<PredicateInstance*>& GetUniPred() const{return univPredList;}

	const list<PredicateInstance*>& GetExistPred() const{return existPredList;}

	const ConstraintsTemplate* GetUniCons() const{return univConsList;}

	const ConstraintsTemplate* GetExistCons() const{return existConsList;}

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

typedef pair<PredicateInstance*, ConstraintsTemplate*> ConsAnnot;
typedef map<string, ConsAnnot> ConsAnnotMap;

class BaseProperty
{
public:
	BaseProperty();

	const ConsAnnotMap& GetProp() const{return propSet;}

	~BaseProperty();
private:
	ConsAnnotMap propSet;
};

typedef pair<PredicateInstance*, Formula*> Annotation;
typedef map<string, Annotation> AnnotMap;

class Invariant
{
public:
	//TODO: For now we hardcode invariant properties
	Invariant();

	const AnnotMap& GetInv() const {return invs;}

	~Invariant();

private:
	AnnotMap invs;
};

#endif /* SDN_PROPERTY_H_ */
