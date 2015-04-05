/*
 * property.cc
 *
 *  Created on: Mar 5, 2015
 *      Author: chen
 */

#include "sdn-property.h"

NS_LOG_COMPONENT_DEFINE ("Property");

Property::Property()
{
	map<string, Variable*> varMap;

	uniVars = list<Variable*>();
	univPredList = list<PredicateInstance*>();
	univConsList = new ConstraintsTemplate();
	existVars = list<Variable*>();
	existPredList = list<PredicateInstance*>();
	existConsList = new ConstraintsTemplate();

	//ProcessUniPred("reachable(src,dest,cost)", varMap);
	//ProcessUniPred("verifyPath(m,n,l)", varMap);
	//ProcessUniPred("ePingPongFinish(s)", varMap);
	//ProcessUniPred("path(x,y,z)", varMap);
	//ProcessUniPred("flowEntry(s,m,o)", varMap);
	//ProcessUniPred("packet(a,b,c,d)", varMap);
	ProcessUniPred("flowEntry(e,f,g,h)", varMap);
	//ProcessUniPred("swToHst(i,j,k)", varMap);

	//ProcessUniCons(varMap);

	//ProcessExistPred("packet(a,b,c,d)", varMap);
	//ProcessExistPred("link(m,n,c)", varMap);
	//ProcessExistPred("tLink(r,s)", varMap);
	//ProcessExistPred("flowEntry(fev1,fev2,fev3,fev4)", varMap);
	ProcessExistPred("matchingPacket(mev1,mev2,mev3,mev4,mev5)", varMap);
	ProcessExistCons(varMap);
}

//TODO: Parse constraints from user input
void
Property::ProcessUniCons(const map<string, Variable*>& varMap)
{
	NS_LOG_FUNCTION("Processing universally quantified constraints...");
	/*Constraint template*/
//	string var1 = "a";
//	Variable* varPtr = varMap.find(var1)->second;
//
//	Constraint* newCons = new Constraint(Constraint::LT, varPtr, new IntVal(4));
//
//	univConsList->AddConstraint(newCons);

//	string var1 = "src";
//	Variable* varPtr = varMap.find(var1)->second;
//
//	Constraint* newCons = new Constraint(Constraint::GT,
//										 varPtr,
//										 new IntVal(6));
//
//	univConsList->AddConstraint(newCons);

	//sdn-mac-learning.olg
	//Property 2 in verification.txt
//	string var1 = "b";
//	Variable* varPtr1 = varMap.find(var1)->second;
//	string var2 = "e";
//	Variable* varPtr2 = varMap.find(var2)->second;
//
//	Constraint* newCons = new Constraint(Constraint::EQ,
//										 varPtr1,
//										 varPtr2);
//	univConsList->AddConstraint(newCons);
//
//	string var3 = "d";
//	Variable* varPtr3 = varMap.find(var3)->second;
//	string var4 = "a";
//	Variable* varPtr4 = varMap.find(var4)->second;
//
//	newCons = new Constraint(Constraint::NEQ,
//										 varPtr3,
//										 varPtr4);
//	univConsList->AddConstraint(newCons);
//
//	string var5 = "i";
//	Variable* varPtr5 = varMap.find(var5)->second;
//
//	newCons = new Constraint(Constraint::EQ,
//										 varPtr5,
//										 varPtr1);
//	univConsList->AddConstraint(newCons);
//
//	string var6 = "j";
//	Variable* varPtr6 = varMap.find(var6)->second;
//
//	newCons = new Constraint(Constraint::EQ,
//										 varPtr6,
//										 varPtr4);
//	univConsList->AddConstraint(newCons);

	//Property 4 in verification.txt
	string var1 = "b";
	Variable* varPtr1 = varMap.find(var1)->second;
	string var3 = "d";
	Variable* varPtr3 = varMap.find(var3)->second;
	string var4 = "a";
	Variable* varPtr4 = varMap.find(var4)->second;

	Constraint* newCons = new Constraint(Constraint::EQ,
										 varPtr3,
										 varPtr4);
	univConsList->AddConstraint(newCons);

	string var5 = "i";
	Variable* varPtr5 = varMap.find(var5)->second;

	newCons = new Constraint(Constraint::EQ,
										 varPtr5,
										 varPtr1);
	univConsList->AddConstraint(newCons);

	string var6 = "j";
	Variable* varPtr6 = varMap.find(var6)->second;

	newCons = new Constraint(Constraint::EQ,
										 varPtr6,
										 varPtr4);
	univConsList->AddConstraint(newCons);
}

void
Property::ProcessExistCons(const map<string, Variable*>& varMap)
{
	/*Constraint template*/

//	string var1 = "r";
//	map<string, Variable*>::const_iterator itm = varMap.find(var1);
//	if (itm == varMap.end())
//	{
//		NS_LOG_ERROR("Variable " << var1 << "not found!");
//		return;
//	}
//	Variable* varPtr1 = itm->second;
//
//	string var2 = "b";
//	itm = varMap.find(var2);
//	if (itm == varMap.end())
//	{
//		NS_LOG_ERROR("Variable " << var1 << "not found!");
//		return;
//	}
//	Variable* varPtr2 = itm->second;
//	Constraint* newCons = new Constraint(Constraint::EQ, varPtr1, varPtr2);
//	existConsList->AddConstraint(newCons);

//	string var1 = "a";
//	Variable* varPtr = varMap.find(var1)->second;
//
//	Constraint* newCons = new Constraint(Constraint::GT,
//										 varPtr,
//										 new IntVal(3));
//
//	existConsList->AddConstraint(newCons);

	//Property verification of path.olg
//	string var1 = "z";
//	Variable* varArg = varMap.find(var1)->second;
//
//	Variable* varPtr = new Variable(Variable::STRING, true);
//	existVars.push_back(varPtr);
//
//	IntVal* value = new IntVal(1);
//
//	Constraint* newCons1 = new Constraint(Constraint::GT,
//											 varPtr,
//											 value);
//
//	Constraint* newCons2 = new Constraint(Constraint::GT,
//										 varArg,
//										 varPtr);
//
//	existConsList->AddConstraint(newCons1);
//	existConsList->AddConstraint(newCons2);

//	string var1 = "z";
//	Variable* varArg = varMap.find(var1)->second;
//
//	IntVal* value = new IntVal(3);
//
//	Constraint* newCons1 = new Constraint(Constraint::GT,
//											 varArg,
//											 value);
//
//	existConsList->AddConstraint(newCons1);

	//Property verification of pingpong.olg
//	string var1 = "s";
//	Variable* varPtr = varMap.find(var1)->second;
//
//	Constraint* newCons = new Constraint(Constraint::LT,
//										 varPtr,
//										 new IntVal(2));
//
//	existConsList->AddConstraint(newCons);

	//sdn-mac-learning.olg
//	string var1 = "a";
//	Variable* varPtr1 = varMap.find(var1)->second;
//	string var2 = "e";
//	Variable* varPtr2 = varMap.find(var2)->second;
//
//
//	Constraint* newCons = new Constraint(Constraint::EQ,
//										 varPtr1,
//										 varPtr2);
//
//	existConsList->AddConstraint(newCons);
//
//	string var3 = "c";
//	Variable* varPtr3 = varMap.find(var3)->second;
//	string var4 = "f";
//	Variable* varPtr4 = varMap.find(var4)->second;
//
//	newCons = new Constraint(Constraint::EQ,
//										 varPtr3,
//										 varPtr4);
//
//	existConsList->AddConstraint(newCons);

//	string var1 = "f";
//	Variable* varPtr1 = varMap.find(var1)->second;
//	string var2 = "d";
//	Variable* varPtr2 = varMap.find(var2)->second;
//
//	Constraint* newCons = new Constraint(Constraint::NEQ,
//										 varPtr1,
//										 varPtr2);
//	existConsList->AddConstraint(newCons);

	//Property 4 in verification.txt
//	string var1 = "fev1";
//	Variable* varPtr1 = varMap.find(var1)->second;
//	string var2 = "b";
//	Variable* varPtr2 = varMap.find(var2)->second;
//
//	Constraint* newCons = new Constraint(Constraint::EQ,
//										 varPtr1,
//										 varPtr2);
//	existConsList->AddConstraint(newCons);
//
//	string var3 = "fev2";
//	Variable* varPtr3 = varMap.find(var3)->second;
//	string var4 = "d";
//	Variable* varPtr4 = varMap.find(var4)->second;
//
//	newCons = new Constraint(Constraint::EQ,
//										 varPtr3,
//										 varPtr4);
//	existConsList->AddConstraint(newCons);

	//Property 5 in verification.txt
	string var1 = "mev1";
	Variable* varPtr1 = varMap.find(var1)->second;
	string var2 = "e";
	Variable* varPtr2 = varMap.find(var2)->second;

	Constraint* newCons = new Constraint(Constraint::EQ,
										 varPtr1,
										 varPtr2);
	existConsList->AddConstraint(newCons);

	string var3 = "mev2";
	Variable* varPtr3 = varMap.find(var3)->second;
	string var4 = "f";
	Variable* varPtr4 = varMap.find(var4)->second;

	newCons = new Constraint(Constraint::EQ,
										 varPtr3,
										 varPtr4);
	existConsList->AddConstraint(newCons);

	string var5 = "mev4";
	Variable* varPtr5 = varMap.find(var5)->second;
	string var6 = "g";
	Variable* varPtr6 = varMap.find(var6)->second;

	newCons = new Constraint(Constraint::EQ,
										 varPtr5,
										 varPtr6);
	existConsList->AddConstraint(newCons);

	string var7 = "mev5";
	Variable* varPtr7 = varMap.find(var7)->second;
	IntVal* value = new IntVal(0);

	newCons = new Constraint(Constraint::EQ,
										 varPtr7,
										 value);
	existConsList->AddConstraint(newCons);
}


vector<Term*>
Property::ParseArgs(const string args, map<string, Variable*>& varMap)
{
	//Example args: "v1,v2,v3...,vn"
	vector<Term*> vlist;
	istringstream ss(args);
	string arg;
	Variable* newVar = NULL;
	while (getline(ss, arg, ','))
	{
		//TODO: Replace default type
		NS_LOG_DEBUG("Process variable: " << arg);
		newVar = new Variable(Variable::STRING, true);
		vlist.push_back(newVar);
		varMap.insert(map<string,Variable*>::value_type(arg, newVar));
	}

	return vlist;
}

void
Property::ProcessUniPred(string line, map<string, Variable*>& varMap)
{
	NS_LOG_FUNCTION("Processing universally quantified predicate...");
	PredicateInstance* predInst = ParsePred(line, varMap);
	univPredList.push_back(predInst);
}

void
Property::ProcessExistPred(const string line, map<string, Variable*>& varMap)
{
	PredicateInstance* predInst = ParsePred(line, varMap);
	existPredList.push_back(predInst);
}

PredicateInstance*
Property::ParsePred(const string line, map<string, Variable*>& varMap)
{
	size_t leftParPos = line.find("(");
	string predName = line.substr(0, leftParPos);
	size_t rightParPos = line.find(")");
	string predArgs = line.substr(leftParPos+1, (rightParPos - leftParPos - 1));
	vector<Term*> args = ParseArgs(predArgs, varMap);
	int arg_length = args.size();
	vector<Variable::TypeCode> typeVec = vector<Variable::TypeCode>(arg_length, Variable::STRING);
	PredicateSchema* schema = new PredicateSchema(predName, typeVec);
	return (new PredicateInstance(schema, args));
}


void
Property::Print() const
{
	cout << endl;
	cout << "********** User-defined Property ***********" << endl;

	//Print universally quantified variables
	cout << "forall ";
	list<Variable*>::const_iterator itv;
	for (itv = uniVars.begin();itv != uniVars.end();itv++)
	{
		(*itv)->PrintTerm();
		cout << ",";
	}

	list<PredicateInstance*>::const_iterator itp;
	for (itp = univPredList.begin();itp != univPredList.end();itp++)
	{
		const vector<Term*>& varVec = (*itp)->GetArgs();
		vector<Term*>::const_iterator itt;
		for (itt = varVec.begin();itt != varVec.end();itt++)
		{
			(*itt)->PrintTerm();
			cout << ",";
		}
	}



	cout << endl;

	//Print universally quantified predicates
	for (itp = univPredList.begin();itp != univPredList.end();itp++)
	{
		(*itp)->Print();
		cout << " /\\ " << endl;
	}

	//Print universally quantified constraints
	univConsList->PrintTemplate();

	cout << endl << "->";

	//Print existentially quantified variables
	cout << "exists ";
	for (itv = existVars.begin();itv != existVars.end();itv++)
	{
		(*itv)->PrintTerm();
		cout << ",";
	}
	for (itp = existPredList.begin();itp != existPredList.end();itp++)
	{
		const vector<Term*>& varVec = (*itp)->GetArgs();
		vector<Term*>::const_iterator itt;
		for (itt = varVec.begin();itt != varVec.end();itt++)
		{
			(*itt)->PrintTerm();
			cout << ",";
		}
	}

	cout << endl;

	//Print existentially quantified predicates
	for (itp = existPredList.begin();itp != existPredList.end();itp++)
	{
		(*itp)->Print();
		cout << " /\\ " << endl;
	}

	existConsList->PrintTemplate();

	cout << "*********************";
	cout << endl;
}

Property::~Property()
{
	delete univConsList;
	delete existConsList;

	list<Variable*>::iterator itv;
	for (itv = uniVars.begin();itv != uniVars.end();itv++)
	{
		delete (*itv);
	}
	for (itv = existVars.begin();itv != existVars.end();itv++)
	{
		delete (*itv);
	}

	list<PredicateInstance*>::iterator itl;
	for (itl = univPredList.begin();itl != univPredList.end();itl++)
	{
		delete (*itl);
	}

	for (itl = existPredList.begin();itl != existPredList.end();itl++)
	{
		delete (*itl);
	}
}

BaseRel::BaseRel()
{
	varMap = map<string, Variable*>();
	basePreds = list<PredicateInstance*>();
	baseForm = NULL;
}

void
BaseRel::InsertPred(string pred)
{
	size_t leftParPos = pred.find("(");
	string predName = pred.substr(0, leftParPos);
	size_t rightParPos = pred.find(")");
	string predArgs = pred.substr(leftParPos+1, (rightParPos - leftParPos - 1));

	vector<Term*> args;
	istringstream ss(predArgs);
	string arg;
	Variable* newVar = NULL;
	while (getline(ss, arg, ','))
	{
		//TODO: Replace default type
		NS_LOG_DEBUG("Process variable: " << arg);
		newVar = new Variable(Variable::STRING, true);
		args.push_back(newVar);
		varMap.insert(map<string,Variable*>::value_type(arg, newVar));
	}

	int arg_length = args.size();
	vector<Variable::TypeCode> typeVec = vector<Variable::TypeCode>(arg_length, Variable::STRING);
	PredicateSchema* schema = new PredicateSchema(predName, typeVec);
	PredicateInstance* predInst = new PredicateInstance(schema, args);
	basePreds.push_back(predInst);
}

void
BaseRel::UpdateFormula(Formula* fml)
{
	baseForm = fml;
}

void
BaseRel::Print()
{
	cout << "***** Print Base Relational Prop *****" << endl;
	list<PredicateInstance*>::iterator itl;
	for (itl = basePreds.begin();itl != basePreds.end();itl++)
	{
		(*itl)->Print();
		cout << endl;
	}
	cout << "," << endl;
	baseForm->Print();
	cout << "***************" << endl;
	cout << endl;
}


BaseRel::~BaseRel()
{
	delete baseForm;
	list<PredicateInstance*>::iterator itl;
	for (itl = basePreds.begin();itl != basePreds.end();itl++)
	{
		delete (*itl);
	}
}

BaseRelProperty::BaseRelProperty()
{
	propSet = list<BaseRel*>();

	//sdn-mac-learning.olg
	//Start constructing a BaseRel
	BaseRel* barl = new BaseRel();

	string pred = "swToHst(v1,v2,v3)";
	barl->InsertPred(pred);
	pred = "swToHst(v4,v5,v6)";
	barl->InsertPred(pred);

	map<string, Variable*>& vmap = barl->varMap;

	string var1 = "v1";
	Variable* varPtr1 = vmap.find(var1)->second;
	string var2 = "v4";
	Variable* varPtr2 = vmap.find(var2)->second;

	Constraint* newCons1 = new Constraint(Constraint::EQ,
										 varPtr1,
										 varPtr2);

	string var3 = "v2";
	Variable* varPtr3 = vmap.find(var3)->second;
	string var4 = "v5";
	Variable* varPtr4 = vmap.find(var4)->second;

	Constraint* newCons2 = new Constraint(Constraint::EQ,
										 varPtr3,
										 varPtr4);

	string var5 = "v3";
	Variable* varPtr5 = vmap.find(var5)->second;
	string var6 = "v6";
	Variable* varPtr6 = vmap.find(var6)->second;

	Constraint* newCons3 = new Constraint(Constraint::EQ,
										 varPtr5,
										 varPtr6);

	Formula* newConn = new Connective(Connective::AND, newCons1, newCons2);
	Formula* leftForm = new Connective(Connective::IMPLY, newConn, newCons3);

	string var7 = "v1";
	Variable* varPtr7 = vmap.find(var7)->second;
	string var8 = "v4";
	Variable* varPtr8 = vmap.find(var8)->second;

	Constraint* newCons4 = new Constraint(Constraint::EQ,
										 varPtr7,
										 varPtr8);

	string var9 = "v2";
	Variable* varPtr9 = vmap.find(var9)->second;
	string var10 = "v5";
	Variable* varPtr10 = vmap.find(var10)->second;

	Constraint* newCons5 = new Constraint(Constraint::EQ,
										 varPtr9,
										 varPtr10);

	string var11 = "v3";
	Variable* varPtr11 = vmap.find(var11)->second;
	string var12 = "v6";
	Variable* varPtr12 = vmap.find(var12)->second;

	Constraint* newCons6 = new Constraint(Constraint::EQ,
										 varPtr11,
										 varPtr12);

	Formula* newConn1 = new Connective(Connective::AND, newCons4, newCons6);
	Formula* rightForm = new Connective(Connective::IMPLY, newConn1, newCons5);

	Formula* form = new Connective(Connective::AND, leftForm, rightForm);

	barl->UpdateFormula(form);
	propSet.push_back(barl);
	//BaseRel construction finished
}


void
BaseRelProperty::Print()
{
	cout << "~~~~~~~~~~~ Print Base Relational Properties ~~~~~~~~~~~" << endl;
	list<BaseRel*>::iterator itb;
	for (itb = propSet.begin();itb != propSet.end();itb++)
	{
		(*itb)->Print();
		cout << endl;
	}

	cout << "~~~~~~~~~~~~~~~~~~~~~~~~" << endl;
}

BaseRelProperty::~BaseRelProperty()
{
	NS_LOG_FUNCTION("Destruct base relational properties.");
	list<BaseRel*>::iterator itb;
	for (itb = propSet.begin();itb != propSet.end();itb++)
	{
		delete (*itb);
	}
}

//TODO: We might need type information to differentiate arguments
BaseProperty::BaseProperty()
{
	propSet = ConsAnnotMap();

	//pingpong.olg
//	string predName = "tLink";
//	int argNum = 2;
//	PredicateSchema* scheme = new PredicateSchema(predName, argNum);
//	vector<Term*> args;
//	for (int i = 0;i < argNum;i++)
//	{
//		Variable* newVar = new Variable(Variable::STRING, true);
//		args.push_back(newVar);
//	}
//	//Use index to create formulas;
//	PredicateInstance* pInst = new PredicateInstance(scheme, args);
//	IntVal* value = new IntVal(10000);
//	Constraint* ct = new Constraint(Constraint::EQ, args[0], value);
//	ConstraintsTemplate* cts = new ConstraintsTemplate();
//	cts->AddConstraint(ct);
//
//	ConsAnnot cat = ConsAnnot(pInst, cts);
//	propSet.insert(ConsAnnotMap::value_type(predName, cat));

	//reachability.olg
//	string predName = "link";
//	int argNum = 3;
//	PredicateSchema* scheme = new PredicateSchema(predName, argNum);
//	vector<Term*> args;
//	for (int i = 0;i < argNum;i++)
//	{
//		Variable* newVar = new Variable(Variable::STRING, true);
//		args.push_back(newVar);
//	}
//	//Use index to create formulas;
//	PredicateInstance* pInst = new PredicateInstance(scheme, args);
//	IntVal* value = new IntVal(0);
//	Constraint* ct = new Constraint(Constraint::GT, args[2], value);
//	ConstraintsTemplate* cts = new ConstraintsTemplate();
//	cts->AddConstraint(ct);
//
//	ConsAnnot cat = ConsAnnot(pInst, cts);
//	propSet.insert(ConsAnnotMap::value_type(predName, cat));

	//sdn-mac-learning.olg
	string predName = "initPacket";
	int argNum = 4;
	PredicateSchema* scheme = new PredicateSchema(predName, argNum);
	vector<Term*> args = vector<Term*>();
	for (int i = 0;i < argNum;i++)
	{
		Variable* newVar = new Variable(Variable::STRING, true);
		args.push_back(newVar);
	}
	//Use index to create formulas;
	PredicateInstance* pInst = new PredicateInstance(scheme, args);
	Constraint* ct = new Constraint(Constraint::NEQ, args[0], args[1]);
	Constraint* ct1 = new Constraint(Constraint::EQ, args[0], args[2]);
	Constraint* ct2 = new Constraint(Constraint::NEQ, args[0], args[3]);
	Constraint* ct3 = new Constraint(Constraint::NEQ, args[1], args[3]);
	ConstraintsTemplate* cts = new ConstraintsTemplate();
	cts->AddConstraint(ct);

	ConsAnnot cat = ConsAnnot(pInst, cts);
	propSet.insert(ConsAnnotMap::value_type(predName, cat));

	//Constraint set on a base predicate
	predName = "maxPriority";
	argNum = 2;
	scheme = new PredicateSchema(predName, argNum);
	args = vector<Term*>();
	for (int i = 0;i < argNum;i++)
	{
		Variable* newVar = new Variable(Variable::STRING, true);
		args.push_back(newVar);
	}
	//Use index to create formulas;
	pInst = new PredicateInstance(scheme, args);
	IntVal* value = new IntVal(0);
	ct1 = new Constraint(Constraint::GT, args[0], value);
	ct2 = new Constraint(Constraint::NEQ, args[0], args[1]);
	cts = new ConstraintsTemplate();
	cts->AddConstraint(ct1);
	cts->AddConstraint(ct2);

	cat = ConsAnnot(pInst, cts);
	propSet.insert(ConsAnnotMap::value_type(predName, cat));
	//End of Constraint set on a base predicate

	predName = "ofconn";
	argNum = 2;
	scheme = new PredicateSchema(predName, argNum);
	args = vector<Term*>();
	for (int i = 0;i < argNum;i++)
	{
		Variable* newVar = new Variable(Variable::STRING, true);
		args.push_back(newVar);
	}
	//Use index to create formulas;
	pInst = new PredicateInstance(scheme, args);
	ct1 = new Constraint(Constraint::NEQ, args[0], args[1]);
	cts = new ConstraintsTemplate();
	cts->AddConstraint(ct1);

	cat = ConsAnnot(pInst, cts);
	propSet.insert(ConsAnnotMap::value_type(predName, cat));

	predName = "swToHst";
	argNum = 3;
	scheme = new PredicateSchema(predName, argNum);
	args = vector<Term*>();
	for (int i = 0;i < argNum;i++)
	{
		Variable* newVar = new Variable(Variable::STRING, true);
		args.push_back(newVar);
	}
	//Use index to create formulas;
	pInst = new PredicateInstance(scheme, args);
	ct1 = new Constraint(Constraint::NEQ, args[0], args[1]);
	ct2 = new Constraint(Constraint::NEQ, args[1], args[2]);
	ct3 = new Constraint(Constraint::NEQ, args[0], args[2]);
	cts = new ConstraintsTemplate();
	cts->AddConstraint(ct1);
	cts->AddConstraint(ct2);
	cts->AddConstraint(ct3);

	cat = ConsAnnot(pInst, cts);
	propSet.insert(ConsAnnotMap::value_type(predName, cat));
}

BaseProperty::~BaseProperty()
{
	NS_LOG_FUNCTION("Destruct BaseProperty...");
	ConsAnnotMap::iterator itm;
	for (itm = propSet.begin();itm != propSet.end();itm++)
	{
		ConsAnnot& cat = itm->second;
		delete cat.second;
		delete cat.first;
	}
}

Invariant::Invariant()
{
	invs = AnnotMap();

	//Invariant of reachability
//	NS_LOG_FUNCTION("Generate invariant...");
//	string predName = "path";
//	int argNum = 3;
//	PredicateSchema* scheme = new PredicateSchema(predName, argNum);
//	vector<Term*> args;
//	for (int i = 0;i < argNum;i++)
//	{
//		Variable* newVar = new Variable(Variable::STRING, true);
//		args.push_back(newVar);
//	}
//	//Use index to create formulas;
//	IntVal* value = new IntVal(3);
//	Formula* form = new Constraint(Constraint::GT, args[2], value);
//	PredicateInstance* pInst = new PredicateInstance(scheme, args);
//	Annotation newAnnot = Annotation(pInst, form);
//	invs.insert(AnnotMap::value_type(predName, newAnnot));

//	NS_LOG_FUNCTION("Generate invariant...");
//	string predName = "path";
//	int argNum = 3;
//	PredicateSchema* scheme = new PredicateSchema(predName, argNum);
//	vector<Term*> args;
//	for (int i = 0;i < argNum;i++)
//	{
//		Variable* newVar = new Variable(Variable::STRING, true);
//		args.push_back(newVar);
//	}
//	//Use index to create formulas;
//	IntVal* value = new IntVal(2);
//	Variable* cost = new Variable(Variable::STRING, true);
//	Formula* form1 = new Constraint(Constraint::GT, cost, value);
//	Formula* form2 = new Constraint(Constraint::GT, args[2], cost);
//	Formula* form3 = new Connective(Connective::AND, form1, form2);
//	vector<Variable*> quantArg(1, cost);
//	Formula* form = new Quantifier(Quantifier::EXISTS, quantArg, form3);
//
//	PredicateInstance* pInst = new PredicateInstance(scheme, args);
//	Annotation newAnnot = Annotation(pInst, form);
//	invs.insert(AnnotMap::value_type(predName, newAnnot));


	//Invariant of sdn-mac-learning.olg
	//Begin invariant specification
	NS_LOG_FUNCTION("Generate invariant...");
	string predName = "packet";
	int argNum = 4;
	PredicateSchema* scheme = new PredicateSchema(predName, argNum);
	vector<Term*> args = vector<Term*>();
	for (int i = 0;i < argNum;i++)
	{
		Variable* newVar = new Variable(Variable::STRING, true);
		args.push_back(newVar);
	}
	//Use index to create formulas;
//	Formula* form = new True();
	Formula* formPk1 = new Constraint(Constraint::NEQ, args[0], args[1]);
	Formula* formPk2 = new Constraint(Constraint::NEQ, args[1], args[2]);
	Formula* formPk3 = new Constraint(Constraint::NEQ, args[1], args[3]);
	Formula* formPk4 = new Constraint(Constraint::NEQ, args[2], args[3]);

	Formula* formPkConn1 = new Connective(Connective::AND, formPk1, formPk2);
	Formula* formPkConn2 = new Connective(Connective::AND, formPkConn1, formPk3);
	Formula* formPkConn3 = new Connective(Connective::AND, formPkConn2, formPk4);

	PredicateInstance* pInst = new PredicateInstance(scheme, args);
	Annotation newAnnot = Annotation(pInst, formPkConn3);
	invs.insert(AnnotMap::value_type(predName, newAnnot));
	//End invariant specification

	//Begin invariant specification
	NS_LOG_FUNCTION("Generate invariant...");
	predName = "matchingPacket";
	argNum = 5;
	scheme = new PredicateSchema(predName, argNum);
	args = vector<Term*>();
	for (int i = 0;i < argNum;i++)
	{
		Variable* newVar = new Variable(Variable::STRING, true);
		args.push_back(newVar);
	}
	//Use index to create formulas;
//	form = new True();
	Formula* formMp1 = new Constraint(Constraint::NEQ, args[0], args[1]);
	Formula* formMp2 = new Constraint(Constraint::NEQ, args[0], args[2]);
	Formula* formMp3 = new Constraint(Constraint::NEQ, args[0], args[3]);
	Formula* formMp4 = new Constraint(Constraint::NEQ, args[0], args[4]);
	Formula* formMp5 = new Constraint(Constraint::NEQ, args[1], args[2]);
	Formula* formMp6 = new Constraint(Constraint::NEQ, args[1], args[3]);
	Formula* formMp7 = new Constraint(Constraint::NEQ, args[1], args[4]);
	Formula* formMp8 = new Constraint(Constraint::NEQ, args[2], args[3]);
	Formula* formMp9 = new Constraint(Constraint::NEQ, args[2], args[4]);
	Formula* formMp10 = new Constraint(Constraint::NEQ, args[3], args[4]);

	Formula* formMpConn1 = new Connective(Connective::AND, formMp1, formMp2);
	Formula* formMpConn2 = new Connective(Connective::AND, formMpConn1, formMp3);
	Formula* formMpConn3 = new Connective(Connective::AND, formMpConn2, formMp4);
	Formula* formMpConn4 = new Connective(Connective::AND, formMpConn3, formMp5);
	Formula* formMpConn5 = new Connective(Connective::AND, formMpConn4, formMp6);
	Formula* formMpConn6 = new Connective(Connective::AND, formMpConn5, formMp7);
	Formula* formMpConn7 = new Connective(Connective::AND, formMpConn6, formMp8);
	Formula* formMpConn8 = new Connective(Connective::AND, formMpConn7, formMp9);
	Formula* formMpConn9 = new Connective(Connective::AND, formMpConn8, formMp10);

	pInst = new PredicateInstance(scheme, args);
	newAnnot = Annotation(pInst, formMpConn9);
	invs.insert(AnnotMap::value_type(predName, newAnnot));
	//End invariant specification

	//Begin invariant specification
	NS_LOG_FUNCTION("Generate invariant...");
	predName = "flowEntry";
	argNum = 4;
	scheme = new PredicateSchema(predName, argNum);
	args = vector<Term*>();
	for (int i = 0;i < argNum;i++)
	{
		Variable* newVar = new Variable(Variable::STRING, true);
		args.push_back(newVar);
	}
	//Use index to create formulas;
//	form = new True();
	Formula* formFe1 = new Constraint(Constraint::NEQ, args[0], args[1]);
	Formula* formFe2 = new Constraint(Constraint::NEQ, args[0], args[2]);
	Formula* formFe3 = new Constraint(Constraint::NEQ, args[0], args[3]);
	Formula* formFe4 = new Constraint(Constraint::NEQ, args[1], args[2]);
	Formula* formFe5 = new Constraint(Constraint::NEQ, args[1], args[3]);
	Formula* formFe6 = new Constraint(Constraint::NEQ, args[2], args[3]);

	Formula* formFeConn1 = new Connective(Connective::AND, formFe1, formFe2);
	Formula* formFeConn2 = new Connective(Connective::AND, formFeConn1, formFe3);
	Formula* formFeConn3 = new Connective(Connective::AND, formFeConn2, formFe4);
	Formula* formFeConn4 = new Connective(Connective::AND, formFeConn3, formFe5);
	Formula* formFeConn5 = new Connective(Connective::AND, formFeConn4, formFe6);

	pInst = new PredicateInstance(scheme, args);
	newAnnot = Annotation(pInst, formFeConn5);
	invs.insert(AnnotMap::value_type(predName, newAnnot));
	//End invariant specification

//	NS_LOG_FUNCTION("Generate invariant...");
//	string predName = "verifyPath";
//	int argNum = 9;
//	PredicateSchema* scheme = new PredicateSchema(predName, argNum);
//	vector<Term*> args;
//	for (int i = 0;i < argNum;i++)
//	{
//		Variable* newVar = new Variable(Variable::STRING, true);
//		args.push_back(newVar);
//	}
//	//Use index to create formulas;
//	IntVal* value = new IntVal(0);
//	Formula* form = new Constraint(Constraint::GT, args[0], value);
//	PredicateInstance* pInst = new PredicateInstance(scheme, args);
//	Annotation newAnnot = Annotation(pInst, form);
//	invs.insert(AnnotMap::value_type(predName, newAnnot));

	//  AnnotMap testMap;
	//  list<Variable::TypeCode> tlist (9, Variable::STRING);
	//  Tuple tp = Tuple("verifyPath", tlist);
	//  const vector<Variable*> arg = tp.GetArgs();
	//  vector<Variable*> quantArg(1, arg[0]);
	//  IntVal* value = new IntVal(10000);
	//  Constraint* ct = new Constraint(Constraint::EQ, arg[0], value);
	//  Quantifier qtf (Quantifier::EXISTS, quantArg, ct);
	//  Annotation anno (&tp, &qtf);
	//  testMap.insert(AnnotMap::value_type("verifyPath", &anno));
	NS_LOG_FUNCTION("Invariant generated.");
}

void
Invariant::Print() const
{
	cout << endl;
	cout << "^^^^^^^^^^^^ Invariant Properties ^^^^^^^^^^^^^" << endl;
	AnnotMap::const_iterator ita;
	for (ita = invs.begin();ita != invs.end();ita++)
	{
		const Annotation& annot = ita->second;
		const PredicateInstance* pred = annot.first;
		const Formula* form = annot.second;

		pred->Print();
		cout << endl;
		form->Print();
		cout << endl << endl;
	}
	cout << "^^^^^^^^^^^^^^^^^^^^^^^^^" << endl;
}

Invariant::~Invariant()
{
	AnnotMap::iterator itv;
	for (itv = invs.begin();itv != invs.end();itv++)
	{
		Annotation& annot = itv->second;
		//The order of deletion cannot be reverted,
		//because Formula refers to variables in PredicateInstance
		delete annot.second;
		delete annot.first;
	}

	list<Variable*>::iterator itvl;
	for (itvl = vlist.begin();itvl != vlist.end();itvl++)
	{
		delete (*itvl);
	}
}
