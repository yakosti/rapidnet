#include <iostream>
#include <string>
#include "sdn-formula.h"
#include "sdn-graph.h"
#include "sdn-derivation.h"
#include <stdio.h>
#include <vector>
#include <algorithm>
#include <fstream>
#include <stdexcept>
#include <stdlib.h>
#include <cstring>
#include <memory>
//#include "z3++.h"

using namespace std;

string parseArithmetic(Arithmetic* a);
string parseTerm(Term* t);
string parseFormula(Formula* f);
string parseConstraint(Constraint* c);
string parseConnective(Connective* c);
string parseQuantifier(Quantifier* q);

// All seperate variables should have DIFFERENT names
// (variableName, variableDeclaration)
std::map<string, string> all_free_variables;
std::map<string, string> all_bound_variables;
std::map<string, string> all_constants;
std::map<string, string> all_predicate_schemas;
std::map<string, string> all_function_schemas;

/* 
 * *******************************************************************************
 *                                                                               *
 *                              HELPER FUNCTIONS                                 *
 *                                                                               *
 * *******************************************************************************
 */

void clearAllVariables() {
	all_free_variables.clear();
	all_bound_variables.clear();
	all_constants.clear();
	all_predicate_schemas.clear();
	all_function_schemas.clear();
}

string IntegerToString(int number) {
	std::ostringstream ostr; //output string stream
	ostr << number; 
	std::string theNumberString = ostr.str(); //the str() function of the stream 
	return theNumberString;
}

string get_console_output(const char* filename) {
	char* result = (char*) malloc(100);
	strcpy(result, "cvc4 "); // copy string one into the result.
	strcat(result, filename); // append string two to the result.
	
	FILE* fp = popen(result, "r");
    if (fp == NULL) { 
        throw std::invalid_argument("Reading file failed");
    } 
    char buffer[1028];
    string str = ""; 
    while (fgets(buffer, 1028, fp) != NULL) { 
        str = str + buffer;
    } 
    pclose(fp);
    return str;
}

/* 
 * *******************************************************************************
 *                                                                               *
 *                              HELPER FUNCTIONS                                 *
 *                                                                               *
 * *******************************************************************************
 */



/* 
 * *******************************************************************************
 *                                                                               *
 *                                WRITE TO Z3	                                 *
 *                                                                               *
 * *******************************************************************************
 */

/* WARNING: BUGGY */

// SMTLIB parse_to_z3(const ConstraintTemplate* contemp) {
// 	const ConstraintList& clist = contemp->GetConstraints();

// 	ConstraintList::const_iterator itc;
// 	string all_constraints = "(set-logic AUFIRA)\n";

// 	for (itc = clist.begin(); itc != clist.end(); itc++) {
// 	    Constraint* newCons = new Constraint((**itc));
// 	    string constr = parseFormula(newCons);
// 	    all_constraints = all_constraints + "(assert" + constr + ")\n";
// 	}

// 	all_constraints += "(check-sat)\n";
// 	all_constraints += "(get-model)\n";

// 	return z3.parseSMTLIB2String(all_constraints);
// }

/* Call only at the end 
 */
// void writeToZ3(const DerivNodeList& dlist) {
// 	DerivNodeList::const_iterator itd;

// 	for (itd = dlist.begin(); itd != dlist.end(); itd++) { 

// 		vector<string> all_constraints = parse_one_derivation(*itd);
// 	}
// }

/* 
 * *******************************************************************************
 *                                                                               *
 *                                WRITE TO Z3	                                 *
 *                                                                               *
 * *******************************************************************************
 */





/* 
 * *******************************************************************************
 *                                                                               *
 *                                WRITE TO FILE                                  *
 *                                                                               *
 * *******************************************************************************
 */

 void writeDeclaration(std::map<string,string> mymap, ofstream& myfile) {
	if (myfile.is_open()) {
		for (std::map<string,string>::const_iterator it = mymap.begin(); it != mymap.end(); it++) {
			myfile << it->second + "\n";
		}
	}
}

vector<string> parse_one_derivation(const DerivNode* deriv) {
	deriv->PrintDerivation();
	const ConstraintsTemplate* contemp = deriv->GetConstraints();
	const ConstraintList& clist = contemp->GetConstraints();

	ConstraintList::const_iterator itc;
	vector<string> all_constraints;
	for (itc = clist.begin(); itc != clist.end(); itc++) {
	    Constraint* newCons = new Constraint((**itc));
	    newCons->Print();
	    string constr = parseFormula(newCons);
	    all_constraints.push_back("(assert" + constr + ")\n");
	}
	return all_constraints;
}


void printDeclaration(std::map<string,string> mymap) {
	for (std::map<string,string>::const_iterator it = mymap.begin(); it != mymap.end(); it++) {
	    cout << it->second << endl;
	}
}


const char* dlist_filename(const char* dlist_name, int counter) {
	stringstream temp_str;
	temp_str<<counter;
	std::string str = temp_str.str();
	const char* pchar = str.c_str();
	char* result = (char*)malloc(100);

	strcpy(result, dlist_name); // copy string one into the result.
	strcat(result, pchar); // append string two to the result.
	strcat(result, ".smt2");

	return result;
}


/* Call only at the end 
 */
void writeToFile(const char* filename, const DerivNodeList& dlist) {
	DerivNodeList::const_iterator itd;
	int counter = 0;

	for (itd = dlist.begin(); itd != dlist.end(); itd++) { 
		counter = counter+1;
		
		ofstream myfile;
		const char* dfname = dlist_filename(filename, counter);
		myfile.open(dfname);

		myfile << "(set-logic S)\n"; // type of logic has strings

		vector<string> all_constraints = parse_one_derivation(*itd);

		// print all the variables declarations
		writeDeclaration(all_free_variables, myfile);
		writeDeclaration(all_constants, myfile);
		writeDeclaration(all_bound_variables, myfile);
		writeDeclaration(all_predicate_schemas, myfile);
		writeDeclaration(all_function_schemas, myfile);

		//assert the constraints
		for (int i=0; i<all_constraints.size(); i++) {
			string constrd = all_constraints[i];
			myfile << constrd;
		}
		
		myfile << "(check-sat)\n"; // type of logic has strings

		myfile.close();

		string output = get_console_output(dfname);
  		cout << "result of running cvc4 on file: " << output << endl;
	}
}


/* 
 * *******************************************************************************
 *                                                                               *
 *                                WRITE TO FILE                                  *
 *                                                                               *
 * *******************************************************************************
 */




/* 
 * *******************************************************************************
 *                                                                               *
 *                                    BASE CASE                                  *
 *                                                                               *
 * *******************************************************************************
 */


string parseVariableType(Variable::TypeCode v) {
	switch (v) {
		case Variable::INT:
			return "Int";
		case Variable::BOOL:
			return "Bool";
		case Variable::DOUBLE:
			return "Real";
		case Variable::STRING:
			return "String";
		default:
			throw std::invalid_argument("Not a valid type, must be INT/BOOL/DOUBLE/STRING");
	}
}

string parseFreeVariable(Variable* v) {
	Variable::TypeCode vartype = v->GetVariableType();
	string varname = v->GetVariableName();

	//present, return stored variable
	if (all_free_variables.find(varname) != all_free_variables.end()) return varname;

	//absent, create and store in hash map
	switch (vartype) {
		case Variable::INT: {
			string declare = "(declare-fun " + varname + " () Int)";
			all_free_variables[varname] = declare;
			return varname;
		} case Variable::DOUBLE: {
			string declare = "(declare-fun " + varname + " () Real)";
			all_free_variables[varname] = declare;
			return varname;
		} case Variable::BOOL: {
			string declare = "(declare-fun " + varname + " () Bool)";
			all_free_variables[varname] = declare;
			return varname;
		} case Variable::STRING: {
			string declare = "(declare-fun " + varname + " () String)";
			all_free_variables[varname] = declare;
			return varname;
		} default: {
			throw std::invalid_argument("Not a valid variable type, must be INT/DOUBLE/BOOL/STRING");
		}
	}
}


string parseBoundVariable(Variable* v, string qt) {
	Variable::TypeCode vartype = v->GetVariableType();
	string varname = v->GetVariableName();

	//present, return stored variable
	if (all_bound_variables.find(varname) != all_bound_variables.end()) return varname;

	//absent, create and store in hash map, but return variable name only
	switch (vartype) {
		case Variable::INT: {
			string declare = qt + " ((" + varname + " Int))";
			all_bound_variables[varname] = declare;
			return varname;
		} case Variable::DOUBLE: {
			string declare = qt + " ((" + varname + " Real))";
			all_bound_variables[varname] = declare;
			return varname;
		} case Variable::BOOL: {
			string declare = qt + " ((" + varname + " Bool))";
			all_bound_variables[varname] = declare;
			return varname;
		} case Variable::STRING: {
			//cout << "&&&&&" << varname << endl;
			string declare = qt + " ((" + varname + " String))";
			all_bound_variables[varname] = declare;
			return varname;
		} default: {
			throw std::invalid_argument("Not a valid variable type, must be INT/DOUBLE/BOOL/STRING");
		}
	}
}


/* 
 * *******************************************************************************
 *                                                                               *
 *                                    BASE CASE                                  *
 *                                                                               *
 * *******************************************************************************
 */



string parsePredicateSchema(PredicateSchema* s) {
	string schema_name = s->GetName();
	if (all_predicate_schemas.find(schema_name) != all_predicate_schemas.end()) 
		return all_predicate_schemas[schema_name];

	vector<Variable::TypeCode> types_rapidnet = s->GetTypes();
	string types_smtlib = "";
	for (int i=0; i<types_rapidnet.size(); i++) {
		string type_smtlib = parseVariableType(types_rapidnet[i]);
		types_smtlib = types_smtlib + type_smtlib + " ";
	}

	string predicateVariable_smtlib = "(declare-fun " + schema_name + " (" + types_smtlib + ") Bool)";

	all_predicate_schemas[schema_name] = predicateVariable_smtlib;
	return predicateVariable_smtlib;
}


string parsePredicateInstance(PredicateInstance* pi) {
	string schema_cvc4 = parsePredicateSchema(pi->GetSchema());

	//parse args
	vector<Term*> args_rapidnet = pi->GetArgs();
	string args_smtlib = "";
	for (int i=0; i<args_rapidnet.size(); i++) {
		string current_term_smtlib = parseTerm(args_rapidnet[i]);
		args_smtlib = args_smtlib + current_term_smtlib + " "; 
	}

	string schema_name = (pi->GetSchema())->GetName();
	return "(" + schema_name + " " + args_smtlib + ")";
}


string parseFormula(Formula* f) { 
	if (dynamic_cast<PredicateInstance*>(f)) {
		return parsePredicateInstance((PredicateInstance*)f);
	} else if (dynamic_cast<Constraint*>(f)) {
		return parseConstraint((Constraint*)f);
	} else {
		if (dynamic_cast<Quantifier*>(f)) {
			return parseQuantifier((Quantifier*)f);
		} else if (dynamic_cast<Connective*>(f)) {
			return parseConnective((Connective*)f);
		}
	}
}

string parseConnective(Connective* c) {
	Connective::ConnType ct = c->GetConnType();
	string leftF = parseFormula(c->GetLeftF());
	string rightF = parseFormula(c->GetRightF());
	switch (ct) {
		case Connective::IMPLY:
			return "(=> " + leftF + " " + rightF + ")";
		case Connective::OR:
			return "(or " + leftF + " " + rightF + ")";
		case Connective::AND:
			return "(and " + leftF + " " + rightF + ")";
		case Connective::NEG:
			return "(not " + leftF + " " + rightF + ")";
		default:
			throw std::invalid_argument("Not a valid connective");
	}
}




string parseConstraint(Constraint* c) {
	Constraint::Operator op = c->GetOperator();
	string leftE = parseTerm(c->GetLeftE());
	string rightE = parseTerm(c->GetRightE());
	switch (op) {
		case Constraint::EQ: 
			return "(= " + leftE + " " + rightE + ")";
		case Constraint::GT:
			return "(> " + leftE + " " + rightE + ")";
		case Constraint::LT:
			return "(<" + leftE + " " + rightE + ")";
		default:
			throw std::invalid_argument("Invalid Constraint format");
	}
}

string parseArithmetic(Arithmetic* a) {
	Arithmetic::ArithOp op = a->GetArithOp();
	string leftE = parseTerm(a->GetLeftE());
	string rightE = parseTerm(a->GetRightE());
	switch (op) {
		case Arithmetic::PLUS:
			return "(+ " + leftE + " " + rightE + ")";
		case Arithmetic::MINUS:
			return "(- " + leftE + " " + rightE + ")";
		case Arithmetic::TIMES:
			return "(* " + leftE + " " + rightE + ")";
		case Arithmetic::DIVIDE:
			return "(div " + leftE + " " + rightE + ")";
		default:
			throw std::invalid_argument("Not a valid arithmetic expression");
	}
}

string makeQuantifierString(string parsed_formula, vector<Variable*> bound_var_list, string qt) {
	string declare = "";
	string end_brackets = "";
	for (int i=0; i<bound_var_list.size(); i++) {
		string bound_var_declaration = parseBoundVariable(bound_var_list[i], qt);
		declare = declare + "(" + all_bound_variables.find(bound_var_declaration)->second;
		end_brackets = end_brackets + ")";
	}
	return declare + parsed_formula + end_brackets;
}

string parseQuantifier(Quantifier* q) {	
	Formula* f = q->GetQuantifierFormula();
	string f_parsed = parseFormula(f);
	vector<Variable*> bound_var_list = q->GetBoundVariables();
	Quantifier::QuanType qt = q->GetQuantifierType();
	//cout << "HEY IM A QUANTIFIER" << endl;
	switch (qt) {
		case Quantifier::FORALL: {
			return makeQuantifierString(f_parsed, bound_var_list, "forall");
		} case Quantifier::EXISTS: {
			return makeQuantifierString(f_parsed, bound_var_list, "exists");
		} default: {
			throw std::invalid_argument("invalid quantifier format");
		}
	}
}

string parseFunctionSchema(FunctionSchema* s) {
	string fname = s->GetName();
	if (all_function_schemas.find(fname) != all_function_schemas.end()) return fname;

	vector<Variable::TypeCode> domain_types_rapidnet = s->GetDomainTypes();
	string domain_types_smtlib;
	for (int i=0; i<domain_types_rapidnet.size(); i++) {
		string domain_type_smtlib = parseVariableType(domain_types_rapidnet[i]);
		domain_types_smtlib = domain_types_smtlib + domain_type_smtlib + " ";
	}

	string range_type_smtlib = parseVariableType(s->GetRangeType());
	
	string function_smtlib = "(declare-fun " + fname + " (" + domain_types_smtlib + ") " + range_type_smtlib + ")";
	all_function_schemas[fname] = function_smtlib;
	return fname;
}



string parseUserFunction(UserFunction* uf) {
	string user_function_schema_smtlib = parseFunctionSchema(uf->GetSchema());

	vector<Term*> user_function_args_rapidnet = uf->GetArgs();
	string user_function_args_smtlib = "";
	for (int i=0; i<user_function_args_rapidnet.size(); i++) {
		//cout << "***** " << ((Variable*)user_function_args_rapidnet[i])->GetVariableName() << endl;
		string current_term_cvc4 = parseTerm(user_function_args_rapidnet[i]);
		user_function_args_smtlib = user_function_args_smtlib + current_term_cvc4 + " ";
	}

	string user_function_smtlib = "(" + user_function_schema_smtlib + " " + user_function_args_smtlib + ")";
	return user_function_smtlib;
}


/* Parse Terms
 * needs bitvector for double integers
 * constants are store here
 */
string parseTerm(Term* t) {
	if (dynamic_cast<IntVal*>(t)) {
		int value = ((IntVal*)t)->GetIntValue();
		string strvalue = IntegerToString(value);
		if (all_constants.find(strvalue) == all_constants.end()) //not declared, declare and store
			all_constants[strvalue] = "(declare-const " + strvalue + " String)";
	 	return strvalue;
	} else if (dynamic_cast<BoolVal*>(t)) {
		bool value = ((BoolVal*)t)->GetBoolValue();
	 	if (value) return "true";
	 	return "false";
	} else if (dynamic_cast<StringVal*>(t)) {
		string value = ((StringVal*)t)->GetStringValue();
		if (all_constants.find(value) == all_constants.end()) //not declared, declare and store
			all_constants[value] = "(declare-const " + value + " String)";
		return value;
	} else if (dynamic_cast<Variable*>(t)) {
		Variable* v = (Variable*)t;
		bool isbound = v->GetFreeOrBound();
		if (isbound) {
			//cout << "******** " << v->GetVariableName() << endl;
			return v->GetVariableName();
			//return parseBoundVariable(v);
		}
		return parseFreeVariable(v);
	} else if (dynamic_cast<UserFunction*>(t)) {
		return parseUserFunction((UserFunction*)t);
	} else { 
		return parseArithmetic((Arithmetic*)t);
	}
}














