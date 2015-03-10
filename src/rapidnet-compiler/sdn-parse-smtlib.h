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
#include "z3++.h"

using namespace z3;
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

std::map<string, Variable*> name_to_rapidnet_free_variable;

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

	name_to_rapidnet_free_variable.clear();
}

string IntegerToString(int number) {
	std::ostringstream ostr; //output string stream
	ostr << number; 
	std::string theNumberString = ostr.str(); //the str() function of the stream 
	return theNumberString;
}

/* likely will delete */
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


void print_rapidnet_names_and_values(std::map<Variable*, int> mymap) {
	for (std::map<Variable*, int>::const_iterator it = mymap.begin(); it != mymap.end(); it++) {
	    cout << (it->first)->GetVariableName() << " = " << it->second << endl;
	}
}


map<Variable*, int> map_substititions(context & c, model m) {
	map<Variable*, int> variable_map;
    for (int i = 0; i < m.size(); i++) {
        func_decl v = m[i];
        symbol name = v.name();
        string namestr = Z3_get_symbol_string(c, name);
        if (v.arity() == 0) { // is a constant 
        	int value = m.get_const_interp(v);
        	Variable* rapidnet_var = name_to_rapidnet_free_variable[namestr];
        	variable_map[rapidnet_var] = value;
        	//std::cout << name << "= " << m.get_const_interp(v) << "\n";
        }
    }
    return variable_map;
}

string variables_declaration_to_str(std::map<string,string> mymap) {
	string str = "";
	for (std::map<string, string>::const_iterator it = mymap.begin(); it != mymap.end(); it++) {
		str += it->second;
	}
	return str;
}

void checking_with_z3(string str_to_check) {
	context c;
	solver s(c);

	Z3_ast parsed = Z3_parse_smtlib2_string(c, str_to_check.c_str(), 0, 0, 0, 0, 0, 0);
    expr e(c, parsed);
    s.add(e); // <--- Add to solver here

    if (s.check() == sat) {
        std::cout << "============== SAT ===============\n";
        model m = s.get_model();
        map<Variable*, int> mapsubst = map_substititions(c, m);
        print_rapidnet_names_and_values(mapsubst);
    } else {
        std::cout << "UNSAT\n";
    }
}

void check_sat(const ConstraintsTemplate* contemp, FormList flist) {
	const ConstraintList& clist = contemp->GetConstraints();

	ConstraintList::const_iterator itc;
	string str_to_check = "(set-option :produce-models true)";
	for (itc = clist.begin(); itc != clist.end(); itc++) {
	    Constraint* newCons = new Constraint((**itc));
	    string constr = parseFormula(newCons);
	    str_to_check += "(assert" + constr + ")";
	}	

	string fvstr = variables_declaration_to_str(all_free_variables);
	string cstr = variables_declaration_to_str(all_constants);
	string bvstr = variables_declaration_to_str(all_bound_variables);
	string pstr = variables_declaration_to_str(all_predicate_schemas);
	string fstr = variables_declaration_to_str(all_function_schemas);
	
	checking_with_z3(fvstr + cstr + bvstr + pstr + fstr + str_to_check);
}


/* Call only at the end 
 */
void write_to_z3(const DerivNodeList& dlist, FormList flist) {
	const DerivNode* deriv = dlist.front();
	const ConstraintsTemplate* contemp = deriv->GetConstraints();
	check_sat(contemp, flist);
}


/* To be removed when everything is build out */
void z3_model_test() {
    std::cout << "z3_parsing_get_model_example\n";

    context c;
    string testing = "(set-option :produce-models true)(set-logic AUFLIA)(declare-fun x () Int)(declare-fun y () Int)(declare-fun z () Int)(declare-fun w () Int)(assert (= x y))(assert (= z w))(assert (distinct x w))";

    Z3_ast parsed = Z3_parse_smtlib2_string(c, testing.c_str(), 0,0,0,0,0,0);
    expr e(c, parsed);

    solver s(c);

    s.add(e); // <--- Add constraints to solver here

    if (s.check() == sat) {
        std::cout << "SAT\n";
    } else {
        std::cout << "UNSAT\n";
    }

    model m = s.get_model();
    std::cout << m << "\n";

    // traversing the model
    for (unsigned i = 0; i < m.size(); i++) {
        func_decl v = m[i];
        // this problem contains only constants
        assert(v.arity() == 0); 
        std::cout << v.name() << " = " << m.get_const_interp(v) << "\n";
    }
}


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
			return "Int";
		default:
			throw std::invalid_argument("Not a valid type, must be INT/BOOL/DOUBLE/STRING");
	}
}

/* need to store SMTLIB declaration
 * need to store name->rapidnet variable also
 */
string parseFreeVariable(Variable* v) {
	Variable::TypeCode vartype = v->GetVariableType();
	string varname = v->GetVariableName();

	//present, return stored variable
	if (all_free_variables.find(varname) != all_free_variables.end()) 
		return varname;
	if (name_to_rapidnet_free_variable.find(varname) != name_to_rapidnet_free_variable.end()) 
		return varname;

	//absent, create and store in hash map
	switch (vartype) {
		case Variable::INT: {
			string declare = "(declare-fun " + varname + " () Int)";
			all_free_variables[varname] = declare;
			name_to_rapidnet_free_variable[varname] = v;
			return varname;
		} case Variable::DOUBLE: {
			string declare = "(declare-fun " + varname + " () Real)";
			all_free_variables[varname] = declare;
			name_to_rapidnet_free_variable[varname] = v;
			return varname;
		} case Variable::BOOL: {
			string declare = "(declare-fun " + varname + " () Bool)";
			all_free_variables[varname] = declare;
			name_to_rapidnet_free_variable[varname] = v;
			return varname;
		} case Variable::STRING: {
			string declare = "(declare-fun " + varname + " () Int)";
			all_free_variables[varname] = declare;
			name_to_rapidnet_free_variable[varname] = v;
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
			string declare = qt + " ((" + varname + " Int))";
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
			all_constants[strvalue] = "(declare-const " + strvalue + " Int";
	 	return strvalue;
	} else if (dynamic_cast<BoolVal*>(t)) {
		bool value = ((BoolVal*)t)->GetBoolValue();
	 	if (value) return "true";
	 	return "false";
	} else if (dynamic_cast<StringVal*>(t)) {
		string value = ((StringVal*)t)->GetStringValue();
		if (all_constants.find(value) == all_constants.end()) //not declared, declare and store
			all_constants[value] = "(declare-const " + value + " Int)";
		return value;
	} else if (dynamic_cast<Variable*>(t)) {
		Variable* v = (Variable*)t;
		bool isbound = v->GetFreeOrBound();
		if (isbound) return v->GetVariableName();
		return parseFreeVariable(v);
	} else if (dynamic_cast<UserFunction*>(t)) {
		return parseUserFunction((UserFunction*)t);
	} else { 
		return parseArithmetic((Arithmetic*)t);
	}
}














