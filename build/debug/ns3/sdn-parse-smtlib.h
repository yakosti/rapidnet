#ifndef SDN_PARSE_SMTLIB_H_
#define SDN_PARSE_SMTLIB_H_

#include <iostream>
#include <string>
#include "sdn-formula.h"
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

//TODO: avoid global variables
extern std::map<string, string> all_free_variables;
extern std::map<string, string> all_bound_variables;
extern std::map<string, string> all_predicate_schemas;
extern std::map<string, string> all_function_schemas;
extern std::map<string, string> all_constants;

// mapping from var to variable
extern std::map<string, Variable*> name_to_rapidnet_variable;

/* 
 * *******************************************************************************
 *                                                                               *
 *                              DECLARE VARIABLES                                *
 *                                                                               *
 * *******************************************************************************
 */

string parseArithmetic(Arithmetic* a);
string parseTerm(Term* t);
string parseFormula(Formula* f);
string parseConstraint(Constraint* c);
string parseConnective(Connective* c);
string parseQuantifier(Quantifier* q);


/* 
 * *******************************************************************************
 *                                                                               *
 *                              HELPER FUNCTIONS                                 *
 *                                                                               *
 * *******************************************************************************
 */

void clearAllVariables();

string IntegerToString(int);

/* likely will delete */
string get_console_output(const char*);

/* 
 * *******************************************************************************
 *                                                                               *
 *                                WRITE TO Z3	                                 *
 *                                                                               *
 * *******************************************************************************
 */


void print_rapidnet_names_and_values(std::map<Variable*, int>);

string truncate_string_at_exclamation(string);

/* map from Z3 model to value */
map<Variable*, int> map_substititions(context &, model);

string variables_declaration_to_str(std::map<string,string>);

map<Variable*, int> checking_with_z3(string);

map<Variable*, int> check_sat(const ConsList&, const FormList&);

map<Variable*, int> check_sat_generalized(const FormList&);

/* To be removed when everything is build out */
void z3_model_test();

/* 
 * *******************************************************************************
 *                                                                               *
 *                                WRITE TO FILE                                  *
 *                                                                               *
 * *******************************************************************************
 */

void writeDeclaration(std::map<string,string>, ofstream&);

void printDeclaration(std::map<string,string>);

const char* dlist_filename(const char*, int);


/* 
 * *******************************************************************************
 *                                                                               *
 *                                    BASE CASE                                  *
 *                                                                               *
 * *******************************************************************************
 */


string parseVariableType(Variable::TypeCode);

/* need to store SMTLIB declaration
 * need to store name->rapidnet variable also
 */
string parseFreeVariable(Variable*);

string parseBoundVariable(Variable*, string);

string parsePredicateSchema(const PredicateSchema*);

string parsePredicateInstance(PredicateInstance*);

string parseFormula(Formula*);

string parseConnective(Connective*);

string parseConstraint(Constraint*);

string parseArithmetic(Arithmetic*);

string makeQuantifierString(string, vector<Variable*>, string);

string parseQuantifier(Quantifier*);

string parseFunctionSchema(FunctionSchema*);


string parsePredicateSchema(const PredicateSchema* s) {
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
	string rightF = "";
	if (c->GetRightF()) {
		rightF = parseFormula(c->GetRightF());
	}
	switch (ct) {
		case Connective::IMPLY:
			return "(=> " + leftF + " " + rightF + ")";
		case Connective::OR:
			return "(or " + leftF + " " + rightF + ")";
		case Connective::AND:
			return "(and " + leftF + " " + rightF + ")";
		case Connective::NOT:
			return "(not " + leftF + ")";
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
		case Constraint::NEQ: 
			return "(not (=" + leftE + " " + rightE + "))";
		case Constraint::GT:
			return "(> " + leftE + " " + rightE + ")";
		case Constraint::GE:
			return "(>= " + leftE + " " + rightE + ")";
		case Constraint::LT:
			return "(< " + leftE + " " + rightE + ")";
		case Constraint::LE:
			return "(<= " + leftE + " " + rightE + ")";
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

string parseUserFunction(UserFunction*);


/* Parse Terms
 * needs bitvector for double integers
 * constants are store here
 */
string parseTerm(Term*);
#endif












