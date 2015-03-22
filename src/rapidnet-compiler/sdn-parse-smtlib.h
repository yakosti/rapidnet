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

string parseUserFunction(UserFunction*);

/* Parse Terms
 * needs bitvector for double integers
 * constants are store here
 */
string parseTerm(Term*);
#endif












