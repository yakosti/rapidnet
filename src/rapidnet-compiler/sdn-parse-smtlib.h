#include <iostream>
#include <string>
#include "sdn-formula.h"
#include <stdio.h>
#include <vector>
#include <algorithm>

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
std::map<string, string> all_predicate_schemas;
//std::map<FunctionSchema*, Expr> all_function_schemas;

void clearAllVariables() {
	all_free_variables.clear();
	all_bound_variables.clear();
}

void printFreeVariablesDeclaration() {
	for (std::map<string,string>::const_iterator it = all_free_variables.begin(); it != all_free_variables.end(); it++) {
	    cout << it->second << endl;
	}
}

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
			return "Not a valid type";
	}
}


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
		default:
			return "Error";
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
			return "Not a valid variable type, must be INT/DOUBLE/BOOL/STRING";
		}
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
			return "Invalid constraint format";
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
			return "Not a valid arithmetic expression";
	}
}

string IntegerToString(int number) {
	std::ostringstream ostr; //output string stream
	ostr << number; 
	std::string theNumberString = ostr.str(); //the str() function of the stream 
	return theNumberString;
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
			string declare = qt + " ((" + varname + " String))";
			all_bound_variables[varname] = declare;
			return varname;
		} default: {
			return "Not a valid variable type, must be INT/DOUBLE/BOOL/STRING";
		}
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
	switch (qt) {
		case Quantifier::FORALL: {
			return makeQuantifierString(f_parsed, bound_var_list, "forall");
		} case Quantifier::EXISTS: {
			return makeQuantifierString(f_parsed, bound_var_list, "exists");
		} default: {
			return "invalid quantifier format";
		}
	}
}


// Parse Terms
// needs bitvector for double integers
string parseTerm(Term* t) {
	if (dynamic_cast<IntVal*>(t)) {
		int value = ((IntVal*)t)->GetIntValue();
	 	return IntegerToString(value);
	} else if (dynamic_cast<BoolVal*>(t)) {
		bool value = ((BoolVal*)t)->GetBoolValue();
	 	if (value) return "true";
	 	return "false";
	} else if (dynamic_cast<StringVal*>(t)) {
		string value = ((StringVal*)t)->GetStringValue();
		return value;
	} else if (dynamic_cast<Variable*>(t)) {
		Variable* v = (Variable*)t;
		bool isbound = v->GetFreeOrBound();
		if (isbound) return v->GetVariableName();
		return parseFreeVariable(v);
	} else if (dynamic_cast<UserFunction*>(t)) {
		//return parseUserFunction(em, (UserFunction*)t);
		return "";
	} else { 
		return parseArithmetic((Arithmetic*)t);
	}
}














