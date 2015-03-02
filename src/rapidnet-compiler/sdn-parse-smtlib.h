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
//std::map<PredicateSchema*, Expr> all_predicate_schemas;
//std::map<FunctionSchema*, Expr> all_function_schemas;

void clearAllVariables() {
	all_free_variables.clear();
}

void printFreeVariablesDeclaration() {
	for (std::map<string,string>::const_iterator it = all_free_variables.begin(); it != all_free_variables.end(); it++) {
	    cout << it->second << endl;
	}
}

string parseFormula(Formula* f) { 
	if (dynamic_cast<PredicateInstance*>(f)) {
		return "";
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
			//return makeVariableType(em, em->booleanType(), isbound, v);
			return "";
		} case Variable::STRING: {
			//return makeVariableType(em, em->stringType(), isbound, v);
			return "";
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
			//return em->mkExpr(kind::GT, leftE, rightE);
		case Constraint::LT:
			//return em->mkExpr(kind::LT, leftE, rightE);
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




string parseBoundVariable(Variable* v) {
	Variable::TypeCode vartype = v->GetVariableType();
	string varname = v->GetVariableName();

	//absent, create and store in hash map
	switch (vartype) {
		case Variable::INT: {
			string declare = "forall ((" + varname + " Int))";
			all_bound_variables[varname] = declare;
			return "";
		} case Variable::DOUBLE: {
			return "";
		} case Variable::BOOL: {
			//return makeVariableType(em, em->booleanType(), isbound, v);
			return "";
		} case Variable::STRING: {
			//return makeVariableType(em, em->stringType(), isbound, v);
			return "";
		} default: {
			return "Not a valid variable type, must be INT/DOUBLE/BOOL/STRING";
		}
	}
}

string parseQuantifier(Quantifier* q) {	
	Formula* f = q->GetQuantifierFormula();
	string f_parsed = parseFormula(f);

	vector<Variable*> bound_var_list = q->GetBoundVariables();

	Quantifier::QuanType qt = q->GetQuantifierType();
	switch (qt) {
		case Quantifier::FORALL: {
			string declare = "";
			return declare;
		} case Quantifier::EXISTS: {
			return "";
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
		if (isbound) return parseBoundVariable(v);
		return parseFreeVariable(v);
	} else if (dynamic_cast<UserFunction*>(t)) {
		//return parseUserFunction(em, (UserFunction*)t);
		return "";
	} else { 
		return parseArithmetic((Arithmetic*)t);
	}
}














