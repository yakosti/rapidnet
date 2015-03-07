/*
 * sdn-formula.h
 *
 *  Created on: Nov 18, 2014
 *      Author: Chen
 */


#include <vector>
#include <string>
#include <iostream>
#include <sstream>
#include <cvc4/cvc4.h>     
#include "sdn-formula.h"
//#include <typeinfo>

using namespace CVC4;

/* 
 * *************************************************************************** *
 *                                                                             *
 *                              GLOBAL VARIABLES                               *
 *                                                                             *
 * *************************************************************************** *
 */


Expr parseVariable(ExprManager* em, Variable* v);
Expr parseArithmetic(ExprManager* em, Arithmetic* a);
Expr parseTerm(ExprManager* em, Term* t);
Expr parseFormula(ExprManager* em, Formula* f);
Expr parseConnective(ExprManager* em, Connective* c); 

// All seperate variables should have DIFFERENT names
std::map<Variable*, Expr> all_variables;
std::map<PredicateSchema*, Expr> all_predicate_schemas;
std::map<FunctionSchema*, Expr> all_function_schemas;

void clearAllVariables() {
	all_variables.clear();
	all_predicate_schemas.clear();
	all_function_schemas.clear();
}


/* 
 * *************************************************************************** *
 *                                                                             *
 *                                  TRANSLATION                                *
 *                                                                             *
 * *************************************************************************** *
 */

Expr makeVariableType(ExprManager* em, Type varType, bool isbound, Variable* v) {
	string varname = v->GetVariableName();
	if (isbound) {
		Expr var = em->mkBoundVar(varname, varType);
		all_variables[v] = var;
		return var;
	} else {
		Expr var = em->mkVar(varname, varType);
		all_variables[v] = var;
		return var;
	}
}

Expr parseVariable(ExprManager* em, Variable* v) {
	Variable::TypeCode vartype = v->GetVariableType();
	bool isbound = v->GetFreeOrBound();

	//present, return stored variable
	if (all_variables.find(v) != all_variables.end()) return all_variables[v];
	
	//absent, create and store in hash map
	switch (vartype) {
		case Variable::INT: {
			return makeVariableType(em, em->integerType(), isbound, v);
		} case Variable::DOUBLE: {
			return makeVariableType(em, em->realType(), isbound, v);
		} case Variable::BOOL: {
			return makeVariableType(em, em->booleanType(), isbound, v);
		} case Variable::STRING: {
			return makeVariableType(em, em->stringType(), isbound, v);
		} default: {
			throw std::invalid_argument( "Not a valid variable type, must be INT/DOUBLE/BOOL/STRING");
		}
	}
}

Expr parseArithmetic(ExprManager* em, Arithmetic* a) {
	Arithmetic::ArithOp op = a->GetArithOp();
	Expr leftE = parseTerm(em, a->GetLeftE());
	Expr rightE = parseTerm(em, a->GetRightE());
	switch (op) {
		case Arithmetic::PLUS:
			return em->mkExpr(kind::PLUS, leftE, rightE);
		case Arithmetic::MINUS:
			return em->mkExpr(kind::MINUS, leftE, rightE);
		case Arithmetic::TIMES:
			return em->mkExpr(kind::MULT, leftE, rightE);
		case Arithmetic::DIVIDE:
			return em->mkExpr(kind::DIVISION, leftE, rightE);
		default:
			throw std::invalid_argument("Not a valid arithmetic expression");
	}
}




Type parseVariableType(ExprManager* em, Variable::TypeCode v) {
	switch (v) {
		case Variable::INT:
			return em->integerType();
		case Variable::BOOL:
			return em->booleanType();
		case Variable::DOUBLE:
			return em->realType();
		case Variable::STRING:
			return em->stringType();
		default:
			throw std::invalid_argument("Not a valid type");
	}
}


Expr parseFunctionSchema(ExprManager* em, FunctionSchema* s) {
	if (all_function_schemas.find(s) != all_function_schemas.end()) return all_function_schemas[s];

	vector<Variable::TypeCode> domain_types_rapidnet = s->GetDomainTypes();
	vector<Type> domain_types_cvc4;
	for (int i=0; i<domain_types_rapidnet.size(); i++) {
		Type domain_type_cvc4 = parseVariableType(em, domain_types_rapidnet[i]);
		domain_types_cvc4.push_back(domain_type_cvc4); 
	}

	Type range_type_cvc4 = parseVariableType(em, s->GetRangeType());

	Type schema_type_cvc4 = em->mkFunctionType(domain_types_cvc4, range_type_cvc4);
	Expr function_cvc4 = em->mkVar(s->GetName(), schema_type_cvc4); 

	all_function_schemas[s] = function_cvc4;
	return function_cvc4;
}



Expr parseUserFunction(ExprManager* em, UserFunction* uf) {

	Expr user_function_schema_cvc4 = parseFunctionSchema(em, uf->GetSchema());

	vector<Term*> user_function_args_rapidnet = uf->GetArgs();
	vector<Expr> user_function_args_cvc4;
	for (int i=0; i<user_function_args_rapidnet.size(); i++) {
		Expr current_term_cvc4 = parseTerm(em, user_function_args_rapidnet[i]);
		user_function_args_cvc4.push_back(current_term_cvc4);
	}

	Expr user_function_cvc4 = em->mkExpr(kind::APPLY_UF, user_function_schema_cvc4, user_function_args_cvc4);

	return user_function_cvc4;
}

// Parse Terms
// needs bitvector for double integers
Expr parseTerm(ExprManager* em, Term* t) {
	if (dynamic_cast<IntVal*>(t)) {
		int value = ((IntVal*)t)->GetIntValue();
	 	Expr int_exp = em->mkConst(Rational(value));
	 	return int_exp;
	} else if (dynamic_cast<BoolVal*>(t)) {
		bool value = ((BoolVal*)t)->GetBoolValue();
	 	Expr bool_exp = em->mkConst(bool(value));
	 	return bool_exp;
	} else if (dynamic_cast<StringVal*>(t)) {
		string value = ((StringVal*)t)->GetStringValue();
		//std::cout << "String val: " << value << std::endl;
		Expr string_exp = em->mkConst(String(value));
		return string_exp;
	} else if (dynamic_cast<Variable*>(t)) {
		return parseVariable(em, (Variable*)t);
	} else if (dynamic_cast<UserFunction*>(t)) {
		return parseUserFunction(em, (UserFunction*)t);
	} else { 
		return parseArithmetic(em, (Arithmetic*)t);
	}
}


/* *************************************************************************** *
 *                                                                             *
 *                                  TRANSLATION                                *
 *                                                                             *
 * *************************************************************************** *
 */



Expr parseConnective(ExprManager* em, Connective* c) {
	Connective::ConnType ct = c->GetConnType();
	Expr leftF = parseFormula(em, c->GetLeftF());
	Expr rightF = parseFormula(em, c->GetRightF());
	switch (ct) {
		case Connective::IMPLY:
			return em->mkExpr(kind::IMPLIES, leftF, rightF);
		case Connective::OR:
			return em->mkExpr(kind::OR, leftF, rightF);
		case Connective::AND:
			return em->mkExpr(kind::AND, leftF, rightF);
		default:
			return em->mkConst(Rational(0)); //defaul
	}
}

Expr parseQuantifier(ExprManager* em, Quantifier* q) {	
	vector<Variable*> list_rapidnet = q->GetBoundVariables();
	vector<Expr> list_cvc4;
	for (int i=0; i<list_rapidnet.size(); i++) {
		Expr parsed = parseVariable(em, list_rapidnet[i]);
		list_cvc4.push_back(parsed);
	}
	Expr boundVarList = em->mkExpr(kind::BOUND_VAR_LIST, list_cvc4);

	Formula* f = q->GetQuantifierFormula();
	Expr f_parsed = parseFormula(em, f);

	Quantifier::QuanType qt = q->GetQuantifierType();
	switch (qt) {
		case Quantifier::FORALL:
			return em->mkExpr(kind::FORALL, boundVarList, f_parsed);
		case Quantifier::EXISTS:
			return em->mkExpr(kind::EXISTS, boundVarList, f_parsed);
		default:	
			throw std::invalid_argument("invalid quantifier formal");
	}
}


Expr parseConstraint(ExprManager* em, Constraint* c) {
	Constraint::Operator op = c->GetOperator();
	Expr leftE = parseTerm(em, c->GetLeftE());
	Expr rightE = parseTerm(em, c->GetRightE());
	switch (op) {
		case Constraint::EQ: 
			return em->mkExpr(kind::EQUAL, leftE, rightE);
		case Constraint::GT:
			return em->mkExpr(kind::GT, leftE, rightE);
		case Constraint::LT:
			return em->mkExpr(kind::LT, leftE, rightE);
		default:
			throw std::invalid_argument("Invalid constraint format");
	}
}


Expr parsePredicateSchema(ExprManager* em, PredicateSchema* s) {
	if (all_predicate_schemas.find(s) != all_predicate_schemas.end()) return all_predicate_schemas[s];

	vector<Variable::TypeCode> types_rapidnet = s->GetTypes();
	vector<Type> types_cvc4;
	for (int i=0; i<types_rapidnet.size(); i++) {
		Type type_cvc4 = parseVariableType(em, types_rapidnet[i]);
		types_cvc4.push_back(type_cvc4); 
	}

	Type predicateFunction_cvc4 = em->mkPredicateType(types_cvc4);
	Expr predicateVariable_cvc4 = em->mkVar(s->GetName(), predicateFunction_cvc4); 

	all_predicate_schemas[s] = predicateVariable_cvc4;
	return predicateVariable_cvc4;
}



Expr parsePredicateInstance(ExprManager* em, PredicateInstance* pi) {
	Expr schema_cvc4 = parsePredicateSchema(em, pi->GetSchema());

	//parse args
	vector<Term*> args_rapidnet = pi->GetArgs();
	vector<Expr> args_cvc4;
	for (int i=0; i<args_rapidnet.size(); i++) {
		Expr current_term_cvc4 = parseTerm(em, args_rapidnet[i]);
		args_cvc4.push_back(current_term_cvc4);
	}

	return em->mkExpr(kind::APPLY_UF, schema_cvc4, args_cvc4);
}


Expr parseFormula(ExprManager* em, Formula* f) { 
	if (dynamic_cast<PredicateInstance*>(f)) {
		return parsePredicateInstance(em, (PredicateInstance*)f);
	} else if (dynamic_cast<Constraint*>(f)) {
		return parseConstraint(em, (Constraint*)f);
	} else {
		if (dynamic_cast<Quantifier*>(f)) {
			return parseQuantifier(em, (Quantifier*)f);
		} else if (dynamic_cast<Connective*>(f)) {
			return parseConnective(em, (Connective*)f);
		}
	}
}




