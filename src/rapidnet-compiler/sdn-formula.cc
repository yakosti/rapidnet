/*
 * sdn-formula.cc
 *
 *  Created on: Nov 24, 2014
 *      Author: cchen
 */

#include "sdn-formula.h"
#include <stdexcept>

NS_LOG_COMPONENT_DEFINE ("Formula");


/* ***************************** TERM ************************************** */

int Term::GetValue() { //dummy return
  return 0;
}

void Term::PrintTerm(){}

/* ***************************** TERM ************************************** */






/* ***************************** FORMULA *********************************** */

Connective::Connective(ConnType ct, Formula* formL, Formula* formR):
    conntype(ct), leftF(formL), rightF(formR){}

Connective::Connective(const Connective& ct)
{
	conntype = ct.conntype;
	leftF = ct.leftF->Clone();
	rightF = ct.rightF->Clone();
}

void
Connective::VarReplace(const VarMap& vmap)
{
	leftF->VarReplace(vmap);
	rightF->VarReplace(vmap);
}

Connective*
Connective::Clone()
{
	return (new Connective(*this));
}

Connective::ConnType Connective::GetConnType() {
  return conntype;
}

Formula* Connective::GetLeftF() {
  return leftF;
}

Formula* Connective::GetRightF() {
  return rightF;
}

void
Connective::Print() const
{
	leftF->Print();
	switch (conntype)
	{
	case Connective::IMPLY: cout << " -> ";break;
	case Connective::OR: cout << " \\/ ";break;
	case Connective::AND: cout << " /\\ ";break;
	case Connective::NEG: cout << " NEG ";break;
	}
	rightF->Print();
}

Connective::~Connective()
{
	delete leftF;
	delete rightF;
}

/* ***************************** FORMULA *********************************** */




/* ***************************** Quantifier *********************************** */


Quantifier::Quantifier(QuanType q, const vector<Variable*>& b, Formula* f):
  quantype(q),boundVarList(b),fml(f){}

Quantifier::Quantifier(const Quantifier& qtf)
{
	quantype = qtf.quantype;
	boundVarList = qtf.boundVarList;
	fml = qtf.fml->Clone();
}

void
Quantifier::VarReplace(const VarMap& vmap)
{
	Variable* varSubst = NULL;
	vector<Variable*>::iterator it;
	for (it = boundVarList.begin();it != boundVarList.end();it++)
	{
		VarMap::const_iterator varIt= vmap.find((*it));
		if (varIt != vmap.end())
		{
			(*it) = varIt->second;
		}
	}

	fml->VarReplace(vmap);
}

Quantifier*
Quantifier::Clone()
{
	return (new Quantifier(*this));
}

vector<Variable*>& Quantifier::GetBoundVariables() {
  return boundVarList;
}

Quantifier::QuanType Quantifier::GetQuantifierType() {
  return quantype;
}

Formula* Quantifier::GetQuantifierFormula() {
  return fml;
}

void
Quantifier::Print() const
{
	switch(quantype)
	{
	case Quantifier::FORALL: cout << "forall "; break;
	case Quantifier::EXISTS: cout << "exists "; break;
	}

	vector<Variable*>::const_iterator it;
	for (it = boundVarList.begin();it != boundVarList.end();it++)
	{
		(*it)->PrintTerm();
		cout << ",";
	}

	cout << endl;
	fml->Print();
}

Quantifier::~Quantifier()
{
	delete fml;
}

/* ***************************** Quantifier *********************************** */






/* ************************* PredicateSchema ******************************** */

PredicateSchema::PredicateSchema(string n, vector<Variable::TypeCode>& t):
  name(n),types(t){}

PredicateSchema::PredicateSchema(const PredicateSchema& predSch)
{
	name = predSch.name;
	types = predSch.types;
}

string PredicateSchema::GetName() {
  return name;
}

vector<Variable::TypeCode>& PredicateSchema::GetTypes () {
  return types;
}

void
PredicateSchema::Print() const
{
	cout << name;
}

/* ************************* PredicateSchema ******************************** */








/* ************************* PredicateInstance ******************************** */

PredicateInstance::PredicateInstance(PredicateSchema* s, vector<Term*>& a):
  schema(s),args(a){}

PredicateInstance::PredicateInstance(const PredicateInstance& pred)
{
	schema = new PredicateSchema(*(pred.schema));

	Term* newTerm = NULL;
	vector<Term*>::const_iterator it;
	for (it = args.begin();it != args.end();it++)
	{
		newTerm = (*it)->Clone();
		args.push_back(newTerm);
	}
}

PredicateInstance*
PredicateInstance::Clone()
{
	return (new PredicateInstance(*this));
}

void
PredicateInstance::VarReplace(const VarMap& vmap)
{
	vector<Term*>::iterator it;
	for (it = args.begin();it != args.end();it++)
	{
		(*it)->ReplaceVar(vmap);
	}
}

PredicateSchema* PredicateInstance::GetSchema() {
  return schema;
}

vector<Term*>& PredicateInstance::GetArgs() {
  return args;
}

void
PredicateInstance::Print() const
{
	schema->Print();
	cout << "(";
	vector<Term*>::const_iterator it;
	for (it = args.begin();it != args.end();it++)
	{
		if (it != args.begin())
		{
			cout << ",";
		}

		(*it)->PrintTerm();
	}
	cout << ")";
}

PredicateInstance::~PredicateInstance()
{
	delete schema;
}

/* ************************* PredicateInstance ******************************** */









/* *************************** CONSTRAINT ************************************** */

Constraint::Constraint(Operator opt, Term* exprL, Term* exprR):
    op(opt),leftE(exprL),rightE(exprR){}

Constraint::Constraint(const Constraint& cst)
{
	op = cst.op;
	leftE = cst.leftE->Clone();
	rightE = cst.rightE->Clone();
}

Constraint::~Constraint()
{
	Variable* var = dynamic_cast<Variable*>(leftE);
	if (var == NULL)
	{
		delete leftE;
	}

	var = dynamic_cast<Variable*>(rightE);
	if (var == NULL)
	{
		delete rightE;
	}
}

Constraint*
Constraint::Clone()
{
	return (new Constraint(*this));
}

Constraint::Operator Constraint::GetOperator() {
  return op;
}

Term* Constraint::GetLeftE() {
  return leftE;
}

Term* Constraint::GetRightE() {
  return rightE;
}

void
Constraint::Print() const
{
  NS_LOG_DEBUG("Printing a constraint");
  leftE->PrintTerm();
  PrintOp();
  NS_LOG_DEBUG("Printing the right term");
  rightE->PrintTerm();
}

bool
Constraint::IsEquiv()
{
	return ((op == Constraint::EQ)?true:false);
}

bool
Constraint::IsUnif()
{
	Variable* varL = NULL;
	Variable* varR = NULL;
	varL = dynamic_cast<Variable*>(leftE);
	varR = dynamic_cast<Variable*>(rightE);
	if (varL != NULL && varR != NULL && this->IsEquiv())
	{
		return true;
	}

	return false;

}

void
Constraint::GetVars(vector<Variable*>& vlist)
{
	leftE->GetVars(vlist);
	rightE->GetVars(vlist);
}

void
Constraint::VarReplace(const VarMap& vmap)
{
	VarMap::const_iterator itm;
	Variable* var = dynamic_cast<Variable*>(leftE);
	if (var != NULL)
	{
		itm = vmap.find(var);
		if (itm != vmap.end())
		{
			leftE = itm->second;
		}
	}
	else
	{
		leftE->ReplaceVar(vmap);
	}

	var = dynamic_cast<Variable*>(rightE);
	if (var != NULL)
	{
		itm = vmap.find(var);
		if (itm != vmap.end())
		{
			rightE = itm->second;
		}
	}
	else
	{
		rightE->ReplaceVar(vmap);
	}
}

void
Constraint::VarReplace(UnionFindSet ufs,
					   const map<Variable*, int> varTable,
					   const map<int, Variable*> varRevTable)
{
	Variable* var = NULL;
	int varId = 0;
	int newId = 0;

	var = dynamic_cast<Variable*>(leftE);
	if (var != NULL)
	{
		varId = varTable.at(var);
		newId = ufs.Root(varId);
		Variable* newVar = varRevTable.at(newId);
	}
	else
	{
		leftE->VarReplace(ufs, varTable, varRevTable);
	}

	var = dynamic_cast<Variable*>(rightE);
	if (var != NULL)
	{
		varId = varTable.at(var);
		newId = ufs.Root(varId);
		Variable* newVar = varRevTable.at(newId);
	}
	else
	{
		rightE->VarReplace(ufs, varTable, varRevTable);
	}
}

void
Constraint::PrintOp() const
{
  switch(op){
  case Constraint::EQ:
    cout << "=";
    break;
  case Constraint::NEQ:
    cout << "!=";
    break;
  case Constraint::GT:
    cout << ">";
    break;
  case Constraint::LT:
    cout << "<";
    break;
  }
}

/* *************************** CONSTRAINT ************************************** */





/* **************************** VARIABLE ************************************** */

int Variable::varCount = 0;

/*
* t: BOOL/INT/DOUBLE/STRING type
* b: free or bound variable?
*/
Variable::Variable(TypeCode t, bool b):
		varType(t),isbound(b)
{
	CreateNewVar();
}

Variable::Variable(ParseVar* varPtr, bool b):
		isbound(b)
{
	ValuePtr vPtr = varPtr->value;
	ParsedValue::TypeCode tp = vPtr->GetTypeCode();
	//NS_LOG_DEBUG("Tuple typecode:" << tp);
	if (tp == ParsedValue::STR || tp == ParsedValue::IP_ADDR)
	{
		varType = Variable::STRING;
	}
	if (tp == ParsedValue::DOUBLE)
	{
		varType = Variable::DOUBLE;
	}
	if (tp == ParsedValue::INT32)
	{
		varType = Variable::INT;
	}
	if (tp == ParsedValue::LIST)
	{
		varType = Variable::LIST;
	}

	CreateNewVar();
}

void
Variable::CreateNewVar()
{
	Variable::varCount = Variable::varCount + 1;
	ostringstream countStream;
	countStream << Variable::varCount;
	name =  "variable"+ countStream.str();
}

Variable::TypeCode Variable::GetVariableType() {
  return varType;
}

string Variable::GetVariableName() {
  return name;
}

void Variable::GetVars(vector<Variable*>& vlist)
{
	vlist.push_back(this);
}

void Variable::PrintTerm() {
  cout << name;
}

bool Variable::GetFreeOrBound() {
  return isbound;
}

/* **************************** VARIABLE ************************************** */








/* ************************* FUNCTION SCHEMA ********************************** */

FunctionSchema::FunctionSchema(string n, vector<Variable::TypeCode>& d, Variable::TypeCode r):
  name(n),domain(d),range(r){}

FunctionSchema::FunctionSchema(const FunctionSchema& fs)
{
	name = fs.name;
	domain = fs.domain;
	range = fs.range;
}

FunctionSchema::~FunctionSchema() {}

string FunctionSchema::GetName() {
  return name;
}

vector<Variable::TypeCode>& FunctionSchema::GetDomainTypes() {
  return domain;
}

Variable::TypeCode FunctionSchema::GetRangeType() {
  return range;
}

void FunctionSchema::PrintName() const {
  cout << name;
}

/* ************************* FUNCTION SCHEMA ********************************** */









/* **************************** USER FUNCTION ********************************* */


UserFunction::UserFunction(FunctionSchema* s, vector<Term*>& a):
    schema(s),args(a){}

UserFunction::UserFunction(const UserFunction& uf)
{
	schema = new FunctionSchema(*(uf.schema));
	vector<Term*>::const_iterator itu;
	for (itu = uf.args.begin(); itu != uf.args.end(); itu++)
	{
		args.push_back((*itu)->Clone());
	}
}

void
UserFunction::GetVars(vector<Variable*>& vlist)
{
	vector<Term*>::iterator itv;
	for (itv = args.begin();itv != args.end();itv++)
	{
		(*itv)->GetVars(vlist);
	}
}

UserFunction::~UserFunction()
{
	delete schema;

	vector<Term*>::iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		Variable* var = dynamic_cast<Variable*>((*it));
		if (var == NULL)
		{
			delete (*it);
		}
	}
}

FunctionSchema* UserFunction::GetSchema() {
  return schema;
}

void
UserFunction::VarReplace(const VarMap& vmap)
{
	vector<Term*>::iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		Variable* var = dynamic_cast<Variable*>(*it);
		if (var != NULL)
		{
			VarMap::const_iterator itm = vmap.find(var);
			if (itm != vmap.end())
			{
				(*it) = itm->second;
			}
		}
		else
		{
			(*it)->ReplaceVar(vmap);
		}
	}
}

void
UserFunction::VarReplace(UnionFindSet ufs,
						 const map<Variable*, int> varTable,
						 const map<int, Variable*> varRevTable)
{
	Variable* var = NULL;
	int varId = 0;
	int newId = 0;

	vector<Term*>::iterator itv;
	for (itv = args.begin();itv != args.end();itv++)
	{
		var = dynamic_cast<Variable*>(*itv);
		if (var != NULL)
		{
			varId = varTable.at(var);
			newId = ufs.Root(varId);
			Variable* newVar = varRevTable.at(newId);
			(*itv) = newVar;
		}
		else
		{
			(*itv)->VarReplace(ufs, varTable, varRevTable);
		}
	}
}


vector<Term*>& UserFunction::GetArgs() {
  return args;
}

UserFunction*
UserFunction::Clone()
{
	return (new UserFunction(*this));
}

void UserFunction::PrintTerm() {
  NS_LOG_DEBUG("Printing function...");
  schema->PrintName();
  cout << "(";
  vector<Term*>::iterator it;
  for (it = args.begin(); it != args.end(); it++)
  {
    if (it != args.begin())
    {
      cout << ",";
    }
    (*it)->PrintTerm();
  }
  cout << ")";
}

/* **************************** USER FUNCTION ********************************* */





/* ********************************** IntVal ********************************** */

IntVal::IntVal(int v):value(v){}

IntVal::IntVal(const IntVal& iv)
{
	value = iv.value;
}

int IntVal::GetIntValue() {
  return value;
}

IntVal*
IntVal::Clone()
{
	return (new IntVal(*this));
}

void IntVal::PrintTerm() {
  cout << value;
}

/* ********************************** IntVal ********************************** */






/* ****************************** DoubleVal ********************************** */

DoubleVal::DoubleVal(double v):value(v){}

DoubleVal::DoubleVal(const DoubleVal& dv)
{
	value = dv.value;
}

double DoubleVal::GetDoubleValue() {
  return value;
}

DoubleVal*
DoubleVal::Clone()
{
	return (new DoubleVal(*this));
}

void DoubleVal::PrintTerm() {
  cout << value;
}

/* ****************************** DoubleVal ********************************** */





/* ****************************** StringVal ********************************* */


StringVal::StringVal(string v):value(v){}

StringVal::StringVal(const StringVal& str)
{
	value = str.value;
}

string StringVal::GetStringValue() {
  return value;
}

StringVal*
StringVal::Clone()
{
	return (new StringVal(*this));
}

void StringVal::PrintTerm() {
  cout << "\"" << value << "\"";
}

/* ****************************** StringVal ********************************* */







/* ****************************** BoolVal *********************************** */

BoolVal::BoolVal(double v):value(v){}

BoolVal::BoolVal(const BoolVal& bv)
{
	value = bv.value;
}

bool BoolVal::GetBoolValue() {
  return value;
}

BoolVal*
BoolVal::Clone()
{
	return (new BoolVal(*this));
}

void BoolVal::PrintTerm() {
  cout << value;
}

/* ****************************** BoolVal *********************************** */






/* *************************** Arithmetic *********************************** */

Arithmetic::Arithmetic(ArithOp opt, Term* exprL, Term* exprR):
    op(opt), leftE(exprL), rightE(exprR){}

Arithmetic::Arithmetic(const Arithmetic& ari)
{
	op = ari.op;
	leftE = ari.leftE->Clone();
	rightE = ari.rightE->Clone();
}

Arithmetic::ArithOp Arithmetic::GetArithOp() {
  return op;
}

Term* Arithmetic::GetLeftE() {
  return leftE;
}

Term* Arithmetic::GetRightE() {
  return rightE;
}

Arithmetic*
Arithmetic::Clone()
{
	return (new Arithmetic(*this));
}

void
Arithmetic::ReplaceVar(const VarMap& vmap)
{
	VarMap::const_iterator itm;
	Variable* var = dynamic_cast<Variable*>(leftE);
	if (var != NULL)
	{
		itm = vmap.find(var);
		if (itm != vmap.end())
		{
			leftE = itm->second;
		}
	}
	else
	{
		leftE->ReplaceVar(vmap);
	}

	var = dynamic_cast<Variable*>(rightE);
	if (var != NULL)
	{
		itm = vmap.find(var);
		if (itm != vmap.end())
		{
			rightE = itm->second;
		}
	}
	else
	{
		rightE->ReplaceVar(vmap);
	}
}

void
Arithmetic::VarReplace(UnionFindSet ufs,
					   const map<Variable*, int> varTable,
					   const map<int, Variable*> varRevTable)
{
	Variable* var = NULL;
	int varId = 0;
	int newId = 0;

	var = dynamic_cast<Variable*>(leftE);
	if (var != NULL)
	{
		varId = varTable.at(var);
		newId = ufs.Root(varId);
		Variable* newVar = varRevTable.at(newId);
	}
	else
	{
		leftE->VarReplace(ufs, varTable, varRevTable);
	}

	var = dynamic_cast<Variable*>(rightE);
	if (var != NULL)
	{
		varId = varTable.at(var);
		newId = ufs.Root(varId);
		Variable* newVar = varRevTable.at(newId);
	}
	else
	{
		rightE->VarReplace(ufs, varTable, varRevTable);
	}
}

void
Arithmetic::GetVars(vector<Variable*>& vlist)
{
	leftE->GetVars(vlist);
	rightE->GetVars(vlist);
}

void Arithmetic::PrintTerm() {
  leftE->PrintTerm();
  PrintOp();
  rightE->PrintTerm();
}

void Arithmetic::PrintOp() {
  switch(op){
  case Arithmetic::PLUS:
    cout << "+";
    break;
  case Arithmetic::MINUS:
    cout << "-";
    break;
  case Arithmetic::TIMES:
    cout << "*";
    break;
  case Arithmetic::DIVIDE:
    cout << "/";
    break;
  }  
}

Arithmetic::~Arithmetic()
{
	Variable* var = dynamic_cast<Variable*>(leftE);
	if (var == NULL)
	{
		delete leftE;
	}

	var = dynamic_cast<Variable*>(rightE);
	if (var == NULL)
	{
		delete rightE;
	}
}

/* *************************** Arithmetic *********************************** */













