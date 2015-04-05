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

True*
True::Clone()
{
	return (new True(*this));
}

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

void
Connective::VarReplace(SimpConstraints& simpCon)
{
	leftF->VarReplace(simpCon);
	rightF->VarReplace(simpCon);
}

void
Connective::ArgSwap()
{
	Formula* temp = leftF;
	leftF = rightF;
	rightF = temp;
}

void
Connective::FindFreeVar(list<Variable*>& varList, VarMap& vmap)
{
	leftF->FindFreeVar(varList, vmap);
	rightF->FindFreeVar(varList, vmap);
}

void
Connective::NullifyMem()
{
	leftF = NULL;
	rightF = NULL;
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
	case Connective::NOT: cout << " neg ";break;
	}
	rightF->Print();
}

void
Connective::PrintInst(VarMap& vmap)
{
	leftF->PrintInst(vmap);
	switch (conntype)
	{
	case Connective::IMPLY: cout << " -> ";break;
	case Connective::OR: cout << " \\/ ";break;
	case Connective::AND: cout << " /\\ ";break;
	case Connective::NOT: cout << " neg ";break;
	}
	rightF->PrintInst(vmap);
}

void
Connective::PrintSimpInst(VarMap& vmap, SimpConstraints& simpCons)
{
	leftF->PrintSimpInst(vmap, simpCons);
	switch (conntype)
	{
	case Connective::IMPLY: cout << " -> ";break;
	case Connective::OR: cout << " \\/ ";break;
	case Connective::AND: cout << " /\\ ";break;
	case Connective::NOT: cout << " neg ";break;
	}
	rightF->PrintSimpInst(vmap, simpCons);
}

void
Connective::PrintSimpInstance(const map<Variable*, int>& valueMap, VarMap& vmap,
		   	   	   	   	   	  SimpConstraints& simpCons, bool printVar) const
{
	leftF->PrintSimpInstance(valueMap, vmap, simpCons, printVar);
	switch (conntype)
	{
	case Connective::IMPLY: cout << " -> ";break;
	case Connective::OR: cout << " \\/ ";break;
	case Connective::AND: cout << " /\\ ";break;
	case Connective::NOT: cout << " neg ";break;
	}
	rightF->PrintSimpInstance(valueMap, vmap, simpCons, printVar);
}

Connective::~Connective()
{
	if (leftF != NULL)
	{
		delete leftF;
	}

	if (rightF != NULL)
	{
		delete rightF;
	}
}

/* ***************************** FORMULA *********************************** */




/* ***************************** Quantifier *********************************** */


Quantifier::Quantifier(QuanType q, const vector<Variable*>& b, Formula* f):
  quantype(q),boundVarList(b),fml(f){}

Quantifier::Quantifier(QuanType q, const vector<Variable*>& b, const ConstraintsTemplate* consTemp):
	quantype(q),boundVarList(b)
{
	const ConstraintList& conslist = consTemp->GetConstraints();
	Formula* conjForm = NULL;
	ConstraintList::const_iterator itcs;
	for (itcs = conslist.begin();itcs != conslist.end();itcs++)
	{
		Constraint* cons = new Constraint(**itcs);
		if (conjForm == NULL)
		{
			conjForm = cons;
		}
		else
		{
			conjForm = new Connective(Connective::AND, conjForm, cons);
		}
	}

	fml = conjForm;
}

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

void
Quantifier::VarReplace(SimpConstraints& simpCon)
{
	vector<Variable*>::iterator itv;
	for (itv = boundVarList.begin();itv != boundVarList.end();itv++)
	{
		Variable* newVar = simpCon.FindRootVar(*itv);
		if (newVar != NULL)
		{
			*itv = newVar;
		}
	}
	fml->VarReplace(simpCon);
}

void
Quantifier::FindFreeVar(list<Variable*>& varList, VarMap& vmap)
{
	vector<Variable*>::iterator itv;
	for (itv = boundVarList.begin();itv != boundVarList.end();itv++)
	{
		Variable* newVar = new Variable(Variable::STRING, true);
		vmap.insert(VarMap::value_type(*itv, newVar));
	}
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

void
Quantifier::PrintInst(VarMap& vmap)
{
	switch(quantype)
	{
	case Quantifier::FORALL: cout << "forall "; break;
	case Quantifier::EXISTS: cout << "exists "; break;
	}

	vector<Variable*>::const_iterator it;
	for (it = boundVarList.begin();it != boundVarList.end();it++)
	{
		Variable* instVar = vmap.at(*it);
		instVar->PrintTerm();
		cout << ",";
	}

	cout << endl;
	fml->PrintInst(vmap);
}


void
Quantifier::PrintSimpInst(VarMap& vmap, SimpConstraints& simpCons)
{
	switch(quantype)
	{
	case Quantifier::FORALL: cout << "forall "; break;
	case Quantifier::EXISTS: cout << "exists "; break;
	}

	vector<Variable*>::const_iterator it;
	for (it = boundVarList.begin();it != boundVarList.end();it++)
	{
		Variable* instVar = vmap.at(*it);
		Variable* simpVar = simpCons.FindRootVar(instVar);
		simpVar->PrintTerm();
		cout << ",";
	}

	cout << endl;
	fml->PrintSimpInst(vmap, simpCons);
}

void
Quantifier::PrintSimpInstance(const map<Variable*, int>& valueMap, VarMap& vmap,
		   	   	   	      	  SimpConstraints& simpCons, bool printVar) const
{
	switch(quantype)
	{
	case Quantifier::FORALL: cout << "forall "; break;
	case Quantifier::EXISTS: cout << "exists "; break;
	}

	vector<Variable*>::const_iterator it;
	for (it = boundVarList.begin();it != boundVarList.end();it++)
	{
		Variable* instVar = vmap.at(*it);
		instVar->PrintTerm();
		cout << ",";
	}

	cout << endl;
	fml->PrintSimpInstance(valueMap, vmap, simpCons, printVar);
}

Quantifier::~Quantifier()
{
	if (fml != NULL)
	{
		delete fml;
	}
}

/* ***************************** Quantifier *********************************** */






/* ************************* PredicateSchema ******************************** */

PredicateSchema::PredicateSchema(string n, int size):
		name(n)
{
	for (int i = 0;i < size;i++)
	{
		types.push_back(Variable::STRING);
	}
}

PredicateSchema::PredicateSchema(string n, vector<Variable::TypeCode>& t):
  name(n),types(t){}

PredicateSchema::PredicateSchema(const PredicateSchema& predSch)
{
	name = predSch.name;
	types = predSch.types;
}

string PredicateSchema::GetName() const{
  return name;
}

const vector<Variable::TypeCode>& PredicateSchema::GetTypes () const{
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

string
PredicateInstance::GetName() const
{
	return schema->GetName();
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

const PredicateSchema* PredicateInstance::GetSchema() const{
  return schema;
}

const vector<Term*>& PredicateInstance::GetArgs() const{
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

void
PredicateInstance::PrintInst(VarMap& vmap)
{
	cout << schema->GetName();
	cout << "(";
	vector<Term*>::iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		if (it != args.begin())
		{
			cout << ",";
		}
		Variable* argVar = dynamic_cast<Variable*>(*it);
		Variable* instVar = vmap.at(argVar);
		instVar->PrintTerm();
	}
	cout << ")";
}


void
PredicateInstance::PrintSimpInst(VarMap& vmap, SimpConstraints& simpCons)
{
	cout << schema->GetName();
	cout << "(";
	vector<Term*>::iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		if (it != args.begin())
		{
			cout << ",";
		}
		Variable* argVar = dynamic_cast<Variable*>(*it);
		Variable* instVar = vmap.at(argVar);
		Variable* simpVar = simpCons.FindRootVar(instVar);
		simpVar->PrintTerm();
	}
	cout << ")";
}

void
PredicateInstance::PrintSimpInstance(const map<Variable*, int>& valueMap, VarMap& vmap,
						   	   	   	 SimpConstraints& simpCons, bool printVar) const
{
	cout << schema->GetName();
	cout << "(";
	vector<Term*>::const_iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		if (it != args.begin())
		{
			cout << ",";
		}
		Variable* argVar = dynamic_cast<Variable*>(*it);
		Variable* instVar = vmap.at(argVar);
		Variable* simpVar = simpCons.FindRootVar(instVar);
		if (printVar == true)
		{
			cout << "(";
			simpVar->PrintTerm();
			cout << ")";
		}
		map<Variable*, int>::const_iterator itm =  valueMap.find(simpVar);
		if (itm != valueMap.end())
		{
			cout << itm->second;
		}
		else
		{
			simpVar->PrintTerm();
		}
	}
	cout << ")";
}

PredicateInstance::~PredicateInstance()
{
	delete schema;
	vector<Term*>::iterator itv;
	for (itv = args.begin();itv != args.end();itv++)
	{
		delete (*itv);
	}
}

/* ************************* PredicateInstance ******************************** */









/* *************************** CONSTRAINT ************************************** */

Constraint::Constraint(Operator opt, Term* exprL, Term* exprR):
    op(opt),leftE(exprL),rightE(exprR)
{
	NS_LOG_FUNCTION("Constraint default constructor." << this);
}

Constraint::Constraint(const Constraint& cst)
{
	NS_LOG_FUNCTION("Constraint copy constructor." << this);
	op = cst.op;
	leftE = cst.leftE->Clone();
	rightE = cst.rightE->Clone();
}

Constraint::~Constraint()
{
	NS_LOG_FUNCTION("Destruct Constraint: " << this);
	//this->Print();
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

Constraint*
Constraint::Revert() const
{
	Operator newOp;
	switch (op)
	{
	case Constraint::EQ: newOp = Constraint::NEQ; break;
	case Constraint::NEQ: newOp = Constraint::EQ; break;
	case Constraint::GT: newOp = Constraint::LE; break;
	case Constraint::GE: newOp = Constraint::LT; break;
	case Constraint::LT: newOp = Constraint::GE; break;
	case Constraint::LE: newOp = Constraint::GT; break;
	}

	Term* newLeftE = leftE->Clone();
	Term* newRightE = rightE->Clone();
	return (new Constraint(newOp, newLeftE, newRightE));
}

Term* Constraint::GetRightE() {
  return rightE;
}

void
Constraint::Print() const
{
	leftE->PrintTerm();
	PrintOp();
	rightE->PrintTerm();
}

void
Constraint::PrintInst(VarMap& vmap)
{
	Variable* var = NULL;
	var = dynamic_cast<Variable*>(leftE);
	if (var == NULL)
	{
		leftE->PrintInst(vmap);
	}
	else
	{
		Variable* instLeftVar = vmap.at(var);
		instLeftVar->PrintTerm();
	}

	PrintOp();

	var = dynamic_cast<Variable*>(rightE);
	if (var == NULL)
	{
		rightE->PrintInst(vmap);
	}
	else
	{
		Variable* instRightVar = vmap.at(var);
		instRightVar->PrintTerm();
	}
}


void
Constraint::PrintSimpInst(VarMap& vmap, SimpConstraints& simpCons)
{
	Variable* var = NULL;
	var = dynamic_cast<Variable*>(leftE);
	if (var == NULL)
	{
		leftE->PrintSimpInst(vmap, simpCons);
	}
	else
	{
		Variable* instLeftVar = vmap.at(var);
		Variable* simpLeftVar = simpCons.FindRootVar(instLeftVar);
		simpLeftVar->PrintTerm();
	}

	PrintOp();

	var = dynamic_cast<Variable*>(rightE);
	if (var == NULL)
	{
		rightE->PrintSimpInst(vmap, simpCons);
	}
	else
	{
		Variable* instRightVar = vmap.at(var);
		Variable* simpRightVar = simpCons.FindRootVar(instRightVar);
		simpRightVar->PrintTerm();
	}
}


void
Constraint::PrintInstance(const map<Variable*, int>& valueMap, bool printVar) const
{
	Variable* var = NULL;
	int value = 0;
	var = dynamic_cast<Variable*>(leftE);
	if (var == NULL)
	{
		leftE->PrintInstance(valueMap, printVar);
	}
	else
	{
		map<Variable*, int>::const_iterator itm =  valueMap.find(var);
		if (itm != valueMap.end())
		{
			cout << itm->second;
		}
		else
		{
			var->PrintTerm();
		}
	}

	PrintOp();

	var = dynamic_cast<Variable*>(rightE);
	if (var == NULL)
	{
		rightE->PrintInstance(valueMap, printVar);
	}
	else
	{
		map<Variable*, int>::const_iterator itm =  valueMap.find(var);
		if (itm != valueMap.end())
		{
			cout << itm->second;
		}
		else
		{
			var->PrintTerm();
		}
	}
}

void
Constraint::PrintInstance(const map<Variable*, int>& valueMap, VarMap& vmap, bool printVar) const
{
	Variable* var = NULL;
	int value = 0;
	var = dynamic_cast<Variable*>(leftE);
	if (var == NULL)
	{
		leftE->PrintInstance(valueMap, vmap, printVar);
	}
	else
	{
		Variable* instVar = vmap.at(var);
		value = valueMap.at(instVar);
		if (printVar == true)
		{
			cout << "(";
			instVar->PrintTerm();
			cout << ")";
		}
		cout << value;
	}

	PrintOp();

	var = dynamic_cast<Variable*>(rightE);
	if (var == NULL)
	{
		rightE->PrintInstance(valueMap, vmap, printVar);
	}
	else
	{
		Variable* instVar = vmap.at(var);
		value = valueMap.at(instVar);
		if (printVar == true)
		{
			cout << "(";
			instVar->PrintTerm();
			cout << ")";
		}
		cout << value;
	}
}

bool
Constraint::IsEquiv() const
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
	map<Variable*, int>::const_iterator itm;

	var = dynamic_cast<Variable*>(leftE);
	if (var != NULL)
	{
		itm = varTable.find(var);
		if (itm != varTable.end())
		{
			varId = itm->second;
			newId = ufs.Root(varId);
			Variable* newVar = varRevTable.at(newId);
			leftE = newVar;
		}
		else
		{
			NS_LOG_ERROR("Variable not found in Union Find Set!");
		}
	}
	else
	{
		leftE->VarReplace(ufs, varTable, varRevTable);
	}

	var = dynamic_cast<Variable*>(rightE);
	if (var != NULL)
	{
		itm = varTable.find(var);
		if (itm != varTable.end())
		{
			varId = itm->second;
			newId = ufs.Root(varId);
			Variable* newVar = varRevTable.at(newId);
			rightE = newVar;
		}
		else
		{
			NS_LOG_ERROR("Variable not found in Union Find Set!");
		}
	}
	else
	{
		rightE->VarReplace(ufs, varTable, varRevTable);
	}
}

void
Constraint::VarReplace(SimpConstraints& simpCons)
{
	VarReplace(simpCons.GetUnionFindSet(),
			   simpCons.GetVarTable(),
			   simpCons.GetRevTable());
}

void
Constraint::CreateVarInst(VarMap& vmap)
{
	Variable* var = dynamic_cast<Variable*>(leftE);
	if (var != NULL)
	{
		if (vmap.find(var) == vmap.end())
		{
			Variable* newVar = new Variable(Variable::STRING, false);
			vmap.insert(VarMap::value_type(var, newVar));
		}
	}

	var = dynamic_cast<Variable*>(rightE);
	if (var != NULL)
	{
		if (vmap.find(var) == vmap.end())
		{
			Variable* newVar = new Variable(Variable::STRING, false);
			vmap.insert(VarMap::value_type(var, newVar));
		}
	}
}

void
Constraint::FindFreeVar(list<Variable*>& varList, VarMap& vmap)
{
	list<Variable*>::iterator itlv;
	Variable* var = dynamic_cast<Variable*>(leftE);
	if (var != NULL)
	{
		bool leftFlag = false;
		for (itlv = varList.begin();itlv != varList.end();itlv++)
		{
			if (*itlv == var)
			{
				leftFlag = true;
				break;
			}
		}

		if (leftFlag == false)
		{
			VarMap::iterator itvm = vmap.find(var);
			if (itvm == vmap.end())
			{
				Variable* newVar = new Variable(Variable::STRING, false);
				vmap.insert(VarMap::value_type(var, newVar));
			}
		}
	}
	else
	{
		leftE->FindReplaceFreeVar(varList, vmap);
	}

	var = dynamic_cast<Variable*>(rightE);
	if (var != NULL)
	{
		bool rightFlag = false;
		for (itlv = varList.begin();itlv != varList.end();itlv++)
		{
			if (*itlv == var)
			{
				rightFlag = true;
				break;
			}
		}

		if (rightFlag == false)
		{
			VarMap::iterator itvm = vmap.find(var);
			if (itvm == vmap.end())
			{
				Variable* newVar = new Variable(Variable::STRING, false);
				vmap.insert(VarMap::value_type(var, newVar));
			}
		}
	}
	else
	{
		rightE->FindReplaceFreeVar(varList, vmap);
	}
}

void
Constraint::PrintSimpInstance(const map<Variable*, int>& valueMap, VarMap& vmap,
							  SimpConstraints& simpCons, bool printVar) const
{
	Variable* var = NULL;
	var = dynamic_cast<Variable*>(leftE);
	if (var == NULL)
	{
		leftE->PrintSimpInstance(valueMap, vmap, simpCons, printVar);
	}
	else
	{
		Variable* instLeftVar = vmap.at(var);
		Variable* simpLeftVar = simpCons.FindRootVar(instLeftVar);
		map<Variable*, int>::const_iterator itm =  valueMap.find(simpLeftVar);
		if (itm != valueMap.end())
		{
			if (printVar == true)
			{
				cout << "(";
				simpLeftVar->PrintTerm();
				cout << ")";
			}

			cout << itm->second;
		}
		else
		{
			simpLeftVar->PrintTerm();
		}
	}

	PrintOp();

	var = dynamic_cast<Variable*>(rightE);
	if (var == NULL)
	{
		rightE->PrintSimpInstance(valueMap, vmap, simpCons, printVar);
	}
	else
	{
		Variable* instRightVar = vmap.at(var);
		Variable* simpRightVar = simpCons.FindRootVar(instRightVar);
		map<Variable*, int>::const_iterator itm =  valueMap.find(simpRightVar);
		if (itm != valueMap.end())
		{
			if (printVar == true)
			{
				cout << "(";
				simpRightVar->PrintTerm();
				cout << ")";
			}

			cout << itm->second;
		}
		else
		{
			simpRightVar->PrintTerm();
		}
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
  case Constraint::GE:
      cout << ">=";
      break;
  case Constraint::LT:
    cout << "<";
    break;
  case Constraint::LE:
      cout << "<=";
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
	name =  "var"+ countStream.str();
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

void
UserFunction::CreateVarInst(VarMap& vmap)
{
	vector<Term*>::iterator itv;
	for (itv = args.begin();itv != args.end();itv++)
	{
		Variable* var = dynamic_cast<Variable*>(*itv);
		if (var != NULL)
		{
			if (vmap.find(var) == vmap.end())
			{
				Variable* newVar = new Variable(Variable::STRING, false);
				vmap.insert(VarMap::value_type(var, newVar));
			}
		}
	}
}

void
UserFunction::FindReplaceFreeVar(list<Variable*>& varList, VarMap& vmap)
{
	vector<Term*>::iterator itv;
	for (itv = args.begin();itv != args.end();itv++)
	{
		Variable* var = dynamic_cast<Variable*>(*itv);
		if (var != NULL)
		{
			bool leftFlag = false;
			list<Variable*>::iterator itlv;
			for (itlv = varList.begin();itlv != varList.end();itlv++)
			{
				if (*itlv == var)
				{
					leftFlag = true;
					break;
				}
			}

			if (leftFlag == false)
			{
				VarMap::iterator itvm = vmap.find(var);
				if (itvm == vmap.end())
				{
					Variable* newVar = new Variable(Variable::STRING, false);
					vmap.insert(VarMap::value_type(var, newVar));
				}
			}
		}
	}
}

void
UserFunction::PrintInst(VarMap& vmap)
{
	schema->PrintName();
	cout << "(";
	vector<Term*>::iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		if (it != args.begin())
		{
			cout << ",";
		}
		Variable* argVar = dynamic_cast<Variable*>(*it);
		Variable* instVar = vmap.at(argVar);
		instVar->PrintTerm();
	}
	cout << ")";
}


void
UserFunction::PrintSimpInst(VarMap& vmap, SimpConstraints& simpCons)
{
	schema->PrintName();
	cout << "(";
	vector<Term*>::iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		if (it != args.begin())
		{
			cout << ",";
		}
		Variable* argVar = dynamic_cast<Variable*>(*it);
		Variable* instVar = vmap.at(argVar);
		Variable* simpVar = simpCons.FindRootVar(instVar);
		simpVar->PrintTerm();
	}
	cout << ")";
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

void
UserFunction::PrintInstance(const map<Variable*, int>& valueMap, bool printVar) const
{
	schema->PrintName();
	cout << "(";
	Variable* var = NULL;
	vector<Term*>::const_iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		if (it != args.begin())
		{
		  cout << ",";
		}
		var = dynamic_cast<Variable*>(*it);
		if (var == NULL)
		{
			(*it)->PrintInstance(valueMap, printVar);
		}
		else
		{
			int value = valueMap.at(var);
			cout << value;
		}
	}
	cout << ")";
}

void
UserFunction::PrintInstance(const map<Variable*, int>& valueMap, VarMap& vmap, bool printVar) const
{
	schema->PrintName();
	cout << "(";
	Variable* var = NULL;
	vector<Term*>::const_iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		if (it != args.begin())
		{
		  cout << ",";
		}
		var = dynamic_cast<Variable*>(*it);
		if (var == NULL)
		{
			(*it)->PrintInstance(valueMap, vmap, printVar);
		}
		else
		{
			Variable* instVar = vmap.at(var);
			int value = valueMap.at(instVar);
			cout << value;
		}
	}
	cout << ")";
}

void
UserFunction::PrintSimpInstance(const map<Variable*, int>& valueMap, VarMap& vmap,
		     	 	 	 	 	SimpConstraints& simpCons, bool printVar) const
{
	schema->PrintName();
	cout << "(";
	Variable* var = NULL;
	vector<Term*>::const_iterator it;
	for (it = args.begin(); it != args.end(); it++)
	{
		if (it != args.begin())
		{
		  cout << ",";
		}
		var = dynamic_cast<Variable*>(*it);
		if (var == NULL)
		{
			(*it)->PrintInstance(valueMap, vmap, printVar);
		}
		else
		{
			Variable* argVar = dynamic_cast<Variable*>(*it);
			Variable* instVar = vmap.at(argVar);
			Variable* simpVar = simpCons.FindRootVar(instVar);
			if (printVar == true)
			{
				cout << "(";
				simpVar->PrintTerm();
				cout << ")";
			}
			int value = valueMap.at(simpVar);
			cout << value;
		}
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

void
IntVal::PrintInstance(const map<Variable*, int>& valueMap, bool printVar) const
{
	cout << value;
}

void
IntVal::PrintInstance(const map<Variable*, int>& valueMap, VarMap& vmap, bool printVar) const
{
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

void
DoubleVal::PrintInstance(const map<Variable*, int>& valueMap, bool printVar) const
{
	cout << value;
}

void
DoubleVal::PrintInstance(const map<Variable*, int>& valueMap, VarMap& vmap, bool printVar) const
{
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

void
StringVal::PrintInstance(const map<Variable*, int>& valueMap, bool printVar) const
{
	cout << value;
}

void
StringVal::PrintInstance(const map<Variable*, int>& valueMap, VarMap& vmap, bool printVar) const
{
	cout << value;
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

void
BoolVal::PrintInstance(const map<Variable*, int>& valueMap, bool printVar) const
{
	cout << value;
}

void
BoolVal::PrintInstance(const map<Variable*, int>& valueMap, VarMap& vmap, bool printVar) const
{
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
Arithmetic::CreateVarInst(VarMap& vmap)
{
	Variable* var = dynamic_cast<Variable*>(leftE);
	if (var != NULL)
	{
		if (vmap.find(var) == vmap.end())
		{
			Variable* newVar = new Variable(Variable::STRING, false);
			vmap.insert(VarMap::value_type(var, newVar));
		}
	}

	var = dynamic_cast<Variable*>(rightE);
	if (var != NULL)
	{
		if (vmap.find(var) == vmap.end())
		{
			Variable* newVar = new Variable(Variable::STRING, false);
			vmap.insert(VarMap::value_type(var, newVar));
		}
	}
}


void
Arithmetic::GetVars(vector<Variable*>& vlist)
{
	leftE->GetVars(vlist);
	rightE->GetVars(vlist);
}

void
Arithmetic::FindReplaceFreeVar(list<Variable*>& varList, VarMap& vmap)
{
	list<Variable*>::iterator itlv;
	Variable* var = dynamic_cast<Variable*>(leftE);
	if (var != NULL)
	{
		bool leftFlag = false;
		for (itlv = varList.begin();itlv != varList.end();itlv++)
		{
			if (*itlv == var)
			{
				leftFlag = true;
				break;
			}
		}

		if (leftFlag == false)
		{
			VarMap::iterator itvm = vmap.find(var);
			if (itvm == vmap.end())
			{
				Variable* newVar = new Variable(Variable::STRING, false);
				vmap.insert(VarMap::value_type(var, newVar));
			}
		}
	}
	else
	{
		leftE->FindReplaceFreeVar(varList, vmap);
	}

	var = dynamic_cast<Variable*>(rightE);
	if (var != NULL)
	{
		bool rightFlag = false;
		for (itlv = varList.begin();itlv != varList.end();itlv++)
		{
			if (*itlv == var)
			{
				rightFlag = true;
				break;
			}
		}

		if (rightFlag == false)
		{
			VarMap::iterator itvm = vmap.find(var);
			if (itvm == vmap.end())
			{
				Variable* newVar = new Variable(Variable::STRING, false);
				vmap.insert(VarMap::value_type(var, newVar));
			}
		}
	}
	else
	{
		rightE->FindReplaceFreeVar(varList, vmap);
	}
}

void Arithmetic::PrintTerm() {
  leftE->PrintTerm();
  PrintOp();
  rightE->PrintTerm();
}

void
Arithmetic::PrintInst(VarMap& vmap)
{
	Variable* var = NULL;
	var = dynamic_cast<Variable*>(leftE);
	if (var == NULL)
	{
		leftE->PrintInst(vmap);
	}
	else
	{
		Variable* instLeftVar = vmap.at(var);
		instLeftVar->PrintTerm();

	}

	PrintOp();

	var = dynamic_cast<Variable*>(rightE);
	if (var == NULL)
	{
		rightE->PrintInst(vmap);
	}
	else
	{
		Variable* instRightVar = vmap.at(var);
		instRightVar->PrintTerm();
	}
}


void
Arithmetic::PrintSimpInst(VarMap& vmap, SimpConstraints& simpCons)
{
	Variable* var = NULL;
	var = dynamic_cast<Variable*>(leftE);
	if (var == NULL)
	{
		leftE->PrintSimpInst(vmap, simpCons);
	}
	else
	{
		Variable* instLeftVar = vmap.at(var);
		Variable* simpLeftVar = simpCons.FindRootVar(instLeftVar);
		simpLeftVar->PrintTerm();

	}

	PrintOp();

	var = dynamic_cast<Variable*>(rightE);
	if (var == NULL)
	{
		rightE->PrintSimpInst(vmap, simpCons);
	}
	else
	{
		Variable* instRightVar = vmap.at(var);
		Variable* simpRightVar = simpCons.FindRootVar(instRightVar);
		simpRightVar->PrintTerm();
	}
}

void
Arithmetic::PrintInstance(const map<Variable*, int>& valueMap, bool printVar) const
{
	Variable* var = NULL;
	int value = 0;
	var = dynamic_cast<Variable*>(leftE);
	if (var == NULL)
	{
		leftE->PrintInstance(valueMap, printVar);
	}
	else
	{
		value = valueMap.at(var);
		cout << value;
	}

	PrintOp();

	var = dynamic_cast<Variable*>(rightE);
	if (var == NULL)
	{
		rightE->PrintInstance(valueMap, printVar);
	}
	else
	{
		value = valueMap.at(var);
		cout << value;
	}
}

void
Arithmetic::PrintInstance(const map<Variable*, int>& valueMap, VarMap& vmap, bool printVar) const
{
	Variable* var = NULL;
	int value = 0;
	var = dynamic_cast<Variable*>(leftE);
	if (var == NULL)
	{
		leftE->PrintInstance(valueMap, vmap, printVar);
	}
	else
	{
		Variable* instVar = vmap.at(var);
		value = valueMap.at(instVar);
		cout << value;
	}

	PrintOp();

	var = dynamic_cast<Variable*>(rightE);
	if (var == NULL)
	{
		rightE->PrintInstance(valueMap, vmap, printVar);
	}
	else
	{
		Variable* instVar = vmap.at(var);
		value = valueMap.at(instVar);
		cout << value;
	}
}

void
Arithmetic::PrintSimpInstance(const map<Variable*, int>& valueMap, VarMap& vmap,
							  SimpConstraints& simpCons, bool printVar) const
{
	Variable* var = NULL;
	var = dynamic_cast<Variable*>(leftE);
	if (var == NULL)
	{
		leftE->PrintSimpInstance(valueMap, vmap, simpCons, printVar);
	}
	else
	{
		Variable* instLeftVar = vmap.at(var);
		Variable* simpLeftVar = simpCons.FindRootVar(instLeftVar);
		if (printVar == true)
		{
			cout << "(";
			simpLeftVar->PrintTerm();
			cout << ")";
		}
		int value = valueMap.at(simpLeftVar);
		cout << value;
	}

	PrintOp();

	var = dynamic_cast<Variable*>(rightE);
	if (var == NULL)
	{
		rightE->PrintSimpInstance(valueMap, vmap, simpCons, printVar);
	}
	else
	{
		Variable* instRightVar = vmap.at(var);
		Variable* simpRightVar = simpCons.FindRootVar(instRightVar);
		if (printVar == true)
		{
			cout << "(";
			simpRightVar->PrintTerm();
			cout << ")";
		}
		int value = valueMap.at(simpRightVar);
		cout << value;
	}
}

void Arithmetic::PrintOp() const{
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

//Implementation of ConstraintsTemplate
ConstraintsTemplate::ConstraintsTemplate()
{
	NS_LOG_FUNCTION("Create ConstraintsTemplate: " << this);
	constraints = ConstraintList();
}

ConstraintsTemplate::ConstraintsTemplate(const ConstraintsTemplate& ct)
{
	NS_LOG_FUNCTION("Create ConstraintsTemplate: " << this);
	ConstraintList::const_iterator it;
	Constraint* newCons;
	for (it = ct.constraints.begin(); it != ct.constraints.end();it++)
	{
		newCons = new Constraint((**it));
		constraints.push_back(newCons);
	}
}

void
ConstraintsTemplate::AddConstraint(Constraint* cst)
{
	constraints.push_back(cst);
}

void
ConstraintsTemplate::ReplaceVar(VarMap& vmap)
{
	ConstraintList::iterator it;
	for (it = constraints.begin();it != constraints.end();it++)
	{
		(*it)->VarReplace(vmap);
	}
}

void
ConstraintsTemplate::ReplaceVar(SimpConstraints& simpCons)
{
	ConstraintList::iterator it;
	for (it = constraints.begin();it != constraints.end();it++)
	{
		(*it)->VarReplace(simpCons);
	}
}

void
ConstraintsTemplate::RemoveUnif()
{
	ConstraintList::iterator itc;
	for (itc = constraints.begin();itc != constraints.end();itc++)
	{
		if ((*itc)->IsUnif())
		{
			delete (*itc);
			(*itc) = NULL;
		}
	}

	constraints.remove(NULL);
}

ConstraintsTemplate*
ConstraintsTemplate::Revert() const
{
	ConstraintsTemplate* newTemp = new ConstraintsTemplate();
	ConstraintList::const_iterator itc;
	Constraint* newCons;
	for (itc = constraints.begin();itc != constraints.end();itc++)
	{
		newCons = (*itc)->Revert();
		newTemp->AddConstraint(newCons);
	}

	return newTemp;
}

ConstraintsTemplate::~ConstraintsTemplate()
{
	NS_LOG_FUNCTION("Destruct ConstraintsTemplate: " << this);
	ConstraintList::iterator it;
	for (it = constraints.begin(); it != constraints.end(); it++)
	{
		delete (*it);
	}
}

bool
ConstraintsTemplate::IsEmpty() const
{
	return (constraints.size() == 0?true:false);
}

void
ConstraintsTemplate::CreateVarInst(VarMap& vmap)
{
	ConstraintList::iterator itc;
	for (itc = constraints.begin();itc != constraints.end();itc++)
	{
		(*itc)->CreateVarInst(vmap);
	}
}

void
ConstraintsTemplate::FindFreeVar(list<Variable*>& varList, VarMap& vmap)
{
	ConstraintList::iterator itc;
	for (itc = constraints.begin();itc != constraints.end();itc++)
	{
		(*itc)->FindFreeVar(varList, vmap);
	}
}

void
ConstraintsTemplate::PrintTemplate() const
{
	NS_LOG_FUNCTION("Printing template:");
	ConstraintList::const_iterator itc;
	for (itc = constraints.begin(); itc != constraints.end(); itc++)
	{
	  cout << "\t";
	  (*itc)->Print();
	  cout << endl;
	}
}

void
ConstraintsTemplate::PrintTempInst(VarMap& vmap)
{
	ConstraintList::iterator itc;
	for (itc = constraints.begin();itc != constraints.end();itc++)
	{
		cout << "\t";
		(*itc)->PrintInst(vmap);
		cout << endl;
	}
}

void
ConstraintsTemplate::PrintSimpTempInst(VarMap& vmap, SimpConstraints& simpCons)
{
	ConstraintList::iterator itc;
	for (itc = constraints.begin();itc != constraints.end();itc++)
	{
		bool unifFlag = (*itc)->IsUnif();
		if (unifFlag == false)
		{
			cout << "\t";
			(*itc)->PrintSimpInst(vmap, simpCons);
			cout << endl;
		}
	}
}

void
ConstraintsTemplate::PrintInstance(const map<Variable*, int>& valueMap, bool printVar) const
{
	ConstraintList::const_iterator itc;
	for (itc = constraints.begin(); itc != constraints.end(); itc++)
	{
	  cout << "\t";
	  (*itc)->PrintInstance(valueMap, printVar);
	  cout << endl;
	}
}

void
ConstraintsTemplate::PrintInstance(const map<Variable*, int>& valueMap, VarMap& vmap, bool printVar) const
{
	ConstraintList::const_iterator itc;
	for (itc = constraints.begin(); itc != constraints.end(); itc++)
	{
	  cout << "\t";
	  (*itc)->PrintInstance(valueMap, vmap, printVar);
	  cout << endl;
	}
}

void
ConstraintsTemplate::PrintSimpInstance(const map<Variable*, int>& valueMap, VarMap& vmap,
		   	   	   	   	   	   	   	   SimpConstraints& simpCons, bool printVar) const
{
	ConstraintList::const_iterator itc;
	for (itc = constraints.begin();itc != constraints.end();itc++)
	{
		bool unifFlag = (*itc)->IsUnif();
		if (unifFlag == false)
		{
			cout << "\t";
			(*itc)->PrintSimpInstance(valueMap, vmap, simpCons, printVar);
			cout << endl;
		}
	}
}

SimpConstraints::SimpConstraints()
{
	cts = ConstraintsTemplate();
	varTable = map<Variable*, int>();
	varRevTable = map<int, Variable*>();
	varSet = UnionFindSet();
	equiClass = map<Variable*, list<Variable*> >();
}


SimpConstraints::SimpConstraints(const list<ConstraintsTemplate*>& clist)
{
	ConsList conList = ConsList();
	list<ConstraintsTemplate*>::const_iterator itl;
	for (itl = clist.begin();itl != clist.end();itl++)
	{
		conList.push_back(*itl);
	}

	Initialize(conList);
}

SimpConstraints::SimpConstraints(const ConsList& clist)
{
	Initialize(clist);
}

void
SimpConstraints::Initialize(const ConsList& ctempList)
{
	int count = 0;
	pair<map<Variable*,int>::iterator, bool> ret;
	ConsList::const_iterator itcl;
	ConstraintList::const_iterator itc;
	cts = ConstraintsTemplate();

	NS_LOG_DEBUG("Size of ConList:" << ctempList.size());

	//First iteration: register all variables
	for (itcl = ctempList.begin();itcl != ctempList.end();itcl++)
	{
		const ConstraintList& clist = (*itcl)->GetConstraints();
		for (itc = clist.begin();itc != clist.end();itc++)
		{
			vector<Variable*> vlist;
			(*itc)->GetVars(vlist);
			vector<Variable*>::iterator itv;

			for (itv = vlist.begin();itv != vlist.end();itv++)
			{
				ret = varTable.insert(map<Variable*, int>::value_type(*itv, count));
				if (ret.second == true)
				{
					varRevTable.insert(map<int, Variable*>::value_type(count, *itv));
					count++;
				}
			}
		}
	}

	varSet = UnionFindSet(count);

	//Second iteration: Build equivalent classes
	for (itcl = ctempList.begin();itcl != ctempList.end();itcl++)
	{
		const ConstraintList& clist = (*itcl)->GetConstraints();
		for (itc = clist.begin();itc != clist.end();itc++)
		{
			//Only process equivalence
			if ((*itc)->IsUnif())
			{
				Term* leftE = (*itc)->GetLeftE();
				Term* rightE = (*itc)->GetRightE();
				Variable* leftVar = dynamic_cast<Variable*>(leftE);
				Variable* rightVar = dynamic_cast<Variable*>(rightE);
				int leftId = varTable.at(leftVar);
				int rightId = varTable.at(rightVar);
				varSet.Union(leftId, rightId);
			}
		}
	}
	CreateEquiClass();

	//Third iteration: Build a new ConstraintsTemplate
	for (itcl = ctempList.begin();itcl != ctempList.end();itcl++)
	{
		const ConstraintList& clist = (*itcl)->GetConstraints();
		for (itc = clist.begin();itc != clist.end();itc++)
		{
			//Replace variables in constraints and
			//insert non-equality constraints
			if ((*itc)->IsUnif() == false)
			{
				Constraint* newCst = new Constraint(**itc);
				newCst->VarReplace(varSet, varTable, varRevTable);
				cts.AddConstraint(newCst);
			}
		}
	}
}


void
SimpConstraints::CreateEquiClass()
{
	map<Variable*, list<Variable*> >::iterator itv;
	map<Variable*, int>::iterator itm;
	for (itm = varTable.begin();itm != varTable.end();itm++)
	{
		int root = varSet.Root(itm->second);
		Variable* rootVar = varRevTable.at(root);
		itv = equiClass.find(rootVar);
		if (itv == equiClass.end())
		{
			list<Variable*> vlist(1, itm->first);
			equiClass.insert(map<Variable*, list<Variable*> >::
							 	 	 value_type(rootVar, vlist));
		}
		else
		{
			itv->second.push_back(itm->first);
		}
	}

}

Variable*
SimpConstraints::FindRootVar(Variable* var)
{
	map<Variable*, int>::iterator itm = varTable.find(var);
	if (itm != varTable.end())
	{
		int value = itm->second;
		int root = varSet.Root(value);
		Variable* rootVar = varRevTable.at(root);
		return rootVar;
	}
	else
	{
		return var;
	}
}

void
SimpConstraints::Print()
{
	cout << "###### Simplified constraints ######" << endl;
	cts.PrintTemplate();
	cout << endl;

	cout << "--------- Equivalent Classes --------" << endl;
	int count = 0;
	map<Variable*, list<Variable*> >::iterator itm;
	list<Variable*>::iterator itl;
	for (itm = equiClass.begin(); itm != equiClass.end();itm++)
	{
		cout << "Class " << count << ":";
		for (itl = itm->second.begin();itl != itm->second.end();itl++)
		{
			if (itl == itm->second.begin())
			{
				//Print the representative element
				//of each equivalent class
				cout << "(";
				itm->first->PrintTerm();
				cout << ")";
			}
			(*itl)->PrintTerm();
			cout << ",";
		}
		count++;
		cout << endl;
	}
	cout << "####################################" << endl;
}












