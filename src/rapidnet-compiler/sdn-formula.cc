/*
 * sdn-formula.cc
 *
 *  Created on: Nov 24, 2014
 *      Author: cchen
 */

#include "sdn-formula.h"

Constraint::~Constraint()
{
	delete leftE;
	delete rightE;
}

void
Constraint::PrintConstraint()
{
  leftE->PrintTerm();
  PrintOp();
  rightE->PrintTerm();
}

void 
Constraint::PrintOp()
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

int Variable::varCount = 0;

Variable::Variable(TypeCode t, bool b):
  varType(t),isbound(b)
{
        Variable::varCount = Variable::varCount + 1;
	ostringstream countStream;
	countStream << Variable::varCount;  
	name =  "variable"+ countStream.str();
}

void
Variable::PrintTerm()
{
  cout << name;
}

void
FunctionSchema::PrintSchema()
{
  cout << name;
}

void
UserFunction::PrintTerm()
{
  schema->PrintSchema();
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
IntVal::PrintTerm()
{
  cout << value;
}

void
DoubleVal::PrintTerm()
{
  cout << value;
}

void
StringVal::PrintTerm()
{
  cout << value;
}

void
BoolVal::PrintTerm()
{
  cout << value;
}

void
Arithmetic::PrintTerm()
{
  leftE->PrintTerm();
  PrintOp();
  rightE->PrintTerm();
}

void
Arithmetic::PrintOp()
{
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
