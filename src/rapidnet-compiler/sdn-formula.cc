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

Variable::Variable(TypeCode type):
		varType(type)
{
	//Assign a new name
	ostringstream nameString;
	nameString << "x" << varCount;
	name = nameString.str();

	varCount++;
}

void
Variable::PrintVar()
{
  cout << name;
}

int Variable::varCount = 0;



