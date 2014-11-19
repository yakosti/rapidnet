/*
 * sdn-constraint.cc
 *
 *  Created on: Nov 8, 2014
 *      Author: chen
 */

#include <sstream>
#include "sdn-constraint.h"

IntVal::IntVal(ValInt32* intPtr):
		value(intPtr->i)
{
}

DoubleVal::DoubleVal(ValDouble* dbPtr):
		value(dbPtr->d)
{
}

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
