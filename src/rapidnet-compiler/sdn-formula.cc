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

int Variable::varCount = 0;

Variable::Variable(TypeCode t, bool b):
  varType(t),isbound(b)
{
        Variable::varCount = Variable::varCount + 1;
	ostringstream countStream;
	countStream << Variable::varCount;  
	name =  "variable"+ countStream.str();
}



