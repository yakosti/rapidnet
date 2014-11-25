/*
 * sdn-constraint.h
 *
 *  Created on: Nov 7, 2014
 *      Author: cchen
 */

#ifndef SDN_CONSTRAINT_H_
#define SDN_CONSTRAINT_H_

#include <iostream>
#include <string>
#include <vector>
#include <sdn-formula.h>
//#include "parser-util.h"

using namespace std;

/*
 * Components of constraint pool
 */

/*Execution tree*/
class Derivation;

typedef vector<Constraint*> ConstraintList;
//typedef pair<Derivation, ConstraintList> ConstraintPair;
//typedef vector<ConstraintPair> ConstraintPairList;
//typedef map<TupleInst, ConstraintPairList> ConstraintPool;

class Cpool
{
private:
	//ConstraintPool pool;
	ConstraintList pool;
};

#endif /* SDN_CONSTRAINT_H_ */
