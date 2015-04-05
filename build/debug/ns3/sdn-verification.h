/*
 * sdn-verification.h
 *
 *  Created on: Mar 22, 2015
 *      Author: chen
 */

#ifndef SDN_VERIFICATION_H_
#define SDN_VERIFICATION_H_

#include <iostream>
#include <string>

#include "sdn-graph.h"
#include "sdn-derivation.h"
#include "sdn-property.h"
#include "sdn-parse-smtlib.h"

map<Variable*, int>
PropAssignment(SimpConstraints&, map<Variable*, int>);

//Counter-example generation
void
GenCounterExp(map<Variable*, int>,
			  list<pair<const DpoolNode*, SimpConstraints&> >&,
			  map<const DpoolNode*, DpoolInstNode*>&);

//TODO: documentation
//assignment: counter-example instances
//return value: [true: constraints sat|false: constraints unsat]
bool
CheckWholeProp(const Property&,
			   list<DpoolTupleInst>&,
			   ConsList&,
			   FormList&,
			   map<Variable*, int>&,
			   list<SimpConstraints*>&);

//Return value: [true: an unsat element, meaning its negation is valid|
//				 false: all sat, its negation invalid]
bool
CheckRecurExist(const Property&,
				DpoolTupleMap&,
				DpoolTupleMap::const_iterator,
				list<DpoolTupleInst>,
				ConsList&,
				FormList&,
				map<Variable*, int>&,
				list<SimpConstraints*>,
				map<const DpoolNode*, DpoolInstNode*>&);

//TODO: Separate the verification of universally
//quantified constraints from CheckExistProp
bool
CheckExistProp(const Property&,
			   const DerivNodeList&,
			   BaseRelProperty&);

//Return value: [true: property holds|false: property does not hold]
bool
CheckRecurUniv(const Dpool&,
			   const Property&,
			   const list<PredicateInstance*>&,
			   list<PredicateInstance*>::const_iterator,
			   DerivNodeList,
			   BaseRelProperty&);

//TODO: Add property checking for base tuples
bool
CheckProperty(const Dpool&,
			  const Property&,
			  BaseRelProperty&);


#endif /* SDN_VERIFICATION_H_ */
