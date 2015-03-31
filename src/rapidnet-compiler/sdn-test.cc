/*
 * sdn-test.h
 *
 *  Created on: Mar 10, 2015
 *      Author: chen
 */

#ifndef SDN_TEST_CC_
#define SDN_TEST_CC_

#include "sdn-parse-smtlib.h"


/*
 * *******************************************************************************
 *                                                                               *
 *                       Create Rapidnet Structures                              *
 *                                                                               *
 * *******************************************************************************
 */

Quantifier* create_forall_x__x_equals_3_rapidnet() {
  IntVal* three = new IntVal(3);
  Variable* x = new Variable(Variable::INT, true);

  vector<Variable*> boundVarList;
  boundVarList.push_back(x);

  Constraint* x_equals_3 = new Constraint(Constraint::GT, x, three);

  Quantifier* forall_x__x_equals_3_rapidnet = new Quantifier(Quantifier::FORALL, boundVarList, x_equals_3);
  return forall_x__x_equals_3_rapidnet;
}

/*
  forall x (
    (0 < x AND x < 5) => exists y (y > x)
  )
 */
Quantifier* forall_rapidnet_example() {
  // 0 < x AND x < 5
  IntVal* zero = new IntVal(0);
  IntVal* five = new IntVal(5);

  Variable* x = new Variable(Variable::INT, true);
  vector<Variable*> boundVarList_x;
  boundVarList_x.push_back(x);

  Constraint* x_gt_0 = new Constraint(Constraint::GT, x, zero);
  Constraint* x_lt_5 = new Constraint(Constraint::LT, x, five);

  Connective* x_gt_0__and__x_lt_5 = new Connective(Connective::AND, x_gt_0, x_lt_5);

  // exists y (y > x)
  Variable* y = new Variable(Variable::INT, true);
  vector<Variable*> boundVarList_y;
  boundVarList_y.push_back(y);

  Constraint* y_gt_x = new Constraint(Constraint::GT, y, x);
  Quantifier* exists_y__y_gt_x = new Quantifier(Quantifier::EXISTS, boundVarList_y, y_gt_x);

  // (0 < x AND x < 5) => exists y (y > x)
  Connective* x_gt_0__and__x_lt_5__implies__exists_y__y_gt_x = new Connective(Connective::IMPLY, x_gt_0__and__x_lt_5, exists_y__y_gt_x);

  // exists x ((0 < x AND x < 5) => exists y (y > x) )
  Quantifier* forall_x__x_gt_0__and__x_lt_5__implies__exists_y__y_gt_x = new Quantifier(Quantifier::FORALL, boundVarList_x, x_gt_0__and__x_lt_5__implies__exists_y__y_gt_x);

  return forall_x__x_gt_0__and__x_lt_5__implies__exists_y__y_gt_x;
}

Connective* create__x_gt_y__AND__y_gt_z__IMPLIES__x_gt_z() {
  Variable* x = new Variable(Variable::INT, false);
  Variable* y = new Variable(Variable::INT, false);
  Variable* z = new Variable(Variable::INT, false);

  Constraint* x_gt_y = new Constraint(Constraint::EQ, x, y);
  Constraint* y_gt_z = new Constraint(Constraint::EQ, y, z);
  Constraint* x_gt_z = new Constraint(Constraint::EQ, x, z);

  Connective* x_gt_y__AND__y_gt_z = new Connective(Connective::AND, x_gt_y, y_gt_z);
  Connective* implies = new Connective(Connective::IMPLY, x_gt_y__AND__y_gt_z, x_gt_z);

  return implies;
}

Quantifier* create_exists_x__isblue_x_rapidnet() {
  // make isblue function
  vector<Variable::TypeCode> types_rapidnet;
  types_rapidnet.push_back(Variable::STRING);
  PredicateSchema* isblue_rapidnet = new PredicateSchema("isblue", types_rapidnet);

  //make bound var
  Variable* x = new Variable(Variable::STRING, true);
  vector<Variable*> boundVarList;
  boundVarList.push_back(x);

  // make the formula isblue(x)
  // x is a bound variable
  vector<Term*> args;
  args.push_back(x);

  PredicateInstance* isblue_x_rapidnet = new PredicateInstance(isblue_rapidnet, args);

  //make it quantifier
  Quantifier* exists_x__isblue_x_rapidnet = new Quantifier(Quantifier::EXISTS, boundVarList, isblue_x_rapidnet);
  return exists_x__isblue_x_rapidnet;
}

/* Program
 * ---------------------
   (set-logic AUFNIRA)
   (assert((not (forall ((x Int)) (= x 3))))
   (check-sat)
 */
Connective* create_negation_on_quantifiers() {
  /* rapidnet */
  IntVal* three = new IntVal(3);
  Variable* x = new Variable(Variable::INT, true);

  vector<Variable*> boundVarList;
  boundVarList.push_back(x);

  Constraint* x_equals_3 = new Constraint(Constraint::EQ, x, three);

  Quantifier* forall_x__x_equals_3_rapidnet = new Quantifier(Quantifier::FORALL, boundVarList, x_equals_3);

  Connective* not_forall_x__x_equals_3_rapidnet = new Connective(Connective::NOT, forall_x__x_equals_3_rapidnet, NULL);

  return not_forall_x__x_equals_3_rapidnet;
}

/*
 * *******************************************************************************
 *                                                                               *
 *                       Create Rapidnet Structures                              *
 *                                                                               *
 * *******************************************************************************
 */








/*
 * *******************************************************************************
 *                                                                               *
 *                                  Test CHECK-SAT                               *
 *                                                                               *
 * *******************************************************************************
 */

/* exists y, forall x ((0 < x AND x < 5) => (y > x)) */
FormList create_formula_list_one() {
  /* expression x > 4 */
  Variable* x_rapidnet = new Variable(Variable::INT, false);
  IntVal* four_rapidnet = new IntVal(4);
  Constraint* x_equals_4_rapidnet = new Constraint(Constraint::GT, x_rapidnet, four_rapidnet);

  Quantifier* forallq = forall_rapidnet_example();

  FormList flist;
  flist.push_back(x_equals_4_rapidnet);
  flist.push_back(forallq);

  return flist;
}

/* 
 * (y == 1)
 * (x > 4)
 * (x < 6)
 * should be SAT
 */
ConsList create_constraint_list_one() {
  /* RAPIDNET */
  Variable* x = new Variable(Variable::INT, false);
  Variable* y = new Variable(Variable::INT, false);

  IntVal* one = new IntVal(1);
  IntVal* four = new IntVal(4);
  IntVal* six = new IntVal(6);

  Constraint* y_equals_one = new Constraint(Constraint::EQ, y, one);
  Constraint* x_gt_four = new Constraint(Constraint::GT, x, four);
  Constraint* x_lt_six = new Constraint(Constraint::LT, x, six);

  ConstraintsTemplate* ctemp = new ConstraintsTemplate();
  ctemp->AddConstraint(y_equals_one);
  ctemp->AddConstraint(x_gt_four);
  ctemp->AddConstraint(x_lt_six);

  ConsList clist;
  clist.push_back(ctemp);
  return clist;
}

/* 
 * should be SAT
 * (y == 1)
 * (x > 4)
 * (x > 6)
 */
ConsList create_constraint_list_two() {
  /* RAPIDNET */
  Variable* x = new Variable(Variable::INT, false);
  Variable* y = new Variable(Variable::INT, false);

  IntVal* one = new IntVal(1);
  IntVal* four = new IntVal(4);
  IntVal* six = new IntVal(6);

  Constraint* y_equals_one = new Constraint(Constraint::EQ, y, one);
  Constraint* x_gt_four = new Constraint(Constraint::GT, x, four);
  Constraint* x_gt_six = new Constraint(Constraint::GT, x, six);

  ConstraintsTemplate* ctemp = new ConstraintsTemplate();
  ctemp->AddConstraint(y_equals_one);
  ctemp->AddConstraint(x_gt_four);
  ctemp->AddConstraint(x_gt_six);

  ConsList clist;
  clist.push_back(ctemp);
  return clist;
}

/* forall x ( x = 3)
 */
FormList create_formula_list_two() {
  FormList flist;
  Quantifier* q = create_forall_x__x_equals_3_rapidnet();
  flist.push_back(q);
  return flist;
}

/* (x > y ) /\ (y > z) => (x > z)
 */
FormList create_formula_list_four() {
  FormList flist;
  Connective* c1 = create__x_gt_y__AND__y_gt_z__IMPLIES__x_gt_z();
  Connective* c2 = create_negation_on_quantifiers();
  flist.push_back(c1);
  flist.push_back(c2);
  return flist;
}

ConsList create_constraint_list_five() {
  vector<Variable::TypeCode> domain_types;
  domain_types.push_back(Variable::STRING);
  FunctionSchema* mother_schema = new FunctionSchema("mother", domain_types, Variable::STRING);

  //assert that MichelleObama is the mother of MaliaObama
  vector<Term*> args;
  StringVal* MaliaObama = new StringVal("MaliaObama");
  args.push_back(MaliaObama);
  UserFunction* mother_malia = new UserFunction(mother_schema, args);

  StringVal* MichelleObama = new StringVal("MichelleObama");
  StringVal* BarbaraBush = new StringVal("BarbaraBush");

  Constraint* michelle_is_mother_of_malia = new Constraint(Constraint::EQ, mother_malia, MichelleObama);

  ConstraintsTemplate* ctemp = new ConstraintsTemplate();
  ctemp->AddConstraint(michelle_is_mother_of_malia);
  ConsList clist;
  clist.push_back(ctemp);
  return clist;
}

FormList create_formula_list_five() {
  vector<Variable::TypeCode> domain_types;
  domain_types.push_back(Variable::STRING);
  FunctionSchema* mother_schema = new FunctionSchema("mother", domain_types, Variable::STRING);

  //assert that MichelleObama is the mother of MaliaObama
  vector<Term*> args;
  StringVal* MaliaObama = new StringVal("MaliaObama");
  args.push_back(MaliaObama);
  UserFunction* mother_malia = new UserFunction(mother_schema, args);

  StringVal* MichelleObama = new StringVal("MichelleObama");
  StringVal* BarbaraBush = new StringVal("BarbaraBush");

  Constraint* michelle_is_mother_of_malia = new Constraint(Constraint::EQ, mother_malia, MichelleObama);

  FormList flist;
  flist.push_back(michelle_is_mother_of_malia);
  return flist;
}


/*
 * CVC4
 * ----
  (declare-fun iseven (Int) Bool)
  (assert (exists ((x Int)) (iseven x)))
 */
FormList create_formula_list_six() {
  Quantifier* q = create_exists_x__isblue_x_rapidnet();

  FormList flist;
  flist.push_back(q);
  return flist;
}


void test_check_sat() {
  cout << "\n================= Testing Check Sat - should be SAT =======================\n";
  ConsList clist1 = create_constraint_list_one();
  FormList flist1;
  map<Variable*, int> mymap1 = check_sat(clist1, flist1);

  cout << "\n================= Testing Check Sat - should be SAT =======================\n";
  ConsList clist2;
  FormList flist2 = create_formula_list_one();
  map<Variable*, int> mymap2 = check_sat(clist2, flist2);

  cout << "\n================= Testing Check Sat - should be SAT =======================\n";
  ConsList clist3;
  FormList flist3 = create_formula_list_two();
  map<Variable*, int> mymap3 = check_sat(clist3, flist3);

  cout << "\n================= Testing Check Sat - should be SAT =======================\n";
  ConsList clist4;
  FormList flist4 = create_formula_list_four();
  map<Variable*, int> mymap4 = check_sat(clist4, flist4);

  cout << "\n================= Testing Check Sat - UserFunction ========================\n";
  ConsList clist5 = create_constraint_list_five();
  FormList flist5;
  map<Variable*, int> mymap5 = check_sat(clist5, flist5);

  cout << "\n================= Testing Check Sat - QuantifyPredicate ===================\n";
  ConsList clist6;
  FormList flist6 = create_formula_list_six();
  map<Variable*, int> mymap6 = check_sat(clist6, flist6);
}

void test_check_sat_generalized() {
  cout << "\n==== Testing Check Sat Generalized - exists y,forall x,((0<x AND x<5)=>(y>x)) ====\n";
  FormList flist2 = create_formula_list_one();
  map<Variable*, int> mymap2 = check_sat_generalized(flist2);

  cout << "\n========= Testing Check Sat Generalized - (x>y)and(y>z)=>(x>z) ==========\n";
  FormList flist4 = create_formula_list_four();
  map<Variable*, int> mymap4 = check_sat_generalized(flist4);

  cout << "\n============ Testing Check Sat Generalized - UserFunction ==========\n";
  FormList flist5 = create_formula_list_five();
  map<Variable*, int> mymap5 = check_sat_generalized(flist5);

  cout << "\n============ Testing Check Sat Generalized - QuantifyPredicate ==========\n";
  FormList flist6 = create_formula_list_six();
  map<Variable*, int> mymap6 = check_sat_generalized(flist6);
}

/*
 * *******************************************************************************
 *                                                                               *
 *                                  Test CHECK-SAT                               *
 *                                                                               *
 * *******************************************************************************
 */









/*
 * *******************************************************************************
 *                                                                               *
 *                                  Check Parsing                                *
 *                                                                               *
 * *******************************************************************************
 */



/* PROGRAM
   ------------------------
   (set-logic QF_LIA)
   (assert (= (+ 3 4) 7))
   (check-sat)
   ------------------------
 * checks that given x=3, then x+4=7
 */
void testIntegersArithmetic() {
    /* RAPIDNET */
    IntVal* three = new IntVal(3);
    IntVal* four = new IntVal(4);
    IntVal* seven = new IntVal(7);

    Arithmetic* three_plus_four_rapidnet = new Arithmetic(Arithmetic::PLUS, three, four);
    Constraint* three_plus_four_equals_seven_rapidnet = new Constraint(Constraint::EQ, three_plus_four_rapidnet, seven);

    /* parse and checl */
    string three_plus_four_equals_seven_smt = parseConstraint(three_plus_four_equals_seven_rapidnet);
    cout << three_plus_four_equals_seven_smt << endl;

    clearAllVariables();
}


/* Program
 * ---------------------
   (set-logic QF_LIA)
   (declare-fun x () Int)
   (declare-fun y () Int)
   (assert (= x y))
   (assert (= y 4))
   (assert (= x 4))
   (check-sat)
 * ----------------------
 * checks that give x=4, x=y, then x=4 as well
 */
void testVariables() {
  /* RAPIDNET */
  Variable* x_rapidnet = new Variable(Variable::INT, false);
  Variable* y_rapidnet = new Variable(Variable::INT, false);
  IntVal* four_rapidnet = new IntVal(4);

  Constraint* x_equals_y_rapidnet = new Constraint(Constraint::EQ, x_rapidnet, y_rapidnet);
  Constraint* y_equals_4_rapidnet = new Constraint(Constraint::EQ, y_rapidnet, four_rapidnet);
  Constraint* x_equals_4_rapidnet = new Constraint(Constraint::EQ, x_rapidnet, four_rapidnet);

  /* parsing */
  string x_equals_y_smt = parseFormula(x_equals_y_rapidnet);
  string y_equals_4_smt = parseFormula(y_equals_4_rapidnet);
  string x_equals_4_smt = parseFormula(x_equals_4_rapidnet);

  printDeclaration(all_free_variables);
  cout << x_equals_y_smt << endl;
  cout << y_equals_4_smt << endl;
  cout << x_equals_4_smt << "\n" << endl;

  clearAllVariables();
}


/* Program
 * ---------------------
   (set-logic AUFLIA)
   (assert(forall ((x Int)) (= x 3)))
   (check-sat)
 */
void testBoundVariables() {
  Quantifier* forall_x__x_equals_3_rapidnet = create_forall_x__x_equals_3_rapidnet();
  /* CVC4 */
  string parsed = parseFormula(forall_x__x_equals_3_rapidnet);
  cout << "\n---------- forall x (x > 3) ------------" << endl;
  cout << parsed << "\n" << endl;

  clearAllVariables();
}

/*
 * (set-logic AUFNIRA)
 * (exists ((y Int)) (=> (> y 3) (exists ((x Int)) (> x 2)) ) )
 */
void testMixedQuantifiers() {
  /* rapidnet */
  IntVal* two = new IntVal(2);
  IntVal* three = new IntVal(3);
  Variable* x = new Variable(Variable::INT, true);
  Variable* y = new Variable(Variable::INT, true);

  vector<Variable*> boundVarListX;
  boundVarListX.push_back(x);

  vector<Variable*> boundVarListY;
  boundVarListY.push_back(y);

  Constraint* x_gt_2 = new Constraint(Constraint::GT, x, two);
  Quantifier* exists_x__x_gt_2 = new Quantifier(Quantifier::EXISTS, boundVarListX, x_gt_2);

  Constraint* y_gt_3 = new Constraint(Constraint::GT, y, three);

  Connective* implies = new Connective(Connective::IMPLY, y_gt_3, exists_x__x_gt_2);

  Quantifier* exists_y__y_gt_3__implies__exists_x__x_gt_2 = new Quantifier(Quantifier::EXISTS, boundVarListY, implies);

  string parsed = parseFormula(exists_y__y_gt_3__implies__exists_x__x_gt_2);
  cout << "\n---------- exists y ((y > 3) => exists x (x > 2)) ------------" << endl;
  cout << parsed << "\n" << endl;

  clearAllVariables();
}

/* Program
 * ---------------------
   (set-logic AUFNIRA)
   (assert(exists ((x Int)) (= x 3)))
   (check-sat)
 */
void testExistVariables() {
  /* rapidnet */
  IntVal* three = new IntVal(3);
  Variable* x = new Variable(Variable::INT, true);

  vector<Variable*> boundVarList;
  boundVarList.push_back(x);

  Constraint* x_equals_3 = new Constraint(Constraint::GT, x, three);

  Quantifier* exists_x__x_equals_3_rapidnet = new Quantifier(Quantifier::EXISTS, boundVarList, x_equals_3);

  /* CVC4 */
  string parsed = parseFormula(exists_x__x_equals_3_rapidnet);
  cout << "---------- exists x (x > 3) ------------" << endl;
  cout << parsed << endl;

  clearAllVariables();
}


/* Program
 * ---------------------
   (set-logic QF_LIA)
   (assert(forall ((x Int)) (> x 3)))
   (check-sat)
 * ((x > y) /\ (y > z)) => (x > z)
 */
void connective__x_gt_y__AND__y_gt_z__IMPLIES__x_gt_z() {
  Connective* implies = create__x_gt_y__AND__y_gt_z__IMPLIES__x_gt_z();

  /* checking */
  string implies_smt = parseFormula(implies);

  printDeclaration(all_free_variables);
  cout << implies_smt << endl;

  clearAllVariables();
}

/*
   DECLARING
   ---------
   (set-logic QF_UFLIA)
   (declare-fun iseven (Int) Bool)
   (assert (even 2))

   CHECKING
   --------
   (assert (even 2))
   (check-sat) !sat

   (assert (not (iseven 2)))
   (check-sat) !unsat
 */
void testEvenPredicate() {
  /* ***************************** rapidnet: make iseven function ****************** */
  vector<Variable::TypeCode> types_rapidnet;
  types_rapidnet.push_back(Variable::INT);
  PredicateSchema* iseven_schema = new PredicateSchema("iseven", types_rapidnet);

  // make the formula iseven(2)
  IntVal* two = new IntVal(2);
  vector<Term*> args_two;
  args_two.push_back(two);
  PredicateInstance* iseven_2 = new PredicateInstance(iseven_schema, args_two);

  /* ****************************** what to do *************************** */
  cout << "\n------------------ Test iseven(n) ----------------------" << endl;
  string PredicateSchema_smtlib = parsePredicateSchema(iseven_schema);
  cout << PredicateSchema_smtlib << endl;
  string iseven2_smtlib = parseFormula(iseven_2);
  cout << iseven2_smtlib << endl;

  clearAllVariables();
}



/*
 * CVC4
 * ----
   (set-logic S)
   (declare-fun isblue (String) Bool)
   (assert (isblue "sky"))
   (exists ((x String)) (isblue x) )
   (check-sat) !sat
 */
void testBoundPredicate() {
  /* ***************************** rapidnet: make isblue function ****************** */

  vector<Variable::TypeCode> types_rapidnet;
  types_rapidnet.push_back(Variable::STRING);
  PredicateSchema* isblue_rapidnet = new PredicateSchema("isblue", types_rapidnet);

  /* ************************ rapidnet: exists x, isblue(x) ************************ */

  //make bound var
  Variable* x = new Variable(Variable::STRING, true);
  vector<Variable*> boundVarList;
  boundVarList.push_back(x);

  // make the formula isblue(x)
  // x is a bound variable
  vector<Term*> args;
  args.push_back(x);

  PredicateInstance* isblue_x_rapidnet = new PredicateInstance(isblue_rapidnet, args);

  //make it quantifier
  Quantifier* exists_x__isblue_x_rapidnet = new Quantifier(Quantifier::EXISTS, boundVarList, isblue_x_rapidnet);

  /* ************************ rapidnet: isblue("sky") ********************* */

  StringVal* sky_string = new StringVal("sky");
  vector<Term*> args_sky_rapidnet;
  args_sky_rapidnet.push_back(sky_string);

  PredicateInstance* isblue_sky_rapidnet = new PredicateInstance(isblue_rapidnet, args_sky_rapidnet);


  /* ******************************* SMTLIB ******************************** */

  cout << "\n----------------- isblue ----------------------- " << endl;
  string isblue_sky_smtlib = parseFormula(isblue_sky_rapidnet);
  cout << isblue_sky_smtlib << endl;
  printDeclaration(all_predicate_schemas);
  string exists_x__isblue_x_smtlib = parseFormula(exists_x__isblue_x_rapidnet);
  cout << exists_x__isblue_x_smtlib << endl;

  clearAllVariables();
}

/*
 * Function symbols testing
 *
   (set-logic S)
   (declare-fun mother (String) String)
   (assert (= (mother "MaliaObama") "MichelleObama"))
   (assert (= (mother "MaliaObama") "BarbaraBush"))
   (check-sat) !unsat, as Barbara Bush is not the mother of Malia Obama
 */
void quantifier__function_child_younger_than_mother() {
  /* ---------------------------- RAPIDNET ------------------------------ */
  //mother
  vector<Variable::TypeCode> domain_types;
  domain_types.push_back(Variable::STRING);
  FunctionSchema* mother_schema = new FunctionSchema("mother", domain_types, Variable::STRING);

  //assert that MichelleObama is the mother of MaliaObama
  vector<Term*> args;
  StringVal* MaliaObama = new StringVal("MaliaObama");
  args.push_back(MaliaObama);
  UserFunction* mother_malia = new UserFunction(mother_schema, args);

  StringVal* MichelleObama = new StringVal("MichelleObama");
  StringVal* BarbaraBush = new StringVal("BarbaraBush");

  //true
  Constraint* michelle_is_mother_of_malia = new Constraint(Constraint::EQ, mother_malia, MichelleObama);
  //false
  Constraint* barbara_is_mother_of_malia = new Constraint(Constraint::EQ, mother_malia, BarbaraBush);

  /* ------------------------------ CVC4 ------------------------------ */

  cout << "\n---------------- Function mother -----------------------" << endl;
  string testing = parseFunctionSchema(mother_schema);
  printDeclaration(all_function_schemas);
  string michelle_is_mother_of_malia_smtlib = parseFormula(michelle_is_mother_of_malia);
  cout << michelle_is_mother_of_malia_smtlib << endl;
  string barbara_is_mother_of_malia_smtlib = parseFormula(barbara_is_mother_of_malia);
  cout << barbara_is_mother_of_malia_smtlib << endl;

  clearAllVariables();
}

/*
 * Function
 * --------
 * mother(x): returns the mother of x
 *
 * Predicate
 * ---------
 * YOUNGER(x,y): x is younger than y
 *
 * ASSERT forall x, YOUNGER(x, mother(x))
 * (everyone is younger than his/her mother)
 *
 * QUERY YOUNGER("MaliaObama", mother("MaliaObama"))? //should be true
 *
   (set-logic S)
   (assert (forall ((y String)) (YOUNGER y (mother y))))
 */
void nested_function_check() {
  /* ---------------------------- RAPIDNET ------------------------------ */
  //bound vars
  Variable* child = new Variable(Variable::STRING, true);

  //mother schema
  vector<Variable::TypeCode> mother_domain_types;
  mother_domain_types.push_back(Variable::STRING);
  FunctionSchema* mother_schema = new FunctionSchema("mother", mother_domain_types, Variable::STRING);

  //mother UserFunction
  vector<Term*> mother_args;
  mother_args.push_back(child);
  UserFunction* mother_function = new UserFunction(mother_schema, mother_args);

  //YOUNGER schema
  vector<Variable::TypeCode> younger_domain_types;
  younger_domain_types.push_back(Variable::STRING);
  younger_domain_types.push_back(Variable::STRING);
  PredicateSchema* YOUNGER_schema = new PredicateSchema("YOUNGER", younger_domain_types);

  //Younger terms
  vector<Term*> YOUNGER_args;
  YOUNGER_args.push_back(child);
  YOUNGER_args.push_back(mother_function);
  PredicateInstance* YOUNGER_x_motherx = new PredicateInstance(YOUNGER_schema, YOUNGER_args);

  // forall x, YOUNGER(x, mother(x))
  vector<Variable*> quantifier_bound_vars;
  quantifier_bound_vars.push_back(child);
  Quantifier* forall_x__YOUNGER_x_motherx = new Quantifier(Quantifier::FORALL, quantifier_bound_vars, YOUNGER_x_motherx);

  /* ---------------------------- RAPIDNET ------------------------------ */

  StringVal* MaliaObama = new StringVal("MaliaObama");

  // mother("MaliaObama")
  vector<Term*> malia_schema_args;
  malia_schema_args.push_back(MaliaObama);
  UserFunction* mother_malia = new UserFunction(mother_schema, malia_schema_args);

  vector<Term*> YOUNGER_malia_args;
  YOUNGER_malia_args.push_back(MaliaObama);
  YOUNGER_malia_args.push_back(mother_malia);
  PredicateInstance* malia_younger_than_her_mother = new PredicateInstance(YOUNGER_schema, YOUNGER_malia_args);

  /* ---------------------------- CVC4 ------------------------------ */
  std::cout << "\n------------------- Nested Function Check --------------" << std::endl;
  string forall_x__YOUNGER_x_motherx_cvc4 = parseFormula(forall_x__YOUNGER_x_motherx);
  printDeclaration(all_predicate_schemas);
  printDeclaration(all_function_schemas);
  cout << forall_x__YOUNGER_x_motherx_cvc4 << endl;

  clearAllVariables();
}

void test_parsing() {
  testIntegersArithmetic();
  testVariables();
  connective__x_gt_y__AND__y_gt_z__IMPLIES__x_gt_z();
  testBoundVariables();
  testExistVariables();
  testMixedQuantifiers();
  testEvenPredicate();
  testBoundPredicate();
  quantifier__function_child_younger_than_mother();
  nested_function_check();
  
  test_check_sat();
  test_check_sat_generalized();
}

/*
 * *******************************************************************************
 *                                                                               *
 *                                  Check Parsing                                *
 *                                                                               *
 * *******************************************************************************
 */



#endif /* SDN_TEST_CC_ */
