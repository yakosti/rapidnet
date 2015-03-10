/*
 * rapidnet-dpgraph-generator.cc
 *
 *  Created on: Nov 3, 2014
 *      Author: chen
 */

/* -*-  Mode: C++; c-file-style: "gnu"; indent-tabs-mode:nil; -*- */
/*
 * Copyright (c) 2009 University of Pennsylvania
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License version 2 as
 * published by the Free Software Foundation;
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 */

#include <iostream>
#include <fstream>
#include <string>
#include <sys/wait.h>

#include "ol-context.h"
#include "eca-context.h"
#include "localize-context.h"
#include "table-store.h"
#include "rapidnet-context.h"

#include "ns3/ptr.h"
#include "ns3/command-line.h"
#include "ns3/log.h"

#include "sdn-graph.h"
#include "sdn-derivation.h"
#include "sdn-parse-smtlib.h"
#include "sdn-property.h"
#include "z3++.h"

using namespace std;
using namespace ns3;
using namespace ns3::rapidnet_compiler;

NS_LOG_COMPONENT_DEFINE ("RapidNetDPGraph");

/**
 * \brief Preprocesses the overlog file using the C-preprocessor
 *        and returns the pre-processed program as a string.
 */
string preprocessReadOverlogProgram (string overlogFilename)
{
  NS_LOG_INFO("Pre-processing...");
  string processedFilename = overlogFilename + ".cpp";
  char* args[6];
  int count = 0;

  args[count++] = (char *) "cpp";
  args[count++] = (char *) "-P";
  args[count++] = (char *) "-C";
  args[count++] = (char*) overlogFilename.c_str ();
  args[count++] = (char*) processedFilename.c_str ();
  args[count++] = NULL;

  // Invoke the preprocessor
  pid_t pid = fork ();
  if (pid == -1)
    {
      NS_LOG_ERROR ("Cannot fork a preprocessor.");
      exit (1);
    }
  else if (pid == 0)
    {
      if (execvp ("cpp", args) < 0)
        {
          NS_LOG_ERROR ("CPP ERROR");
        }
      exit (1);
    }
  else
    {
      wait (NULL);
    }

  // Read processed script.
  ifstream file;
  file.open (processedFilename.c_str ());

  if (!file.is_open ())
    {
      NS_LOG_ERROR ("Cannot open processed overlog file '" << processedFilename
          << "'!");
      return string ();
    }
  else
    {
      NS_LOG_INFO("Generated pre-processed file " << processedFilename);
      ostringstream scriptStream;
      string line;

      while (std::getline (file, line))
        {
          scriptStream << line << "\n";
        }
      file.close ();
      return scriptStream.str ();
    }
}

void printToFile (string filename, string contents)
{
    ofstream file;
    file.open (filename.c_str ());
    file << contents;
    file.close ();
    NS_LOG_INFO("Generated dependency graph " << filename);
}

/**
 * \brief Parses the overlog file and sets up overlog context and
 *        table information.
 */
void parseOverlog (string overlogFile, Ptr<OlContext> ctxt,
  Ptr<TableStore> tableStore, bool provenanceEnabled)
{
  string program = preprocessReadOverlogProgram (overlogFile);
  NS_LOG_INFO("Parsing NDlog...");

  istringstream istr (program);
  ctxt->ParseStream (&istr, provenanceEnabled);

  if(provenanceEnabled && !ctxt->IsSendlog())
  {
	  string query_file = "rapidnet/compiler/provenance-query.olg";
	  string query_program = preprocessReadOverlogProgram (query_file);
	  istringstream querystr (query_program);
	  Ptr<OlContext> query (new OlContext ());
	  query->ParseStream (&querystr, false);

	  ctxt->CombineProvenanceQueryRules(query);
	  printToFile (overlogFile + ".prov", ctxt->ToString ());
  }
  // else case will never execute because this is handled
  // in the OlContext::SetContext method that is called
  // when the token stream is parsed.

  if (ctxt->GotErrors ())
    {
      NS_LOG_ERROR ("Parse Errors Found");
      ctxt->DumpErrors ();
      NS_LOG_ERROR ("Compilation aborted");
      exit (-1);
    }
}

/**
 * Compiles the application to generate depndency graph
 */
void compile (string overlogFile, bool provenanceEnabled)
{
  NS_LOG_INFO ("Compiling NDLog file:\t" << overlogFile);
  // Parse
  Ptr<OlContext> ctxt (new OlContext ());
  Ptr<TableStore> tableStore (new TableStore (ctxt));
  parseOverlog (overlogFile, ctxt, tableStore, provenanceEnabled);

  Ptr<DPGraph> graphNdlog (new DPGraph(ctxt));
  //graphNdlog->PrintGraph();

  //Ptr<MiniGraph> miniGraph (new MiniGraph(graphNdlog));
  //miniGraph->PrintGraph();

  AnnotMap testMap;
  list<Variable::TypeCode> tlist (9, Variable::STRING);
  Tuple tp = Tuple("verifyPath", tlist);
  const vector<Variable*> arg = tp.GetArgs();
  IntVal* value = new IntVal(10000);
  Constraint* ct = new Constraint(Constraint::EQ, arg[0], value);
  Quantifier qtf (Quantifier::FORALL, arg, ct);
  Annotation anno (&tp, &qtf);
  testMap.insert(AnnotMap::value_type("verifyPath", &anno));
  Ptr<Dpool> dpool (new Dpool(graphNdlog, testMap));
  //dpool->PrintDpool();
  //dpool->PrintAllDeriv();
  //dpool->PrintDeriv("advertisements");

  /* adding smt solver part */
  const DerivNodeList& dlist = dpool->GetDerivList("advertisements");
  //writeToFile("testing_constraints", dlist); //laykuan testing
  
  /* this is sat*/
  Variable* x_rapidnet = new Variable(Variable::INT, false);
  IntVal* four_rapidnet = new IntVal(4);
  Constraint* x_equals_4_rapidnet = new Constraint(Constraint::GT, x_rapidnet, four_rapidnet);

  FormList flist;
  flist.push_back(x_equals_4_rapidnet);
  //flist.push_back(&qtf);
  write_to_z3(dlist, flist);

  //const DerivNodeList& dlist = dpool->GetDerivList("advertisements");
  //Use DerivNode::GetAllObligs() to get all proof obligations

  //User-defined property
  //Property p = Property();
  //p.Print();
}


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
  /* rapidnet */
  IntVal* three = new IntVal(3);
  Variable* x = new Variable(Variable::INT, true);

  vector<Variable*> boundVarList;
  boundVarList.push_back(x);

  Constraint* x_equals_3 = new Constraint(Constraint::GT, x, three);

  Quantifier* forall_x__x_equals_3_rapidnet = new Quantifier(Quantifier::FORALL, boundVarList, x_equals_3);

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
  /* RAPIDNET */
  Variable* x = new Variable(Variable::INT, false);
  Variable* y = new Variable(Variable::INT, false);
  Variable* z = new Variable(Variable::INT, false);

  Constraint* x_gt_y = new Constraint(Constraint::EQ, x, y);
  Constraint* y_gt_z = new Constraint(Constraint::EQ, y, z);
  Constraint* x_gt_z = new Constraint(Constraint::EQ, x, z);

  Connective* x_gt_y__AND__y_gt_z = new Connective(Connective::AND, x_gt_y, y_gt_z);
  Connective* implies = new Connective(Connective::IMPLY, x_gt_y__AND__y_gt_z, x_gt_z);

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
  /* ***************************** rapidnet: make isblue function ****************** */
  vector<Variable::TypeCode> types_rapidnet;
  types_rapidnet.push_back(Variable::INT);
  PredicateSchema* iseven_schema = new PredicateSchema("iseven", types_rapidnet);

  // make the formula iseven(2)
  IntVal* two = new IntVal(2);
  vector<Term*> args_two;
  args_two.push_back(two);
  PredicateInstance* iseven_2 = new PredicateInstance(iseven_schema, args_two);

  //make the formula neg (iseven(2))

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
  printDeclaration(all_constants);

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
}

/* 
 * *******************************************************************************
 *                                                                               *
 *                                  Check Parsing                                *
 *                                                                               *
 * *******************************************************************************
 */

//NDLog program should be free of recursion
//NDLog program should have no value as argument of a tuple
int main (int argc, char** argv)
{
  LogComponentEnable ("RapidNetDPGraph", LOG_LEVEL_INFO);
//  LogComponentEnable ("DPGraph", LOG_LEVEL_INFO);
//  LogComponentEnable ("Formula", LOG_LEVEL_INFO);
//  LogComponentEnable ("Dpool", LOG_LEVEL_INFO);
  LogComponentEnable ("Property", LOG_LEVEL_INFO);
  LogComponentEnable ("Dpool", LOG_INFO);
//  LogComponentEnable ("DPGraph", LOG_INFO);
//  LogComponentEnable ("Formula", LOG_INFO);
//  LogComponentEnable ("Property", LOG_INFO);

  test_parsing();

  string overlogFile;
  string baseoverlogFile = DEFAULT_RN_APP_BASE;
  bool provenance = 0;
  string baseDefinition;

  CommandLine cmd;
  cmd.AddValue ("ndlog", "Application NDlog file", overlogFile);
  cmd.AddValue ("base-ndlog", "Application's base NDlog file (optional)",
    baseoverlogFile);
  cmd.AddValue ("provenance", "Enable provenance for this application (optional)",
    provenance);
  cmd.Parse (argc, argv);

  compile(overlogFile, provenance);
  return 0;
}







