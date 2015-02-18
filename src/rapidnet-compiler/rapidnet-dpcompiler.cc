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
#include <cvc4/cvc4.h>
#include "sdn-formula-to-cvc4.h"

using namespace CVC4;
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
  list<Variable::TypeCode> tlist (4, Variable::STRING);
  Tuple tp = Tuple("verifyPath", tlist);
  const vector<Variable*> arg = tp.GetArgs();
  IntVal* value = new IntVal(10000);
  Constraint* ct = new Constraint(Constraint::EQ, arg[0], value);
  Quantifier qtf (Quantifier::FORALL, arg, ct);
  Annotation anno (&tp, &qtf);
  testMap.insert(AnnotMap::value_type("verifyPath", &anno));
  Ptr<Dpool> dpool (new Dpool(graphNdlog, testMap));
  //dpool->PrintDpool();
  dpool->PrintAllDeriv();

//  pair<RuleListC, RuleListC> p = miniGraph->TopoSort(testMap);
//  RuleListC::const_iterator it;
//  cout << "Rules:" << endl;
//  for (it = p.first.begin();it != p.first.end();it++)
//  {
//	  (*it)->PrintName();
//	  cout << ",";
//  }
//  cout << endl;
//  for (it = p.second.begin();it != p.second.end();it++)
//  {
//	  (*it)->PrintName();
//	  cout << ",";
//  }
}

/* 
 * check that 
 * 3+4 = 7 is VALID 
 */
void testIntegersArithmetic() {
    ExprManager em;
    SmtEngine smt(&em);

    /* RAPIDNET */
    IntVal* three = new IntVal(3);
    IntVal* four = new IntVal(4);
    IntVal* seven = new IntVal(7);

    Arithmetic* three_plus_four_rapidnet = new Arithmetic(Arithmetic::PLUS, three, four); 
    Constraint* three_plus_four_equals_seven_rapidnet = new Constraint(Constraint::EQ, three_plus_four_rapidnet, seven);

    /* CVC4*/
    Expr three_plus_four_cvc4 = parseTerm(&em, three_plus_four_rapidnet);
    Expr three_plus_four_equals_seven_cvc4 = parseFormula(&em, three_plus_four_equals_seven_rapidnet); 

    /* CHECKING PARSING */
    std::cout << "\n" << three_plus_four_equals_seven_cvc4 << " is: " << smt.query(three_plus_four_equals_seven_cvc4) << std::endl;

    clearAllVariables();
}

/* check that 
 * (x=y) and (y=4)
 * IMPLIES (x=4)
 */
void testVariables() {
    ExprManager em;
    SmtEngine smt(&em);

    /* RAPIDNET */
    Variable* x_rapidnet = new Variable(Variable::INT, false);
    Variable* y_rapidnet = new Variable(Variable::INT, false);
    IntVal* four_rapidnet = new IntVal(4);

    Constraint* x_equals_y_rapidnet = new Constraint(Constraint::EQ, x_rapidnet, y_rapidnet);
    Constraint* y_equals_4_rapidnet = new Constraint(Constraint::EQ, y_rapidnet, four_rapidnet);
    Constraint* x_equals_4_rapidnet = new Constraint(Constraint::EQ, x_rapidnet, four_rapidnet);

    /* CVC4 */

    //declare variables
    Expr x_equals_y_cvc4 = parseFormula(&em, x_equals_y_rapidnet);
    Expr y_equals_4_cvc4 = parseFormula(&em, y_equals_4_rapidnet);
    Expr x_equals_4_cvc4 = parseFormula(&em, x_equals_4_rapidnet);

    smt.assertFormula(y_equals_4_cvc4);
    smt.assertFormula(x_equals_4_cvc4);
    smt.push();

    /* CHECKING PARSING */
    std::cout << "\n" << y_equals_4_cvc4 << " and " << x_equals_4_cvc4 << " implies that: " << x_equals_4_cvc4 << " is: " << smt.query(x_equals_4_cvc4) << std::endl;

    clearAllVariables();
}

/*
 * FORALL x, (x=3)
 * Should be INVALID
 */
void testBoundVariables() {
    ExprManager em;
    SmtEngine smt(&em);

    /* rapidnet */

    IntVal* three = new IntVal(3);
    Variable* x = new Variable(Variable::INT, true);

    vector<Variable*> boundVarList;
    boundVarList.push_back(x);

    Constraint* x_equals_3 = new Constraint(Constraint::EQ, x, three);

    Quantifier* forall_x__x_equals_3_rapidnet = new Quantifier(Quantifier::FORALL, boundVarList, x_equals_3);

    /* CVC4 */
    Expr forall_x__x_equals_3_cvc4 = parseFormula(&em, forall_x__x_equals_3_rapidnet);

    /* check smt */
    std::cout << "\nTest " << forall_x__x_equals_3_cvc4 << " is: "<< smt.query(forall_x__x_equals_3_cvc4) << std::endl;

    clearAllVariables();
}

/*
 * CVC4
 * ----
 * isblue: STRING -> BOOLEAN
 * ASSERT isblue("sky")
 * QUERY EXISTS x, isblue(x) 
 */
void testBoundPredicate() {
    ExprManager em;
    SmtEngine smt(&em);

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


    /* ******************************* CVC4 ******************************** */

    Expr isblue_sky_cvc4 = parseFormula(&em, isblue_sky_rapidnet);


    Expr exists_x__isblue_x_cvc4 = parseFormula(&em, exists_x__isblue_x_rapidnet);

    /* **************************** CHECK SMT ******************************** */

    std::cout << "\nSky not blue: "  << exists_x__isblue_x_cvc4 << smt.query(exists_x__isblue_x_cvc4) << std::endl;

    smt.assertFormula(isblue_sky_cvc4);

    std::cout  << "\nSky is blue: " << exists_x__isblue_x_cvc4 << smt.query(exists_x__isblue_x_cvc4) << std::endl;

    clearAllVariables();
}

/*
 * QUERY (FORALL (x:INT): (EXISTS (y:INT): x+y = 4));
 */
void testArithmeticNestedQuantifier() {
    ExprManager em;
    SmtEngine smt(&em);

    /* rapidnet */
    IntVal* four = new IntVal(4);
    Variable* x = new Variable(Variable::INT, true);
    Variable* y = new Variable(Variable::INT, true);

    vector<Variable*> boundVarList_exists;
    boundVarList_exists.push_back(y);

    vector<Variable*> boundVarList_forall;
    boundVarList_forall.push_back(x);

    Arithmetic* x_plus_y = new Arithmetic(Arithmetic::PLUS, x, y);
    Constraint* x_plus_y_eq_4 = new Constraint(Constraint::EQ, x_plus_y, four);
    Quantifier* exists_y__x_plus_y_eq_4 = new Quantifier(Quantifier::EXISTS, boundVarList_exists, x_plus_y_eq_4);

    Quantifier* forall_x__exists_y__x_plus_y_eq_4 = new Quantifier(Quantifier::FORALL, boundVarList_forall, exists_y__x_plus_y_eq_4);

    /* CVC4 */
    Expr forall_x__exists_y__x_plus_y_eq_4__cvc4 = parseFormula(&em, forall_x__exists_y__x_plus_y_eq_4);

    /* **************************** CHECK SMT ******************************** */

    std::cout << "\n" << forall_x__exists_y__x_plus_y_eq_4__cvc4 << " is: " << smt.query(forall_x__exists_y__x_plus_y_eq_4__cvc4) << std::endl;

    clearAllVariables();
}

/*
 * ((x > y) /\ (y > z)) => (x > z)
 */
void connective__x_gt_y__AND__y_gt_z__IMPLIES__x_gt_z() {
    ExprManager em;
    SmtEngine smt(&em);

    /* RAPIDNET */
    Variable* x = new Variable(Variable::INT, false);
    Variable* y = new Variable(Variable::INT, false);
    Variable* z = new Variable(Variable::INT, false);

    Constraint* x_gt_y = new Constraint(Constraint::EQ, x, y);
    Constraint* y_gt_z = new Constraint(Constraint::EQ, y, z);
    Constraint* x_gt_z = new Constraint(Constraint::EQ, x, z);

    Connective* x_gt_y__AND__y_gt_z = new Connective(Connective::AND, x_gt_y, y_gt_z);
    Connective* implies = new Connective(Connective::IMPLY, x_gt_y__AND__y_gt_z, x_gt_z);

    /* CVC4 */
    Expr implies_cvc4 = parseFormula(&em, implies);

    /* CHECKING PARSING */
    std::cout << "\nTest: " << implies_cvc4 << " is: " << smt.query(implies_cvc4) << std::endl;

    clearAllVariables();
}

/*
 * (4+3)-(2+1) = 4 
 */
void arithmetic__4_plus_3__minus__2_plus_1__equals__4() {
    ExprManager em;
    SmtEngine smt(&em);

    /* RAPIDNET */
    IntVal* one = new IntVal(1);
    IntVal* two = new IntVal(2);
    IntVal* three = new IntVal(3);
    IntVal* four = new IntVal(4);

    Arithmetic* four_plus_three = new Arithmetic(Arithmetic::PLUS, four, three); 
    Arithmetic* two_plus_one = new Arithmetic(Arithmetic::PLUS, two, one);
    Arithmetic* four_plus_three__minus__two_plus_one = new Arithmetic(Arithmetic::MINUS, four_plus_three, two_plus_one);
    Constraint* equal_sides = new Constraint(Constraint::EQ, four_plus_three__minus__two_plus_one, four);

    /* CVC4 */
    Expr equal_sides_cvc4 = parseFormula(&em, equal_sides);

    /* CHECKING PARSING */
    std::cout << "\nTest" << equal_sides_cvc4 << " is: " << smt.query(equal_sides_cvc4) << std::endl;

    clearAllVariables();
}

/* ADAM is the ancestor of everyone 
 * Ancestor("LilyPotter", "HarryPotter") means LilyPotter is an ancestor of HarryPotter
 */
void quantifier__predicate__ancestor() {
    ExprManager em;
    SmtEngine smt(&em);

    /* ***************************** rapidnet: make Ancestor(x,y) ****************** */

    vector<Variable::TypeCode> types_rapidnet;
    types_rapidnet.push_back(Variable::STRING);
    types_rapidnet.push_back(Variable::STRING);
    PredicateSchema* ancestor_rapidnet = new PredicateSchema("Ancestor", types_rapidnet);

    /* ********************** rapidnet: forall x, Ancestor("Adam",x) ***************** */

    //make bound var
    StringVal* ADAM = new StringVal("Adam");
    Variable* str1 = new Variable(Variable::STRING, true);
    vector<Variable*> boundVarList;
    boundVarList.push_back(str1);

    // make the formula ancestor("Adam", x)
    // x is a bound variable
    vector<Term*> args;
    args.push_back(ADAM);
    args.push_back(str1);

    PredicateInstance* ancestor_adam_x = new PredicateInstance(ancestor_rapidnet, args);

    //make it quantifier
    Quantifier* forall_x__ancestor_ADAM_x = new Quantifier(Quantifier::FORALL, boundVarList, ancestor_adam_x);

    /* ********************** rapidnet: ancestor("Adam","Obama") ********************* */

    StringVal* OBAMA = new StringVal("Obama");
    vector<Term*> args_obama_rapidnet;
    args_obama_rapidnet.push_back(ADAM);
    args_obama_rapidnet.push_back(OBAMA);

    PredicateInstance* ancestor_adam_obama = new PredicateInstance(ancestor_rapidnet, args_obama_rapidnet);

    /* ******************************* CVC4 ******************************** */

    Expr ancestor_obama_cvc4 = parseFormula(&em, ancestor_adam_obama);
    Expr forall_x__ancestor_ADAM_x_cvc4 = parseFormula(&em, forall_x__ancestor_ADAM_x);

    /* **************************** CHECK SMT ******************************** */

    smt.assertFormula(forall_x__ancestor_ADAM_x_cvc4);
    std::cout << "\nSince " << forall_x__ancestor_ADAM_x_cvc4 << " hence "<<  ancestor_obama_cvc4 << " is: " << smt.query(ancestor_obama_cvc4) << std::endl;

    clearAllVariables();
}

/*
 * Function symbols testing
 * 
 */
void quantifier__function_child_younger_than_mother() {
    ExprManager em;
    SmtEngine smt(&em);

    /* ---------------------------- RAPIDNET ------------------------------ */
    //mother
    vector<Variable::TypeCode> domain_types;
    domain_types.push_back(Variable::STRING);
    FunctionSchema* mother_schema = new FunctionSchema("mother", domain_types, Variable::STRING);

    //
    vector<Term*> args;
    StringVal* MaliaObama = new StringVal("MaliaObama");
    args.push_back(MaliaObama);
    UserFunction* mother_malia = new UserFunction(mother_schema, args);

    StringVal* MichelleObama = new StringVal("MichelleObama");
    StringVal* BarbaraBush = new StringVal("BarbaraBush");

    Constraint* michelle_is_mother_of_malia = new Constraint(Constraint::EQ, mother_malia, MichelleObama);
    Constraint* barbara_is_mother_of_malia = new Constraint(Constraint::EQ, mother_malia, BarbaraBush);

    /* ------------------------------ CVC4 ------------------------------ */
    Expr michelle_is_mother_of_malia_cvc4 = parseFormula(&em, michelle_is_mother_of_malia);
    Expr barbara_is_mother_of_malia_cvc4 = parseFormula(&em, barbara_is_mother_of_malia);

    smt.assertFormula(michelle_is_mother_of_malia_cvc4);
    std::cout << "\nSince " << michelle_is_mother_of_malia_cvc4 << ", hence " << barbara_is_mother_of_malia_cvc4 << " is: " << smt.query(barbara_is_mother_of_malia_cvc4) << std::endl;

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
 */
void nested_function_check() {
    ExprManager em;
    SmtEngine smt(&em);

    std::cout << "\nNested Function Check" << std::endl;

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

    Expr forall_x__YOUNGER_x_motherx_cvc4 = parseFormula(&em, forall_x__YOUNGER_x_motherx);
    Expr malia_younger_than_her_mother_cvc4 = parseFormula(&em, malia_younger_than_her_mother);

    smt.assertFormula(forall_x__YOUNGER_x_motherx_cvc4);
    std::cout << "Since "<< forall_x__YOUNGER_x_motherx_cvc4 << " therefore " << malia_younger_than_her_mother_cvc4 << " is: " << smt.query(malia_younger_than_her_mother_cvc4) << std::endl;

    clearAllVariables();
}

//NDLog program should be free of recursion
//NDLog program should have no value as argument of a tuple
int main (int argc, char** argv)
{
  LogComponentEnable ("RapidNetDPGraph", LOG_LEVEL_INFO);
//  LogComponentEnable ("DPGraph", LOG_LEVEL_INFO);
//  LogComponentEnable ("Formula", LOG_LEVEL_INFO);
//  LogComponentEnable ("Dpool", LOG_LEVEL_INFO);
  LogComponentEnable ("Dpool", LOG_INFO);
  LogComponentEnable ("DPGraph", LOG_INFO);
  LogComponentEnable ("Formula", LOG_INFO);
//  LogComponentEnable ("DPGraph", LOG_INFO);
//  LogComponentEnable ("Formula", LOG_INFO);

  // test cvc4 parsing
  testIntegersArithmetic();
  testVariables();
  testBoundVariables();
  testBoundPredicate();
  testArithmeticNestedQuantifier();
  connective__x_gt_y__AND__y_gt_z__IMPLIES__x_gt_z();
  arithmetic__4_plus_3__minus__2_plus_1__equals__4();
  quantifier__predicate__ancestor(); 
  quantifier__function_child_younger_than_mother();
  nested_function_check();

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

  compile (overlogFile, provenance);
  return 0;
}
