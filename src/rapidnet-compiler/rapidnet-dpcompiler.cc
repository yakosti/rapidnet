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

  printFreeVariablesDeclaration();
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

  printFreeVariablesDeclaration();
  cout << implies_smt << endl;

  clearAllVariables();
}

/* 
   DECLARING
   ---------
   (set-logic QF_UFLIA)
   (declare-fun iseven (Int) Bool)
   (assert (even 2))
   (assert (not (even 3)))

   CHECKING
   --------
   (assert (even 2))
   (check-sat)

   (assert (even 3))
   (check-sat)
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

  // make the formula iseven(3)
  IntVal* three = new IntVal(3);
  vector<Term*> args_three;
  args_three.push_back(three);
  PredicateInstance* iseven_3 = new PredicateInstance(iseven_schema, args_three);

  /* what to do */
  cout << "\n------------------ Test iseven(n) ----------------------" << endl;
  string PredicateSchema_smtlib = parsePredicateSchema(iseven_schema);
  cout << PredicateSchema_smtlib << endl;

  /* ***************************** parsing ************************** */

  clearAllVariables();
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
// LogComponentEnable ("RapidNetDPGraph", LOG_LEVEL_INFO);
//  LogComponentEnable ("DPGraph", LOG_LEVEL_INFO);
//  LogComponentEnable ("Formula", LOG_LEVEL_INFO);
//  LogComponentEnable ("Dpool", LOG_LEVEL_INFO);
// LogComponentEnable ("Dpool", LOG_INFO);
//  LogComponentEnable ("DPGraph", LOG_INFO);
//  LogComponentEnable ("Formula", LOG_INFO);

  /* testing parsing */
  testIntegersArithmetic();
  testVariables();
  connective__x_gt_y__AND__y_gt_z__IMPLIES__x_gt_z();
  testBoundVariables(); 
  testExistVariables();
  testMixedQuantifiers();
  testEvenPredicate();

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
