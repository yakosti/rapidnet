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
#include "sdn-property.h"
#include "sdn-verification.h"
#include "sdn-test.h"
#include "z3++.h"

using namespace std;
using namespace ns3;
using namespace ns3::rapidnet_compiler;

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
//  list<Variable::TypeCode> tlist (9, Variable::STRING);
//  Tuple tp = Tuple("verifyPath", tlist);
//  const vector<Variable*> arg = tp.GetArgs();
//  vector<Variable*> quantArg(1, arg[0]);
//  IntVal* value = new IntVal(10000);
//  Constraint* ct = new Constraint(Constraint::EQ, arg[0], value);
//  Quantifier qtf (Quantifier::EXISTS, quantArg, ct);
//  Annotation anno (&tp, &qtf);
//  testMap.insert(AnnotMap::value_type("verifyPath", &anno));
  Ptr<Dpool> dpool (new Dpool(graphNdlog, testMap));
  //dpool->PrintDeriv("ePingPongFinish");
  NS_LOG_DEBUG("Dpool constructed.");
  //User-defined property
  Property p = Property();

  NS_LOG_DEBUG("Property constructed.");
  //Verify the property
  map<Variable*, int> assignment;
  bool res = CheckProperty(*dpool, p, assignment);
  cout << "The property is valid: " << res << endl;

  /* adding smt solver part */
  //const DerivNodeList& dlist = dpool->GetDerivList("advertisements");
  //writeToFile("testing_constraints", dlist); //laykuan testing

  test_check_sat();

  //Use DerivNode::GetAllObligs() to get all proof obligations
}


//NDLog program should be free of recursion
//NDLog program should have no value as argument of a tuple
int main (int argc, char** argv)
{
  test_parsing();

  LogComponentEnable ("RapidNetDPGraph", LOG_LEVEL_FUNCTION);
//  LogComponentEnable ("DPGraph", LOG_LEVEL_FUNCTION);
  LogComponentEnable ("Formula", LOG_LEVEL_FUNCTION);
//  LogComponentEnable ("Dpool", LOG_LEVEL_FUNCTION);
  LogComponentEnable ("Property", LOG_LEVEL_FUNCTION);
  LogComponentEnable ("Dpool", LOG_INFO);
//  LogComponentEnable ("DPGraph", LOG_INFO);
//  LogComponentEnable ("Formula", LOG_INFO);
//  LogComponentEnable ("Property", LOG_INFO);

  //test_parsing();

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







