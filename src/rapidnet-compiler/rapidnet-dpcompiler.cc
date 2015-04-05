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
#include <ctime>

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
//#include "sdn-parse-smtlib.h"

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
  cout << "Pre-processing..." << endl;
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
      cout << "Generated pre-processed file " << processedFilename << endl;
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
    cout << "Generated dependency graph " << filename << endl;
}

/**
 * \brief Parses the overlog file and sets up overlog context and
 *        table information.
 */
void parseOverlog (string overlogFile, Ptr<OlContext> ctxt,
  Ptr<TableStore> tableStore, bool provenanceEnabled)
{
  string program = preprocessReadOverlogProgram (overlogFile);
  cout << "Parsing NDlog..." << endl;

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

	//Construct the dependency graph
	Ptr<DPGraph> graphNdlog (new DPGraph(ctxt));
	//graphNdlog->PrintGraph();

	//Base properties
	BaseProperty baseProp = BaseProperty();

	//Base relational properties
	BaseRelProperty baseRel = BaseRelProperty();
	//baseRel.Print();

	//Input recursive invariant
	Invariant inv = Invariant();
	inv.Print();
	Ptr<NewDPGraph> newGraph (new NewDPGraph(graphNdlog, inv));
	//newGraph->Print();

	//Construct mini graph for topological sorting
	Ptr<MiniGraph> miniGraph (new MiniGraph(newGraph, inv));
	//miniGraph->PrintGraph();

	//Dpool construction
	Ptr<Dpool> dpool (new Dpool(newGraph, miniGraph, baseProp, inv));
//  dpool->PrintDpool();
//  dpool->PrintAllDeriv();

	//Verify invariant property
	//dpool->VerifyInvariants(inv, baseRel);

	//Property verification
	//User-defined property

	Property p = Property();
	p.Print();

	NS_LOG_DEBUG("Property constructed.");
	//Verify the property
	int start_s=clock();
	bool res = CheckProperty(*dpool, p, baseRel);
	cout << endl;
	cout << "Is the property valid? " << (res?"Yes":"No");
	cout << endl;

	int stop_s=clock();
	cout << "Running time: " << (stop_s-start_s)/double(CLOCKS_PER_SEC)*1000 << "ms" << endl;

  //test_check_sat();
}


//NDLog program should be free of recursion
//NDLog program should have no value as argument of a tuple
int main (int argc, char** argv)
{
//  LogComponentEnable ("RapidNetDPGraph", LOG_LEVEL_FUNCTION);
//  LogComponentEnable ("DPGraph", LOG_LEVEL_FUNCTION);
//  LogComponentEnable ("Formula", LOG_LEVEL_FUNCTION);
//  LogComponentEnable ("Dpool", LOG_LEVEL_FUNCTION);
//  LogComponentEnable ("Verification", LOG_LEVEL_FUNCTION);
//  LogComponentEnable ("Property", LOG_LEVEL_FUNCTION);

//  LogComponentEnable ("RapidNetDPGraph", LOG_INFO);
  LogComponentEnable ("Dpool", LOG_INFO);
  LogComponentEnable ("DPGraph", LOG_INFO);
  LogComponentEnable ("Formula", LOG_INFO);
  LogComponentEnable ("Property", LOG_INFO);
  LogComponentEnable ("Verification", LOG_INFO);
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







