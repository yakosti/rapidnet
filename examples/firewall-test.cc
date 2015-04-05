/* -*- Mode:C++; c-file-style:"gnu"; indent-tabs-mode:nil; -*- */
/*
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
 */

#include "ns3/core-module.h"
#include "ns3/simulator-module.h"
#include "ns3/node-module.h"
#include "ns3/helper-module.h"

#include "ns3/firewall-module.h"
#include "ns3/rapidnet-module.h"
#include "ns3/values-module.h"
#include "ns3/ipv4-address.h"
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <stdio.h>

/*
 * Representation in NS3
 * ---------------------
 * Host: Ipv4Value
 * Controller: Ipv4Value
 * Switch: Ipv4Value
 * Port: Int32Value
 * 
 * Primary Key
 * ----------- 
 * pktIn(@Switch, Src, SrcPort, Dst) => key(1,2,3,4)
 * perFlowRule(@Switch, Src, SrcPort, Dst, DstPort) => key(1,2,3,4,5)
 * openConnectionToController(@Switch, Controller) => key(1) 
 * trustedControllerMemory(@Controller, Switch, Host) => key(2,3)
 */

/* 
 * ***************************************************************************** *
 *                                                                               *
 *                                  DEFINITIONS                                  *
 *                                                                               *
 * ***************************************************************************** *
 */

/* switch */

#define pktIn(Switch, Src, SrcPort, Dst) \
  tuple (Firewall::PKTIN, \
    attr ("pktIn_attr1", Ipv4Value, Switch), \
    attr ("pktIn_attr2", Ipv4Value, Src), \
    attr ("pktIn_attr3", Int32Value, SrcPort), \
    attr ("pktIn_attr4", Ipv4Value, Dst) \
  )

#define insert_pktIn(Switch, Src, SrcPort, Dst) \
  app(Switch) -> Insert(pktIn(addr(Switch), addr(Src), SrcPort, addr(Dst)));




/* controller memory */

#define trustedControllerMemory(Controller, Switch, Host)\
  tuple (Firewall::TRUSTEDCONTROLLERMEMORY, \
    attr("trustedControllerMemory_attr1", Ipv4Value, Controller), \
    attr("trustedControllerMemory_attr2", Ipv4Value, Switch), \
    attr("trustedControllerMemory_attr3", Ipv4Value, Host) \
  )

#define insert_trustedControllerMemory(Controller, Switch, Host) \
  app(Controller) -> Insert(trustedControllerMemory(addr(Controller), addr(Switch), addr(Host)));




/* openConnectionToController */

#define connection(Switch, Controller)\
  tuple (Firewall::CONNECTION, \
    attr("connection_attr1", Ipv4Value, Switch), \
    attr("connection_attr2", Ipv4Value, Controller) \
  )

#define insert_connection(Switch, Controller) \
  app(Switch) -> Insert(connection(addr(Switch), addr(Controller)));


/* perFlowRule */
#define perFlowRule(Switch, Src, SrcPort, Dst, DstPort) \
  tuple (Firewall::PERFLOWRULE, \
    attr("perFlowRule_attr1", Ipv4Value, Switch), \
    attr("perFlowRule_attr2", Ipv4Value, Src), \
    attr("perFlowRule_attr3", Int32Value, SrcPort), \
    attr("perFlowRule_attr4", Ipv4Value, Dst), \
    attr("perFlowRule_attr5", Int32Value, DstPort) \
  )

#define insert_perFlowRule(Switch, Src, SrcPort, Dst, DstPort) \
  app(Switch) -> Insert(perFlowRule(addr(Switch), addr(Src), SrcPort, addr(Dst), DstPort));

/* 
 * ***************************************************************************** *
 *                                                                               *
 *                                  DEFINITIONS                                  *
 *                                                                               *
 * ***************************************************************************** *
 */










/* 
 * ***************************************************************************** *
 *                                                                               *
 *                           RUNNING SIMULATION                                  *
 *                                                                               *
 * ***************************************************************************** *
 */

#define nodeNum 5

#define CONTROLLER 1
#define SWITCH 2
#define HOST3 3
#define HOST4 4 

#define TRUSTED_PORT 1
#define UNTRUSTED_PORT 2

using namespace std;
using namespace ns3;
using namespace ns3::rapidnet;
using namespace ns3::rapidnet::firewall;

ApplicationContainer apps;

/*
 * pktIn(Switch, Src, SrcPort, Dst)
 * 
 * SWITCH receives a packet sent by HOST3 ( TRUSTED_PORT) to HOST4 (UNTRUSTED_PORT)
 * send to untrusted host
 */
void
SimulatePktIn1 ()
{
  insert_pktIn(SWITCH, HOST3, TRUSTED_PORT, HOST4);
}

/*
 * Switch receives a packet sent by HOST3 (TRUSTED_PORT)
 * to Host Dst 4 (untrusted port 2)
 * 
 * This is sent, since InitControllerMemory remembers this
 */
void
SimulatePktIn2 ()
{
  insert_pktIn(1,1,1,4);
}

/*
 * Switch 1 receives a packet sent by Host Src 3 ( Trusted port 1)
 * to Host Dst 5 (untrusted port 2)
 * 
 * This is sent, since InitControllerMemory remembers this
 */
void
SimulatePktIn3 ()
{
  insert_pktIn(1,3,1,5);
}

/*
 * The controller remembers that 
 * Switch 1 should trust Host 4 (from untrusted port 2)
 */
void 
InitControllerMemory() 
{
  insert_trustedControllerMemory(1,1,4);
}

/*
 * Switch 1 can talk to the controller 
 */
void 
InitConnection() 
{
  insert_connection(1,1);
}

/*
 * Switch 1 can send packets from 
 * Src Host 3 (trusted port 1) -> Dst Host 5 (untrusted port 2)
 */
void 
InitPerFlowRule()
{
  insert_perFlowRule(1,3,1,5,2);
}

void PrintRelation()
{
  PrintRelation(apps, Firewall::PKTRECEIVED);
}

int
main (int argc, char *argv[])
{
  LogComponentEnable("Firewall", LOG_LEVEL_INFO);
  LogComponentEnable("RapidNetApplicationBase", LOG_LEVEL_INFO);

  apps = InitRapidNetApps (nodeNum, Create<FirewallHelper> ());
  apps.Start (Seconds (0.0));
  apps.Stop (Seconds (10.0));

  schedule (0.0002, InitConnection);
  schedule (0.0005, InitPerFlowRule);
  schedule(0.0005, InitControllerMemory); 

  schedule (0.006, SimulatePktIn1); /* dropped */
  schedule (0.007, SimulatePktIn2); /* sent */
  schedule (0.008, SimulatePktIn3); /* sent */

  schedule (20, PrintRelation); /* trace */

  Simulator::Run ();
  Simulator::Destroy ();
  return 0;
}

/* 
 * ***************************************************************************** *
 *                                                                               *
 *                           RUNNING SIMULATION                                  *
 *                                                                               *
 * ***************************************************************************** *
 */


