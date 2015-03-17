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
    attr("trustedControllerMemory_attr1", Ipv4Value, Switch), \
    attr("trustedControllerMemory_attr2", Ipv4Value, Host) \
  )

#define insert_trustedControllerMemory(Controller, Switch, Host) \
  app(Controller) -> Insert(trustedControllerMemory(addr(Controller), addr(Switch), addr(Host)));




/* openConnectionToController */

#define openConnectionToController(Switch, Controller)\
  tuple (Firewall::OPENCONNECTIONTOCONTROLLER, \
    attr("openConnectionToController_attr1", Ipv4Value, Switch), \
    attr("openConnectionToController_attr2", Ipv4Value, Controller) \
  )

#define insert_openConnectionToController(Switch, Controller) \
  app(Switch) -> Insert(openConnectionToController(addr(Switch), addr(Controller)));


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

using namespace std;
using namespace ns3;
using namespace ns3::rapidnet;
using namespace ns3::rapidnet::firewall;

ApplicationContainer apps;

/*
 * Switch 1 receives a packet sent by Host Src 1 ( Trusted port 1)
 * to Host Dst 2 (??)
 */
void
InitPktIn1 ()
{
  insert_pktIn(1,1,1,2);
}

/*
 * The controller remembers that 
 * Switch 1 should trust Host 2
 */
void 
InitControllerMemory() 
{
  insert_trustedControllerMemory(1,1,2);
}

/*
 * Switch 1 can talk to the controller 
 */
void 
InitOpenConnectionToController() 
{
  insert_openConnectionToController(1,1);
}

/*
 * Switch 1 can send packets from 
 * Src Host 3 (trusted port 1) -> Dst Host 4 (untrusted port 2)
 */
void 
InitPerFlowRule()
{
  insert_perFlowRule(1,3,1,4,2);
}

int
main (int argc, char *argv[])
{
  LogComponentEnable("Firewall", LOG_LEVEL_INFO);
  LogComponentEnable("RapidNetApplicationBase", LOG_LEVEL_INFO);

  apps = InitRapidNetApps (2, Create<FirewallHelper> ());
  apps.Start (Seconds (0.0));
  apps.Stop (Seconds (10.0));

  schedule (0.0002, InitOpenConnectionToController);
  schedule (0.0003, InitPktIn1);
  schedule (0.0005, InitPerFlowRule); /* GIVES ME AN ERROR HERE! */

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


