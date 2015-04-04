/*
 * ************************************************************************** *
 * 
 *                           --------------- ----------------------
 *                          | Controller(1) |----------------      |
 *                           ---------------                 |     |
 *                                 |                         |     |
 *                                 |                         |     |
 *                     -------------------------             |     |
 *                    | port25 | sw(1) | port26 |            |     |
 *                     -------------------------             |     |
 *                   /                                       |     |
 *   -------------- /       -------------------------        |     |
 *  | LoadBalancer |----- | port35 | sw(3) | port36 | -------|     |
 *   -------------- \      -------------------------               |
 *                   \                                             |
 *                     -------------------------                   |
 *                    | port45 | sw(4) | port46 |------------------
 *                     -------------------------
 *
 *                                           -------
 *                                          | Host4 |
 *                                           -------
 * 
 *                                           -------
 *                                          | Host5 |
 *                                           -------
 *
 *                                           -------
 *                                          | Host6 |
 *                                           -------
 * 
 * Port XY meast switch X is connected to Host Y
 * 
 *                
 * 
 * Packets always end up on the load balancer
 * The load balancer decides which switch of the several possible ones the packet gets routed to
 * The switch the packet ends up on, does what sdn-mac-learning-bcast is to do
 * ************************************************************************** *
 */


#include "ns3/core-module.h"
#include "ns3/simulator-module.h"
#include "ns3/node-module.h"
#include "ns3/helper-module.h"

#include "ns3/load-balancer-learning-module.h"
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
 * ******************************************************************* *
 *                                                                     *
 *                           INITIALIZE                                *
 *                                                                     *
 * ******************************************************************* *
 */

/* ================== switch/controller program ====================== */

//Openflow connections
#define ofconn(host1, host2)\
  tuple(LoadBalancerLearning::OFCONN,			\
	attr("ofconn_attr1", Ipv4Value, host1),\
	attr("ofconn_attr2", Ipv4Value, host2))

#define insert_ofconn(host1, host2)			\
  app(host1) -> Insert (ofconn(addr(host1), addr(host2)));

/* ================== switch/controller program ====================== */





/* ======================== switch program =========================== */

/* flow entry */
#define flowentry(sw, mac, outport, priority)		\
  tuple(LoadBalancerLearning::FLOWENTRY,\
	attr("flowEntry_attr1", Ipv4Value, sw),\
	attr("flowEntry_attr2", StrValue, mac),\
	attr("flowEntry_attr3", Int32Value, outport),	\
	attr("flowEntry_attr4", Int32Value, priority))

#define insert_flowentry(sw, mac, outport, priority)				\
  app(sw) -> Insert(flowentry(addr(sw), mac, outport, priority))



/* link */
#define link(sw, nei, port)\
  tuple(LoadBalancerLearning::LINK,\
	attr("link_attr1", Ipv4Value, sw),	\
	attr("link_attr2", Ipv4Value, nei),		\
	attr("link_attr3", Int32Value, port))

#define insert_link(sw, nei, port)\
  app(sw) -> Insert(link(addr(sw), addr(nei), port));



/* packet */
#define initpacket(SrcHost, LoadBalancer, srcmac, dstmac)\
  tuple(LoadBalancerLearning::INITPACKET,\
	attr("initPacket_attr1", Ipv4Value, SrcHost),\
	attr("initPacket_attr2", Ipv4Value, LoadBalancer),\
	attr("initPacket_attr3", StrValue, srcmac),\
	attr("initPacket_attr4", StrValue, dstmac))

#define insert_packet(SrcHost, LoadBalancer, srcmac, dstmac)\
  app(SrcHost) -> Insert(initpacket(addr(SrcHost), addr(LoadBalancer), srcmac, dstmac));

/* priority */
#define maxPriority(sw, priority)\
  tuple(LoadBalancerLearning::MAXPRIORITY,\
	attr("maxPriority_attr1", Ipv4Value, sw),\
	attr("maxPriority_attr2", Int32Value, priority))

#define insert_priority(sw, priority)\
  app(sw) -> Insert(maxPriority(addr(sw), priority));

/* ======================== switch program =========================== */






/* ===================== load balancer program ======================= */

#define switchMapping(LoadBalancer, Switch, SwitchNum)\
  tuple(LoadBalancerLearning::SWITCHMAPPING,\
    attr("switchMapping_attr1", Ipv4Value, LoadBalancer),\
    attr("switchMapping_attr2", Ipv4Value, Switch),\
    attr("switchMapping_attr3", Int32Value, SwitchNum))

#define insert_switchMapping(LoadBalancer, Switch, SwitchNum)\
  app(LoadBalancer) -> Insert(switchMapping(addr(LoadBalancer), addr(Switch), SwitchNum));

/* ===================== load balancer program ======================= */

/*
 * ******************************************************************* *
 *                                                                     *
 *                           INITIALIZE                                *
 *                                                                     *
 * ******************************************************************* *
 */







/*
 * ******************************************************************* *
 *                                                                     *
 *                             SIMULATE                                *
 *                                                                     *
 * ******************************************************************* *
 */

#define nodeNum 8

#define SWITCH1 1
#define SWITCH2 2
#define SWITCH3 3

#define SWITCH1_TopPriority 1
#define SWITCH2_TopPriority 2
#define SWITCH3_TopPriority 3

#define HOST4 4
#define HOST5 5
#define HOST6 6

#define HOST4_MacAddress "00:19:B9:F9:2G:0C"
#define HOST5_MacAddress "00:19:B9:F9:2F:0D"
#define HOST6_MacAddress "00:19:B9:F9:2A:0E"

#define LOAD_BALANCER 7

#define CONTROLLER 8


using namespace std;
using namespace ns3;
using namespace ns3::rapidnet;
using namespace ns3::rapidnet::loadbalancerlearning;

ApplicationContainer apps;

void InitPriority()
{
  insert_priority(SWITCH1, SWITCH1_TopPriority);
  insert_priority(SWITCH2, SWITCH2_TopPriority);
  insert_priority(SWITCH3, SWITCH3_TopPriority);
}

/* all switches are connected to all hosts 
 */
void InitPort()
{
  /* SWITCH 1 */
  insert_link(SWITCH1, HOST4, 14);
  insert_link(HOST4, SWITCH1, 14);
  insert_link(SWITCH1, HOST5, 15);
  insert_link(HOST5, SWITCH1, 15);
  insert_link(SWITCH1, HOST6, 16);
  insert_link(HOST6, SWITCH1, 16);

  /* SWITCH 2 */
  insert_link(SWITCH2, HOST4, 24);
  insert_link(HOST4, SWITCH2, 24);
  insert_link(SWITCH2, HOST5, 25);
  insert_link(HOST5, SWITCH2, 24);
  insert_link(SWITCH2, HOST6, 26);
  insert_link(HOST6, SWITCH2, 26);

  /* SWITCH 3 */
  insert_link(SWITCH3, HOST4, 34);
  insert_link(HOST4, SWITCH3, 34);
  insert_link(SWITCH3, HOST5, 35);
  insert_link(HOST5, SWITCH3, 35);
  insert_link(SWITCH3, HOST6, 36);
  insert_link(HOST6, SWITCH3, 36);
}

/* flowEntry(@Switch, MacAdd, OutPort, Priority) */
void InitFlowTable()
{
  insert_flowentry(SWITCH1, HOST6_MacAddress, 14, SWITCH1_TopPriority);

  insert_flowentry(SWITCH2, "default", 24, SWITCH2_TopPriority);

  insert_flowentry(SWITCH3, "default", 34, 1);
  insert_flowentry(SWITCH3, "default", 35, 0);
  insert_flowentry(SWITCH3, "default", 36, 0);
}

/* Controller is connected to all switches
 * all switches connected to the controler
 */
void InitOpenflowConn()
{
  // Switch 1
  insert_ofconn(CONTROLLER,SWITCH1);
  insert_ofconn(SWITCH1,CONTROLLER);

  // Switch 2
  insert_ofconn(CONTROLLER,SWITCH2);
  insert_ofconn(SWITCH2,CONTROLLER);

  // Switch 3
  insert_ofconn(CONTROLLER,SWITCH3);
  insert_ofconn(SWITCH3,CONTROLLER);
}

/* initPacket(@Host, LoadBalancer, SrcMac, DstMac) */
void PacketInsertion1()
{
  insert_packet(HOST4, LOAD_BALANCER, HOST4_MacAddress, HOST5_MacAddress);
  insert_packet(HOST5, LOAD_BALANCER, HOST5_MacAddress, HOST6_MacAddress);
  insert_packet(HOST6, LOAD_BALANCER, HOST6_MacAddress, HOST4_MacAddress);
}


void PrintRelation()
{
  PrintRelation(apps, LoadBalancerLearning::FLOWENTRY);
  PrintRelation(apps, LoadBalancerLearning::PACKET);  
  PrintRelation(apps, LoadBalancerLearning::MAXPRIORITY);  
  PrintRelation(apps, LoadBalancerLearning::PACKET);  
}


/* Load balancer knows which numbers refers to which switch */
void InitSwitchMappings() 
{
  insert_switchMapping(LOAD_BALANCER, SWITCH1, 1);
  insert_switchMapping(LOAD_BALANCER, SWITCH2, 2);
  insert_switchMapping(LOAD_BALANCER, SWITCH3, 3);
}

int main(int argc, char *argv[])
{
  LogComponentEnable("LoadBalancerLearning", LOG_LEVEL_INFO);
  LogComponentEnable("RapidNetApplicationBase", LOG_LEVEL_INFO);

  apps = InitRapidNetApps (nodeNum, Create<LoadBalancerLearningHelper>());
  apps.Start (Seconds (0.0));
  apps.Stop (Seconds (10.0));

  schedule (0.001, InitSwitchMappings);
  schedule (0.015, InitOpenflowConn);
  schedule (0.002, InitPriority);
  schedule (0.005, InitPort);
  schedule (0.010, InitFlowTable);  
 
  schedule (0.020, PacketInsertion1);     
  //schedule (20.0, PrintRelation);

  Simulator::Run();
  Simulator::Destroy();
  return 0;
}

/*
 * ******************************************************************* *
 *                                                                     *
 *                             SIMULATE                                *
 *                                                                     *
 * ******************************************************************* *
 */





