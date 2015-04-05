/********************
 *                   Controller(1)
 *                         |
 *                         |
 *                 -------------------------
 *                | port25 | sw(2) | port26 | 
 *                 -------------------------
 *
 *         -------------------------
 *        | port35 | sw(3) | port36 | 
 *         -------------------------
 *
 *
 *
 *         -------------------------
 *        | port45 | sw(4) | port46 | 
 *         -------------------------
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
 ********************/


#include "ns3/core-module.h"
#include "ns3/simulator-module.h"
#include "ns3/node-module.h"
#include "ns3/helper-module.h"

#include "ns3/sdn-mac-learning-bcast-module.h"
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


/* ============== Database for controller/switch ==================== */

//Openflow connections
#define ofconn(host1, host2)\
  tuple(SdnMacLearningBcast::OFCONN,			\
	attr("ofconn_attr1", Ipv4Value, host1),\
	attr("ofconn_attr2", Ipv4Value, host2))

#define insert_ofconn(host1, host2)			\
  app(host1) -> Insert (ofconn(addr(host1), addr(host2)));

/* ============== Database for controller/switch ==================== */








/* ====================== Database for switch ======================== */

/* flow entry */
#define flowentry(sw, mac, outport, priority)		\
  tuple(SdnMacLearningBcast::FLOWENTRY,\
	attr("flowEntry_attr1", Ipv4Value, sw),\
	attr("flowEntry_attr2", StrValue, mac),\
	attr("flowEntry_attr3", Int32Value, outport),	\
	attr("flowEntry_attr4", Int32Value, priority))

#define insert_flowentry(sw, mac, outport, priority)				\
  app(sw) -> Insert(flowentry(addr(sw), mac, outport, priority))

/* link */
#define link(sw, nei, port)\
  tuple(SdnMacLearningBcast::LINK,\
	attr("link_attr1", Ipv4Value, sw),	\
	attr("link_attr2", Ipv4Value, nei),		\
	attr("link_attr3", Int32Value, port))

#define insert_link(sw, nei, port)\
  app(sw) -> Insert(link(addr(sw), addr(nei), port));

/* priority */
#define maxPriority(sw, priority)\
  tuple(SdnMacLearningBcast::MAXPRIORITY,\
	attr("maxPriority_attr1", Ipv4Value, sw),\
	attr("maxPriority_attr2", Int32Value, priority))

#define insert_priority(sw, priority)\
  app(sw) -> Insert(maxPriority(addr(sw), priority));

/* ====================== Database for switch ======================== */







/* ======================== Database for host ======================== */

#define initpacket(sw, nei, srcmac, dstmac)\
  tuple(SdnMacLearningBcast::INITPACKET,\
  attr("initPacket_attr1", Ipv4Value, sw),  \
  attr("initPacket_attr2", Ipv4Value, nei), \
  attr("initPacket_attr3", StrValue, srcmac), \
  attr("initPacket_attr4", StrValue, dstmac))

#define insert_packet(sw, nei, srcmac, dstmac)\
  app(sw) -> Insert(initpacket(addr(sw), addr(nei), srcmac, dstmac));

/* ======================== Database for host ======================== */

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
 *                           SIMULATE                                  *
 *                                                                     *
 * ******************************************************************* *
 */

#define nodeNum 6

#define CONTROLLER 1

#define SWITCH2 2
#define SWITCH3 3
#define SWITCH4 4

#define SWITCH2_TopPriority 2
#define SWITCH3_TopPriority 1
#define SWITCH4_TopPriority 4

#define HOST5 5
#define HOST6 6

#define HOST5_MacAddress "00:19:B9:F9:2D:0C"
#define HOST6_MacAddress "00:19:B9:F9:2D:0F"

using namespace std;
using namespace ns3;
using namespace ns3::rapidnet;
using namespace ns3::rapidnet::sdnmaclearningbcast;

ApplicationContainer apps;

void InitPriority()
{
  insert_priority(SWITCH2, SWITCH2_TopPriority);
  insert_priority(SWITCH3, SWITCH3_TopPriority);
  insert_priority(SWITCH4, SWITCH4_TopPriority);
}

/*
 * All switches are connected to all hosts via some sort of port 
 * Note the naming pattern for ports
 */
void InitPort()
{
  // switch2
  insert_link(SWITCH3, HOST5, 25);
  insert_link(HOST5, SWITCH2, 25);
  insert_link(SWITCH3, HOST6, 26);
  insert_link(HOST6, SWITCH2, 26);

  // switch3
  insert_link(SWITCH3, HOST5, 35);
  insert_link(HOST5, SWITCH3, 35);
  insert_link(SWITCH3, HOST6, 36);
  insert_link(HOST6, SWITCH3, 36);

  // switch4
  insert_link(SWITCH2, HOST5, 45);
  insert_link(SWITCH2, HOST6, 46);
}

/* Switch 2 is connected to HOST5 initially 
 * flowEntry(@Switch, MacAdd, OutPort, Priority)
 */
void InitFlowTable()
{
  //insert_flowentry(SWITCH2,"default",0,1);
  insert_flowentry(SWITCH2, HOST5_MacAddress, 25, SWITCH2_TopPriority);
  insert_flowentry(SWITCH2, HOST6_MacAddress, 26, SWITCH2_TopPriority);

  insert_flowentry(SWITCH3, HOST6_MacAddress, 36, SWITCH3_TopPriority);
}

/*
 * All switches connected to controller and vice versa
 */
void InitOpenflowConn()
{
  insert_ofconn(CONTROLLER, SWITCH2);
  insert_ofconn(SWITCH2, CONTROLLER);

  insert_ofconn(CONTROLLER, SWITCH3);
  insert_ofconn(SWITCH3, CONTROLLER);

  insert_ofconn(CONTROLLER, SWITCH4);
  insert_ofconn(SWITCH4, CONTROLLER);
}

/*
 * Host 5 sends a packet to Host 6 via switch 2
 * has flow entry match 
 */
void PacketInsertion1()
{
  insert_packet(HOST5, SWITCH2, HOST5_MacAddress, HOST6_MacAddress);
}

/*
 * No flow entry, must query controller
 */
void PacketInsertion2()
{
  insert_packet(HOST6, SWITCH3, HOST5_MacAddress, HOST6_MacAddress);  
}

void PrintRelation()
{
  PrintRelation(apps, SdnMacLearningBcast::FLOWENTRY);
  PrintRelation(apps, SdnMacLearningBcast::PACKET);  
  PrintRelation(apps, SdnMacLearningBcast::MAXPRIORITY);  
}

int main(int argc, char *argv[])
{
  LogComponentEnable("SdnMacLearningBcast", LOG_LEVEL_INFO);
  LogComponentEnable("RapidNetApplicationBase", LOG_LEVEL_INFO);

  apps = InitRapidNetApps (nodeNum, Create<SdnMacLearningBcastHelper>());
  apps.Start (Seconds (0.0));
  apps.Stop (Seconds (10.0));

  schedule (0.002, InitPriority);
  schedule (0.005, InitPort);
  schedule (0.010, InitFlowTable);  
  schedule (0.015, InitOpenflowConn);
  schedule (0.020, PacketInsertion1);  
  schedule (1.200, PacketInsertion2);    

  Simulator::Run();
  Simulator::Destroy();
  return 0;
}

/*
 * ******************************************************************* *
 *                                                                     *
 *                           SIMULATE                                  *
 *                                                                     *
 * ******************************************************************* *
 */




