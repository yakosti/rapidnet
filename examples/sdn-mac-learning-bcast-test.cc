/********************
 *                   Controller(1)
 *                         |
 *                         |
 *       sw(3)  -- port1  sw(2) port2 -- sw(4)
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
	attr("flowEntry_attr4", Int32Value, outport),	\
	attr("flowEntry_attr3", Int32Value, priority))

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

#define nodeNum 4

using namespace std;
using namespace ns3;
using namespace ns3::rapidnet;
using namespace ns3::rapidnet::sdnmaclearningbcast;

ApplicationContainer apps;

void InitPriority()
{
  insert_priority(2,0);
}


void InitPort()
{
  insert_link(2,3,1);
  insert_link(2,4,2);
}

void InitFlowTable()
{
  insert_flowentry(2,"default",0,1);
  insert_flowentry(2,"00:19:B9:F9:2D:0F",1,0);
}

void InitOpenflowConn()
{
  insert_ofconn(1,2);
  insert_ofconn(2,1);
}

void PacketInsertion1()
{
  insert_packet(2,3,"00:19:B9:F9:2D:0F", "00:19:B9:F9:2D:0C");
}

void PacketInsertion2()
{
  insert_packet(2,4,"00:19:B9:F9:2D:0C", "00:19:B9:F9:2D:0F");  
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
  schedule (20.0, PrintRelation);

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




