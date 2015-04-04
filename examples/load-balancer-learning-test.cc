/*
 * 
 *                                    Host
 *                Controller            |
 *                  |\       \          |
 *                  | \       \         |
 *                  |  \       \---- Switch1 ----- Host
 *                  |   \              /           /
 *                  |    \            /           /
 *                  |     \          /           /           
 *                  |      \        /           /        
 * IncomingPacket ------- LoadBalancer ------------- Switch2 ----- Host
 *                  |               \         /
 *                  |                \       /
 *                  |                 \     /
 *                  |                  \   /
 *                  ---------------- Switch3 ----- Host
 *                                      |
 *                                      |
 *                                      |
 *                                     Host
 *
 *
 * Packets always end up on the load balancer
 * The load balancer decides which switch of the several possible ones the packet gets routed to
 * The switch the packet ends up on, does what sdn-mac-learning-bcast is to do
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

//Openflow connections
#define ofconn(host1, host2)\
  tuple(LoadBalancerLearning::OFCONN,			\
	attr("ofconn_attr1", Ipv4Value, host1),\
	attr("ofconn_attr2", Ipv4Value, host2))

#define insertofconn(host1, host2)			\
  app(host1) -> Insert (ofconn(addr(host1), addr(host2)));

#define flowentry(sw, mac, outport, priority)		\
  tuple(LoadBalancerLearning::FLOWENTRY,\
	attr("flowEntry_attr1", Ipv4Value, sw),\
	attr("flowEntry_attr2", StrValue, mac),\
	attr("flowEntry_attr4", Int32Value, outport),	\
	attr("flowEntry_attr3", Int32Value, priority))

#define insertflowentry(sw, mac, outport, priority)				\
  app(sw) -> Insert(flowentry(addr(sw), mac, outport, priority))

#define link(sw, nei, port)\
  tuple(LoadBalancerLearning::LINK,\
	attr("link_attr1", Ipv4Value, sw),	\
	attr("link_attr2", Ipv4Value, nei),		\
	attr("link_attr3", Int32Value, port))

#define insertlink(sw, nei, port)\
  app(sw) -> Insert(link(addr(sw), addr(nei), port));

#define initpacket(sw, nei, srcmac, dstmac)\
  tuple(LoadBalancerLearning::INITPACKET,\
	attr("initPacket_attr1", Ipv4Value, sw),	\
	attr("initPacket_attr2", Ipv4Value, nei),	\
	attr("initPacket_attr3", StrValue, srcmac),	\
	attr("initPacket_attr4", StrValue, dstmac))

#define insertpacket(sw, nei, srcmac, dstmac)\
  app(sw) -> Insert(initpacket(addr(sw), addr(nei), srcmac, dstmac));

#define maxPriority(sw, priority)\
  tuple(LoadBalancerLearning::MAXPRIORITY,\
	attr("maxPriority_attr1", Ipv4Value, sw),\
	attr("maxPriority_attr2", Int32Value, priority))

#define insertpriority(sw, priority)\
  app(sw) -> Insert(maxPriority(addr(sw), priority));

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

using namespace std;
using namespace ns3;
using namespace ns3::rapidnet;
using namespace ns3::rapidnet::loadbalancerlearning;

ApplicationContainer apps;

void InitPriority()
{
  insertpriority(2,0);
}


void InitPort()
{
  insertlink(2,3,1);
  insertlink(2,4,2);
}

void InitFlowTable()
{
  insertflowentry(2,"default",0,1);
  //  insertflowentry(2,"00:19:B9:F9:2D:0F",1,0);
}

void InitOpenflowConn()
{
  insertofconn(1,2);
  insertofconn(2,1);
}

void PacketInsertion1()
{
  insertpacket(2,3,"00:19:B9:F9:2D:0F", "00:19:B9:F9:2D:0C");
}

void PacketInsertion2()
{
  insertpacket(2,4,"00:19:B9:F9:2D:0C", "00:19:B9:F9:2D:0F");  
}

void PrintRelation()
{
  PrintRelation(apps, LoadBalancerLearning::FLOWENTRY);
  PrintRelation(apps, LoadBalancerLearning::PACKET);  
  PrintRelation(apps, LoadBalancerLearning::MAXPRIORITY);  
}

int main(int argc, char *argv[])
{
  LogComponentEnable("LoadBalancerLearning", LOG_LEVEL_INFO);
  LogComponentEnable("RapidNetApplicationBase", LOG_LEVEL_INFO);

  apps = InitRapidNetApps (nodeNum, Create<LoadBalancerLearningHelper>());
  apps.Start (Seconds (0.0));
  apps.Stop (Seconds (10.0));

  // schedule (0.002, InitPriority);
  // schedule (0.005, InitPort);
  // schedule (0.010, InitFlowTable);  
  // schedule (0.015, InitOpenflowConn);
  // schedule (0.020, PacketInsertion1);  
  // schedule (1.200, PacketInsertion2);    
  // schedule (20.0, PrintRelation);

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





