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

#include "ns3/sdn-mac-learning-module.h"
#include "ns3/rapidnet-module.h"
#include "ns3/values-module.h"
#include "ns3/ipv4-address.h"
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <stdio.h>

//Openflow connections
#define ofconn(host1, host2)\
  tuple(SdnMacLearning::OFCONN,			\
	attr("ofconn_attr1", Ipv4Value, host1),\
	attr("ofconn_attr2", Ipv4Value, host2))

#define insertofconn(host1, host2)			\
  app(host1) -> Insert (ofconn(addr(host1), addr(host2)));

//Miss entries. Now only mac is matched
#define missentry(sw, mac)\
  tuple(SdnMacLearning::MISSENTRY,		\
	attr("missEntry_attr1", Ipv4Value, sw),\
	attr("missEntry_attr2", StrValue, mac))

#define insertmissentry(sw, mac)\
  app(sw) -> Insert(missentry(addr(sw), mac));

#define macport(controller, sw, outport, dstmac)\
  tuple(SdnMacLearning::MACPORT,\
	attr("macPort_attr1", Ipv4Value, controller),\
	attr("macPort_attr2", Ipv4Value, sw),\
	attr("macPort_attr3", Int32Value, outport),\
	attr("macPort_attr4", StrValue, dstmac))

#define insertmacport(controller, sw, outport, dstmac)\
  app(controller) -> Insert(macport(addr(controller), addr(sw),\
				    outport, dstmac));

#define inport(sw, nei, port)\
  tuple(SdnMacLearning::INPORT,\
	attr("inPort_attr1", Ipv4Value, sw),	\
	attr("inPort_attr2", Ipv4Value, nei),		\
	attr("inPort_attr3", Int32Value, port))

#define insertinport(sw, nei, port)\
  app(sw) -> Insert(inport(addr(sw), addr(nei), port));

#define outport(sw, nei, port)\
  tuple(SdnMacLearning::OUTPORT,\
	attr("outPort_attr1", Ipv4Value, sw),	\
	attr("outPort_attr2", Ipv4Value, nei),		\
	attr("outPort_attr3", Int32Value, port))

#define insertoutport(sw, nei, port)\
  app(sw) -> Insert(outport(addr(sw), addr(nei), port));

#define packet(sw, nei, srcmac, dstmac)\
  tuple(SdnMacLearning::PACKET,\
	attr("packet_attr1", Ipv4Value, sw),	\
	attr("packet_attr2", Ipv4Value, nei),	\
	attr("packet_attr3", StrValue, srcmac),	\
	attr("packet_attr4", StrValue, dstmac))

#define insertpacket(sw, nei, srcmac, dstmac)\
  app(sw) -> Insert(packet(addr(sw), addr(nei), srcmac, dstmac));

#define nodeNum 4

using namespace std;
using namespace ns3;
using namespace ns3::rapidnet;
using namespace ns3::rapidnet::sdnmaclearning;

ApplicationContainer apps;

void InitMacTable()
{
  insertmacport(1,2,2,"00:19:B9:F9:2D:0C");
}

void InitPort()
{
  insertinport(2,3,1);
  insertoutport(2,4,2);
}

void InitMissEntry()
{
  insertmissentry(2,"00:19:B9:F9:2D:0C");
}

void InitOpenflowConn()
{
  insertofconn(1,2);
  insertofconn(2,1);
}

void SimulatePacket()
{
  insertpacket(2,3,"00:19:B9:F9:2D:0F", "00:19:B9:F9:2D:0C");
}

void PrintRelation()
{
  PrintRelation(apps, SdnMacLearning::FLOWENTRY);
}

int main(int argc, char *argv[])
{
  LogComponentEnable("SdnMacLearning", LOG_LEVEL_INFO);
  LogComponentEnable("RapidNetApplicationBase", LOG_LEVEL_INFO);

  apps = InitRapidNetApps (nodeNum, Create<SdnMacLearningHelper>());
  apps.Start (Seconds (0.0));
  apps.Stop (Seconds (10.0));

  schedule (0.001, InitMacTable);
  schedule (0.005, InitPort);
  schedule (0.010, InitMissEntry);
  schedule (0.015, InitOpenflowConn);
  schedule (0.020, SimulatePacket);  
  schedule (20.0, PrintRelation);

  Simulator::Run();
  Simulator::Destroy();
  return 0;
}




