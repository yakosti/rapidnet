#include "ns3/core-module.h"
#include "ns3/simulator-module.h"
#include "ns3/node-module.h"
#include "ns3/arp-module.h"
#include "ns3/rapidnet-module.h"
#include "ns3/values-module.h"

#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <stdio.h>

//link operation
#define linkswc(src, next, port)			\
  tuple (Arp::LINKSWC, \
	 attr("linkSwc_attr1", Ipv4Value, src),	\
         attr("linkSwc_attr2", Ipv4Value, next),	\
         attr("linkSwc_attr3", Int32Value, port))

#define insertlinkswc(from, to, port)			    \
  app(from) -> Insert (linkswc(addr(from), addr(to), port));

#define linkhst(src, next, port)			\
  tuple (Arp::LINKHST, \
	 attr("linkHst_attr1", Ipv4Value, src),	\
         attr("linkHst_attr2", Ipv4Value, next),	\
         attr("linkHst_attr3", Int32Value, port))

#define insertlinkhst(from, to, port)			    \
  app(from) -> Insert (linkhst(addr(from), addr(to), port));

//ofconn operation
#define ofconnctl(src, dst) \
  tuple (Arp::OFCONNCTL, \
	 attr("ofconnCtl_attr1", Ipv4Value, src),	\
	 attr("ofconnCtl_attr2", Ipv4Value, dst))

#define insertofconnctl(from, to) \
  app(from) -> Insert (ofconnctl(addr(from), addr(to))); \

#define ofconnswc(src, dst) \
  tuple (Arp::OFCONNSWC, \
	 attr("ofconnSwc_attr1", Ipv4Value, src),	\
	 attr("ofconnSwc_attr2", Ipv4Value, dst))

#define insertofconnswc(from, to) \
  app(from) -> Insert (ofconnswc(addr(from), addr(to))); \

//flowentry operation
#define flowentry(switch, match, prio, action)\
  tuple (Arp::FLOWENTRY,\
	 attr("flowEntry_attr1", Ipv4Value, switch),	\
	 attr("flowEntry_attr2", StrValue, match),	\
	 attr("flowEntry_attr3", Int32Value, prio),		\
	 attr("flowEntry_attr4", StrValue, action))

#define insertflowentry(switch, match, prio, action)\
  app(switch) -> Insert (flowentry(addr(switch), match, prio, action));

//arp request operation
#define arprequest(host, srcip, srcmac, dstip, dstmac)\
  tuple (Arp::ARPREQUEST,\
	 attr("arpRequest_attr1", Ipv4Value, host),\
	 attr("arpRequest_attr2", Ipv4Value, srcip),\
	 attr("arpRequest_attr3", StrValue, srcmac),\
	 attr("arpRequest_attr4", Ipv4Value, dstip),\
	 attr("arpRequest_attr5", StrValue, dstmac))

#define insertarprequest(host, srcip, srcmac, dstip, dstmac)\
  app(host) -> Insert (arprequest(addr(host), addr(srcip), srcmac, addr(dstip), dstmac));

#define nodeNum 5

using namespace std;
using namespace ns3;
using namespace ns3::rapidnet;
using namespace ns3::rapidnet::arp;

ApplicationContainer apps;

void Print()
{
  //PrintRelation(apps, Sbgp::LINK);
  //PrintRelation(apps, Sbgp::ROUTE);
  PrintRelation(apps, Arp::ARPREPLY);
  //PrintRelation(apps, Sbgp::ADVERTISEMENTS);
}

void UpdateConnection()
{
  insertofconnctl(1,2);
  insertofconnctl(1,3);
  insertofconnswc(2,1);
  insertofconnswc(3,1);

  insertlinkswc(2,4,2);
  insertlinkhst(4,2,1);
  insertlinkswc(3,5,2);
  insertlinkhst(5,3,1);
}

void UpdateFlowentry()
{
  insertflowentry(2,"ARP",1,"controller");
  insertflowentry(3,"ARP",1,"controller");
}

void UpdateArpReq1()
{
  insertarprequest(4,4,"c4:f6:e0:12:db:db",5,"ff:ff:ff:ff:ff:ff");
}

void UpdateArpReq2()
{
  insertarprequest(5,5,"b6:4a:81:66:b8:07",4,"ff:ff:ff:ff:ff:ff");
}

int main(int argc, char *argv[])
{
  LogComponentEnable("Arp", LOG_LEVEL_INFO);
  LogComponentEnable("RapidNetApplicationBase", LOG_LEVEL_INFO);

  apps = InitRapidNetApps (nodeNum, Create<ArpHelper> ());
  apps.Start (Seconds (0.0));
  apps.Stop (Seconds (10.0));

  schedule (0.001, UpdateConnection);
  schedule (0.002, UpdateFlowentry);
  schedule (0.003, UpdateArpReq1);
  schedule (0.105, UpdateArpReq2);
  schedule (40.0, Print);

  Simulator::Run();
  Simulator::Destroy();
  return 0;
}
