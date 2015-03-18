#include "ns3/core-module.h"
#include "ns3/simulator-module.h"
#include "ns3/node-module.h"
#include "ns3/helper-module.h"

#include "ns3/load-balancing-module.h"
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
 * **************************************************************** *
 *                                                                  *
 *                            DEFINE TUPLES                         *
 *                                                                  *
 * **************************************************************** *
 */


/* switch connection */

#define switchConnection(Switch1, Switch2) \
  tuple(LoadBalancing::SWITCHCONNECTION, \
    attr("switchConnection_attr1", Ipv4Value, Switch1),\
    attr("switchConnection_attr2", Ipv4Value, Switch2))

#define insert_switchConnection(Switch1, Switch2) \
  app(Switch1) -> Insert(switchConnection(addr(Switch1),addr(Switch2)));

/* pktClient */

#define pktClient(Switch, Client) \
  tuple(LoadBalancing::PKTCLIENT, \
    attr("pktClient_attr1", Ipv4Value, Switch),\
    attr("pktClient_attr2", Ipv4Value, Client))

#define insert_pktClient(Switch, Client) \
  app(Switch) -> Insert(pktClient(addr(Switch),add(Client)));

/* 
 * **************************************************************** *
 *                                                                  *
 *                            DEFINE TUPLES                         *
 *                                                                  *
 * **************************************************************** *
 */








/* 
 * **************************************************************** *
 *                                                                  *
 *                            SIMULATION                            *
 *                                                                  *
 * **************************************************************** *
 */

#define nodeNum 4

using namespace std;
using namespace ns3;
using namespace ns3::rapidnet;
using namespace ns3::rapidnet::loadbalancing;

ApplicationContainer apps;

void InitMacTable()
{
  //insertmacport(1,2,2,"00:19:B9:F9:2D:0C");
}



int main(int argc, char *argv[])
{
  LogComponentEnable("LoadBalancing", LOG_LEVEL_INFO);
  LogComponentEnable("RapidNetApplicationBase", LOG_LEVEL_INFO);

  apps = InitRapidNetApps (nodeNum, Create<LoadBalancingHelper>());
  apps.Start (Seconds (0.0));
  apps.Stop (Seconds (10.0));

  //schedule (0.001, InitMacTable);

  Simulator::Run();
  Simulator::Destroy();
  return 0;
}

/* 
 * **************************************************************** *
 *                                                                  *
 *                            SIMULATION                            *
 *                                                                  *
 * **************************************************************** *
 */






