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
  app(Switch) -> Insert(pktClient(addr(Switch),addr(Client)));





/* loadBalancerConnectionToServer */
#define loadBalancerConnectionToServer(SwitchLoadBalancer, Server) \
  tuple(LoadBalancing::LOADBALANCERCONNECTIONTOSERVER, \
    attr("loadBalancerConnectionToServer_attr1", Ipv4Value, SwitchLoadBalancer),\
    attr("loadBalancerConnectionToServer_attr2", StrValue, Server))

#define insert_loadBalancerConnectionToServer(SwitchLoadBalancer, Server) \
  app(SwitchLoadBalancer) -> \
    Insert(loadBalancerConnectionToServer(addr(SwitchLoadBalancer), Server));

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

/* define constants */
#define nodeNum 11
#define GATEWAY_SWITCH 10
#define LOAD_BALANCER_SWITCH 11

/* boilderplate */
using namespace std;
using namespace ns3;
using namespace ns3::rapidnet;
using namespace ns3::rapidnet::loadbalancing;

ApplicationContainer apps;

/* init connection between gateway and load-balancer */
void init_switchConnection() {
  insert_switchConnection(GATEWAY_SWITCH, LOAD_BALANCER_SWITCH);
}

/* model 5 packets send from the same two clients */
void init_pktClient() {
  insert_pktClient(GATEWAY_SWITCH, 1);
  insert_pktClient(GATEWAY_SWITCH, 1);
  //insert_pktClient(GATEWAY_SWITCH, 2);
  //insert_pktClient(GATEWAY_SWITCH, 2);
  //insert_pktClient(GATEWAY_SWITCH, 2);
}

/* model 2 servers to send stuff to */
void init_loadBalancerConnectionToServer() {
  insert_loadBalancerConnectionToServer(LOAD_BALANCER_SWITCH, \
    "728ff2b66172bf95a00ec29a11a5f15b249be11a"); //hash 1
}

/* run the simulation */
int main(int argc, char *argv[])
{
  LogComponentEnable("LoadBalancing", LOG_LEVEL_INFO);
  LogComponentEnable("RapidNetApplicationBase", LOG_LEVEL_INFO);

  apps = InitRapidNetApps (nodeNum, Create<LoadBalancingHelper>());
  apps.Start (Seconds (0.0));
  apps.Stop (Seconds (10.0));

  /* initialization */
  schedule (0.001, init_switchConnection);
  schedule (0.002, init_pktClient);
  schedule (0.003, init_loadBalancerConnectionToServer);

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






