#include "ns3/core-module.h"
#include "ns3/simulator-module.h"
#include "ns3/node-module.h"
#include "ns3/helper-module.h"
#include "ns3/sdn-load-balancing-module.h"
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


/* initPacket */
#define initPacket(Client, Server, LoadBalancer) \
  tuple(SdnLoadBalancing::INITPACKET, \
    attr("initPacket_attr1", Ipv4Value, Client), \
    attr("initPacket_attr2", Ipv4Value, Server), \
    attr("initPacket_attr3", Ipv4Value, LoadBalancer))

#define insert_initPacket(Client, Server, LoadBalancer) \
  app(Client) -> \
    Insert(initPacket(addr(Client), addr(Server), addr(LoadBalancer)))


/* serverMapping */
#define serverMapping(LoadBalancer, Server, ServerNum) \
  tuple(SdnLoadBalancing::SERVERMAPPING, \
    attr("serverMapping_attr1", Ipv4Value, LoadBalancer), \
    attr("serverMapping_attr2", Ipv4Value, Server), \
    attr("serverMapping_attr3", Int32Value, ServerNum))

#define insert_serverMapping(LoadBalancer, Server, ServerNum) \
  app(LoadBalancer) -> \
    Insert(serverMapping(addr(LoadBalancer), addr(Server), ServerNum))



/* packet */
#define packet(LoadBalancer, Client, Server) \
  tuple(SdnLoadBalancing::PACKET, \
    attr("packet_attr1", Ipv4Value, LoadBalancer), \
    attr("packet_attr2", Ipv4Value, Client), \
    attr("packet_attr3", Ipv4Value, Server))

#define insert_packet(LoadBalancer, Client, Server) \
  app(LoadBalancer) -> \
    Insert(packet(addr(LoadBalancer), addr(Client), addr(Server))) 


/* designated */
#define designated(LoadBalancer, DesignatedDst) \
  tuple(SdnLoadBalancing::DESIGNATED, \
    attr("designated_attr1", Ipv4Value, LoadBalancer),\
    attr("designated_attr2", Ipv4Value, DesignatedDst))

#define insert_designated(LoadBalancer, DesignatedDst) \
  app(LoadBalancer) -> \
    Insert(designated(addr(LoadBalancer), addr(DesignatedDst)))


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

/* ====================== define constants ======================== */
#define nodeNum 12

#define SERVER_1 1 // mapped to ServerNum 1
#define SERVER_2 2 // mapped to ServerNum 2
#define SERVER_3 3 // mapped to ServerNum 3
#define SERVER_4 4 // mapped to ServerNum 4
#define SERVER_5 5 // mapped to ServerNum 5

#define CLIENT_6 6
#define CLIENT_7 7
#define CLIENT_8 8
#define CLIENT_9 9
#define CLIENT_10 10

#define LOAD_BALANCER_A 11
#define LOAD_BALANCER_B 12
#define DESIGNATED_DEST_A 4 //hash if dest is server 4
#define DESIGNATED_DEST_B 5 //hash if dest is server 5

/* ====================== define constants ======================== */




/* boilderplate */
using namespace std;
using namespace ns3;
using namespace ns3::rapidnet;
using namespace ns3::rapidnet::sdnloadbalancing;

ApplicationContainer apps;

// both load balancers are connected to ALL available servers
void init_serverMapping() 
{
  insert_serverMapping(LOAD_BALANCER_A, SERVER_1, 1);
  insert_serverMapping(LOAD_BALANCER_A, SERVER_2, 2);
  insert_serverMapping(LOAD_BALANCER_A, SERVER_3, 3);
  insert_serverMapping(LOAD_BALANCER_A, SERVER_4, 4);
  insert_serverMapping(LOAD_BALANCER_A, SERVER_5, 5);

  insert_serverMapping(LOAD_BALANCER_B, SERVER_1, 1);
  insert_serverMapping(LOAD_BALANCER_B, SERVER_2, 2);
  insert_serverMapping(LOAD_BALANCER_B, SERVER_3, 3);
  insert_serverMapping(LOAD_BALANCER_B, SERVER_4, 4);
  insert_serverMapping(LOAD_BALANCER_B, SERVER_5, 5);
}

void init_designated()
{
  insert_designated(LOAD_BALANCER_A, DESIGNATED_DEST_A);
  insert_designated(LOAD_BALANCER_B, DESIGNATED_DEST_B);
}

/* CLIENT_6 wants to send:
 * (1) packet to server 3 to LoadBalancerA 
 * (2) packet to server 3 to LoadBalancerB
 * Should end up on server 3, as server 3 is NOT a designated destination 
 * of either load balancer
 */
void init_initPacket1() 
{
  insert_initPacket(CLIENT_6, SERVER_3, LOAD_BALANCER_A);
  insert_initPacket(CLIENT_6, SERVER_3, LOAD_BALANCER_B);
}

/* CLIENT_8 wants to send:
 * (1) packet to SERVER_4 to LOAD_BALANCER_A 
 * (2) packet to SERVER_4 to LOAD_BALANCER_B
 * may not end up on the same server, as server 4 is the 
 * designated destination of LOAD_BALANCER_A
 */
void init_initPacket2() 
{
  insert_initPacket(CLIENT_8, SERVER_4, LOAD_BALANCER_A);
  insert_initPacket(CLIENT_8, SERVER_4, LOAD_BALANCER_B);
}


/* run the simulation */
int main(int argc, char *argv[])
{
  LogComponentEnable("SdnLoadBalancing", LOG_LEVEL_INFO);
  LogComponentEnable("RapidNetApplicationBase", LOG_LEVEL_INFO);

  apps = InitRapidNetApps (nodeNum, Create<SdnLoadBalancingHelper>());
  apps.Start (Seconds (0.0));
  apps.Stop (Seconds (10.0));

  /* initialization */
  schedule (0.001, init_serverMapping);
  schedule (0.002, init_designated);
  schedule (0.003, init_initPacket1);
  schedule (0.100, init_initPacket2);

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






