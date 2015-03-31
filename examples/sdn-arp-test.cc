


#include "ns3/core-module.h"
#include "ns3/simulator-module.h"
#include "ns3/node-module.h"
#include "ns3/helper-module.h"

#include "ns3/sdn-arp-module.h"
#include "ns3/rapidnet-module.h"
#include "ns3/values-module.h"
#include "ns3/ipv4-address.h"
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <stdio.h>



#define nodeNum 4

using namespace std;
using namespace ns3;
using namespace ns3::rapidnet;
using namespace ns3::rapidnet::sdnarp;

ApplicationContainer apps;


/* 
 * ******************************************************************* *
 *                                                                     *
 *                         PREDICATE DEFINITIONS                       *
 *                                                                     *
 * ******************************************************************* *
 */

/* 
 * ------------------------------------------------------------------- *
 *                         OFCONN OPERATION                            *
 * ------------------------------------------------------------------- *
 */

#define ofconnctl(src, dst) \
  tuple (Arp::OFCONNCTL, \
   attr("ofconnCtl_attr1", Ipv4Value, src), \
   attr("ofconnCtl_attr2", Ipv4Value, dst))

#define insert_ofconnctl(from, to) \
  app(from) -> Insert (ofconnctl(addr(from), addr(to))); \

#define ofconnswc(src, dst) \
  tuple (Arp::OFCONNSWC, \
   attr("ofconnSwc_attr1", Ipv4Value, src), \
   attr("ofconnSwc_attr2", Ipv4Value, dst))

#define insert_ofconnswc(from, to) \
  app(from) -> Insert (ofconnswc(addr(from), addr(to))); \
/* 
 * ------------------------------------------------------------------- *
 *                         OFCONN OPERATION                            *
 * ------------------------------------------------------------------- *
 */



/* 
 * ------------------------------------------------------------------- *
 *                           LINK OPERATION                            *
 * ------------------------------------------------------------------- *
 */

#define linkswc(src, next, port)      \
  tuple (Arp::LINKSWC, \
   attr("linkSwc_attr1", Ipv4Value, src), \
         attr("linkSwc_attr2", Ipv4Value, next),  \
         attr("linkSwc_attr3", Int32Value, port))

#define insert_linkswc(from, to, port)         \
  app(from) -> Insert (linkswc(addr(from), addr(to), port));

#define linkhst(src, next, port)      \
  tuple (Arp::LINKHST, \
   attr("linkHst_attr1", Ipv4Value, src), \
         attr("linkHst_attr2", Ipv4Value, next),  \
         attr("linkHst_attr3", Int32Value, port))

#define insert_linkhst(from, to, port)         \
  app(from) -> Insert (linkhst(addr(from), addr(to), port));

/* 
 * ------------------------------------------------------------------- *
 *                           LINK OPERATION                            *
 * ------------------------------------------------------------------- *
 */





/* 
 * ******************************************************************* *
 *                                                                     *
 *                         PREDICATE DEFINITIONS                       *
 *                                                                     *
 * ******************************************************************* *
 */










/* 
 * ******************************************************************* *
 *                                                                     *
 *                             SIMULATION                              *
 *                                                                     *
 * ******************************************************************* *
 */

int main(int argc, char *argv[])
{
  LogComponentEnable("SdnArp", LOG_LEVEL_INFO);
  LogComponentEnable("RapidNetApplicationBase", LOG_LEVEL_INFO);

  apps = InitRapidNetApps (nodeNum, Create<SdnArpHelper>());
  apps.Start (Seconds (0.0));
  apps.Stop (Seconds (10.0));

 

  Simulator::Run();
  Simulator::Destroy();
  return 0;
}

/* 
 * ******************************************************************* *
 *                                                                     *
 *                             SIMULATION                              *
 *                                                                     *
 * ******************************************************************* *
 */



