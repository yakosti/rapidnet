


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





