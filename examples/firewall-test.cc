/* -*- Mode:C++; c-file-style:"gnu"; indent-tabs-mode:nil; -*- */
/*
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License version 2 as
 * published by the Free Software Foundation;
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

#include "ns3/core-module.h"
#include "ns3/simulator-module.h"
#include "ns3/node-module.h"
#include "ns3/pingpong-module.h"
#include "ns3/rapidnet-module.h"
#include "ns3/values-module.h"

#define pktIn(Switch, Src, SrcPort, Dst) \
  tuple (Firewall::PKTIN, \
    attr ("pktIn_attr1", Ipv4Value, Switch), \
    attr ("pktIn_attr2", Ipv4Value, Src), \
    attr ("pktIn_attr3", Ipv4Value, SrcPort), \
    attr ("pktIn_attr4", Ipv4Value, Dst))

#define insert_PktIn() \
  app(from)->Insert (tlink (addr (from), addr (to))); \
  app(to)->Insert (tlink (addr (to), addr (from)));

#define delete_PktIn(from, to) \
  app(from)->Delete (tlink (addr (from), addr (to))); \
  app(to)->Delete (tlink (addr (to), addr (from)));

using namespace std;
using namespace ns3;
using namespace ns3::rapidnet;
using namespace ns3::rapidnet::firewall;

ApplicationContainer apps;

/** Create a 2 nodes */
void
UpdateIncomingPackets1 ()
{
  insert_PktIn (1, 2);
}

int
main (int argc, char *argv[])
{
  LogComponentEnable("Firewall", LOG_LEVEL_INFO);
  LogComponentEnable("RapidNetApplicationBase", LOG_LEVEL_INFO);

  apps = InitRapidNetApps (2, Create<FirewallHelper> ());
  apps.Start (Seconds (0.0));
  apps.Stop (Seconds (10.0));

  schedule (0.0001, UpdateIncomingPackets1);

  Simulator::Run ();
  Simulator::Destroy ();
  return 0;
}

