/* A RapidNet application. Generated by RapidNet compiler. */

#ifndef LOADBALANCING_H
#define LOADBALANCING_H

#include <string>
#include <iostream>
#include "ns3/ptr.h"
#include "ns3/event-id.h"
#include "ns3/ipv4-address.h"
#include "ns3/rapidnet-header.h"
#include "ns3/relation-base.h"
#include "ns3/database.h"
#include "ns3/rapidnet-application-base.h"
#include "ns3/aggregator.h"
#include "ns3/aggwrap.h"

using namespace std;
using namespace ns3;

namespace ns3 {

class Socket;
class Packet;

namespace rapidnet {
namespace loadbalancing {

class LoadBalancing : public RapidNetApplicationBase
{
public:
  static const string PKTCLIENT;
  static const string PKTSERVER;
  static const string PKTTOBALANCE;
  static const string RANDOMLYOBTAINEDSERVER;
  static const string SERVERMAPPING;
  static const string SWITCHCONNECTION;

  static TypeId GetTypeId (void);

  LoadBalancing ();

  virtual ~LoadBalancing ();

protected:

  virtual void DoDispose (void);

  virtual void StartApplication (void);

  virtual void StopApplication (void);

  virtual void InitDatabase (void);

  virtual void DemuxRecv (Ptr<Tuple> tuple);

  virtual void R1Eca0Ins (Ptr<Tuple> pktClient);

  virtual void R1Eca1Ins (Ptr<Tuple> switchConnection);

  virtual void R2_eca (Ptr<Tuple> pktToBalance);

  virtual void R3_eca (Ptr<Tuple> randomlyObtainedServer);

};

} // namespace loadbalancing
} // namespace rapidnet
} // namespace ns3

#endif // LOADBALANCING_H
