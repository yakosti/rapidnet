/* A RapidNet application. Generated by RapidNet compiler. */

#ifndef LOADBALANCERLEARNING_H
#define LOADBALANCERLEARNING_H

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
namespace loadbalancerlearning {

class LoadBalancerLearning : public RapidNetApplicationBase
{
public:
  static const string BROADCAST;
  static const string FLOWENTRY;
  static const string FLOWMOD;
  static const string INITPACKET;
  static const string LINK;
  static const string MATCHINGPACKET;
  static const string MAXPRIORITY;
  static const string OFPACKET;
  static const string OFCONN;
  static const string PACKET;
  static const string RANDOMLYOBTAINEDSWITCH;
  static const string RECVPACKET;
  static const string SWITCHMAPPING;

  static TypeId GetTypeId (void);

  LoadBalancerLearning ();

  virtual ~LoadBalancerLearning ();

protected:

  virtual void DoDispose (void);

  virtual void StartApplication (void);

  virtual void StopApplication (void);

  virtual void InitDatabase (void);

  virtual void DemuxRecv (Ptr<Tuple> tuple);

  virtual void Rc1_eca (Ptr<Tuple> ofPacket);

  virtual void Rc2_eca (Ptr<Tuple> ofPacket);

  virtual void Rs1_eca (Ptr<Tuple> packet);

  virtual void Rs2_eca (Ptr<Tuple> matchingPacket);

  virtual void Rs3_eca (Ptr<Tuple> matchingPacket);

  virtual void Rs4_eca (Ptr<Tuple> matchingPacket);

  virtual void Rs5_eca (Ptr<Tuple> flowMod);

  virtual void Rs6Eca0Ins (Ptr<Tuple> flowEntry);

  virtual void Rs6Eca0Del (Ptr<Tuple> flowEntry);

  virtual void Rs7_eca (Ptr<Tuple> broadcast);

  virtual void Lb1_eca (Ptr<Tuple> packet);

  virtual void Lb2_eca (Ptr<Tuple> randomlyObtainedSwitch);

  virtual void Rh1Eca0Ins (Ptr<Tuple> initPacket);

  virtual void Rh2_eca (Ptr<Tuple> packet);

};

} // namespace loadbalancerlearning
} // namespace rapidnet
} // namespace ns3

#endif // LOADBALANCERLEARNING_H