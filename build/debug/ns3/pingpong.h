/* A RapidNet application. Generated by RapidNet compiler. */

#ifndef PINGPONG_H
#define PINGPONG_H

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
namespace pingpong {

class Pingpong : public RapidNetApplicationBase
{
public:
  static const string EPING;
  static const string EPINGPONGFINISH;
  static const string EPONG;
  static const string PERIODIC;
  static const string R1_ECAPERIODIC;
  static const string TLINK;

  static TypeId GetTypeId (void);

  Pingpong ();

  virtual ~Pingpong ();

protected:

  virtual void DoDispose (void);

  virtual void StartApplication (void);

  virtual void StopApplication (void);

  virtual void InitDatabase (void);

  virtual void DemuxRecv (Ptr<Tuple> tuple);

  virtual void R1_ecaperiodic ();

  virtual void R1_eca (Ptr<Tuple> r1_ecaperiodic);

  virtual void R2_eca (Ptr<Tuple> ePing);

  virtual void R3_eca (Ptr<Tuple> ePong);

  EventId m_event_r1_ecaperiodic;
};

} // namespace pingpong
} // namespace rapidnet
} // namespace ns3

#endif // PINGPONG_H
