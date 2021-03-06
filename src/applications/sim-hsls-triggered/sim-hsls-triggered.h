/* A RapidNet application. Generated by RapidNet compiler. */

#ifndef SIMHSLSTRIGGERED_H
#define SIMHSLSTRIGGERED_H

#include <string>
#include <iostream>
#include "ns3/ptr.h"
#include "ns3/event-id.h"
#include "ns3/ipv4-address.h"
#include "ns3/rapidnet-header.h"
#include "ns3/relation-base.h"
#include "ns3/database.h"
#include "ns3/discovery.h"
#include "ns3/aggregator.h"
#include "ns3/aggwrap.h"

using namespace std;
using namespace ns3;
using namespace ns3::rapidnet::discovery;

namespace ns3 {

class Socket;
class Packet;

namespace rapidnet {
namespace simhslstriggered {

class SimHslsTriggered : public Discovery
{
public:
  static const string ELSU;
  static const string ELSUCHANGE;
  static const string ELSUCOUNT;
  static const string ELSULOC;
  static const string ELINKADD;
  static const string ELINKCOUNT;
  static const string LINK;
  static const string PERIODIC;
  static const string R11A_ECAPERIODIC;
  static const string R11B_ECAPERIODIC;
  static const string R12A_ECAPERIODIC;
  static const string R12B_ECAPERIODIC;
  static const string R13A_ECAPERIODIC;
  static const string R13B_ECAPERIODIC;
  static const string R14A_ECAPERIODIC;
  static const string R14B_ECAPERIODIC;
  static const string TLSU;
  static const string TLINK;

  static TypeId GetTypeId (void);

  SimHslsTriggered ();

  virtual ~SimHslsTriggered ();

protected:

  virtual void DoDispose (void);

  virtual void StartApplication (void);

  virtual void StopApplication (void);

  virtual void InitDatabase (void);

  virtual void DemuxRecv (Ptr<Tuple> tuple);

  virtual void R01Eca0Ins (Ptr<Tuple> link);

  virtual void R01Eca0Ref (Ptr<Tuple> link);

  virtual void R02_eca (Ptr<Tuple> eLinkAdd);

  virtual void R03_eca (Ptr<Tuple> eLinkCount);

  virtual void R04_eca (Ptr<Tuple> eLinkAdd);

  virtual void R11A_ecaperiodic ();

  virtual void R11A_eca (Ptr<Tuple> r11A_ecaperiodic);

  virtual void R11B_ecaperiodic ();

  virtual void R11B_eca (Ptr<Tuple> r11B_ecaperiodic);

  virtual void R12A_ecaperiodic ();

  virtual void R12A_eca (Ptr<Tuple> r12A_ecaperiodic);

  virtual void R12B_ecaperiodic ();

  virtual void R12B_eca (Ptr<Tuple> r12B_ecaperiodic);

  virtual void R13A_ecaperiodic ();

  virtual void R13A_eca (Ptr<Tuple> r13A_ecaperiodic);

  virtual void R13B_ecaperiodic ();

  virtual void R13B_eca (Ptr<Tuple> r13B_ecaperiodic);

  virtual void R14A_ecaperiodic ();

  virtual void R14A_eca (Ptr<Tuple> r14A_ecaperiodic);

  virtual void R14B_ecaperiodic ();

  virtual void R14B_eca (Ptr<Tuple> r14B_ecaperiodic);

  virtual void R15Eca1Ins (Ptr<Tuple> tLink);

  virtual void R15Eca1Ref (Ptr<Tuple> tLink);

  virtual void R21_eca (Ptr<Tuple> eLSU);

  virtual void R22_eca (Ptr<Tuple> eLSULoc);

  virtual void R23_eca (Ptr<Tuple> eLSUCount);

  virtual void R24_eca (Ptr<Tuple> eLSULoc);

  virtual void R31Eca0Ins (Ptr<Tuple> tLSU);

  virtual void R31Eca0Ref (Ptr<Tuple> tLSU);

  virtual void R32_eca (Ptr<Tuple> eLSUChange);

  EventId m_event_r11a_ecaperiodic;
  EventId m_event_r11b_ecaperiodic;
  EventId m_event_r12a_ecaperiodic;
  EventId m_event_r12b_ecaperiodic;
  EventId m_event_r13a_ecaperiodic;
  EventId m_event_r13b_ecaperiodic;
  EventId m_event_r14a_ecaperiodic;
  EventId m_event_r14b_ecaperiodic;
};

} // namespace simhslstriggered
} // namespace rapidnet
} // namespace ns3

#endif // SIMHSLSTRIGGERED_H
