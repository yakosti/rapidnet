/* A RapidNet application. Generated by RapidNet compiler. */

#ifndef CHORD_H
#define CHORD_H

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
namespace chord {

class Chord : public RapidNetApplicationBase
{
public:
  static const string BESTLOOKUPDIST;
  static const string BESTSUCC;
  static const string BESTSUCCDIST;
  static const string C1_ECAPERIODIC;
  static const string CM1_ECAPERIODIC;
  static const string DELETESUCC;
  static const string EAGERFINGER;
  static const string F1_ECAPERIODIC;
  static const string FFIX;
  static const string FFIXEVENT;
  static const string FINGER;
  static const string FORWARDLOOKUP;
  static const string JOIN;
  static const string JOINEVENT;
  static const string JOINREQ;
  static const string LANDMARK;
  static const string LOOKUP;
  static const string LOOKUPRESULTS;
  static const string NEWSUCCEVENT;
  static const string NEXTFINGERFIX;
  static const string NODE;
  static const string NODEFAILURE;
  static const string NODE_INIT_ECAPERIODIC;
  static const string PENDINGPING;
  static const string PERIODIC;
  static const string PINGREQ;
  static const string PINGRESP;
  static const string PP1_ECAPERIODIC;
  static const string PP2_ECAPERIODIC;
  static const string PP3_ECAPERIODIC;
  static const string PP5_ECAPERIODIC;
  static const string PRED;
  static const string SB0_ECAPERIODIC;
  static const string SB1ASTABILIZEEVENTNODEBESTSUCCSI;
  static const string SB2LOCAL2SUCCEVICTPOLICYSEND;
  static const string SB2STABILIZEEVENTNODESUCCEVICTPOLICYSI;
  static const string SB3STABILIZEEVENTNODESUCCEVICTPOLICYSI;
  static const string STABILIZEEVENT;
  static const string SUCCEVICTPOLICY;
  static const string SUCCEVICTPOLICYEVENT;
  static const string UNIQUEFINGER;

  static TypeId GetTypeId (void);

  Chord ();

  virtual ~Chord ();

protected:

  virtual void DoDispose (void);

  virtual void StartApplication (void);

  virtual void StopApplication (void);

  virtual void InitDatabase (void);

  virtual void DemuxRecv (Ptr<Tuple> tuple);

  virtual void Node_init_ecaperiodic ();

  virtual void Node_init_eca (Ptr<Tuple> node_init_ecaperiodic);

  virtual void L1_eca (Ptr<Tuple> lookup);

  virtual void L2_eca (Ptr<Tuple> lookup);

  virtual void L3_eca (Ptr<Tuple> bestLookupDist);

  virtual void L4_eca (Ptr<Tuple> forwardLookup);

  virtual void N0Eca0Ins (Ptr<Tuple> succEvictPolicy);

  virtual void N2_eca (Ptr<Tuple> deleteSucc);

  virtual void N1_eca (Ptr<Tuple> newSuccEvent);

  virtual void N3_eca (Ptr<Tuple> bestSuccDist);

  virtual void N4Eca1Ins (Ptr<Tuple> bestSucc);

  virtual void N4Eca1Del (Ptr<Tuple> bestSucc);

  virtual void F1_ecaperiodic ();

  virtual void F1_eca (Ptr<Tuple> f1_ecaperiodic);

  virtual void F2Eca0Ins (Ptr<Tuple> fFix);

  virtual void F2Eca0Ref (Ptr<Tuple> fFix);

  virtual void F3_eca (Ptr<Tuple> fFixEvent);

  virtual void F4_eca (Ptr<Tuple> lookupResults);

  virtual void F5_eca (Ptr<Tuple> eagerFinger);

  virtual void F6_eca (Ptr<Tuple> eagerFinger);

  virtual void F7_eca (Ptr<Tuple> eagerFinger);

  virtual void F8_eca (Ptr<Tuple> eagerFinger);

  virtual void F9_eca (Ptr<Tuple> eagerFinger);

  virtual void F10Eca0Ins (Ptr<Tuple> finger);

  virtual void C1_ecaperiodic ();

  virtual void C1_eca (Ptr<Tuple> c1_ecaperiodic);

  virtual void C2_eca (Ptr<Tuple> joinEvent);

  virtual void C3_eca (Ptr<Tuple> joinEvent);

  virtual void C4_eca (Ptr<Tuple> joinEvent);

  virtual void C5_eca (Ptr<Tuple> joinReq);

  virtual void C6_eca (Ptr<Tuple> lookupResults);

  virtual void Sb0_ecaperiodic ();

  virtual void Sb0_eca (Ptr<Tuple> sb0_ecaperiodic);

  virtual void Sb1ALocal1_eca (Ptr<Tuple> stabilizeEvent);

  virtual void Sb1ALocal2_eca (Ptr<Tuple> sb1AstabilizeEventnodebestSuccSI);

  virtual void Sb1B_eca (Ptr<Tuple> succEvictPolicyEvent);

  virtual void Sb2Local1_eca (Ptr<Tuple> stabilizeEvent);

  virtual void Sb2Local2ECAMat (Ptr<Tuple> sb2Local2succEvictPolicysend);

  virtual void Sb2Local2_eca (Ptr<Tuple> sb2stabilizeEventnodesuccEvictPolicySI);

  virtual void Sb3Local1_eca (Ptr<Tuple> stabilizeEvent);

  virtual void Sb3Local2_eca (Ptr<Tuple> sb3stabilizeEventnodesuccEvictPolicySI);

  virtual void Pp1_ecaperiodic ();

  virtual void Pp1_eca (Ptr<Tuple> pp1_ecaperiodic);

  virtual void Pp2_ecaperiodic ();

  virtual void Pp2_eca (Ptr<Tuple> pp2_ecaperiodic);

  virtual void Pp3_ecaperiodic ();

  virtual void Pp3_eca (Ptr<Tuple> pp3_ecaperiodic);

  virtual void Pp4_eca (Ptr<Tuple> pingReq);

  virtual void Pp5_ecaperiodic ();

  virtual void Pp5_eca (Ptr<Tuple> pp5_ecaperiodic);

  virtual void Pp6_eca (Ptr<Tuple> pingResp);

  virtual void Cm1_ecaperiodic ();

  virtual void Cm1_eca (Ptr<Tuple> cm1_ecaperiodic);

  virtual void Cm1a_eca (Ptr<Tuple> nodeFailure);

  virtual void Cm2a_eca (Ptr<Tuple> nodeFailure);

  virtual void Cm2b_eca (Ptr<Tuple> deleteSucc);

  virtual void Cm3_eca (Ptr<Tuple> nodeFailure);

  virtual void Cm4_eca (Ptr<Tuple> nodeFailure);

  virtual void Cm6_eca (Ptr<Tuple> nodeFailure);

  Ptr<AggWrap> m_aggr_bestlookupdistMinD;
  Ptr<AggWrap> m_aggr_bestsuccdistMinD;
  Ptr<AggWrap> m_aggr_forwardlookupMinBI;
  uint32_t m_count_c1_ecaperiodic;
  uint32_t m_count_node_init_ecaperiodic;
  EventId m_event_c1_ecaperiodic;
  EventId m_event_cm1_ecaperiodic;
  EventId m_event_f1_ecaperiodic;
  EventId m_event_node_init_ecaperiodic;
  EventId m_event_pp1_ecaperiodic;
  EventId m_event_pp2_ecaperiodic;
  EventId m_event_pp3_ecaperiodic;
  EventId m_event_pp5_ecaperiodic;
  EventId m_event_sb0_ecaperiodic;
};

} // namespace chord
} // namespace rapidnet
} // namespace ns3

#endif // CHORD_H