/* A RapidNet application. Generated by RapidNet compiler. */

#ifndef TEMP_H
#define TEMP_H

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
namespace temp {

class Temp : public RapidNetApplicationBase
{
public:
  static const string OPENCONNECTIONTOCONTROLLER;
  static const string PERFLOWRULE;
  static const string PKTIN;
  static const string PKTRECEIVED;
  static const string R2TRUSTEDCONTROLLERMEMORYSEND;
  static const string TRUSTEDCONTROLLERMEMORY;

  static TypeId GetTypeId (void);

  Temp ();

  virtual ~Temp ();

protected:

  virtual void DoDispose (void);

  virtual void StartApplication (void);

  virtual void StopApplication (void);

  virtual void InitDatabase (void);

  virtual void DemuxRecv (Ptr<Tuple> tuple);

  virtual void R1Eca0Ins (Ptr<Tuple> pktIn);

  virtual void R2ECAMat (Ptr<Tuple> r2trustedControllerMemorysend);

  virtual void R2_eca (Ptr<Tuple> pktReceived);

};

} // namespace temp
} // namespace rapidnet
} // namespace ns3

#endif // TEMP_H
