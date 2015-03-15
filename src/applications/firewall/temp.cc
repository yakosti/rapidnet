/* A RapidNet application. Generated by RapidNet compiler. */

#include "temp.h"
#include <cstdlib>
#include "ns3/nstime.h"
#include "ns3/simulator.h"
#include "ns3/type-ids.h"
#include "ns3/rapidnet-types.h"
#include "ns3/rapidnet-utils.h"
#include "ns3/assignor.h"
#include "ns3/selector.h"
#include "ns3/rapidnet-functions.h"

using namespace std;
using namespace ns3;
using namespace ns3::rapidnet;
using namespace ns3::rapidnet::temp;

const string Temp::OPENCONNECTIONTOCONTROLLER = "openConnectionToController";
const string Temp::PERFLOWRULE = "perFlowRule";
const string Temp::PKTIN = "pktIn";
const string Temp::PKTRECEIVED = "pktReceived";
const string Temp::R2TRUSTEDCONTROLLERMEMORYSEND = "r2trustedControllerMemorysend";
const string Temp::TRUSTEDCONTROLLERMEMORY = "trustedControllerMemory";

NS_LOG_COMPONENT_DEFINE ("Temp");
NS_OBJECT_ENSURE_REGISTERED (Temp);

TypeId
Temp::GetTypeId (void)
{
  static TypeId tid = TypeId ("ns3::rapidnet::temp::Temp")
    .SetParent<RapidNetApplicationBase> ()
    .AddConstructor<Temp> ()
    ;
  return tid;
}

Temp::Temp()
{
  NS_LOG_FUNCTION_NOARGS ();
}

Temp::~Temp()
{
  NS_LOG_FUNCTION_NOARGS ();
}

void
Temp::DoDispose (void)
{
  NS_LOG_FUNCTION_NOARGS ();

  RapidNetApplicationBase::DoDispose ();
}

void
Temp::StartApplication (void)
{
  NS_LOG_FUNCTION_NOARGS ();

  RapidNetApplicationBase::StartApplication ();
  RAPIDNET_LOG_INFO("Temp Application Started");
}

void
Temp::StopApplication ()
{
  NS_LOG_FUNCTION_NOARGS ();

  RapidNetApplicationBase::StopApplication ();
  RAPIDNET_LOG_INFO("Temp Application Stopped");
}

void
Temp::InitDatabase ()
{
  //RapidNetApplicationBase::InitDatabase ();

  AddRelationWithKeys (OPENCONNECTIONTOCONTROLLER, attrdeflist (
    attrdef ("openConnectionToController_attr1", IPV4)));

  AddRelationWithKeys (PERFLOWRULE, attrdeflist (
    attrdef ("perFlowRule_attr2", IPV4),
    attrdef ("perFlowRule_attr3", IPV4),
    attrdef ("perFlowRule_attr4", IPV4),
    attrdef ("perFlowRule_attr5", IPV4)));

  AddRelationWithKeys (PKTIN, attrdeflist (
    attrdef ("pktIn_attr1", IPV4),
    attrdef ("pktIn_attr2", IPV4),
    attrdef ("pktIn_attr3", IPV4),
    attrdef ("pktIn_attr4", IPV4)));

  AddRelationWithKeys (TRUSTEDCONTROLLERMEMORY, attrdeflist (
    attrdef ("trustedControllerMemory_attr1", IPV4),
    attrdef ("trustedControllerMemory_attr2", IPV4),
    attrdef ("trustedControllerMemory_attr3", IPV4)));

}

void
Temp::DemuxRecv (Ptr<Tuple> tuple)
{
  RapidNetApplicationBase::DemuxRecv (tuple);

  if (IsInsertEvent (tuple, PKTIN))
    {
      R1Eca0Ins (tuple);
    }
  if (IsRecvEvent (tuple, R2TRUSTEDCONTROLLERMEMORYSEND))
    {
      R2ECAMat (tuple);
    }
  if (IsRecvEvent (tuple, PKTRECEIVED))
    {
      R2_eca (tuple);
    }
}

void
Temp::R1Eca0Ins (Ptr<Tuple> pktIn)
{
  RAPIDNET_LOG_INFO ("R1Eca0Ins triggered");

  Ptr<Tuple> result = pktIn;

  result->Assign (Assignor::New ("Uport",
    ValueExpr::New (Int32Value::New (2))));

  result->Assign (Assignor::New ("pktIn_attr3",
    ValueExpr::New (Int32Value::New (1))));

  result = result->Project (
    PKTRECEIVED,
    strlist ("pktIn_attr4",
      "Uport",
      "pktIn_attr2",
      "pktIn_attr3",
      "pktIn_attr1",
      "pktIn_attr4"),
    strlist ("pktReceived_attr1",
      "pktReceived_attr2",
      "pktReceived_attr3",
      "pktReceived_attr4",
      "pktReceived_attr5",
      RN_DEST));

  Send (result);
}

void
Temp::R2ECAMat (Ptr<Tuple> r2trustedControllerMemorysend)
{
  RAPIDNET_LOG_INFO ("R2ECAMat triggered");

  Ptr<Tuple> result = r2trustedControllerMemorysend;

  result = result->Project (
    TRUSTEDCONTROLLERMEMORY,
    strlist ("r2trustedControllerMemorysend_attr1",
      "r2trustedControllerMemorysend_attr2",
      "r2trustedControllerMemorysend_attr3"),
    strlist ("trustedControllerMemory_attr1",
      "trustedControllerMemory_attr2",
      "trustedControllerMemory_attr3"));

  Insert (result);
}

void
Temp::R2_eca (Ptr<Tuple> pktReceived)
{
  RAPIDNET_LOG_INFO ("R2_eca triggered");

  Ptr<RelationBase> result;

  result = GetRelation (OPENCONNECTIONTOCONTROLLER)->Join (
    pktReceived,
    strlist ("openConnectionToController_attr1"),
    strlist ("pktReceived_attr1"));

  result->Assign (Assignor::New ("pktReceived_attr2",
    ValueExpr::New (Int32Value::New (2))));

  result->Assign (Assignor::New ("pktReceived_attr4",
    ValueExpr::New (Int32Value::New (1))));

  result = result->Project (
    R2TRUSTEDCONTROLLERMEMORYSEND,
    strlist ("openConnectionToController_attr2",
      "pktReceived_attr5",
      "pktReceived_attr1",
      "openConnectionToController_attr2"),
    strlist ("r2trustedControllerMemorysend_attr1",
      "r2trustedControllerMemorysend_attr2",
      "r2trustedControllerMemorysend_attr3",
      RN_DEST));

  Send (result);
}

