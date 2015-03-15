/* A RapidNet application. Generated by RapidNet compiler. */

#include "firewall.h"
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
using namespace ns3::rapidnet::firewall;

const string Firewall::CONTROLLERCONNECTION = "controllerConnection";
const string Firewall::OPENCONNECTIONTOCONTROLLER = "openConnectionToController";
const string Firewall::PERFLOWRULE = "perFlowRule";
const string Firewall::PKTFROMSWITCH = "pktFromSwitch";
const string Firewall::PKTIN = "pktIn";
const string Firewall::PKTRECEIVED = "pktReceived";
const string Firewall::R2TRUSTEDCONTROLLERMEMORYSEND = "r2trustedControllerMemorysend";
const string Firewall::R3TRUSTEDCONTROLLERMEMORYSEND = "r3trustedControllerMemorysend";
const string Firewall::R6PERFLOWRULESEND = "r6perFlowRulesend";
const string Firewall::TRUSTEDCONTROLLERMEMORY = "trustedControllerMemory";
const string Firewall::TRUSTEDCONTROLLERMEMORYDELETE = "trustedControllerMemoryDelete";

NS_LOG_COMPONENT_DEFINE ("Firewall");
NS_OBJECT_ENSURE_REGISTERED (Firewall);

TypeId
Firewall::GetTypeId (void)
{
  static TypeId tid = TypeId ("ns3::rapidnet::firewall::Firewall")
    .SetParent<RapidNetApplicationBase> ()
    .AddConstructor<Firewall> ()
    ;
  return tid;
}

Firewall::Firewall()
{
  NS_LOG_FUNCTION_NOARGS ();
}

Firewall::~Firewall()
{
  NS_LOG_FUNCTION_NOARGS ();
}

void
Firewall::DoDispose (void)
{
  NS_LOG_FUNCTION_NOARGS ();

  RapidNetApplicationBase::DoDispose ();
}

void
Firewall::StartApplication (void)
{
  NS_LOG_FUNCTION_NOARGS ();

  RapidNetApplicationBase::StartApplication ();
  RAPIDNET_LOG_INFO("Firewall Application Started");
}

void
Firewall::StopApplication ()
{
  NS_LOG_FUNCTION_NOARGS ();

  RapidNetApplicationBase::StopApplication ();
  RAPIDNET_LOG_INFO("Firewall Application Stopped");
}

void
Firewall::InitDatabase ()
{
  //RapidNetApplicationBase::InitDatabase ();

  AddRelationWithKeys (OPENCONNECTIONTOCONTROLLER, attrdeflist (
    attrdef ("openConnectionToController_attr1", IPV4)));

  AddRelationWithKeys (PERFLOWRULE, attrdeflist (
    attrdef ("perFlowRule_attr1", IPV4),
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
    attrdef ("trustedControllerMemory_attr2", IPV4),
    attrdef ("trustedControllerMemory_attr3", IPV4)));

}

void
Firewall::DemuxRecv (Ptr<Tuple> tuple)
{
  RapidNetApplicationBase::DemuxRecv (tuple);

  if (IsInsertEvent (tuple, PKTIN))
    {
      R1Eca0Ins (tuple);
    }
  if (IsRecvEvent (tuple, R2TRUSTEDCONTROLLERMEMORYSEND))
    {
      R2Eca0RemoteIns (tuple);
    }
  if (IsRecvEvent (tuple, TRUSTEDCONTROLLERMEMORYDELETE))
    {
      R2Eca0RemoteDel (tuple);
    }
  if (IsInsertEvent (tuple, PKTIN))
    {
      R2Eca0Ins (tuple);
    }
  if (IsDeleteEvent (tuple, PKTIN))
    {
      R2Eca0Del (tuple);
    }
  if (IsInsertEvent (tuple, OPENCONNECTIONTOCONTROLLER))
    {
      R2Eca1Ins (tuple);
    }
  if (IsDeleteEvent (tuple, OPENCONNECTIONTOCONTROLLER))
    {
      R2Eca1Del (tuple);
    }
  if (IsRecvEvent (tuple, R3TRUSTEDCONTROLLERMEMORYSEND))
    {
      R3Eca0RemoteIns (tuple);
    }
  if (IsInsertEvent (tuple, PKTIN))
    {
      R3Eca0Ins (tuple);
    }
  if (IsInsertEvent (tuple, OPENCONNECTIONTOCONTROLLER))
    {
      R3Eca1Ins (tuple);
    }
  if (IsInsertEvent (tuple, PKTIN))
    {
      R4Eca0Ins (tuple);
    }
  if (IsInsertEvent (tuple, PERFLOWRULE))
    {
      R4Eca1Ins (tuple);
    }
  if (IsRecvEvent (tuple, CONTROLLERCONNECTION))
    {
      R5_eca (tuple);
    }
  if (IsRecvEvent (tuple, R6PERFLOWRULESEND))
    {
      R6ECAMat (tuple);
    }
  if (IsRecvEvent (tuple, PKTFROMSWITCH))
    {
      R6_eca (tuple);
    }
  if (IsInsertEvent (tuple, PERFLOWRULE))
    {
      R7Eca0Ins (tuple);
    }
  if (IsInsertEvent (tuple, PKTIN))
    {
      R7Eca1Ins (tuple);
    }
}

void
Firewall::R1Eca0Ins (Ptr<Tuple> pktIn)
{
  RAPIDNET_LOG_INFO ("R1Eca0Ins triggered");

  Ptr<Tuple> result = pktIn;

  result->Assign (Assignor::New ("Uport",
    ValueExpr::New (Int32Value::New (2))));

  result = result->Select (Selector::New (
    Operation::New (RN_EQ,
      VarExpr::New ("pktIn_attr3"),
      ValueExpr::New (Int32Value::New (1)))));

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
Firewall::R2Eca0RemoteIns (Ptr<Tuple> r2trustedControllerMemorysend)
{
  RAPIDNET_LOG_INFO ("R2Eca0RemoteIns triggered");

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
Firewall::R2Eca0RemoteDel (Ptr<Tuple> trustedControllerMemoryDelete)
{
  RAPIDNET_LOG_INFO ("R2Eca0RemoteDel triggered");

  Ptr<Tuple> result = trustedControllerMemoryDelete;

  result = result->Project (
    TRUSTEDCONTROLLERMEMORY,
    strlist ("trustedControllerMemoryDelete_attr1",
      "trustedControllerMemoryDelete_attr2",
      "trustedControllerMemoryDelete_attr3"),
    strlist ("trustedControllerMemory_attr1",
      "trustedControllerMemory_attr2",
      "trustedControllerMemory_attr3"));

  Delete (result);
}

void
Firewall::R2Eca0Ins (Ptr<Tuple> pktIn)
{
  RAPIDNET_LOG_INFO ("R2Eca0Ins triggered");

  Ptr<RelationBase> result;

  result = GetRelation (OPENCONNECTIONTOCONTROLLER)->Join (
    pktIn,
    strlist ("openConnectionToController_attr1"),
    strlist ("pktIn_attr1"));

  result = result->Select (Selector::New (
    Operation::New (RN_EQ,
      VarExpr::New ("pktIn_attr3"),
      ValueExpr::New (Int32Value::New (1)))));

  result = result->Project (
    R2TRUSTEDCONTROLLERMEMORYSEND,
    strlist ("openConnectionToController_attr2",
      "pktIn_attr1",
      "pktIn_attr4",
      "openConnectionToController_attr2"),
    strlist ("r2trustedControllerMemorysend_attr1",
      "r2trustedControllerMemorysend_attr2",
      "r2trustedControllerMemorysend_attr3",
      RN_DEST));

  Send (result);
}

void
Firewall::R2Eca0Del (Ptr<Tuple> pktIn)
{
  RAPIDNET_LOG_INFO ("R2Eca0Del triggered");

  Ptr<RelationBase> result;

  result = GetRelation (OPENCONNECTIONTOCONTROLLER)->Join (
    pktIn,
    strlist ("openConnectionToController_attr1"),
    strlist ("pktIn_attr1"));

  result = result->Select (Selector::New (
    Operation::New (RN_EQ,
      VarExpr::New ("pktIn_attr3"),
      ValueExpr::New (Int32Value::New (1)))));

  result = result->Project (
    TRUSTEDCONTROLLERMEMORYDELETE,
    strlist ("openConnectionToController_attr2",
      "pktIn_attr1",
      "pktIn_attr4",
      "openConnectionToController_attr2"),
    strlist ("trustedControllerMemoryDelete_attr1",
      "trustedControllerMemoryDelete_attr2",
      "trustedControllerMemoryDelete_attr3",
      RN_DEST));

  Send (result);
}

void
Firewall::R2Eca1Ins (Ptr<Tuple> openConnectionToController)
{
  RAPIDNET_LOG_INFO ("R2Eca1Ins triggered");

  Ptr<RelationBase> result;

  result = GetRelation (PKTIN)->Join (
    openConnectionToController,
    strlist ("pktIn_attr1"),
    strlist ("openConnectionToController_attr1"));

  result = result->Select (Selector::New (
    Operation::New (RN_EQ,
      VarExpr::New ("pktIn_attr3"),
      ValueExpr::New (Int32Value::New (1)))));

  result = result->Project (
    R2TRUSTEDCONTROLLERMEMORYSEND,
    strlist ("openConnectionToController_attr2",
      "openConnectionToController_attr1",
      "pktIn_attr4",
      "openConnectionToController_attr2"),
    strlist ("r2trustedControllerMemorysend_attr1",
      "r2trustedControllerMemorysend_attr2",
      "r2trustedControllerMemorysend_attr3",
      RN_DEST));

  Send (result);
}

void
Firewall::R2Eca1Del (Ptr<Tuple> openConnectionToController)
{
  RAPIDNET_LOG_INFO ("R2Eca1Del triggered");

  Ptr<RelationBase> result;

  result = GetRelation (PKTIN)->Join (
    openConnectionToController,
    strlist ("pktIn_attr1"),
    strlist ("openConnectionToController_attr1"));

  result = result->Select (Selector::New (
    Operation::New (RN_EQ,
      VarExpr::New ("pktIn_attr3"),
      ValueExpr::New (Int32Value::New (1)))));

  result = result->Project (
    TRUSTEDCONTROLLERMEMORYDELETE,
    strlist ("openConnectionToController_attr2",
      "openConnectionToController_attr1",
      "pktIn_attr4",
      "openConnectionToController_attr2"),
    strlist ("trustedControllerMemoryDelete_attr1",
      "trustedControllerMemoryDelete_attr2",
      "trustedControllerMemoryDelete_attr3",
      RN_DEST));

  Send (result);
}

void
Firewall::R3Eca0RemoteIns (Ptr<Tuple> r3trustedControllerMemorysend)
{
  RAPIDNET_LOG_INFO ("R3Eca0RemoteIns triggered");

  Ptr<Tuple> result = r3trustedControllerMemorysend;

  result = result->Project (
    TRUSTEDCONTROLLERMEMORY,
    strlist ("r3trustedControllerMemorysend_attr1",
      "r3trustedControllerMemorysend_attr2",
      "r3trustedControllerMemorysend_attr3"),
    strlist ("trustedControllerMemory_attr1",
      "trustedControllerMemory_attr2",
      "trustedControllerMemory_attr3"));

  Insert (result);
}

void
Firewall::R3Eca0Ins (Ptr<Tuple> pktIn)
{
  RAPIDNET_LOG_INFO ("R3Eca0Ins triggered");

  Ptr<RelationBase> result;

  result = GetRelation (OPENCONNECTIONTOCONTROLLER)->Join (
    pktIn,
    strlist ("openConnectionToController_attr1"),
    strlist ("pktIn_attr1"));

  result = result->Select (Selector::New (
    Operation::New (RN_EQ,
      VarExpr::New ("pktIn_attr3"),
      ValueExpr::New (Int32Value::New (1)))));

  result = result->Project (
    R3TRUSTEDCONTROLLERMEMORYSEND,
    strlist ("openConnectionToController_attr2",
      "pktIn_attr1",
      "pktIn_attr4",
      "openConnectionToController_attr2"),
    strlist ("r3trustedControllerMemorysend_attr1",
      "r3trustedControllerMemorysend_attr2",
      "r3trustedControllerMemorysend_attr3",
      RN_DEST));

  Send (result);
}

void
Firewall::R3Eca1Ins (Ptr<Tuple> openConnectionToController)
{
  RAPIDNET_LOG_INFO ("R3Eca1Ins triggered");

  Ptr<RelationBase> result;

  result = GetRelation (PKTIN)->Join (
    openConnectionToController,
    strlist ("pktIn_attr1"),
    strlist ("openConnectionToController_attr1"));

  result = result->Select (Selector::New (
    Operation::New (RN_EQ,
      VarExpr::New ("pktIn_attr3"),
      ValueExpr::New (Int32Value::New (1)))));

  result = result->Project (
    R3TRUSTEDCONTROLLERMEMORYSEND,
    strlist ("openConnectionToController_attr2",
      "openConnectionToController_attr1",
      "pktIn_attr4",
      "openConnectionToController_attr2"),
    strlist ("r3trustedControllerMemorysend_attr1",
      "r3trustedControllerMemorysend_attr2",
      "r3trustedControllerMemorysend_attr3",
      RN_DEST));

  Send (result);
}

void
Firewall::R4Eca0Ins (Ptr<Tuple> pktIn)
{
  RAPIDNET_LOG_INFO ("R4Eca0Ins triggered");

  Ptr<RelationBase> result;

  result = GetRelation (PERFLOWRULE)->Join (
    pktIn,
    strlist ("perFlowRule_attr4", "perFlowRule_attr2", "perFlowRule_attr1", "perFlowRule_attr3"),
    strlist ("pktIn_attr4", "pktIn_attr2", "pktIn_attr1", "pktIn_attr3"));

  result = result->Select (Selector::New (
    Operation::New (RN_EQ,
      VarExpr::New ("pktIn_attr3"),
      ValueExpr::New (Int32Value::New (1)))));

  result = result->Project (
    PKTRECEIVED,
    strlist ("pktIn_attr4",
      "perFlowRule_attr5",
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
Firewall::R4Eca1Ins (Ptr<Tuple> perFlowRule)
{
  RAPIDNET_LOG_INFO ("R4Eca1Ins triggered");

  Ptr<RelationBase> result;

  result = GetRelation (PKTIN)->Join (
    perFlowRule,
    strlist ("pktIn_attr4", "pktIn_attr2", "pktIn_attr1", "pktIn_attr3"),
    strlist ("perFlowRule_attr4", "perFlowRule_attr2", "perFlowRule_attr1", "perFlowRule_attr3"));

  result = result->Select (Selector::New (
    Operation::New (RN_EQ,
      VarExpr::New ("perFlowRule_attr3"),
      ValueExpr::New (Int32Value::New (1)))));

  result = result->Project (
    PKTRECEIVED,
    strlist ("perFlowRule_attr4",
      "perFlowRule_attr5",
      "perFlowRule_attr2",
      "perFlowRule_attr3",
      "perFlowRule_attr1",
      "perFlowRule_attr4"),
    strlist ("pktReceived_attr1",
      "pktReceived_attr2",
      "pktReceived_attr3",
      "pktReceived_attr4",
      "pktReceived_attr5",
      RN_DEST));

  Send (result);
}

void
Firewall::R5_eca (Ptr<Tuple> controllerConnection)
{
  RAPIDNET_LOG_INFO ("R5_eca triggered");

  Ptr<RelationBase> result;

  result = GetRelation (PKTIN)->Join (
    controllerConnection,
    strlist ("pktIn_attr1"),
    strlist ("controllerConnection_attr1"));

  result = result->Select (Selector::New (
    Operation::New (RN_EQ,
      VarExpr::New ("pktIn_attr3"),
      ValueExpr::New (Int32Value::New (2)))));

  result = result->Project (
    PKTFROMSWITCH,
    strlist ("controllerConnection_attr2",
      "controllerConnection_attr1",
      "pktIn_attr2",
      "pktIn_attr3",
      "pktIn_attr4",
      "controllerConnection_attr2"),
    strlist ("pktFromSwitch_attr1",
      "pktFromSwitch_attr2",
      "pktFromSwitch_attr3",
      "pktFromSwitch_attr4",
      "pktFromSwitch_attr5",
      RN_DEST));

  Send (result);
}

void
Firewall::R6ECAMat (Ptr<Tuple> r6perFlowRulesend)
{
  RAPIDNET_LOG_INFO ("R6ECAMat triggered");

  Ptr<Tuple> result = r6perFlowRulesend;

  result = result->Project (
    PERFLOWRULE,
    strlist ("r6perFlowRulesend_attr1",
      "r6perFlowRulesend_attr2",
      "r6perFlowRulesend_attr3",
      "r6perFlowRulesend_attr4",
      "r6perFlowRulesend_attr5"),
    strlist ("perFlowRule_attr1",
      "perFlowRule_attr2",
      "perFlowRule_attr3",
      "perFlowRule_attr4",
      "perFlowRule_attr5"));

  Insert (result);
}

void
Firewall::R6_eca (Ptr<Tuple> pktFromSwitch)
{
  RAPIDNET_LOG_INFO ("R6_eca triggered");

  Ptr<RelationBase> result;

  result = GetRelation (TRUSTEDCONTROLLERMEMORY)->Join (
    pktFromSwitch,
    strlist ("trustedControllerMemory_attr1", "trustedControllerMemory_attr3", "trustedControllerMemory_attr2"),
    strlist ("pktFromSwitch_attr1", "pktFromSwitch_attr3", "pktFromSwitch_attr2"));

  result->Assign (Assignor::New ("Tport",
    ValueExpr::New (Int32Value::New (1))));

  result = result->Select (Selector::New (
    Operation::New (RN_EQ,
      VarExpr::New ("pktFromSwitch_attr4"),
      ValueExpr::New (Int32Value::New (2)))));

  result = result->Project (
    R6PERFLOWRULESEND,
    strlist ("pktFromSwitch_attr2",
      "pktFromSwitch_attr3",
      "pktFromSwitch_attr4",
      "pktFromSwitch_attr5",
      "Tport",
      "pktFromSwitch_attr2"),
    strlist ("r6perFlowRulesend_attr1",
      "r6perFlowRulesend_attr2",
      "r6perFlowRulesend_attr3",
      "r6perFlowRulesend_attr4",
      "r6perFlowRulesend_attr5",
      RN_DEST));

  Send (result);
}

void
Firewall::R7Eca0Ins (Ptr<Tuple> perFlowRule)
{
  RAPIDNET_LOG_INFO ("R7Eca0Ins triggered");

  Ptr<RelationBase> result;

  result = GetRelation (PKTIN)->Join (
    perFlowRule,
    strlist ("pktIn_attr4", "pktIn_attr2", "pktIn_attr1", "pktIn_attr3"),
    strlist ("perFlowRule_attr4", "perFlowRule_attr2", "perFlowRule_attr1", "perFlowRule_attr3"));

  result = result->Select (Selector::New (
    Operation::New (RN_EQ,
      VarExpr::New ("perFlowRule_attr3"),
      ValueExpr::New (Int32Value::New (2)))));

  result = result->Select (Selector::New (
    Operation::New (RN_EQ,
      VarExpr::New ("perFlowRule_attr5"),
      ValueExpr::New (Int32Value::New (1)))));

  result = result->Project (
    PKTRECEIVED,
    strlist ("perFlowRule_attr4",
      "perFlowRule_attr5",
      "perFlowRule_attr2",
      "perFlowRule_attr3",
      "perFlowRule_attr1",
      "perFlowRule_attr4"),
    strlist ("pktReceived_attr1",
      "pktReceived_attr2",
      "pktReceived_attr3",
      "pktReceived_attr4",
      "pktReceived_attr5",
      RN_DEST));

  Send (result);
}

void
Firewall::R7Eca1Ins (Ptr<Tuple> pktIn)
{
  RAPIDNET_LOG_INFO ("R7Eca1Ins triggered");

  Ptr<RelationBase> result;

  result = GetRelation (PERFLOWRULE)->Join (
    pktIn,
    strlist ("perFlowRule_attr4", "perFlowRule_attr2", "perFlowRule_attr1", "perFlowRule_attr3"),
    strlist ("pktIn_attr4", "pktIn_attr2", "pktIn_attr1", "pktIn_attr3"));

  result = result->Select (Selector::New (
    Operation::New (RN_EQ,
      VarExpr::New ("pktIn_attr3"),
      ValueExpr::New (Int32Value::New (2)))));

  result = result->Select (Selector::New (
    Operation::New (RN_EQ,
      VarExpr::New ("perFlowRule_attr5"),
      ValueExpr::New (Int32Value::New (1)))));

  result = result->Project (
    PKTRECEIVED,
    strlist ("pktIn_attr4",
      "perFlowRule_attr5",
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

