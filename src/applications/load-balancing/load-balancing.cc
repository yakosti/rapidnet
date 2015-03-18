/* A RapidNet application. Generated by RapidNet compiler. */

#include "load-balancing.h"
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
using namespace ns3::rapidnet::loadbalancing;

const string LoadBalancing::LOADBALANCERCONNECTIONTOSERVER = "loadBalancerConnectionToServer";
const string LoadBalancing::PKTCLIENT = "pktClient";
const string LoadBalancing::PKTSERVER = "pktServer";
const string LoadBalancing::PKTTOBALANCE = "pktToBalance";
const string LoadBalancing::RANDOMLYOBTAINEDSERVER = "randomlyObtainedServer";
const string LoadBalancing::SWITCHCONNECTION = "switchConnection";

NS_LOG_COMPONENT_DEFINE ("LoadBalancing");
NS_OBJECT_ENSURE_REGISTERED (LoadBalancing);

TypeId
LoadBalancing::GetTypeId (void)
{
  static TypeId tid = TypeId ("ns3::rapidnet::loadbalancing::LoadBalancing")
    .SetParent<RapidNetApplicationBase> ()
    .AddConstructor<LoadBalancing> ()
    ;
  return tid;
}

LoadBalancing::LoadBalancing()
{
  NS_LOG_FUNCTION_NOARGS ();
}

LoadBalancing::~LoadBalancing()
{
  NS_LOG_FUNCTION_NOARGS ();
}

void
LoadBalancing::DoDispose (void)
{
  NS_LOG_FUNCTION_NOARGS ();

  RapidNetApplicationBase::DoDispose ();
}

void
LoadBalancing::StartApplication (void)
{
  NS_LOG_FUNCTION_NOARGS ();

  RapidNetApplicationBase::StartApplication ();
  RAPIDNET_LOG_INFO("LoadBalancing Application Started");
}

void
LoadBalancing::StopApplication ()
{
  NS_LOG_FUNCTION_NOARGS ();

  RapidNetApplicationBase::StopApplication ();
  RAPIDNET_LOG_INFO("LoadBalancing Application Stopped");
}

void
LoadBalancing::InitDatabase ()
{
  //RapidNetApplicationBase::InitDatabase ();

  AddRelationWithKeys (LOADBALANCERCONNECTIONTOSERVER, attrdeflist (
    attrdef ("loadBalancerConnectionToServer_attr2", IPV4)));

  AddRelationWithKeys (PKTCLIENT, attrdeflist (
    attrdef ("pktClient_attr2", IPV4)));

  AddRelationWithKeys (SWITCHCONNECTION, attrdeflist (
    attrdef ("switchConnection_attr1", IPV4),
    attrdef ("switchConnection_attr2", IPV4)));

}

void
LoadBalancing::DemuxRecv (Ptr<Tuple> tuple)
{
  RapidNetApplicationBase::DemuxRecv (tuple);

  if (IsInsertEvent (tuple, PKTCLIENT))
    {
      R1Eca0Ins (tuple);
    }
  if (IsInsertEvent (tuple, SWITCHCONNECTION))
    {
      R1Eca1Ins (tuple);
    }
  if (IsRecvEvent (tuple, PKTTOBALANCE))
    {
      R2_eca (tuple);
    }
  if (IsRecvEvent (tuple, RANDOMLYOBTAINEDSERVER))
    {
      R3_eca (tuple);
    }
}

void
LoadBalancing::R1Eca0Ins (Ptr<Tuple> pktClient)
{
  RAPIDNET_LOG_INFO ("R1Eca0Ins triggered");

  Ptr<RelationBase> result;

  result = GetRelation (SWITCHCONNECTION)->Join (
    pktClient,
    strlist ("switchConnection_attr1"),
    strlist ("pktClient_attr1"));

  result = result->Project (
    PKTTOBALANCE,
    strlist ("switchConnection_attr2",
      "pktClient_attr1",
      "pktClient_attr2",
      "switchConnection_attr2"),
    strlist ("pktToBalance_attr1",
      "pktToBalance_attr2",
      "pktToBalance_attr3",
      RN_DEST));

  Send (result);
}

void
LoadBalancing::R1Eca1Ins (Ptr<Tuple> switchConnection)
{
  RAPIDNET_LOG_INFO ("R1Eca1Ins triggered");

  Ptr<RelationBase> result;

  result = GetRelation (PKTCLIENT)->Join (
    switchConnection,
    strlist ("pktClient_attr1"),
    strlist ("switchConnection_attr1"));

  result = result->Project (
    PKTTOBALANCE,
    strlist ("switchConnection_attr2",
      "switchConnection_attr1",
      "pktClient_attr2",
      "switchConnection_attr2"),
    strlist ("pktToBalance_attr1",
      "pktToBalance_attr2",
      "pktToBalance_attr3",
      RN_DEST));

  Send (result);
}

void
LoadBalancing::R2_eca (Ptr<Tuple> pktToBalance)
{
  RAPIDNET_LOG_INFO ("R2_eca triggered");

  Ptr<RelationBase> result;

  result = GetRelation (LOADBALANCERCONNECTIONTOSERVER)->Join (
    pktToBalance,
    strlist ("loadBalancerConnectionToServer_attr1"),
    strlist ("pktToBalance_attr1"));

  result->Assign (Assignor::New ("loadBalancerConnectionToServer_attr2",
    FSha1::New (
      VarExpr::New ("pktToBalance_attr3"))));

  result = result->Project (
    RANDOMLYOBTAINEDSERVER,
    strlist ("pktToBalance_attr1",
      "loadBalancerConnectionToServer_attr2",
      "pktToBalance_attr3"),
    strlist ("randomlyObtainedServer_attr1",
      "randomlyObtainedServer_attr2",
      "randomlyObtainedServer_attr3"));

  SendLocal (result);
}

void
LoadBalancing::R3_eca (Ptr<Tuple> randomlyObtainedServer)
{
  RAPIDNET_LOG_INFO ("R3_eca triggered");

  Ptr<Tuple> result = randomlyObtainedServer;

  result = result->Project (
    PKTSERVER,
    strlist ("randomlyObtainedServer_attr2",
      "randomlyObtainedServer_attr3",
      "randomlyObtainedServer_attr2"),
    strlist ("pktServer_attr1",
      "pktServer_attr2",
      RN_DEST));

  Send (result);
}
