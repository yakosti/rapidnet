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

}

void
Firewall::DemuxRecv (Ptr<Tuple> tuple)
{
  RapidNetApplicationBase::DemuxRecv (tuple);

}
