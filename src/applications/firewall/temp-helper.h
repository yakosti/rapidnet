#ifndef TEMP_HELPER_H
#define TEMP_HELPER_H

#include "ns3/rapidnet-application-helper.h"
#include "temp.h"

namespace ns3 {
namespace rapidnet {
namespace temp {

class Temp;

class TempHelper: public RapidNetApplicationHelper
{
public:
  TempHelper ()
  {
    m_factory.SetTypeId (Temp::GetTypeId ());
  }
  virtual ~TempHelper ()
  {
  }

protected:
  Ptr<RapidNetApplicationBase> CreateNewApplication ()
  {
    return m_factory.Create<Temp> ();
  }
};

} // namespace temp
} // namespace rapidnet
} // namespace ns3

#endif // TEMP_HELPER_H

