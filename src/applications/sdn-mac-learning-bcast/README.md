# Summary

## Controller Program

### RC1

Summary: Install rules on switch

Head Tuple: flowMod(@Switch, SrcMac, InPort)

### RC2

Summary: Instruct the switch to send out the unmatching packet

Head Tuple: broadcast(@Switch, InPort, SrcMac, DstMac)

## Switch program

Summary: Query the controller when receiving unknown packets

Head Tuple: matchingPacket(@Switch, SrcMac, DstMac, InPort, TopPriority)

