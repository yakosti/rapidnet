# Summary

## Controller Program

### RC1

Summary: Install rules on switch

Head Tuple: flowMod(@Switch, SrcMac, InPort)

### RC2

Summary: Instruct the switch to send out the unmatching packet

Head Tuple: broadcast(@Switch, InPort, SrcMac, DstMac)

## Switch program

### rs1

Summary: Query the controller when receiving unknown packets

Head Tuple: matchingPacket(@Switch, SrcMac, DstMac, InPort, TopPriority)

### rs2 

Summary: Recursively matching flow entries

Head Tuple: matchingPacket(@Switch, SrcMac, DstMac, InPort, NextPriority)

### rs3 

Summary: A hit in flow table, forward the packet accordingly

Head Tuple: packet(@OutNei, Switch, SrcMac, DstMac)

### rs4 

Summary:

Head Tuple:

### rs5

Summary:

Head Tuple:

### rs6

Summary:

### rs7 

Summary:

Head Tuple:

## Host Program

### rh1

Summary:

Head Tuple:

### rh2

Summary:

Head Tuple:


