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

Summary: If no flow matches, send the packet to the controller

Head Tuple: ofPacket(@Controller, Switch, InPort, SrcMac, DstMac) 

### rs5

Summary: Insert a flow entry into forwarding table

Head Tuple: flowEntry(@Switch, DstMac, OutPort, Priority)

### rs6

Summary: should be a_MAX<Priority> in the head tuple

HeadTuple: maxPriority(@Switch, Priority)

### rs7 

Summary: Following the controller's instruction, send out the packet as broadcast

Head Tuple: packet(@OutNei, Switch, SrcMac, DstMac)

## Host Program

### rh1

Summary: Packet initialization

Head Tuple: packet(@Switch, Host, SrcMac, DstMac)

### rh2

Summary: Receive a packet

Head Tuple: recvPacket(@Host, SrcMac, DstMac) 


