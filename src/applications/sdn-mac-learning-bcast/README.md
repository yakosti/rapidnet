# Summary

## Controller Program

### RC1

Summary: Controller installs flow rule on switch

Head Tuple: flowMod(@Switch, SrcMac, InPort)

### RC2

Summary: Controller instructs the switch to send out the unmatching packet

Head Tuple: broadcast(@Switch, InPort, SrcMac, DstMac)

## Switch program

### rs1

Summary: Begin querying the controller upon receiving an unknown

Head Tuple: matchingPacket(@Switch, SrcMac, DstMac, InPort, TopPriority)

### rs2 

Summary: Recursively querying flow table in order of decreasing priority for matching flow entries

Head Tuple: matchingPacket(@Switch, SrcMac, DstMac, InPort, NextPriority)

### rs3 

Summary: A hit in flow table, forward the packet accordingly

Head Tuple: packet(@OutNei, Switch, SrcMac, DstMac)

### rs4 

Summary: No flow matches found, send the packet to the controller for processing

Head Tuple: ofPacket(@Controller, Switch, InPort, SrcMac, DstMac) 

### rs5

Summary: Controller has sent the switch a flow rule for the unknown packet. Use it to insert an appropriate flow entry into forwarding table

Head Tuple: flowEntry(@Switch, DstMac, OutPort, Priority)

### rs6

Summary: NEEDS WORK / REMOVE 

HeadTuple: maxPriority(@Switch, Priority)

### rs7 

Summary: Following instructions from the controller, the switch sends out an unknown packet as broadcast  

Head Tuple: packet(@OutNei, Switch, SrcMac, DstMac)

## Host Program

### rh1

Summary: Host initializes a packet to be sent to some destination via a switch 

Head Tuple: packet(@Switch, Host, SrcMac, DstMac)

### rh2

Summary: Host has received a packet

Head Tuple: recvPacket(@Host, SrcMac, DstMac) 

# Base Tuples Contraints

## Link

```
link(a,b,c) => (a != b /\ b != c /\ a != c)
(link(a,b,c) /\ link(e,f,g) /\ a == e /\ b == f) => (c == g)
```
