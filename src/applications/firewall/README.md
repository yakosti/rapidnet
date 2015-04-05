# Firewall Properties

## Safety Invariant 1

### English

For every packet switch sent from an untrusted host to a trusted host, in the past some untrusted host has received a packet from switch, send from some trusted host. (VeriCon generates counterexamples)

### Logic

```
forall Switch, Src, SrcPort, Dst,
  pktIn(Switch, Src, SrcPort, Dst) AND SrcPort = UNTRUSTED_PORT 
    ->
    exists Originator, OriginatorPort,
      pktReceived(Src, SrcPort, Originator, OriginatorPort, Switch)
      AND OriginatorPort = TRUSTED_PORT 
```

Result: True
Time: 40ms

## Safety Invariant 2

### English

If the flow table on the switch contains an entry between Source (via untrusted port) and destination (via trusted port), then in the past the source (via untrusted port) has received a packet from some trusted host (via trusted port) from Switch

### Logic

```
forall Switch, Src, SrcPort, Dst, DstPort,
  perFlowRule(Switch, Src, SrcPort, Dst, DstPort) 
  AND SrcPort = UNTRUSTED_PORT
  AND DstPort = TRUSTED_PORT 
  ->
  exists Host, HostPort,
    pktReceived(Src, SrcPort, Host, HostPort, Switch),
    HostPort = TRUSTED_PORT
```

Result: True
Time: 10ms

## Safety Invariant 3

### English

If trusted controller memory records that a Switch trusts Host2, then Host2 once received a packet sent by Switch from trusted Host1 to Host2.

### Logic

```
forall Controller, Switch, Host
  trustedControllerMemory(Controller, Switch, Host) 
  ->
  exists HostPort, Src, SrcPort
    pktReceived(Host, HostPort, Src, SrcPort, Switch)
    AND SrcPort = TRUSTED_PORT
```
Result: True
Time: 10ms

# Base Tuple Constraints

## pktIn

```
pktIn(a,b,c,d) => a!=b /\ a!=c /\ a!=d /\ b!=c /\ b!=d /\ c!=d

pktIn(a,b,c,d) /\ pktIn(e,f,g,h) /\ a=e /\ b=f /\ d=h => c=g
```

## openConnectionToController

`openConnectionToController(a,b) => a != b`
