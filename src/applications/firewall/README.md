# Firewall Properties

## Safety Invariant 1

### English

(@Switch) For every packet sent from an untrusted host to a trusted host, there exists a packet sent to that untrusted host from some trusted host. (VeriCon generates counterexamples)

### Logic

```
forall Switch, Src, SrcPort, Dst
  pktIn(Switch, Src, SrcPort, Dst) AND SrcPort = UNTRUSTED_PORT 
    ->
    exists Originator, OriginatorPort,
      pktReceived(Src, SrcPort, Originator, OriginatorPort, Switch)
      AND OriginatorPort = TRUSTED_PORT 
```

## Safety Invariant 2

### English

Flow table entries only contain forwarding rules from trusted hosts
trusted hosts means that src is from a trusted port, or src is trusted on switch

### Logic

```
forall Switch, Src, Uport, Dst, Tport,
  perFlowRule(Switch, Src, SrcPort, Dst, DstPort) 
  ->
  exists Controller,
    SrcPort == TRUSTED_PORT 
    OR (DstPort == UNTRUSTED_PORT AND trustedControllerMemory(Controller, Switch, Src))
```

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
