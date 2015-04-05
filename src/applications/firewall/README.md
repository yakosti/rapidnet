# Firewall Properties

## Safety Invariant 1

For every packet switch sent from an untrusted host to a trusted host, in the past the controller has received a packet from the switch from that same untrusted host to a trusted host 

```
forall Switch, Src, SrcPort, Dst,
  pktIn(Switch, Src, SrcPort, Dst) AND SrcPort = UNTRUSTED_PORT 
    ->
    exists Controller
      pktFromSwitch(Controller, Switch, Src, SrcPort, Dst)
```

## Safety Invariant 2

If the flow table on the switch contains an entry between Src (via untrusted port) and Dst (via trusted port), then in the past the switch has received a packet send from some Host (via trusted port) to Src

```
forall Switch, Src, SrcPort, Dst, DstPort,
  perFlowRule(Switch, Src, SrcPort, Dst, DstPort) 
  AND SrcPort = UNTRUSTED_PORT
  AND DstPort = TRUSTED_PORT 
  ->
  exists Host, HostPort,
    pktIn(Switch, Host, HostPort, Src),
    HostPort = TRUSTED_PORT
```

## Safety Invariant 3

If trusted controller memory records a connection between Switch and a host, then in a past some trusted source had sent a packet to that host

```
forall Controller, Switch, Host
  trustedControllerMemory(Controller, Switch, Host) 
  ->
  exists Src, SrcPort, 
    pktIn(Switch, Src, SrcPort, Host),
    AND SrcPort = TRUSTED_PORT
```

