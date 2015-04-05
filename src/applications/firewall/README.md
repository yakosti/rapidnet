# Firewall Properties

## Safety Invariant 1

For every packet a trusted host receives from an untrusted host via Switch, in the past the switch has received a packet sent from some trusted host' to the untrusted host. 

```
forall Switch, Src, SrcPort, Dst,
  pktReceived(@Dst, PortDst, Src, PortSrc, Switch)
  AND PortDst = TRUSTED_PORT
  AND PortSrc = UNTRUSTED_PORT
    ->
    exists Controller, Host, HostPort,
      pktIn(Switch, Host, HostPort, Src) 
      AND HostPort = TRUSTED_PORT
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

