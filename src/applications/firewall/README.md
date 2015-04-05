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

Result: True
Time: 40ms

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

Result: True
Time: 10ms

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

Result: True
Time: 10ms

# Base Tuple Constraints

# Liveness Properties

## No Black Holes violated

all packets are delivered to their intended destination. A counter example is the case when packets are sent from untrusted host -> untrusted host are dropped. 

## Host migration unsupported

Assume that a host is trusted if it either sent/received (on some switch) a message through/from a trusted port. Thus, when a trusted host migrates to a new switch, the controller will remember it was trusted before and will allow communication from either port. The implementation we have doesn't support it yet, as trust is specified relative to a switch. 
