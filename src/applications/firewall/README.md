# Firewall Properties

## Safety Invariant 1

### English

For every packet sent from an untrusted host to a trusted host, there exists a packet sent to that untrusted host from some trusted host. (VeriCon generates counterexamples)

### Logic



## Safety Invariant 2

### English

Flow table entries only contain forwarding rules from trusted hosts

### Logic



## Safety Invariant 3

### English

If `trustedControllerMemory` records a host, in the past, Switch must have forwarded Controller a packet from a trusted host, destined for an untrusted host 

### Logic

```
forall trustedControllerMemory(Controller, Switch, Host) 
  ->
  exists Host, PktIn(Switch, Src, Tport, Host) 
```
