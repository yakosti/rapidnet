# Firewall Properties

## Safety Invariant 1

### English

For every packet sent from an untrusted host to a trusted host, there exists a packet sent to that untrusted host from some trusted host. (VeriCon generates counterexamples)


## Safety Invariant 2

### English

Flow table entries only contain forwarding rules from trusted hosts

### Logic

## Safety Invariant 3

### English

Controller data structure `trustedControllerMemory` records the correct hosts 
