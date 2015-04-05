# MAC Learning

[Description](https://telconotes.wordpress.com/2013/03/09/how-a-switch-works/)

## Properties that can be checked using our algorithm

### Property 1

(@ Switch): Forall: have routing entry for MAC address A -> 
(@Switch) have received a frame sourced from A 
(Assumptions: no spoofing, no changing it to a frame that has source MAC address A)

```
forall Switch, Mac_A, OutPort, flowEntry(Switch, MAC_A, OutPort) ->
	exists Nei, DstMac, packet(Switch, Nei, Mac_A, DstMac) 
```

## Properties to be checked for future work

### Property 2

Forall: (@End-host) Have received a frame B that is not destined to end-host A 
       -> (@Switch) Switch does not have a routing entry for B's dest address

```
forall Switch, Nei, Mac, Outport, 
  packet(Switch, Nei, Mac, Mac_B) AND Mac!=Mac_A AND Mac!=Mac_B ->
  (flowEntry(Switch, Mac, Outport) AND Mac!=Mac_B)
```

### Property 3

(@Switch) Not exist a routing entry to MAC address A -> (@Switch) never have received/forwarded a packet sourced from A

```
forall Switch, OutPort, Mac, 
 (flowEntry(Switch, Mac, Outport) -> Mac != Mac_A)
 ->
 (forall Nei', Mac', DstMac', 
 packet(Switch, Nei', Mac', DstMac') -> Mac' != Mac_A)
```
