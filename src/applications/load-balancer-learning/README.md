# load-balancer-learning

[Understanding Mac Learning](http://www.globalknowledge.ae/about-us/Knowledge-Center/Article/How-do-Switches-Work/)

## Flow Affinity

### English

(@switch) two packets on different switches
->
(@Host) either different source or different destination 

### Logic

```
forall Switch1, Nei1, SrcMac1, DstMac1, Switch2, Nei2, SrcMac2, DstMac2,
  packet(Switch1, Nei1, SrcMac1, DstMac1) 
  AND packet(Switch2, Nei2, SrcMac2, DstMac2) 
  AND Switch1 != Switch2,
  ->
  exists Host1, Host2, LoadBalancer, 
  	(initPacket(Host1, LoadBalancer, SrcMac1, DstMac1) 
  	AND initPacket(Host2, LoadBalancer, SrcMac2, DstMac2)
  	AND ((Host1 != Host2) OR (DstMac1 != DstMac2))
```







