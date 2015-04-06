# SDN-ARP

[ARP Explained](http://www.omnisecu.com/tcpip/address-resolution-protocol-arp.php)

## Properties for testing

### Test 1

Forall: (@Host1) receive a ARP response for IP A -> 
	(@Host2) have sent a broadcast ARP request message for IP A. 

```
forall Host1, IP_A, Mac_A, DstIP, DstMac,
	arpReply(Host1, IP_A, Mac_A, DstIP, DstMac)
	-> exists Host2, SrcIP, SrcMac, arpRequest(Host2, SrcIp, SrcMac, IP_A, Mac_A)
```

### Test 2

Forall: (@Controller )have a map between IP A and MAC A -> 
	either (@Host) A has responded to an ARP request 
	or (@Host) A has sent a broadcast ARP request

```
forall Controller, IP_A, Mac_A,
	arpMapping(Controller, IP_A, Mac_A) 
	->
	exists Host, SrcIP, SrcMac, DstIP, DstMac,
		arpReply(Host, SrcIP, SrcMac, IP_A, Mac_A) **responded to ARP request sent by A** 
		OR arpRequest(Host, Ip_A, Mac_A, DstIP, DstMac) **A has sent a broadcast request** 
```

## Liveness Property

### Liveness 1

Forall: (@Switch)Send a broadcast ARP message for IP A -> 
	@(Controller) no entry that maps IP A to a MAC address

```
forall Switch, Controller, Port, DstMac, DstIp, SrcMac, SrcIP, Mac_A, IP_A,
   packetOut(Switch, Controller, Port,  DstMac, DstIp, SrcMac, SrcIp, Arptype, Type)
   AND DstMac = MAC_A
   AND DstIp = IP_A
   ->
   forall Ip, Mac, (arpMapping(Controller, IP, Mac) -> IP != IP_A)
```

