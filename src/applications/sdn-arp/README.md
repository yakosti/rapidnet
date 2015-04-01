# ARP

## Properties for testing

### Test 1

#### English

Forall: (@Host1) receive a ARP response for IP A -> 
	(@Host2) have sent a broadcast ARP request message for IP A. 

#### Logic

```
forall Host1, IP_A, Mac_A, DstIP, DstMac,
	arpReply(Host1, IP_A, Mac_A, DstIP, DstMac)
	-> exists Host2, SrcIP, SrcMac, arpRequest(Host2, SrcIp, SrcMac, IP_A, Mac_A)
```

### Test 2

#### English

Forall: (@Controller )have a map between IP A and MAC A -> 
	either (@Host) A has responded to an ARP request 
	or (@Host) A has sent a broadcast ARP request

#### Logic

```
forall Controller, IP_A, Mac_A,
	arpMapping(Controller, IP_A, Mac_A) 
	->
	exists Host, SrcIP, SrcMac, DstIP, DstMac,
		arpReply(Host, SrcIP, SrcMac, IP_A, Mac_A) **responded to ARP request sent by A** OR
		arpRequest(Host, Ip_A, Mac_A, DstIP, DstMac) **A has sent a broadcast request** 
```

## Liveness Property

### Liveness 1

#### English

Forall: (@Switch)Send a broadcast ARP message for IP A -> 
	@(Controller) no entry that maps IP A to a MAC address

#### Logic

```
forall Switch, Controller, Port, SrcMac, SrcIP, Mac_A, IP_A,
   packetOut(Switch, Controller, Port, 
 	   f_prepend(SrcIP,
          	f_prepend(DstIp,
          		f_prepend(ARP_TYPE,
          			f_prepend(ARP_REPLY,
          				f_prepend(SrcIp,
          					f_prepend(SrcMac,
          						f_prepend(IP_A,
          							f_prepend(IP_A, 
          								f_prepend(Mac_A, f_empty())))))))))
     -> 
     forall IP, Mac, ( (Mac!=Mac_A) -> (arpMapping(Controller,IP,Mac)!=arpMapping(@Controller,IP_A,Mac_A)) )
```
