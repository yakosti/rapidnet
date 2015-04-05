# ARP

## Properties for testing

### Test 1

Base Properties:

linkHst(v1,v2,v3):
v1 != v2
v2 != v3
v1 != v3

arpRequest(v4,v5,v6,v7,v8):
v4 == v5
v4 != v6
v4 != v7
v4 != v8
v6 != v7
v6 != v8
v8 == 255

ofconnCtl(v9,v10):
v9 != v10

ofconnSwc(v11,v12):
v11 != v12

linkSwc(v13,v14,v15):
v13 != v14
v14 != v15
v15 != v13

flowEntry(v16,v17,v18,v19):
v16 != v17
v16 != v18
v16 != v19
v17 == 2054
v18 == 1
v19 == 100

linkSwc(v20,v21,v22) /\ linkSwc(v23,v24,v25):
((v20 == v23 /\ v21 == v24) => (v22 == v25)) /\
((v20 == v23 /\ v22 == v25) => (v21 == v24))

linkHst(v26,v27,v28) /\ linkHst(v29,v30,v31):
v26 == v29 => (v27 == v30) /\ (v28 == v31)

ofconnSwc(v32,v33) /\ ofconnSwc(v34,v35):
(v32 == v34 => v33 == v35)


#### English

Forall: (@Controller) sends an ARP response for IP A -> 
	(@Host1) have sent a broadcast ARP request message for IP A. 

#### Logic

```
forall Controller, IP_A, Mac_A, DstIP, DstMac,
	arpReplyCtl(Controller, IP_A, Mac_A, DstIP, DstMac)
	-> exists Qmac, arpRequest(Host, DstIp, DstMac, IP_A, Qmac) /\
	   	  	 	       Qmac == 255.
```

Result: True
Time: 210ms

### Test 2

#### English

Forall: (@Controller )have a map between IP A and MAC A -> 
	(@Host) A has sent a broadcast ARP request

#### Logic

```
forall Controller, IP_A, Mac_A,
	arpMapping(Controller, IP_A, Mac_A) 
	->
	exists Host, SrcIP, SrcMac, DstIP, DstMac,
		arpReply(Host, IP_A, Mac_A, DstIp, DstMac) /\
			       DstMac == 255

```

Result: True
Time: 30ms

## Liveness Property

### Liveness 1

#### English

Forall: (@Switch)Send a broadcast ARP message for IP A -> 
	@(Controller) no entry that maps IP A to a MAC address

#### Logic

```
forall Switch, Controller, Port, DstMac, DstIp, SrcMac, SrcIP, Mac_A, IP_A,
   packetOut(Switch, Controller, Port,  DstMac, DstIp, SrcMac, SrcIp, Arptype, Type)
   AND DstMac = MAC_A
   AND DstIp = IP_A
   ->
   forall Ip, Mac, (arpMapping(Controller, IP, Mac) -> IP != IP_A)
```

