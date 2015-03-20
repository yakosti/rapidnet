/*Controller serves as ARP agent*/

/*Constants*/









/*Database for controller*/
materialize(ofconnCtl,infinity,infinity,keys(2)). //Openflow connection to switches
/*Arguments: (controller, switch)*/
materialize(arpMapping,infinity,infinity,keys(2)). //Ip=>MAC mapping
/*Arguments: (controller, ip, mac)*/
materialize(hostPos,infinity,infinity,keys(2)). //Position of host
/*Arguments: (controller, host, switch, port)*/

/*Database for switch*/
materialize(ofconnSwc,infinity,infinity,keys(2)). //Openflow connection to controller
/*Arguments: (switch, controller)*/
materialize(linkSwc,infinity,infinity,keys(3:int32)). //Inter-switch and switch-host connections
/*Arguments: (switch, switch/host, port)*/
materialize(flowEntry,infinity,infinity,keys(2:str)). //Flow table at switch
/*Arguments: (switch, match, priority, action)*/

/*Database for host*/
materialize(linkHst,infinity,infinity,keys(3:int32)). //Host-switch connection
/*Arguments: (host, switch, port)*/
materialize(arpRequest,infinity,infinity,keys(2,3:str,4,5:str)). //ARP requests
/*Arguments: (host, src_ip, src_mac, dst_ip, dst_mac)*/
materialize(arpReply,infinity,infinity,keys(2,3:str,4,5:str)). //ARP replys
/*Arguments: (host, src_ip, src_mac, dst_ip, dst_mac)*/

/*Non-materialized tuple:*/
/*packet(@Nexthop, Src, Dst, Packet_load)*/
/*packetOut(@Switch, Controller, Port, Packet)*/
/*packetIn(@Controller, Switch, InPort, Pkt)*/

/*Host program*/
/*Send ARP request to directly connected switch*/
rh1 packet(@Switch, Host, Dst, PktLoad) :-
	linkHst(@Host, Switch, Port),
	arpRequest(@Host, SrcIp, SrcMac, DstIp, DstMac),
	PktLoad1 := f_empty(),
	PktLoad2 := f_prepend(DstMac, PktLoad1),
	PktLoad3 := f_prepend(DstIp, PktLoad2),
	PktLoad4 := f_prepend(SrcMac, PktLoad3),
	PktLoad5 := f_prepend(SrcIp, PktLoad4),
	PktLoad6 := f_prepend(1, PktLoad5),
	PktLoad := f_prepend("ARP", PktLoad6),
	Dst := "ff:ff:ff:ff:ff".

/*Received packet from switch and extract ARP reply packets*/
rh2 arpReply(@Host, SrcIp, SrcMac, DstIp, DstMac) :-
	linkHst(@Host, Switch, Port),
	packet(@Host, Switch, Dst, PktLoad),
	Dst == Host,
	"ARP" == f_first(PktLoad),
	PktLoad1 := f_removeFirst(PktLoad),
	2 == f_first(PktLoad1),
	PktLoad2 := f_removeFirst(PktLoad1),
	SrcIp := f_first(PktLoad2),
	PktLoad3 := f_removeFirst(PktLoad2),
	SrcMac := f_first(PktLoad3),
	PktLoad4 := f_removeFirst(PktLoad3),
	DstIp := f_first(PktLoad4),
	PktLoad5 := f_removeFirst(PktLoad4),
	DstMac := f_first(PktLoad5).

/************************************************************/
/*Controller program*/
/*Register host position*/
rc1 hostPos(@Controller, SrcHost, Switch, InPort) :-
	ofconnCtl(@Controller, Switch),
	packetIn(@Controller, Switch, InPort, Pkt),
	SrcHost := f_first(Pkt).

/*Recover ARP request*/
rc2 arpReqCtl(@Controller, SrcIp, SrcMac, DstIp, DstMac) :-
	packetIn(@Controller, Switch, InPort, Pkt),
	ofconnCtl(@Controller, Switch),
	PktLoad1 := f_removeFirst(Pkt),
	PktLoad2 := f_removeFirst(PktLoad1),
	"ARP" == f_first(PktLoad2),
	PktLoad3 := f_removeFirst(PktLoad2),
	1 == f_first(PktLoad3),
	PktLoad4 := f_removeFirst(PktLoad3),
	SrcIp := f_first(PktLoad4),
	PktLoad5 := f_removeFirst(PktLoad4),
	SrcMac := f_first(PktLoad5),
	PktLoad6 := f_removeFirst(PktLoad5),
	DstIp := f_first(PktLoad6),
	PktLoad7 := f_removeFirst(PktLoad6),
	DstMac := f_first(PktLoad7).

/*Learn ARP mapping*/
rc3 arpMapping(@Controller, SrcIp, SrcMac) :-
	arpReqCtl(@Controller, SrcIp, SrcMac, DstIp, DstMac).

/*Generate ARP reply*/
rc4 arpReplyCtl(@Controller, DstIp, Mac, SrcIp, SrcMac) :-
	arpReqCtl(@Controller, SrcIp, SrcMac, DstIp, DstMac),
	arpMapping(@Controller, DstIp, Mac).

/*Send out packet_out message*/
rc6 packetOut(@Switch, Controller, Port, Pkt) :-
	arpReplyCtl(@Controller, SrcIp, SrcMac, DstIp, DstMac),
	ofconnCtl(@Controller, Switch),
	hostPos(@Controller, SrcIp, Switch, Port),
	PktLoad1 := f_empty(),
	PktLoad2 := f_prepend(DstMac, PktLoad1),
	PktLoad3 := f_prepend(DstIp, PktLoad2),
	PktLoad4 := f_prepend(SrcMac, PktLoad3),
	PktLoad5 := f_prepend(SrcIp, PktLoad4),
	PktLoad6 := f_prepend(2, PktLoad5),
	PktLoad := f_prepend("ARP", PktLoad6),
	Pkt1 := f_prepend(DstIp, PktLoad),
	Pkt := f_prepend(SrcIp, Pkt1).

/************************************************************/
/*Switch program*/
rs1 packetIn(@Controller, Switch, InPort, Pkt) :-
	ofconnSwc(@Switch, Controller),
	packet(@Switch, Host, Dst, PktLoad),
	linkSwc(@Switch, Host, InPort),
	Match == "ARP",
	Match == f_first(PktLoad),
	Prio == 1,
	Actions == "controller",
	flowEntry(@Switch, Match, Prio, Actions),
	Pkt1 := f_prepend(Dst, PktLoad),
	Pkt := f_prepend(Host, Pkt1).

rs2 packet(@Host, Switch, Host, PktLoad) :-
	packetOut(@Switch, Controller, OutPort, Pkt),
	linkSwc(@Switch, Host, Port),
	PktLoad1 := f_removeFirst(Pkt),
	PktLoad := f_removeFirst(PktLoad1).



	
