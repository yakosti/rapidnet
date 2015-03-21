/* 
 *  ===============
 * ||   SDN ARP   ||
 *  ===============
 * Controller serves as ARP agent
 *
 * Base Tuples
 * -----------
 * 
 * arpRequest(@Host, SrcIp, SrcMac, DstIp, DstMac)
 * 
 * linkHst(@Host, Switch, Port)
 * 
 * Derived Tuples
 * --------------
 * packet(@Switch, Host, Dst, PktLoad)
 *     Switch Received packet sent from Host, to be forwarded to Dst. 
 *     DstMac, DstIp, SrcMac, SrcIp, ARP_REQUEST, ARP_TYPE
 */

/* Constants */









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
/*packet(@Switch, Host, Dst, DstMac, DstIp, SrcMac, SrcIp, Req, Type)*/
/*packetOut(@Switch, Controller, Port, DstMac, DstIp, SrcMac, SrcIp, Req, Type)*/
/*packetIn(@Controller, Switch, InPort, DstMac, DstIp, SrcMac, SrcIp, Req, Type, SrcHost)*/

/* ********************************************************** */

/* 
 * Host program 
 * Send ARP request to directly connected switch
 */
rh1 packet(@Switch, Host, Dst, DstMac, DstIp, SrcMac, SrcIp, Req, Type) :-
	linkHst(@Host, Switch, Port),
	arpRequest(@Host, SrcIp, SrcMac, DstIp, DstMac),
	Req := 1,
	Type := "ARP",
	Dst := "ff:ff:ff:ff:ff".

/* Received packet from switch and extract ARP reply packets */
rh2 arpReply(@Host, SrcIp, SrcMac, DstIp, DstMac) :-
	linkHst(@Host, Switch, Port),
	packet(@Switch, Host, Dst, DstMac, DstIp, SrcMac, SrcIp, Req, Type),
	Dst == Host.

/* ********************************************************** */

/* 
 * Controller program
 * Register host position
 */
rc1 hostPos(@Controller, SrcHost, Switch, InPort) :-
	ofconnCtl(@Controller, Switch),
	packetIn(@Controller, Switch, InPort, SrcHost, Type, Req, SrcIP, SrcMac, DstIP, DstMac).

/*Recover ARP request*/
rc2 arpReqCtl(@Controller, SrcIp, SrcMac, DstIp, DstMac) :-
	packetIn(@Controller, Switch, InPort, DstMac, DstIp, SrcMac, SrcIp, Req, Type, SrcHost),
	ofconnCtl(@Controller, Switch),
	Type == "ARP",
	Req == 1 .

/*Learn ARP mapping*/
rc3 arpMapping(@Controller, SrcIp, SrcMac) :-
	arpReqCtl(@Controller, SrcIp, SrcMac, DstIp, DstMac).

/*Generate ARP reply*/
rc4 arpReplyCtl(@Controller, DstIp, Mac, SrcIp, SrcMac) :-
	arpReqCtl(@Controller, SrcIp, SrcMac, DstIp, DstMac),
	arpMapping(@Controller, DstIp, Mac).

/*Send out packet_out message*/
rc6 packetOut(@Switch, Controller, Port, DstMac, DstIp, SrcMac, SrcIp, Req, Type) :-
	arpReplyCtl(@Controller, SrcIp, SrcMac, DstIp, DstMac),
	ofconnCtl(@Controller, Switch),
	hostPos(@Controller, SrcIp, Switch, Port),
	Req := 2,
	Type := "ARP".

/************************************************************/
/*Switch program*/
rs1 packetIn(@Controller, Switch, InPort, DstMac, DstIp, SrcMac, SrcIp, Req, Type, SrcHost) :-
	ofconnSwc(@Switch, Controller),
	packet(@Switch, Host, Dst, DstMac, DstIp, SrcMac, SrcIp, Req, Type),
	linkSwc(@Switch, Host, InPort),
	Type == "ARP",
	Prio == 1,
	Actions == "controller",
	flowEntry(@Switch, Match, Prio, Actions).

rs2 packet(@Host, Switch, Host, DstMac, DstIp, SrcMac, SrcIp, Req, Type) :-
	packetOut(@Switch, Controller, OutPort, DstMac, DstIp, SrcMac, SrcIp, Req, Type),
	linkSwc(@Switch, Host, Port).










