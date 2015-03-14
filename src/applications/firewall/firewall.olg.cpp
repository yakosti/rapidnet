// DECLARE PREDICATES
// ===================
// 
// Constants
// ---------
// TRUSTED_PORT
// UNTRUSTED_PORT
//
// A packet from host Src appeared on Switch via SrcPort and is to be send to Dst
// This is the only base tuple
// --------------------------------------------------------------------------------------------
// pktIn(@Switch, Src, SrcPort, Dst)  
//  
// a packet sent by Src via PortSrc was received from Switch at Dst via PortDst
// -------------------------------------------------------
// pktReceived(@Dst, PortDst, Src, PortSrc, Switch) 
//
// relation table entry: packet sent from host Src via port SrcPort is forwarded by Switch
// -------------------------------------------------------
// forwardingEntry(@Switch, Src, SrcPort, Dst) to host DST.
//
// relation table entry in controller memory: switch and trusted Host 
// -------------------------------------------------------
// trustedControllerMemory(@Controller, Switch, Host) 
//
// Ok for the switch to forward packets from Src via PortIn to Dst via PortOut
// -------------------------------------------------------
// perFlowRule(@Switch, Src, SrcPort, Dst, DstPort)
//  
// Stupid Switch asks the Smart controller is this host Src is trusted on Switch
// pktFromSwitch(@Controller, Switch, Src)

// ************************************************* //




/*Database for controller*/
//stores the pairs of trusted switch-host 
materialize(trustedControllerMemory,infinity,infinity,keys(2)) 

/* Database for */
materialize(pktIn,infinity,infinity,keys(1,2,3,4)). //a packet is sent to a switch

// ************************************************* //

// a packet from a trusted host via 1 appeared on switch without a forwarding rule
// we know its from a trusted host since it came via 1
// forward packet to untrusted hosts
pktReceived(@Dst, 2, Src, 1, Switch)  :- 
	pktIn(@Switch, Src, Dst, 1),

// a packet from a trusted host appeared on switch without a forwarding rule
// we know its from a trusted host since it came via 1
// Insert the target of the packet into trusted controller memory
trustedControllerMemory(@Controller, Switch, Dst) :-
	pktReceived(@Dst, 2, Src, 1, Switch).

// ************************************************* //

// a packet from a trusted host appeared on switch without a forwarding rule
// we know its from a trusted host since it came via 1
// Insert a per-flow rule to forward future packets 
perFlowRule(@Switch, Src, 1, Dst, 2) :-
	trustedControllerMemory(@Controller, Switch, Dst), 
	pktIn(@Switch, Src, 1, Dst),

// ************************************************* //

// a packet from trusted hosts with a forwarding rule
pktReceived(@Dst, PortDst, Src, 1, Switch) :- 
 	pktIn(@Switch, Src, 1, Dst),
	perFlowRule(@Switch, Src, 1, Dst, PortDst).

// ************************************************* //

// Packet from unstrusted host appeared on switch
// Send it to the controller to check if it is trused
pktFromSwitch(@Controller, Switch, Src, 2, Dst) :- 
	pktIn(@Switch, Src, 2, Dst).

// Packet from untrusted host appeared on switch
// the controller checked, and tells the switch the Src is trusted
// Controller tells the switch it can forward the packet to the trusted hosts
//  	by inserting a per flow rule into the swtich for that host
perFlowRule(@Switch, Src, 2, Dst, 1) :-  // installs a flow rule on Switch
	pktFromSwitch(@Controller, Switch, Src, 2, Dst), //controller received packet from switch
	trustedControllerMemory(@Controller, Switch, Src)  // Controller knows that Switch trusts Src

// ************************************************* //

// (previous) Switch now has perFlowRule from an untrusted host, so it forst the packet to the target trusted host
// (current) A packet from untrusted hosts with a forwarding rule also falls into this category
pktReceived(@Dst, 1, Src, UNTRUSTED_POST, Switch) :-
	perFlowRule(@Switch, Src, 2, Dst, 1),
 	pktIn(@Switch, Src, 2, Dst).

// ************************************************* //























