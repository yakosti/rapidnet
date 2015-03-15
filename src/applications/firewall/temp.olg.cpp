




materialize(trustedControllerMemory,infinity,infinity,keys(1,2,3)). 
materialize(openConnectionToController,infinity,infinity,keys(1)).

materialize(pktIn,infinity,infinity,keys(1,2,3,4)).

materialize(perFlowRule,infinity,infinity,keys(2,3,4,5)).


// ************************************************* //

// a packet from a trusted host via 1 appeared on switch without a forwarding rule
// we know its from a trusted host since it came via 1
// forward packet to untrusted hosts
r1 pktReceived(@Dst, Uport, Src, Tport, Switch)  :- 
	pktIn(@Switch, Src, Tport, Dst),
	Uport := 2,
	Tport := 1 .

// a packet from a trusted host appeared on switch without a forwarding rule
// we know its from a trusted host since it came via 1
// Insert the target of the packet into trusted controller memory
r2 trustedControllerMemory(@Controller, Switch, Dst) :-
	pktReceived(@Dst, Uport, Src, Tport, Switch),
	openConnectionToController(@Dst, Controller),
	Uport := 2,
	Tport := 1 .

// ************************************************* //

// a packet from a trusted host appeared on switch without a forwarding rule
// we know its from a trusted host since it came via 1
// Insert a per-flow rule to forward future packets 
trustedControllerMemory(@Controller, Switch, Dst) :-
	pktIn(@Switch, Src, Tport, Dst),
	controllerConnection(@Switch, Controller),
	Tport := 1 .

// ************************************************* //

// a packet from trusted hosts with a forwarding rule
pktReceived(@Dst, PortDst, Src, Tport, Switch) :- 
 	pktIn(@Switch, Src, Tport, Dst),
	perFlowRule(@Switch, Src, Tport, Dst, PortDst),
	Tport := 1 .


// ************************************************* //

// Packet from unstrusted host appeared on switch
// Send it to the controller to check if it is trused
pktFromSwitch(@Controller, Switch, Src, Uport, Dst) :- 
	pktIn(@Switch, Src, Uport, Dst),
	controllerConnection(@Switch, Controller),
	Uport := 2 .

// Packet from untrusted host appeared on switch
// the controller checked, and tells the switch the Src is trusted
// Controller tells the switch it can forward the packet to the trusted hosts
//  	by inserting a per flow rule into the swtich for that host
perFlowRule(@Switch, Src, Uport, Dst, Tport) :-  
	pktFromSwitch(@Controller, Switch, Src, Uport, Dst), 
	trustedControllerMemory(@Controller, Switch, Src),
	Uport := 2,
	Tport := 1 .

// ************************************************* //

// (previous) Switch now has perFlowRule from an untrusted host, so it forst the packet to the target trusted host
// (current) A packet from untrusted hosts with a forwarding rule also falls into this category
pktReceived(@Dst, Tport, Src, Uport, Switch) :-
	perFlowRule(@Switch, Src, Uport, Dst, Tport),
 	pktIn(@Switch, Src, Uport, Dst),
 	Uport := 2,
	Tport := 1 .

// ************************************************* //








