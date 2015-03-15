




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

r2 trustedControllerMemory(@Controller, Switch, Dst) :-
	pktReceived(@Dst, Uport, Src, Tport, Switch),
	openConnectionToController(@Dst, Controller),
	Uport := 2,
	Tport := 1 .














