




materialize(trustedControllerMemory,infinity,infinity,keys(1,2,3)). 
materialize(openConnectionToController,infinity,infinity,keys(1,2)).

materialize(pktIn,infinity,infinity,keys(1,2,3,4)).


// ************************************************* //

// a packet from a trusted host via 1 appeared on switch without a forwarding rule
// we know its from a trusted host since it came via 1
// forward packet to untrusted hosts
pktReceived(@Dst, 2, Src, 1, Switch)  :- 
	pktIn(@Switch, Src, Dst, 1).

// a packet from a trusted host appeared on switch without a forwarding rule
// we know its from a trusted host since it came via 1
// Insert the target of the packet into trusted controller memory
trustedControllerMemory(@Controller, Switch, Dst) :-
	pktReceived(@Dst, 2, Src, 1, Switch),
	openConnectionToController(@Dst, Controller).

// ************************************************* //




