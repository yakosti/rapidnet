/*TODO: Program to be tested in simulation*/

/*Database for controller*/
materialize(ofconn,infinity,infinity,keys(2)). /*Openflow connection to switch*/

/*Database for switch*/
materialize(ofconn,infinity,infinity,keys(2)). /*Openflow connection to controller*/
materialize(flowEntry,infinity,infinity,keys(2:str)). /*Flow table at switch*/
materialize(link,infinity,infinity,keys(2)). /*Neighboring relationship*/
materialize(maxPriority,infinity,1,keys(1)). /*Records the maximum priority, initial value == 0*/

/*Database for host*/
materialize(initPacket,infinity,infinity,keys(2,3:str,4:str)). /*Packet for simulation initialization*/
materialize(recvPacket,infinity,infinity,keys(2:str,3:str)). /*Packet for simulation initialization*/



/*Controller program*/
/*Install rules on switch*/
rc1 flowMod(@Switch, SrcMac, InPort) :-
	ofconn(@Controller, Switch),
	ofPacket(@Controller, Switch, InPort, SrcMac, DstMac).

/*Instruct the switch to send out the unmatching packet*/
rc2 broadcast(@Switch, InPort, SrcMac, DstMac) :-
	ofconn(@Controller, Switch),
	ofPacket(@Controller, Switch, InPort, SrcMac, DstMac).


/*Switch program*/
/*Query the controller when receiving unknown packets */
rs1 matchingPacket(@Switch, SrcMac, DstMac, InPort, TopPriority) :-
	packet(@Switch, Nei, SrcMac, DstMac),
	link(@Switch, Nei, InPort),
	maxPriority(@Switch, TopPriority).

/*Recursively matching flow entries*/
rs2 matchingPacket(@Switch, SrcMac, DstMac, InPort, NextPriority) :-
	matchingPacket(@Switch, SrcMac, DstMac, InPort, Priority),
	flowEntry(@Switch, MacAdd, OutPort, Priority),
	Priority > 0,
	DstMac != MacAdd,
	NextPriority := Priority - 1.

/*A hit in flow table, forward the packet accordingly*/
rs3 packet(@OutNei, Switch, SrcMac, DstMac) :-
	matchingPacket(@Switch, SrcMac, DstMac, InPort, Priority),
	flowEntry(@Switch, MacAdd, OutPort, Priority),
	link(@Switch, OutNei, OutPort),
	Priority > 0,
	DstMac == MacAdd.

/*If no flow matches, send the packet to the controller*/
rs4 ofPacket(@Controller, Switch, InPort, SrcMac, DstMac) :-
	ofconn(@Switch, Controller),
	matchingPacket(@Switch, SrcMac, DstMac, InPort, Priority),
	Priority == 0.

/*Insert a flow entry into forwarding table*/
/*(TODO): We assume all flow entries are independent, which is not general*/
rs5 flowEntry(@Switch, DstMac, OutPort, Priority) :-
	flowMod(@Switch, DstMac, OutPort),
	ofconn(@Switch, Controller),
	maxPriority(@Switch, TopPriority),
	Priority := TopPriority + 1.

/*TODO: should be a_MAX<Priority> in the head tuple*/
rs6 maxPriority(@Switch, Priority) :-
	flowEntry(@Switch, DstMac, OutPort, Priority).

/*Following the controller's instruction, send out the packet as broadcast*/
rs7 packet(@OutNei, Switch, SrcMac, DstMac) :-
	broadcast(@Switch, InPort, SrcMac, DstMac),
	link(@Switch, OutNei, OutPort),
        OutPort != InPort.


/*Host program*/
/*Packet initialization*/
rh1 packet(@Switch, Host, SrcMac, DstMac) :-
	initPacket(@Host, Switch, SrcMac, DstMac),
	link(@Host, Switch, OutPort).

/*Receive a packet*/
rh2 recvPacket(@Host, SrcMac, DstMac) :-
	packet(@Host, Switch, SrcMac, DstMac),
	link(@Host, Switch, InPort).

