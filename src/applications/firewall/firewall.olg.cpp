/* 
 * ------------------------------------------------------------------------------------
 *  -------------------
 * | Tuples Definition |
 *  -------------------
 * 
 * pktReceived(@Dst, DstPort, Src, SrcPort, Switch):
 *     Host Dst received a packet via DstPort from switch, that
 *     was originally sent by Host Src via SrcPort
 * 
 * pktIn(@Switch, Src, SrcPort, Dst):
 * 	   Switch received a packet from host Src via SrcPort, that
 *     Src wants to send to host Dst
 *
 * trustedControllerMemory(@Controller, Switch, Host):
 *     Controller stores in its memory table, that Switch trusts Host
 *
 * connection(@Switch, Controller):
 *     Allows switch to open a connection to controller to communicate with it
 *
 * perFlowRule(@Switch, Src, SrcPort, Dst, DstPort):
 *     Switch stores in its memory table, that whenever packet from host Src
 *     appears via SrcPort, and is to be sent to host Dst, send it via DstPort.
 *     This is allowed because it has been done before at least once.
 * ------------------------------------------------------------------------------------
 * 
 * One controller
 * multiple switches
 * multiple hosts
 * multiple ports
 *
 * ------------------------------------------------------------------------------------
 */




materialize(trustedControllerMemory,infinity,infinity,keys(2,3)). 
materialize(connection,infinity,infinity,keys(1)).
materialize(pktIn,infinity,infinity,keys(1,2,3:int32,4)).
materialize(perFlowRule,infinity,infinity,keys(1,2,3:int32,4,5:int32)).


/* ************************************************* */

/* (@Switch) Program
 * a packet from a trusted host via TRUSTED_PORT appeared on switch without a forwarding rule
 * we know its from a trusted host since it came via TRUSTED_PORT
 * forward packet to untrusted hosts
 */
r1 pktReceived(@Dst, Uport, Src, Tport, Switch)  :- 
	pktIn(@Switch, Src, Tport, Dst),
	Uport := 2,
	Tport == 1 .

/* (@Switch) Program
 * a packet from a trusted host appeared on switch without a forwarding rule
 * we know its from a trusted host since it came via TRUSTED_PORT
 * Insert the target of the packet into trusted controller memory
 */
r2 trustedControllerMemory(@Controller, Switch, Dst) :-
	pktIn(@Switch, Src, Tport, Dst),
	connection(@Switch, Controller),
	Tport == 1 .


/* ************************************************* */

/* (@Switch) Program
 * a packet from with a forwarding rule appears on the switch
 * Forward according to the rule
 * The packet may be from a trusted/untrusted source
 */
r3 pktReceived(@Dst, PortDst, Src, PortSrc, Switch) :- 
 	pktIn(@Switch, Src, PortSrc, Dst),
	perFlowRule(@Switch, Src, PortSrc, Dst, PortDst).

/* ************************************************* */

/* (@Switch) Program
 * Packet from unstrusted host appeared on switch
 * Send it to the controller to check if it is trused
 */
r4 pktFromSwitch(@Controller, Switch, Src, Uport, Dst) :- 
	pktIn(@Switch, Src, Uport, Dst),
	connection(@Switch, Controller),
	Uport == 2 .

/* (@Controller) Program
 * Packet from untrusted host appeared on switch
 * the controller checked, and tells the switch the Src is trusted
 * Controller tells the switch it can forward the packet to the trusted hosts
 *  	by inserting a per flow rule into the swtich for that host
 */
r5 perFlowRule(@Switch, Src, Uport, Dst, Tport) :-  
	pktFromSwitch(@Controller, Switch, Src, Uport, Dst), 
	trustedControllerMemory(@Controller, Switch, Src),
	Uport == 2,
	Tport := 1 .

/* ************************************************* */







