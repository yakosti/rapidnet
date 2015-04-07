/* SdnLoadBalancing
 * ================
 * 
 * Flow Affinity
 * -------------
 * a flow cannot be split on two destination servers.
 * 
 * Description
 * ------------
 * matches packets on a particular destination address (e.g. an address for web service), a
 * and split them based on hash values of their source addresses. 
 * load balancer has a default rule that allows traffic not destined to the 
 * designated destination to go as it would usually.
 * 
 * Could break flow affinity property
 * ----------------------------------
 * When a machine is connected to two load balancers 
 * and sends packets of the same flow to both of the load balancers,
 * one of the flow will match on the default rule of a load balancer and may 
 * potentially be directed to a different server
 * 
 * Nodes
 * -----
 * Multiple clients
 * Multiple load balancers
 * Multipler Servers (5 in this case with identical functions, different IP addresses) 
 * 
 * Base Tuples
 * -----------
 * initPacket(@Client, Server, LoadBalancer):
 *     Client initializes a packet and sends it to a load balancer it is connected to
 * designated(@LoadBalancer, DesignatedDst):
 *     LoadBalancer's designated destination is DesignatedDst
 * serverMapping(@LoadBalancer, Server, ServerNum):
 *     LoadBalancer stores which ServerNum (1 <= ServerNum <= NUM_SERVERS)
 *     is mapped to which server
 */

// total number of possible servers that the load balancers can send a packet to 


materialize(serverMapping, infinity, infinity, keys(1,2,3:int32)).
materialize(initPacket, infinity, infinity, keys(1,2,3)).
materialize(designated, infinity, infinity, keys(1,2)).




/* Initialize Packets*/

// LoadBalancer received a packet from Client that has destination Server
r1 packet(@LoadBalancer, Client, Server) :-
	initPacket(@Client, Server, LoadBalancer).





/* Packet appearing on LoadBalancer is to be sent to its designated server */

// LoadBalancer had received a packet to be sent to its designated destination
// Hash the Client (source) and use that result modulo the number of servers
// to get a number corresponding to a server
r2 hashed(@LoadBalancer, Client, ServerNum) :- 
    packet(@LoadBalancer, Client, Server),
 	designated(@LoadBalancer, DesignatedDst),
 	DesignatedDst == Server,
 	Value := f_hashIp(Client),
	ServerNum := 1+f_modulo(Value, 5).

// Match ServerNum obtained by hashing to a server to send the packet to 
r3 recvPacket(@Server, Client) :- 
	hashed(@LoadBalancer, Client, ServerNum),
	serverMapping(@LoadBalancer, Server, ServerNum).





/* Packet appearing on LoadBalancer is NOT to be sent to its designated server */

// LoadBalancer received a packet to be sent to a server that is NOT its designated destination
// forwards the packet directly to the destination as prescribed by the packet
r4 recvPacket(@Server, Client) :- 
	packet(@LoadBalancer, Client, Server),
	designated(@LoadBalancer, DesignatedDst),
	Server != DesignatedDst.






























