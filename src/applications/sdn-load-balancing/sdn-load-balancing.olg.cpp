



materialize(serverMapping, infinity, infinity, keys(1,2,3:int32)).
materialize(initPacket, infinity, infinity, keys(1,2,3)).
materialize(designated, infinity, infinity, keys(1,2)).

/* Multiple clients
 * Multiple load balancers
 * Multipler Servers (5 in this case with identical functions, different IP addresses) 
 */

/* Base Tuple: Client initializes a packet and sends it to a load balancer it is connected to
// initPacket(@Client, Server, LoadBalancer)
// LoadBalancer received a packet from client that has destination 
r1 packet(@LoadBalancer, Client, Server) :-
	initPacket(@Client, Server, LoadBalancer).

/* Base Tuple: Load Balancer's designated destination */
// designated(@LoadBalancer, DesignatedDst)
// LoadBalancer received a packet to be sent to its designated destination
//Hash the Client (source) and use that result modulo the number of servers
//  to get a number corresponding to a server
r2 hashed(@LoadBalancer, Client, ServerNum) :- 
    packet(@LoadBalancer, Client, Server),
 	designated(@LoadBalancer, DesignatedDst),
 	DesignatedDst == Server,
 	Value := f_hashIp(Client),
	ServerNum := 1+f_modulo(Value, 5).

/* Base Tuple: serverMapping */
// Match ServerNum obtained by hashing to a server to send the packet to 
r3 recvPacket(@Server, Client) :- 
	hashed(@LoadBalancer, Client, ServerNum),
	serverMapping(@LoadBalancer, Server, ServerNum).

// LoadBalancer received a packet to be sent to a server that is NOT its designated destination
// forward the packet directly to the destination as prescribed by the packet
r4 recvPacket(@Server, Client) :- 
	packet(@LoadBalancer, Client, Server).






























