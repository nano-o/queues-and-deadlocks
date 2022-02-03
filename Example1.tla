------------------------------ MODULE Example1 ------------------------------

(***************************************************************************)
(* We have a distributed system in which nodes communicate through         *)
(* fixed-capacity message queues and a send primitive that blocks when the *)
(* receipient's queue is full.  We want to use the TLC model-checker to    *)
(* find the smallest queue capacity that guarantees that there are no      *)
(* deadlocks.                                                              *)
(*                                                                         *)
(* Nodes are placed in a network represented by a directed graph, where an *)
(* edge from node n to node m means n can send to m.  Nodes send           *)
(* "nominate" and "vote" messages that are flooded throughout the network. *)
(* A node that receives a "nominate" message containing value v floods a   *)
(* "vote" message for value v in response.  When a node observes that a    *)
(* value v has been voted for by all nodes, it terminates.                 *)
(*                                                                         *)
(* To speed up model-checking, we'll model queues as sets (to avoid the    *)
(* combinatorial explosion caused by queue permutations).  Thus the system *)
(* will behave as if a node were allowed to process a message that's       *)
(* anywhere in its queue, not just at the top.                             *)
(*                                                                         *)
(* Results:                                                                *)
(*                                                                         *)
(* With 4 nodes and the ring topology, we need queues of size at least 2.  *)
(* If we add one arbitrary edge, we then need queues of size at least 3.   *)
(*                                                                         *)
(* With 3 nodes and a fully connected network, there is a deadlock with    *)
(* queues of size 3, but I wasn't patient enough to explore the whole      *)
(* state-space with queues of size 4.                                      *)
(*                                                                         *)
(* I'm not sure how useful this all is, as even for 3 or 4 nodes it takes  *)
(* forever to explore the state space, and one can figure out the answers  *)
(* by hand much faster.                                                    *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
        N \* the number of nodes
    ,   C \* the capacity of the queues
    ,   V \* the set of values

Node == 0..N-1

(***************************************************************************)
(* Network topologies                                                      *)
(***************************************************************************)    
FullNetwork == Node\times Node
RingNetwork == {<<n,(n+1)%N>> : n \in Node}
RingNetworkPlusOneEdge == RingNetwork \cup {CHOOSE e \in Node\times Node : \neg e \in RingNetwork /\ e[1] # e[2]}
\* bi-directional ring:
BiRingNetwork == {<<n,(n+1)%N>> : n \in Node} \cup {<<(n+1)%N,n>> : n \in Node}

Peers(n, links) == {m \in Node : <<n,m>> \in links}

Full(q) == Cardinality(q) = C

Network == FullNetwork

(*
--algorithm algo {
    variables
        queue = [n \in Node |-> {}],
        nominated = FALSE;
    procedure flood(message) \* send message m to all peers, unless we sent it already
        variable done = {}, 
    {
flood1:      
        while (done # Peers(self, Network)) {
            with (peer \in Peers(self, Network) \ done) {
                when (\neg Full(queue[peer]) \/ message \in queue[peer]); \* block until the peer's queue has room
                queue[peer] := @ \cup {message}; \* '@' means the value we're assigning to, i.e. queue[peer] in this case.
                done := done \cup {peer}
            }
        };
        return
    }
    process (node \in Node)
        variables
            votes = [n \in Node |-> {}], \* the votes received
            msg;  \* the message we're working on
    {
l1:     \* we start by possibly nominating a value
        if (nominated)
            skip;
        else {
            nominated := TRUE;
            with (v \in V)
            call flood([type |-> "nominate", val |-> v]);
        };
l3:     \* then we enter a receive loop
        while (TRUE) {
            either { \* receive a message
                with (m \in queue[self])
                    msg := m;
                call flood(msg); \* flood the message to neighbors
l4:
                if (msg.type = "nominate") {
                    call flood([sender |-> self, type |-> "vote", val |-> msg.val]);
                }
                else if (msg.type = "vote") {
                    votes[msg.sender] := @ \cup {msg.val};
                };
l5:
                queue[self] := @ \ {msg};
            }
            or {    \* decide and be done
                with (v \in V) {
                    when (\A n \in Node : v \in votes[n]);
                    goto Done;
                }
            }
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "59d323fd" /\ chksum(tla) = "842fe618")
CONSTANT defaultInitValue
VARIABLES queue, nominated, pc, stack, message, done, votes, msg

vars == << queue, nominated, pc, stack, message, done, votes, msg >>

ProcSet == (Node)

Init == (* Global variables *)
        /\ queue = [n \in Node |-> {}]
        /\ nominated = FALSE
        (* Procedure flood *)
        /\ message = [ self \in ProcSet |-> defaultInitValue]
        /\ done = [ self \in ProcSet |-> {}]
        (* Process node *)
        /\ votes = [self \in Node |-> [n \in Node |-> {}]]
        /\ msg = [self \in Node |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "l1"]

flood1(self) == /\ pc[self] = "flood1"
                /\ IF done[self] # Peers(self, Network)
                      THEN /\ \E peer \in Peers(self, Network) \ done[self]:
                                /\ (\neg Full(queue[peer]) \/ message[self] \in queue[peer])
                                /\ queue' = [queue EXCEPT ![peer] = @ \cup {message[self]}]
                                /\ done' = [done EXCEPT ![self] = done[self] \cup {peer}]
                           /\ pc' = [pc EXCEPT ![self] = "flood1"]
                           /\ UNCHANGED << stack, message >>
                      ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                           /\ done' = [done EXCEPT ![self] = Head(stack[self]).done]
                           /\ message' = [message EXCEPT ![self] = Head(stack[self]).message]
                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           /\ queue' = queue
                /\ UNCHANGED << nominated, votes, msg >>

flood(self) == flood1(self)

l1(self) == /\ pc[self] = "l1"
            /\ IF nominated
                  THEN /\ TRUE
                       /\ pc' = [pc EXCEPT ![self] = "l3"]
                       /\ UNCHANGED << nominated, stack, message, done >>
                  ELSE /\ nominated' = TRUE
                       /\ \E v \in V:
                            /\ /\ message' = [message EXCEPT ![self] = [type |-> "nominate", val |-> v]]
                               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "flood",
                                                                        pc        |->  "l3",
                                                                        done      |->  done[self],
                                                                        message   |->  message[self] ] >>
                                                                    \o stack[self]]
                            /\ done' = [done EXCEPT ![self] = {}]
                            /\ pc' = [pc EXCEPT ![self] = "flood1"]
            /\ UNCHANGED << queue, votes, msg >>

l3(self) == /\ pc[self] = "l3"
            /\ \/ /\ \E m \in queue[self]:
                       msg' = [msg EXCEPT ![self] = m]
                  /\ /\ message' = [message EXCEPT ![self] = msg'[self]]
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "flood",
                                                              pc        |->  "l4",
                                                              done      |->  done[self],
                                                              message   |->  message[self] ] >>
                                                          \o stack[self]]
                  /\ done' = [done EXCEPT ![self] = {}]
                  /\ pc' = [pc EXCEPT ![self] = "flood1"]
               \/ /\ \E v \in V:
                       /\ (\A n \in Node : v \in votes[self][n])
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED <<stack, message, done, msg>>
            /\ UNCHANGED << queue, nominated, votes >>

l4(self) == /\ pc[self] = "l4"
            /\ IF msg[self].type = "nominate"
                  THEN /\ /\ message' = [message EXCEPT ![self] = [sender |-> self, type |-> "vote", val |-> msg[self].val]]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "flood",
                                                                   pc        |->  "l5",
                                                                   done      |->  done[self],
                                                                   message   |->  message[self] ] >>
                                                               \o stack[self]]
                       /\ done' = [done EXCEPT ![self] = {}]
                       /\ pc' = [pc EXCEPT ![self] = "flood1"]
                       /\ votes' = votes
                  ELSE /\ IF msg[self].type = "vote"
                             THEN /\ votes' = [votes EXCEPT ![self][msg[self].sender] = @ \cup {msg[self].val}]
                             ELSE /\ TRUE
                                  /\ votes' = votes
                       /\ pc' = [pc EXCEPT ![self] = "l5"]
                       /\ UNCHANGED << stack, message, done >>
            /\ UNCHANGED << queue, nominated, msg >>

l5(self) == /\ pc[self] = "l5"
            /\ queue' = [queue EXCEPT ![self] = @ \ {msg[self]}]
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << nominated, stack, message, done, votes, msg >>

node(self) == l1(self) \/ l3(self) \/ l4(self) \/ l5(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: flood(self))
           \/ (\E self \in Node: node(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Feb 02 17:45:41 PST 2022 by nano
\* Created Tue Feb 01 16:18:02 PST 2022 by nano
