------------------------------ MODULE Example1 ------------------------------

(***************************************************************************)
(* We have a distributed system in which nodes run a toy version of        *)
(* Stellar's nomination protocol and communicate through fixed-capacity    *)
(* message queues and a send primitive that blocks when the receipient's   *)
(* queue is full.  We want to use the TLC model-checker to find the        *)
(* smallest queue capacity that guarantees that there are no deadlocks.    *)
(*                                                                         *)
(* Nodes are placed in a network represented by a directed graph, where an *)
(* edge from node n to node m means n can send to m.  Nodes send           *)
(* "nominate" and "vote" messages that are flooded throughout the network. *)
(* One node first floods a "nominate" message.  Then, a node that receives *)
(* a "nominate" message floods a "vote" message in response.  When a node  *)
(* observes that all nodes have sent a "vote" message, it terminates.      *)
(*                                                                         *)
(* To speed up model-checking, we model queues as sets (to avoid the       *)
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

Node == 0..N-1

(***************************************************************************)
(* Network topologies                                                      *)
(***************************************************************************)    
FullNetwork == Node\times Node \ {<<n,n>> : n \in Node}
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
            with (peer = CHOOSE n \in Peers(self, Network) \ done : TRUE) {
                when (\neg Full(queue[peer]) \/ message \in queue[peer]); \* block until the peer's queue has room
                queue[peer] := @ \cup {message}; \* '@' means the value we're assigning to, i.e. queue[peer] in this case.
                done := done \cup {peer}
            }
        };
        return
    }
    process (node \in Node)
        variables
            votes = {}, \* the votes received
            msg;  \* the message we're working on
    {
l1:     \* we start by possibly nominating a value
        if (nominated)
            skip;
        else {
            nominated := TRUE;
            call flood([type |-> "nominate"]);
        };
l2:     \* then we enter a receive loop
        while (\E n \in Node : \neg n \in votes) {
            \* receive a message
            with (m \in queue[self])
                msg := m;
            call flood(msg); \* flood the message to neighbors
l3:
            if (msg.type = "nominate") {
                call flood([sender |-> self, type |-> "vote"]);
            }
            else if (msg.type = "vote") {
                votes := @ \cup {msg.sender};
            };
l4:
            queue[self] := @ \ {msg};
        }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "a6fbcb1b" /\ chksum(tla) = "c7c943a4")
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
        /\ votes = [self \in Node |-> {}]
        /\ msg = [self \in Node |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "l1"]

flood1(self) == /\ pc[self] = "flood1"
                /\ IF done[self] # Peers(self, Network)
                      THEN /\ LET peer == CHOOSE n \in Peers(self, Network) \ done[self] : TRUE IN
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
                       /\ pc' = [pc EXCEPT ![self] = "l2"]
                       /\ UNCHANGED << nominated, stack, message, done >>
                  ELSE /\ nominated' = TRUE
                       /\ /\ message' = [message EXCEPT ![self] = [type |-> "nominate"]]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "flood",
                                                                   pc        |->  "l2",
                                                                   done      |->  done[self],
                                                                   message   |->  message[self] ] >>
                                                               \o stack[self]]
                       /\ done' = [done EXCEPT ![self] = {}]
                       /\ pc' = [pc EXCEPT ![self] = "flood1"]
            /\ UNCHANGED << queue, votes, msg >>

l2(self) == /\ pc[self] = "l2"
            /\ IF \E n \in Node : \neg n \in votes[self]
                  THEN /\ \E m \in queue[self]:
                            msg' = [msg EXCEPT ![self] = m]
                       /\ /\ message' = [message EXCEPT ![self] = msg'[self]]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "flood",
                                                                   pc        |->  "l3",
                                                                   done      |->  done[self],
                                                                   message   |->  message[self] ] >>
                                                               \o stack[self]]
                       /\ done' = [done EXCEPT ![self] = {}]
                       /\ pc' = [pc EXCEPT ![self] = "flood1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << stack, message, done, msg >>
            /\ UNCHANGED << queue, nominated, votes >>

l3(self) == /\ pc[self] = "l3"
            /\ IF msg[self].type = "nominate"
                  THEN /\ /\ message' = [message EXCEPT ![self] = [sender |-> self, type |-> "vote"]]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "flood",
                                                                   pc        |->  "l4",
                                                                   done      |->  done[self],
                                                                   message   |->  message[self] ] >>
                                                               \o stack[self]]
                       /\ done' = [done EXCEPT ![self] = {}]
                       /\ pc' = [pc EXCEPT ![self] = "flood1"]
                       /\ votes' = votes
                  ELSE /\ IF msg[self].type = "vote"
                             THEN /\ votes' = [votes EXCEPT ![self] = @ \cup {msg[self].sender}]
                             ELSE /\ TRUE
                                  /\ votes' = votes
                       /\ pc' = [pc EXCEPT ![self] = "l4"]
                       /\ UNCHANGED << stack, message, done >>
            /\ UNCHANGED << queue, nominated, msg >>

l4(self) == /\ pc[self] = "l4"
            /\ queue' = [queue EXCEPT ![self] = @ \ {msg[self]}]
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << nominated, stack, message, done, votes, msg >>

node(self) == l1(self) \/ l2(self) \/ l3(self) \/ l4(self)

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
\* Last modified Wed Feb 02 18:14:56 PST 2022 by nano
\* Created Tue Feb 01 16:18:02 PST 2022 by nano
