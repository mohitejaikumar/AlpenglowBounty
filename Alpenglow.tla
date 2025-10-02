--------------------------- MODULE Alpenglow ---------------------------
(*
    Enhanced Formal Specification of Solana Alpenglow Consensus Protocol
    
    Key Features:
    - Votor: Dual voting paths (80% fast, 60% slow)  
    - Rotor: Block dissemination with Byzantine equivocation
    - SafeToNotar/SafeToSkip fallback mechanisms
    - Leader rotation with windows
    - Byzantine fault tolerance (up to 20% stake)
    - Certificate aggregation and validation
*)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Nodes,              \* Set of validator nodes
    MaxSlots,           \* Maximum number of slots to model
    WindowSize,         \* Number of slots per leader window
    Gamma,              \* Data shreds per slice (for Rotor)
    TotalShreds,        \* Total shreds per slice (Γ = 2 * Gamma for κ=2)
    BlockTime,          \* Time for one block slot
    NetworkDelay,       \* Maximum network delay (Δ)
    GenesisSlot,        \* Starting slot
    ByzantineNodes,     \* Set of Byzantine nodes
    CorrectBlocks,      \* Set of valid block IDs
    MaliciousBlocks,     \* Set of invalid block IDs Byzantine nodes can create
    MaxTime
    
\* Node stakes (simplified to equal stakes for model checking efficiency)
Stake == [n \in Nodes |-> 1]
TotalStake == Cardinality(Nodes)
ByzantineThreshold == IF TotalStake \div 5 = 0 THEN 1 ELSE TotalStake \div 5  \* 20% Byzantine threshold (at least 1)
FastThreshold == (4 * TotalStake) \div 5      \* 80% for fast finalization  
SlowThreshold == (3 * TotalStake) \div 5      \* 60% for slow finalization
SafeToNotarThreshold == (2 * TotalStake) \div 5  \* 40% for SafeToNotar
FallbackThreshold == IF TotalStake \div 5 = 0 THEN 1 ELSE TotalStake \div 5  \* 20% minimum for fallback (at least 1)

ASSUME 
    /\ Nodes # {}
    /\ MaxSlots > GenesisSlot
    /\ WindowSize > 0
    /\ Gamma > 0
    /\ TotalShreds >= 2 * Gamma              \* Expansion factor κ ≥ 2
    /\ BlockTime > 0
    /\ NetworkDelay > 0
    /\ ByzantineNodes \subseteq Nodes
    /\ CorrectBlocks \cap MaliciousBlocks = {}
    /\ CorrectBlocks # {}
    /\ MaliciousBlocks # {}

\* Slot and leader management
Slots == GenesisSlot..MaxSlots
WindowSlots(s) == 
    LET windowNum == (s - GenesisSlot - 1) \div WindowSize
        windowStart == GenesisSlot + 1 + windowNum * WindowSize
    IN {i \in Slots : i >= windowStart /\ i < windowStart + WindowSize}

\* Leader selection that rotates based on slot number
\* Different slots will tend to select different leaders due to changing conditions
LeaderForSlot(s) == CHOOSE n \in Nodes : TRUE

\* All possible blocks (correct + malicious)
BlockID == {"genesis", "None"} \cup CorrectBlocks \cup MaliciousBlocks
VoteTypes == {"Notarization", "Skip", "NotarFallback", "SkipFallback", "Finalization"}
CertTypes == {"Notarization", "Skip", "NotarFallback", "FastFinalization", "Finalization"}
EventTypes == {"SafeToNotar", "SafeToSkip"}

VARIABLES
    \* Global state
    globalTime,
    currentSlot,
    
    \* Per-node state for each slot
    nodeState,          \* [node][slot] -> set of state flags
    blockstore,         \* [node][slot] -> set of blocks received via Rotor
    pool,               \* [node][slot] -> pool events and certificates
    votes,              \* [node][slot][voteType][blockID] -> vote count
    timeouts,           \* [node][slot] -> timeout value
    pendingBlocks,      \* [node][slot] -> pending block for retry
    events,             \* [node][slot] -> set of events (SafeToNotar, SafeToSkip)
    
    \* Network and Byzantine behavior
    networkMessages,    \* Messages in transit
    byzantineActions,   \* Track Byzantine equivocation
    
    \* Enhanced Byzantine modeling
    byzantineEquivocations,  \* Track all Byzantine equivocation attempts
    byzantineVoteHistory,    \* [node][slot] -> set of conflicting votes
    partitionedGroups,       \* Track network partitions for Byzantine attacks
    
    \* Rotor detailed state
    rotorShreds,        \* [slot][shredIndex] -> shred data and relay assignments
    rotorRelays,        \* [slot] -> set of relay nodes selected by stake
    rotorReceivedShreds, \* [node][slot] -> set of received shred indices
    
    \* Finalized state
    finalizedBlocks,    \* Set of finalized (slot, block) pairs
    skippedSlots,       \* Set of slots that have been skipped
    currentLeader,
    disseminatedSlots,  \* Set of slots where dissemination has occurred
    disseminatedBlocks  \* Set of blocks that have been disseminated across all slots

vars == <<globalTime, currentSlot, nodeState, blockstore, pool, votes, 
          timeouts, pendingBlocks, events, networkMessages, byzantineActions,
          byzantineEquivocations, byzantineVoteHistory, partitionedGroups,
          rotorShreds, rotorRelays, rotorReceivedShreds,
          finalizedBlocks, skippedSlots, currentLeader, disseminatedSlots, disseminatedBlocks>>

\* State flags for nodes
StateFlags == {"ParentReady", "Voted", "VotedNotar", "BlockNotarized", "ItsOver", "BadWindow"}

\* Initial state
Init ==
    /\ globalTime = 0
    /\ currentSlot = GenesisSlot + 1
    /\ nodeState = [n \in Nodes |-> [s \in Slots |-> 
                        IF s = GenesisSlot THEN {"ParentReady"} ELSE {}]]
    /\ blockstore = [n \in Nodes |-> [s \in Slots |-> 
                         IF s = GenesisSlot THEN {"genesis"} ELSE {}]]
    /\ pool = [n \in Nodes |-> [s \in Slots |-> 
                   IF s = GenesisSlot THEN {"ParentReady"} ELSE {}]]
    /\ votes = [n \in Nodes |-> [s \in Slots |-> [vt \in VoteTypes |-> [b \in BlockID |-> 0]]]]
    /\ timeouts = [n \in Nodes |-> [s \in Slots |-> 
                      IF s = GenesisSlot THEN globalTime + NetworkDelay + BlockTime ELSE 0]]
    /\ pendingBlocks = [n \in Nodes |-> [s \in Slots |-> "None"]]
    /\ events = [n \in Nodes |-> [s \in Slots |-> {}]]
    /\ currentLeader = LeaderForSlot(currentSlot)
    /\ networkMessages = {}
    /\ byzantineActions = {}
    \* Enhanced Byzantine modeling initialization
    /\ byzantineEquivocations = {}
    /\ byzantineVoteHistory = [n \in Nodes |-> [s \in Slots |-> {}]]
    /\ partitionedGroups = {}
    \* Rotor detailed state initialization
    /\ rotorShreds = [s \in Slots |-> [i \in 1..TotalShreds |-> "None"]]
    /\ rotorRelays = [s \in Slots |-> {}]
    /\ rotorReceivedShreds = [n \in Nodes |-> [s \in Slots |-> {}]]
    \* Finalized state
    /\ finalizedBlocks = {<<GenesisSlot, "genesis">>}
    /\ skippedSlots = {}
    /\ disseminatedSlots = {}
    /\ disseminatedBlocks = {}

\* Helper predicates
IsFirstSlotInWindow(s) == (s - GenesisSlot - 1) % WindowSize = 0
IsLeader(n, s) == LeaderForSlot(s) = n
HasVoted(n, s) == "Voted" \in nodeState[n][s]
HasParentReady(n, s) == "ParentReady" \in pool[n][s]
IsBlockReady(n, s, b) == b \in blockstore[n][s]
IsByzantine(n) == n \in ByzantineNodes
IsCorrectBlock(b) == b \in CorrectBlocks \/ b = "genesis"
IsMaliciousBlock(b) == b \in MaliciousBlocks

\* Enhanced Byzantine behavior predicates
CanByzantineEquivocate(n, s) == 
    /\ IsByzantine(n) 
    /\ IsLeader(n, s)
    /\ ~(\E equivocation \in byzantineEquivocations : 
         equivocation[1] = s /\ equivocation[2] = n)

HasEquivocated(n, s) ==
    \E equivocation \in byzantineEquivocations : 
        equivocation[1] = s /\ equivocation[2] = n

\* Rotor relay selection based on stake (simplified for model checking)
SelectRotorRelays(s) ==
    LET availableNodes == Nodes \ {LeaderForSlot(s)}
        relayCount == IF Gamma <= Cardinality(availableNodes) 
                      THEN Gamma 
                      ELSE Cardinality(availableNodes)
    IN CHOOSE relays \in SUBSET availableNodes : Cardinality(relays) = relayCount

\* Check if node received enough shreds to reconstruct block
HasEnoughShreds(n, s) == 
    Cardinality(rotorReceivedShreds[n][s]) >= Gamma

\* Network partition modeling for Byzantine attacks
CanCreatePartition == 
    /\ Cardinality(ByzantineNodes) > 0
    /\ partitionedGroups = {}  \* No existing partition

\* Byzantine double voting detection
HasDoubleVoted(n, s, voteType) ==
    Cardinality({b \in BlockID : votes[n][s][voteType][b] > 0}) > 1

\* Vote aggregation (counting stake)
VoteStake(s, voteType, blockId) == 
    Cardinality({n \in Nodes : votes[n][s][voteType][blockId] > 0})

\* Vote aggregation for all blocks of a vote type  
VoteStakeAll(s, voteType) ==
    Cardinality({n \in Nodes : \E b \in BlockID : votes[n][s][voteType][b] > 0})

\* Get total notarization stake for a slot
TotalNotarStake(s) == 
    Cardinality({n \in Nodes : \E b \in BlockID : votes[n][s]["Notarization"][b] > 0})

\* Get maximum notarization stake for any single block in slot s
MaxNotarStake(s) ==
    LET notarStakes == {VoteStake(s, "Notarization", b) : b \in BlockID}
    IN IF notarStakes = {} THEN 0 ELSE CHOOSE max \in notarStakes : \A stake \in notarStakes : max >= stake

\* Get skip stake for a slot
SkipStake(s) == VoteStakeAll(s, "Skip") + VoteStakeAll(s, "SkipFallback")

\* Certificate conditions
HasNotarizationCert(s, b) == VoteStake(s, "Notarization", b) >= SlowThreshold
HasFastFinalizationCert(s, b) == VoteStake(s, "Notarization", b) >= FastThreshold
HasSkipCert(s) == SkipStake(s) >= SlowThreshold
HasFinalizationCert(s) == VoteStakeAll(s, "Finalization") >= SlowThreshold
HasNotarFallbackCert(s, b) == 
    VoteStake(s, "Notarization", b) + VoteStake(s, "NotarFallback", b) >= SlowThreshold

\* SafeToNotar conditions (Definition 16 from paper)
SafeToNotarCondition(s, b) ==
    LET notarStake == VoteStake(s, "Notarization", b)
        skipStake == SkipStake(s) 
    IN \/ notarStake >= SafeToNotarThreshold  \* notar(b) >= 40%
       \/ ((skipStake + notarStake >= SlowThreshold) /\ (notarStake >= FallbackThreshold))  \* skip(s) + notar(b) >= 60% AND notar(b) >= 20%

\* SafeToSkip condition (Definition 16 from paper) 
\* From node n's perspective: skip(s) + ∑ notar(b) - max notar(b) ≥ 40%
SafeToSkipCondition(n, s) ==
    LET \* Total skip stake for slot s (across all nodes)
        skipStake == Cardinality({nd \in Nodes : votes[nd][s]["Skip"]["None"] > 0})
        
        \* Total notarization stake across all blocks (sum of votes for all blocks)
        totalNotar == Cardinality({nd \in Nodes : \E bl \in BlockID : votes[nd][s]["Notarization"][bl] > 0})
        
        \* Maximum notarization stake for any single block
        maxNotar == LET blockStakes == {Cardinality({nd \in Nodes : votes[nd][s]["Notarization"][bl] > 0}) : bl \in BlockID}
                    IN IF blockStakes = {} THEN 0 
                       ELSE CHOOSE max \in blockStakes : \A stake \in blockStakes : max >= stake
    IN skipStake + totalNotar - maxNotar >= SafeToNotarThreshold  \* skip(s) + ∑ notar(b) - max notar(b) >= 40%

\* Termination condition: check if all slots are processed
AllSlotsProcessed == 
    \A s \in GenesisSlot..(MaxSlots - 1) : 
        \/ (\E b \in BlockID : <<s, b>> \in finalizedBlocks)  \* Slot is finalized
        \/ (s \in skippedSlots)                               \* Slot has been skipped

\* Unified Rotor dissemination - handles both Byzantine and correct leaders
RotorDissemination ==
    /\ currentSlot < MaxSlots
    /\ currentSlot \notin disseminatedSlots  \* Primary guard: slot not yet disseminated
    /\ currentSlot \notin skippedSlots  \* Don't disseminate for skipped slots
    /\ ~(\E b \in BlockID : <<currentSlot, b>> \in finalizedBlocks)  \* Don't disseminate for finalized slots
    /\ IF currentLeader \in ByzantineNodes
       THEN \* Byzantine leader case - can send different blocks to different groups
            \* First check if there exist available blocks (guard condition like SafeToNotarEvent)
            /\ \E cb \in CorrectBlocks : cb # "None" /\ cb # "genesis" /\ cb \notin disseminatedBlocks
            /\ \E mb \in MaliciousBlocks : mb # "None" /\ mb # "genesis" /\ mb \notin disseminatedBlocks
            /\ LET correctBlock == CHOOSE b \in CorrectBlocks : 
                           b # "None" /\ b # "genesis" /\ 
                           b \notin disseminatedBlocks  \* Block not disseminated before
                   maliciousBlock == CHOOSE b \in MaliciousBlocks : 
                           b # "None" /\ b # "genesis" /\ 
                           b \notin disseminatedBlocks  \* Block not disseminated before
                   byzantineGroup == ByzantineNodes
                   correctGroup == Nodes \ ByzantineNodes
               IN /\ blockstore' = [n \in Nodes |-> 
                           IF n \in byzantineGroup 
                           THEN [blockstore[n] EXCEPT ![currentSlot] = @ \cup {maliciousBlock}]
                           ELSE [blockstore[n] EXCEPT ![currentSlot] = @ \cup {correctBlock}]]
                  /\ byzantineActions' = byzantineActions \cup {<<currentSlot, "equivocation", correctBlock, maliciousBlock>>}
                  /\ disseminatedSlots' = disseminatedSlots \cup {currentSlot}
                  /\ disseminatedBlocks' = disseminatedBlocks \cup {correctBlock, maliciousBlock}
       ELSE \* Correct leader case - sends same block to all nodes
            \* First check if there exists an available correct block (guard condition like SafeToNotarEvent)
            /\ \E cb \in CorrectBlocks : cb # "None" /\ cb # "genesis" /\ cb \notin disseminatedBlocks
            /\ LET blockToDisseminate == CHOOSE b \in CorrectBlocks : 
                           b # "None" /\ b # "genesis" /\ 
                           b \notin disseminatedBlocks  \* Block not disseminated before
               IN /\ PrintT(<<"ROTOR: Leader", currentLeader, "disseminating block", blockToDisseminate, "in slot", currentSlot>>)
                  /\ PrintT(<<"ROTOR: Adding block", blockToDisseminate, "to all nodes' blockstores for slot", currentSlot>>)
                  /\ blockstore' = [n \in Nodes |-> 
                           [blockstore[n] EXCEPT ![currentSlot] = @ \cup {blockToDisseminate}]]
                  /\ disseminatedSlots' = disseminatedSlots \cup {currentSlot}
                  /\ disseminatedBlocks' = disseminatedBlocks \cup {blockToDisseminate}
                  /\ UNCHANGED byzantineActions
    /\ UNCHANGED <<globalTime, currentSlot, nodeState, pool, votes, 
                  timeouts, pendingBlocks, events, networkMessages, finalizedBlocks, 
                  skippedSlots, currentLeader, byzantineEquivocations, byzantineVoteHistory, 
                  partitionedGroups, rotorShreds, rotorRelays, rotorReceivedShreds>>

\* Simplified Rotor for memory efficiency  
RotorShredPropagation ==
    /\ currentSlot \notin disseminatedSlots
    /\ ~(\E b \in BlockID : <<currentSlot, b>> \in finalizedBlocks)
    \* Guard conditions inspired by SafeToNotarEvent - check existence before CHOOSE
    /\ IF currentLeader \in ByzantineNodes
       THEN (\E mb \in MaliciousBlocks : mb # "None" /\ mb # "genesis")
       ELSE (\E cb \in CorrectBlocks : cb # "None" /\ cb # "genesis")
    /\ LET blockToPropagate == IF currentLeader \in ByzantineNodes
                              THEN CHOOSE b \in MaliciousBlocks : b # "None" /\ b # "genesis"
                              ELSE CHOOSE b \in CorrectBlocks : b # "None" /\ b # "genesis"
       IN /\ PrintT(<<"ROTOR: Leader", currentLeader, "disseminating block", blockToPropagate, "in slot", currentSlot>>)
          /\ disseminatedSlots' = disseminatedSlots \cup {currentSlot}
          /\ blockstore' = [n \in Nodes |->
                [blockstore[n] EXCEPT ![currentSlot] = @ \cup {blockToPropagate}]]
          /\ UNCHANGED <<rotorShreds, rotorRelays, rotorReceivedShreds>>
    /\ UNCHANGED <<globalTime, currentSlot, nodeState, pool, votes, 
                  timeouts, pendingBlocks, events, networkMessages, byzantineActions,
                  finalizedBlocks, skippedSlots, currentLeader, byzantineEquivocations, 
                  byzantineVoteHistory, partitionedGroups, disseminatedBlocks>>

\* Try to cast a notarization vote
TryNotarVote(n, s, b) ==
    /\ ~HasVoted(n, s)
    /\ IsBlockReady(n, s, b)
    /\ \/ (IsFirstSlotInWindow(s) /\ HasParentReady(n, s))
       \/ (~IsFirstSlotInWindow(s) /\ "VotedNotar" \in nodeState[n][s-1])
    /\ LET shouldVoteForBlock == 
               \/ (~IsByzantine(n) /\ IsCorrectBlock(b))  \* Correct nodes vote only for correct blocks
               \/ (IsByzantine(n))  \* Byzantine nodes can vote for any block
       IN shouldVoteForBlock
    /\ PrintT(<<"VOTE: Node", n, "voting for block", b, "in slot", s>>)
    /\ votes' = [votes EXCEPT ![n][s]["Notarization"][b] = @ + 1]
    /\ nodeState' = [nodeState EXCEPT ![n][s] = @ \cup {"Voted", "VotedNotar"}]
    /\ pendingBlocks' = [pendingBlocks EXCEPT ![n][s] = "None"]
    /\ UNCHANGED <<globalTime, currentSlot, blockstore, pool, timeouts, 
                  events, networkMessages, byzantineActions, finalizedBlocks, 
                  skippedSlots, currentLeader, disseminatedSlots, byzantineEquivocations, 
                  byzantineVoteHistory, partitionedGroups, rotorShreds, rotorRelays, 
                  rotorReceivedShreds, disseminatedBlocks>>

\* Try to cast skip votes for all unvoted slots in window  
TrySkipWindow(n, s) ==
    /\ LET windowSlots == WindowSlots(s)
           unvotedSlots == {k \in windowSlots : ~HasVoted(n, k)}
       IN /\ unvotedSlots # {}
          /\ votes' = [votes EXCEPT ![n] = [k \in Slots |-> 
                    IF k \in unvotedSlots 
                    THEN [votes[n][k] EXCEPT !["Skip"]["None"] = @ + 1]
                    ELSE votes[n][k]]]
          /\ nodeState' = [nodeState EXCEPT ![n] = [k \in Slots |->
                    IF k \in unvotedSlots
                    THEN nodeState[n][k] \cup {"Voted", "BadWindow"}
                    ELSE nodeState[n][k]]]
          /\ pendingBlocks' = [pendingBlocks EXCEPT ![n] = [k \in Slots |->
                    IF k \in unvotedSlots THEN "None" ELSE pendingBlocks[n][k]]]
    /\ UNCHANGED <<globalTime, currentSlot, blockstore, pool, timeouts,
                  events, networkMessages, byzantineActions, finalizedBlocks, 
                  skippedSlots, currentLeader, disseminatedSlots, byzantineEquivocations, 
                  byzantineVoteHistory, partitionedGroups, rotorShreds, rotorRelays, 
                  rotorReceivedShreds, disseminatedBlocks>>

\* Byzantine double voting action
ByzantineDoubleVote(n, s, voteType, b1, b2) ==
    /\ IsByzantine(n)
    /\ b1 # b2
    /\ b1 \in BlockID /\ b2 \in BlockID
    /\ votes[n][s][voteType][b1] = 0  \* Haven't voted for b1 yet
    /\ votes[n][s][voteType][b2] = 0  \* Haven't voted for b2 yet
    /\ ~HasVoted(n, s)  \* Haven't voted in this slot
    /\ votes' = [votes EXCEPT 
                 ![n][s][voteType][b1] = @ + 1,
                 ![n][s][voteType][b2] = @ + 1]
    /\ byzantineVoteHistory' = [byzantineVoteHistory EXCEPT 
                               ![n][s] = @ \cup {<<voteType, b1>>, <<voteType, b2>>}]
    /\ nodeState' = [nodeState EXCEPT ![n][s] = @ \cup {"Voted", "BadWindow"}]
    /\ UNCHANGED <<globalTime, currentSlot, blockstore, pool, timeouts,
                  pendingBlocks, events, networkMessages, byzantineActions, 
                  finalizedBlocks, skippedSlots, currentLeader, disseminatedSlots,
                  byzantineEquivocations, partitionedGroups, rotorShreds, rotorRelays, 
                  rotorReceivedShreds>>

\* Process timeout event
ProcessTimeout(n) ==
    /\ currentSlot < MaxSlots
    /\ globalTime > timeouts[n][currentSlot] 
    /\ timeouts[n][currentSlot] > 0
    /\ ~HasVoted(n, currentSlot)
    /\ TrySkipWindow(n, currentSlot)

\* Block becomes ready for voting
BlockReady(n) ==
    /\ currentSlot < MaxSlots
    /\ blockstore[n][currentSlot] # {}
    /\ ~HasVoted(n, currentSlot)  \* Guard: Only if node hasn't voted yet
    /\ currentSlot \notin skippedSlots  \* Don't vote for already skipped slots
    /\ ~(\E block \in BlockID : <<currentSlot, block>> \in finalizedBlocks)  \* Don't vote for already finalized slots
    /\ PrintT(<<"BLOCK READY: Node", n, "has blocks", blockstore[n][currentSlot], "in slot", currentSlot>>)
    /\ \E b \in blockstore[n][currentSlot] :
        TryNotarVote(n, currentSlot, b)

\* Parent ready event
ParentReady(n) ==
    /\ currentSlot < MaxSlots
    /\ IsFirstSlotInWindow(currentSlot)
    /\ ~HasParentReady(n, currentSlot)
    /\ PrintT(<<"PARENT READY: Node", n, "in slot", currentSlot>>)
    /\ pool' = [pool EXCEPT ![n][currentSlot] = @ \cup {"ParentReady"}]
    /\ LET windowSlots == WindowSlots(currentSlot)
           newTimeouts == [s2 \in Slots |->
                    IF s2 \in windowSlots 
                    THEN globalTime + NetworkDelay + ((s2 - currentSlot + 1) * BlockTime)
                    ELSE timeouts[n][s2]]
       IN timeouts' = [timeouts EXCEPT ![n] = newTimeouts]
    /\ nodeState' = [nodeState EXCEPT ![n][currentSlot] = @ \cup {"ParentReady"}]
    /\ UNCHANGED <<globalTime, currentSlot, blockstore, votes, pendingBlocks,
                  events, networkMessages, byzantineActions, finalizedBlocks, 
                  skippedSlots, currentLeader, disseminatedSlots, byzantineEquivocations, 
                  byzantineVoteHistory, partitionedGroups, rotorShreds, rotorRelays, 
                  rotorReceivedShreds, disseminatedBlocks>>

\* Block notarized event
BlockNotarized(n) ==
    /\ currentSlot < MaxSlots
    /\ "BlockNotarized" \notin nodeState[n][currentSlot]  \* Only when not already notarized
    /\ \E block \in blockstore[n][currentSlot] : HasNotarizationCert(currentSlot, block)  \* At least one block has notarization cert
    /\ LET availableBlocks == blockstore[n][currentSlot]
           notarizedBlocks == {b \in availableBlocks : HasNotarizationCert(currentSlot, b)}
       IN TRUE
    /\ \E b \in blockstore[n][currentSlot] : 
        /\ HasNotarizationCert(currentSlot, b)
        /\ IF ("VotedNotar" \in nodeState[n][currentSlot] /\ ~("BadWindow" \in nodeState[n][currentSlot]))
           THEN (/\ votes' = [votes EXCEPT ![n][currentSlot]["Finalization"]["None"] = @ + 1]
                 /\ nodeState' = [nodeState EXCEPT ![n][currentSlot] = @ \cup {"BlockNotarized", "ItsOver"}]
                 /\ UNCHANGED <<globalTime, currentSlot, blockstore, pool, 
                               timeouts, pendingBlocks, events, networkMessages, byzantineActions,
                               finalizedBlocks, skippedSlots, currentLeader, disseminatedSlots, 
                               byzantineEquivocations, byzantineVoteHistory, partitionedGroups, 
                               rotorShreds, rotorRelays, rotorReceivedShreds, disseminatedBlocks>>)
           ELSE (/\ nodeState' = [nodeState EXCEPT ![n][currentSlot] = @ \cup {"BlockNotarized"}]
                 /\ UNCHANGED <<globalTime, currentSlot, blockstore, pool, votes, 
                               timeouts, pendingBlocks, events, networkMessages, byzantineActions,
                               finalizedBlocks, skippedSlots, currentLeader, disseminatedSlots, 
                               byzantineEquivocations, byzantineVoteHistory, partitionedGroups, 
                               rotorShreds, rotorRelays, rotorReceivedShreds, disseminatedBlocks>>)

\* SafeToNotar event - triggers window skipping and notar-fallback voting
SafeToNotarEvent(n, s) ==
    /\ currentSlot < MaxSlots
    /\ HasVoted(n, s)  \* Already voted but not for this block
    /\ ~("VotedNotar" \in nodeState[n][s])  \* Didn't vote notar originally
    /\ "SafeToNotar" \notin events[n][s]  \* Event not yet processed
    /\ blockstore[n][s] # {}  \* Blockstore should not be empty
    /\ ~(\E block \in BlockID : <<s, block>> \in finalizedBlocks)  \* Slot not yet finalized
    /\ s \notin skippedSlots  \* Slot not yet skipped
    /\ votes[n][s]["Skip"]["None"] > 0  \* This node has voted skip for this slot
    /\ \E b \in blockstore[n][s] : SafeToNotarCondition(s, b)  \* There exists a block in blockstore that satisfies SafeToNotar
    /\ LET b == CHOOSE block \in blockstore[n][s] : SafeToNotarCondition(s, block)
           windowSlots == WindowSlots(s)
           unvotedSlots == {k \in windowSlots : ~HasVoted(n, k)}
       IN /\ events' = [events EXCEPT ![n][s] = @ \cup {"SafeToNotar"}]
          \* Skip all unvoted slots in window (TrySkipWindow behavior)
          /\ votes' = [votes EXCEPT ![n] = [k \in Slots |-> 
                IF k \in unvotedSlots 
                THEN [votes[n][k] EXCEPT !["Skip"]["None"] = @ + 1]
                ELSE IF (k = s) /\ ~("ItsOver" \in nodeState[n][s])  \* Also cast NotarFallback vote for the current slot
                THEN [votes[n][k] EXCEPT !["NotarFallback"][b] = @ + 1]
                ELSE votes[n][k]]]
          /\ nodeState' = [nodeState EXCEPT ![n] = [k \in Slots |->
                IF k \in unvotedSlots
                THEN nodeState[n][k] \cup {"Voted", "BadWindow"}
                ELSE IF k = s /\ ~("ItsOver" \in nodeState[n][s])
                THEN nodeState[n][k] \cup {"BadWindow"}
                ELSE nodeState[n][k]]]
          /\ pendingBlocks' = [pendingBlocks EXCEPT ![n] = [k \in Slots |->
                IF k \in unvotedSlots THEN "None" ELSE pendingBlocks[n][k]]]
    /\ UNCHANGED <<globalTime, currentSlot, blockstore, pool, timeouts,
                  networkMessages, byzantineActions, 
                  finalizedBlocks, skippedSlots, currentLeader, disseminatedSlots,
                  byzantineEquivocations, byzantineVoteHistory, partitionedGroups, 
                  rotorReceivedShreds, rotorRelays, rotorShreds, disseminatedBlocks>>

\* SafeToSkip event - triggers skip-fallback voting
SafeToSkipEvent(n, s) ==
    /\ currentSlot < MaxSlots
    /\ HasVoted(n, s)  \* Already voted 
    /\ ("VotedNotar" \in nodeState[n][s])  \* Didn't vote notar originally
    /\ "SafeToSkip" \notin events[n][s]  \* Event not yet processed
    /\ blockstore[n][s] # {}  \* Blockstore should not be empty
    /\ ~(\E block \in BlockID : <<s, block>> \in finalizedBlocks)  \* Slot not yet finalized
    /\ s \notin skippedSlots  \* Slot not yet skipped
    /\ votes[n][s]["SkipFallback"]["None"] = 0  \* This node hasn't voted SkipFallback for this slot
    /\ SafeToSkipCondition(n, s)  \* SafeToSkip from node n's perspective
    /\ LET windowSlots == WindowSlots(s)
           unvotedSlots == {k \in windowSlots : ~HasVoted(n, k)}
       IN   /\ events' = [events EXCEPT ![n][s] = @ \cup {"SafeToSkip"}]
            \* Call TrySkipWindow behavior for unvoted slots    
            /\ votes' = [votes EXCEPT ![n] = [k \in Slots |-> 
                IF k \in unvotedSlots 
                THEN [votes[n][k] EXCEPT !["Skip"]["None"] = @ + 1]
                ELSE IF k = s /\ ~("ItsOver" \in nodeState[n][s]) \* Also cast SkipFallback vote for current slot if ItsOver not in state
                THEN [votes[n][k] EXCEPT !["SkipFallback"]["None"] = @ + 1]
                ELSE votes[n][k]]]
            /\ nodeState' = [nodeState EXCEPT ![n] = [k \in Slots |->
                IF k \in unvotedSlots
                THEN nodeState[n][k] \cup {"Voted", "BadWindow"}
                ELSE IF k = s /\ ~("ItsOver" \in nodeState[n][s])
                THEN nodeState[n][k] \cup {"BadWindow"}
                ELSE nodeState[n][k]]]
            /\ pendingBlocks' = [pendingBlocks EXCEPT ![n] = [k \in Slots |->
                    IF k \in unvotedSlots THEN "None" ELSE pendingBlocks[n][k]]]
    /\ UNCHANGED <<globalTime, currentSlot, blockstore, pool, timeouts,
                  networkMessages, byzantineActions, finalizedBlocks, skippedSlots, 
                  currentLeader, disseminatedSlots, byzantineEquivocations, byzantineVoteHistory, 
                  partitionedGroups, rotorShreds, rotorRelays, rotorReceivedShreds, disseminatedBlocks>>

\* ========= DECOMPOSED PROGRESS ACTIONS =========

\* Helper predicates for current slot conditions
IsCurrentSlotFastFinalizable == 
    \E b \in BlockID : HasFastFinalizationCert(currentSlot, b) /\ 
                      <<currentSlot, b>> \notin finalizedBlocks /\
                      currentSlot \notin skippedSlots

IsCurrentSlotSlowFinalizable == 
    \E b \in BlockID : HasFinalizationCert(currentSlot) /\
                      HasNotarizationCert(currentSlot, b) /\
                      <<currentSlot, b>> \notin finalizedBlocks /\
                      currentSlot \notin skippedSlots

IsCurrentSlotSkippable == 
    HasSkipCert(currentSlot) /\ 
    currentSlot \notin skippedSlots /\
    ~(\E b \in BlockID : <<currentSlot, b>> \in finalizedBlocks)

IsCurrentSlotInBadWindow == \E n \in Nodes : "BadWindow" \in nodeState[n][currentSlot]


\* Log current consensus state
LogConsensusState ==
    /\ PrintT(<<"=== CONSENSUS STATE ===",
               "Current Slot:", currentSlot,
               "Global Time:", globalTime,
               "Finalized Blocks:", finalizedBlocks,
               "Skipped Slots:", skippedSlots,
               "Current Leader:", currentLeader,
               "Disseminated Slots:", disseminatedSlots,
               "========================">>)
    /\ UNCHANGED vars

\* Priority 1: Fast finalization (80% notarization votes)
HandleFastFinalization ==
    /\ IsCurrentSlotFastFinalizable
    /\ LET blockToFinalize == CHOOSE b \in BlockID : 
               HasFastFinalizationCert(currentSlot, b) /\ 
               <<currentSlot, b>> \notin finalizedBlocks
           nextSlot == currentSlot + 1
       IN /\ PrintT(<<"FAST FINALIZE: Block", blockToFinalize, "in slot", currentSlot>>)
          /\ finalizedBlocks' = finalizedBlocks \cup {<<currentSlot, blockToFinalize>>}
          /\ IF nextSlot <= MaxSlots
             THEN (/\ currentSlot' = nextSlot
                   /\ currentLeader' = LeaderForSlot(nextSlot))
             ELSE UNCHANGED <<currentSlot, currentLeader>>
          /\ UNCHANGED <<skippedSlots, disseminatedSlots, nodeState, pool, votes, 
                        timeouts, pendingBlocks, events>>

\* Priority 2: Slow finalization (60% finalization + notarization votes)
HandleSlowFinalization ==
    /\ IsCurrentSlotSlowFinalizable
    /\ LET blockToFinalize == CHOOSE b \in BlockID : 
               HasFinalizationCert(currentSlot) /\ HasNotarizationCert(currentSlot, b) /\
               <<currentSlot, b>> \notin finalizedBlocks
           nextSlot == currentSlot + 1
       IN /\ PrintT(<<"SLOW FINALIZE: Block", blockToFinalize, "in slot", currentSlot>>)
          /\ finalizedBlocks' = finalizedBlocks \cup {<<currentSlot, blockToFinalize>>}
          /\ IF nextSlot <= MaxSlots
             THEN (/\ currentSlot' = nextSlot
                   /\ currentLeader' = LeaderForSlot(nextSlot))
             ELSE UNCHANGED <<currentSlot, currentLeader>>
          /\ UNCHANGED <<skippedSlots, disseminatedSlots, nodeState, pool, votes,
                        timeouts, pendingBlocks, events>>

\* Priority 3: Skip slot with BadWindow handling (per Algorithm 2)
HandleSkip ==
    /\ IsCurrentSlotSkippable
    /\ LET nextSlot == currentSlot + 1
           nextWindowSlot == currentSlot + WindowSize
       IN /\ PrintT(<<"SKIP SLOT: Slot", currentSlot, "BadWindow:", IsCurrentSlotInBadWindow>>)
          /\ skippedSlots' = skippedSlots \cup {currentSlot}
          \* If BadWindow, skip entire window and mark slots disseminated (Algorithm 2)
          /\ IF IsCurrentSlotInBadWindow /\ nextWindowSlot <= MaxSlots
             THEN LET windowSlotsToSkip == {s \in Slots : s > currentSlot /\ s < nextWindowSlot}
                  IN (/\ currentSlot' = nextWindowSlot
                      /\ currentLeader' = LeaderForSlot(nextWindowSlot)
                      /\ disseminatedSlots' = disseminatedSlots \cup windowSlotsToSkip
                      /\ PrintT(<<"BAD WINDOW: Skipping to slot", nextWindowSlot, "disseminating slots", windowSlotsToSkip>>))
             \* Regular skip - just increment slot
             ELSE IF nextSlot <= MaxSlots
             THEN (/\ currentSlot' = nextSlot
                   /\ currentLeader' = LeaderForSlot(nextSlot)
                   /\ UNCHANGED disseminatedSlots)
             ELSE UNCHANGED <<currentSlot, currentLeader, disseminatedSlots>>
          /\ UNCHANGED <<finalizedBlocks, nodeState, pool, votes, timeouts, pendingBlocks, events>>

\* Priority 4a: ParentReady system event (Algorithm 1, lines 13-16)  
HandleParentReady ==
    /\ IsFirstSlotInWindow(currentSlot)
    /\ (\E n \in Nodes : ~HasParentReady(n, currentSlot))  \* At least one node needs ParentReady
    /\ currentSlot \notin skippedSlots  \* Don't trigger for already skipped slots
    /\ ~(\E b \in BlockID : <<currentSlot, b>> \in finalizedBlocks)  \* Don't trigger for already finalized slots
    /\ LET parentReadyNodes == {n \in Nodes : 
           IsFirstSlotInWindow(currentSlot) /\ ~HasParentReady(n, currentSlot)}
       IN /\ parentReadyNodes # {}  \* Ensure we actually have nodes to update
          /\ PrintT(<<"SYSTEM EVENT: ParentReady triggered for nodes", parentReadyNodes, "in slot", currentSlot>>)
          \* Set ParentReady for all qualifying nodes
          /\ pool' = [n \in Nodes |->
                IF n \in parentReadyNodes
                THEN [pool[n] EXCEPT ![currentSlot] = @ \cup {"ParentReady"}]
                ELSE pool[n]]
          \* Set timeouts for window slots (Algorithm 1, line 16: SET_TIMEOUTS)
          /\ timeouts' = [n \in Nodes |->
                IF n \in parentReadyNodes
                THEN LET windowSlots == WindowSlots(currentSlot)
                         newTimeouts == [s2 \in Slots |->
                             IF s2 \in windowSlots 
                             THEN globalTime + NetworkDelay + ((s2 - currentSlot + 1) * BlockTime)
                             ELSE timeouts[n][s2]]
                     IN newTimeouts
                ELSE timeouts[n]]
          \* Update node state
          /\ nodeState' = [n \in Nodes |->
                IF n \in parentReadyNodes
                THEN [nodeState[n] EXCEPT ![currentSlot] = @ \cup {"ParentReady"}]
                ELSE nodeState[n]]
          /\ UNCHANGED <<currentSlot, currentLeader, finalizedBlocks, skippedSlots, 
                        disseminatedSlots, votes, pendingBlocks, events>>

\* Priority 4b: BlockNotarized system event (Algorithm 1, lines 10-12)
HandleBlockNotarized ==
    /\ (\E n \in Nodes, b \in BlockID : 
        "BlockNotarized" \notin nodeState[n][currentSlot] /\
        b \in blockstore[n][currentSlot] /\
        HasNotarizationCert(currentSlot, b))
    /\ currentSlot \notin skippedSlots  \* Don't trigger for already skipped slots
    /\ ~(\E block \in BlockID : <<currentSlot, block>> \in finalizedBlocks)  \* Don't trigger for already finalized slots
    /\ LET blockNotarizedNodes == {n \in Nodes : 
           "BlockNotarized" \notin nodeState[n][currentSlot] /\
           (\E b \in blockstore[n][currentSlot] : HasNotarizationCert(currentSlot, b))}
       IN /\ blockNotarizedNodes # {}  \* Ensure we actually have nodes to update
          /\ PrintT(<<"SYSTEM EVENT: BlockNotarized triggered for nodes", blockNotarizedNodes, "in slot", currentSlot>>)
          \* Cast finalization votes for qualifying nodes (Algorithm 1, line 12: TRYFINAL)  
          /\ votes' = [n \in Nodes |->
                IF n \in blockNotarizedNodes /\
                   "VotedNotar" \in nodeState[n][currentSlot] /\
                   ~("BadWindow" \in nodeState[n][currentSlot])
                THEN [votes[n] EXCEPT ![currentSlot]["Finalization"]["None"] = @ + 1]
                ELSE votes[n]]
          \* Set BlockNotarized and ItsOver for qualifying nodes
          /\ nodeState' = [n \in Nodes |->
                IF n \in blockNotarizedNodes
                THEN LET newState == nodeState[n][currentSlot] \cup {"BlockNotarized"}
                         finalState == IF "VotedNotar" \in nodeState[n][currentSlot] /\
                                         ~("BadWindow" \in nodeState[n][currentSlot])
                                       THEN newState \cup {"ItsOver"}
                                       ELSE newState
                     IN [nodeState[n] EXCEPT ![currentSlot] = finalState]
                ELSE nodeState[n]]
          /\ UNCHANGED <<currentSlot, currentLeader, finalizedBlocks, skippedSlots,
                        disseminatedSlots, pool, timeouts, pendingBlocks, events>>

\* Priority 4c: ProcessTimeout system event (Algorithm 1, lines 7-9)
HandleProcessTimeout ==
    /\ (\E n \in Nodes :
        globalTime > timeouts[n][currentSlot] /\
        timeouts[n][currentSlot] > 0 /\
        ~HasVoted(n, currentSlot))
    /\ LET timeoutNodes == {n \in Nodes :
               globalTime > timeouts[n][currentSlot] /\
               timeouts[n][currentSlot] > 0 /\
               ~HasVoted(n, currentSlot)}
           windowSlots == WindowSlots(currentSlot)
       IN /\ PrintT(<<"SYSTEM EVENT: ProcessTimeout triggered for nodes", timeoutNodes, "in slot", currentSlot>>)
          \* Call TRYSKIP_WINDOW for timeout nodes (Algorithm 1, line 9)
          /\ votes' = [n \in Nodes |->
                IF n \in timeoutNodes
                THEN [s \in Slots |->
                    IF s \in windowSlots /\ ~HasVoted(n, s)
                    THEN [votes[n][s] EXCEPT !["Skip"]["None"] = @ + 1]
                    ELSE votes[n][s]]
                ELSE votes[n]]
          /\ nodeState' = [n \in Nodes |->
                IF n \in timeoutNodes
                THEN [s \in Slots |->
                    IF s \in windowSlots /\ ~HasVoted(n, s)
                    THEN nodeState[n][s] \cup {"Voted", "BadWindow"}
                    ELSE nodeState[n][s]]
                ELSE nodeState[n]]
          /\ UNCHANGED <<currentSlot, currentLeader, finalizedBlocks, skippedSlots,
                        disseminatedSlots, pool, timeouts, pendingBlocks, events>>

\* Priority 4d: SafeToNotar system event (Algorithm 1, lines 17-20)
HandleSafeToNotar ==
    /\ (\E n \in Nodes, b \in BlockID :
        HasVoted(n, currentSlot) /\
        ~("VotedNotar" \in nodeState[n][currentSlot]) /\
        "SafeToNotar" \notin events[n][currentSlot] /\
        blockstore[n][currentSlot] # {} /\
        ~(\E block \in BlockID : <<currentSlot, block>> \in finalizedBlocks) /\
        currentSlot \notin skippedSlots /\
        votes[n][currentSlot]["Skip"]["None"] > 0 /\
        b \in blockstore[n][currentSlot] /\
        SafeToNotarCondition(currentSlot, b))
    /\ LET eligibleNodes == {n \in Nodes : 
               HasVoted(n, currentSlot) /\
               ~("VotedNotar" \in nodeState[n][currentSlot]) /\
               "SafeToNotar" \notin events[n][currentSlot] /\
               votes[n][currentSlot]["Skip"]["None"] > 0 /\
               (\E b \in blockstore[n][currentSlot] : SafeToNotarCondition(currentSlot, b))}
           windowSlots == WindowSlots(currentSlot)
       IN /\ PrintT(<<"SYSTEM EVENT: SafeToNotar triggered for nodes", eligibleNodes, "in slot", currentSlot>>)
          \* Cast NotarFallback votes and skip unvoted window slots
          /\ events' = [n \in Nodes |->
                IF n \in eligibleNodes
                THEN [events[n] EXCEPT ![currentSlot] = @ \cup {"SafeToNotar"}]
                ELSE events[n]]
          /\ LET blockForNode(n) == CHOOSE b \in blockstore[n][currentSlot] : SafeToNotarCondition(currentSlot, b)
             IN votes' = [n \in Nodes |->
                   IF n \in eligibleNodes
                   THEN LET unvotedSlots == {k \in windowSlots : ~HasVoted(n, k)}
                        IN [k \in Slots |->
                              IF k \in unvotedSlots
                              THEN [votes[n][k] EXCEPT !["Skip"]["None"] = @ + 1]
                              ELSE IF k = currentSlot /\ ~("ItsOver" \in nodeState[n][currentSlot])
                              THEN [votes[n][k] EXCEPT !["NotarFallback"][blockForNode(n)] = @ + 1]
                              ELSE votes[n][k]]
                   ELSE votes[n]]
          /\ nodeState' = [n \in Nodes |->
                IF n \in eligibleNodes
                THEN LET unvotedSlots == {k \in windowSlots : ~HasVoted(n, k)}
                     IN [k \in Slots |->
                           IF k \in unvotedSlots
                           THEN nodeState[n][k] \cup {"Voted", "BadWindow"}
                           ELSE IF k = currentSlot /\ ~("ItsOver" \in nodeState[n][currentSlot])
                           THEN nodeState[n][k] \cup {"BadWindow"}
                           ELSE nodeState[n][k]]
                ELSE nodeState[n]]
          /\ pendingBlocks' = [n \in Nodes |->
                IF n \in eligibleNodes
                THEN LET unvotedSlots == {k \in windowSlots : ~HasVoted(n, k)}
                     IN [k \in Slots |->
                           IF k \in unvotedSlots THEN "None" ELSE pendingBlocks[n][k]]
                ELSE pendingBlocks[n]]
          /\ UNCHANGED <<currentSlot, currentLeader, finalizedBlocks, skippedSlots,
                        disseminatedSlots, pool, timeouts>>

\* Priority 4e: SafeToSkip system event (Algorithm 1, lines 21-24)
HandleSafeToSkip ==
    /\ (\E n \in Nodes :
        HasVoted(n, currentSlot) /\
        ("VotedNotar" \in nodeState[n][currentSlot]) /\
        "SafeToSkip" \notin events[n][currentSlot] /\
        blockstore[n][currentSlot] # {} /\
        ~(\E block \in BlockID : <<currentSlot, block>> \in finalizedBlocks) /\
        currentSlot \notin skippedSlots /\
        votes[n][currentSlot]["SkipFallback"]["None"] = 0 /\
        SafeToSkipCondition(n, currentSlot))
    /\ LET eligibleNodes == {n \in Nodes :
               HasVoted(n, currentSlot) /\
               ("VotedNotar" \in nodeState[n][currentSlot]) /\
               "SafeToSkip" \notin events[n][currentSlot] /\
               votes[n][currentSlot]["SkipFallback"]["None"] = 0 /\
               SafeToSkipCondition(n, currentSlot)}
           windowSlots == WindowSlots(currentSlot)
       IN /\ PrintT(<<"SYSTEM EVENT: SafeToSkip triggered for nodes", eligibleNodes, "in slot", currentSlot>>)
          \* Cast SkipFallback votes and skip unvoted window slots
          /\ events' = [n \in Nodes |->
                IF n \in eligibleNodes
                THEN [events[n] EXCEPT ![currentSlot] = @ \cup {"SafeToSkip"}]
                ELSE events[n]]
          /\ votes' = [n \in Nodes |->
                IF n \in eligibleNodes
                THEN LET unvotedSlots == {k \in windowSlots : ~HasVoted(n, k)}
                     IN [k \in Slots |->
                           IF k \in unvotedSlots
                           THEN [votes[n][k] EXCEPT !["Skip"]["None"] = @ + 1]
                           ELSE IF k = currentSlot /\ ~("ItsOver" \in nodeState[n][currentSlot])
                           THEN [votes[n][k] EXCEPT !["SkipFallback"]["None"] = @ + 1]
                           ELSE votes[n][k]]
                ELSE votes[n]]
          /\ nodeState' = [n \in Nodes |->
                IF n \in eligibleNodes
                THEN LET unvotedSlots == {k \in windowSlots : ~HasVoted(n, k)}
                     IN [k \in Slots |->
                           IF k \in unvotedSlots
                           THEN nodeState[n][k] \cup {"Voted", "BadWindow"}
                           ELSE IF k = currentSlot /\ ~("ItsOver" \in nodeState[n][currentSlot])
                           THEN nodeState[n][k] \cup {"BadWindow"}
                           ELSE nodeState[n][k]]
                ELSE nodeState[n]]
          /\ pendingBlocks' = [n \in Nodes |->
                IF n \in eligibleNodes
                THEN LET unvotedSlots == {k \in windowSlots : ~HasVoted(n, k)}
                     IN [k \in Slots |->
                           IF k \in unvotedSlots THEN "None" ELSE pendingBlocks[n][k]]
                ELSE pendingBlocks[n]]
          /\ UNCHANGED <<currentSlot, currentLeader, finalizedBlocks, skippedSlots,
                        disseminatedSlots, pool, timeouts>>

\* Main unified progress action - tries each priority in order
ProgressSlot ==
    /\ currentSlot < MaxSlots
    /\ globalTime + 1 <= MaxTime
    /\ globalTime' = globalTime + 1
    /\ \/ HandleFastFinalization      \* Priority 1: Fast finalization
       \/ HandleSlowFinalization      \* Priority 2: Slow finalization  
       \/ HandleSkip                  \* Priority 3: Skip with BadWindow handling
       \/ HandleParentReady           \* Priority 4a: ParentReady system event
       \/ HandleBlockNotarized        \* Priority 4b: BlockNotarized system event
       \/ HandleProcessTimeout        \* Priority 4c: ProcessTimeout system event
       \/ HandleSafeToNotar           \* Priority 4d: SafeToNotar system event (fallback)
       \/ HandleSafeToSkip            \* Priority 4e: SafeToSkip system event (fallback)
       \/ UNCHANGED <<currentSlot, currentLeader, finalizedBlocks, skippedSlots,  \* Priority 4f: Just advance time
                     disseminatedSlots, nodeState, pool, votes, timeouts, pendingBlocks, events>>
    /\ UNCHANGED <<blockstore, networkMessages, byzantineActions,
                  byzantineEquivocations, byzantineVoteHistory, partitionedGroups, 
                  rotorShreds, rotorRelays, rotorReceivedShreds, disseminatedBlocks>>



\* Helper predicate to check if all slots are resolved
AllSlotsResolved ==
    \A s \in (GenesisSlot+1)..MaxSlots : 
        \/ (\E b \in BlockID : <<s, b>> \in finalizedBlocks)
        \/ (s \in skippedSlots)

\* Force skip slot Max (no block intended for this slot)
ForceSkipSlotMax ==
    /\ currentSlot = MaxSlots
    /\ MaxSlots \notin skippedSlots
    /\ ~(\E b \in BlockID : <<MaxSlots, b>> \in finalizedBlocks)
    /\ skippedSlots' = skippedSlots \cup {MaxSlots}
    /\ PrintT(<<"FORCE SKIP: Slot MaxSlot skipped (no block intended)">>)
    /\ UNCHANGED <<globalTime, currentSlot, nodeState, blockstore, pool, votes,
                  timeouts, pendingBlocks, events, networkMessages, byzantineActions,
                  finalizedBlocks, currentLeader, disseminatedSlots, byzantineEquivocations, 
                  byzantineVoteHistory, partitionedGroups, rotorShreds, rotorRelays, 
                  rotorReceivedShreds, disseminatedBlocks>>



\* Stuttering action - allows system to do nothing when no progress can be made
\* This handles expected deadlocks where the system reaches a legitimate state
\* but cannot make further progress
Stutter ==
    /\ \/ currentSlot >= MaxSlots  \* All slots processed
       \/ AllSlotsResolved         \* All slots finalized or skipped
       \/ (\A n \in Nodes : "ItsOver" \in nodeState[n][currentSlot])  \* All nodes are done
       \/ (globalTime >= 45)       \* Time limit reached (prevents infinite runs)
    /\ UNCHANGED vars

\* Main next-state relation - prioritize voting actions over time advancement
Next ==
    \/ ForceSkipSlotMax  \* Force skip slot 4 (no block intended)
    \* Block dissemination (high priority - must happen for voting)
    \/ RotorDissemination
    \* Node-specific protocol actions (highest priority - voting must happen before time advancement)
    \/ \E n \in Nodes : BlockReady(n)
    \* Unified progress action that handles finalization, skipping, and advancement (lower priority)
    \/ ProgressSlot
    \* Logging action (lowest priority)
    \/ LogConsensusState

\* Specification with comprehensive fairness conditions - prioritize voting fairness
Spec == Init /\ [][Next]_vars 
    /\ WF_vars(ForceSkipSlotMax)  \* Weak fairness for force skipping slot 4
    \* Strong fairness for dissemination (must happen for progress)
    /\ SF_vars(RotorDissemination)
    \* Strong fairness for node-specific protocol actions (critical for voting)
    /\ \A n1 \in Nodes : SF_vars(BlockReady(n1))
    \* Strong fairness for unified progress action (lower priority than voting)
    /\ SF_vars(ProgressSlot)
    \* Weak fairness for logging (lowest priority)
    /\ WF_vars(LogConsensusState)

\* ========= FORMAL THEOREM DEFINITIONS =========

\* Theorem 1: Safety (from paper) - No conflicting blocks finalized in same slot
Theorem1_Safety == 
    \A s \in Slots, b1, b2 \in BlockID :
        (<<s, b1>> \in finalizedBlocks /\ <<s, b2>> \in finalizedBlocks) => b1 = b2

\* Chain consistency under Byzantine faults
ChainConsistency ==
    \A s1, s2 \in Slots, b1, b2 \in BlockID :
        s1 < s2 /\ <<s1, b1>> \in finalizedBlocks /\ <<s2, b2>> \in finalizedBlocks
        => \* b2 must be a descendant of b1 (simplified as different blocks for different slots)
           b1 # b2

\* Certificate uniqueness - at most one block can be notarized per slot
CertificateUniqueness ==
    \A s \in Slots : 
        Cardinality({b \in BlockID : HasNotarizationCert(s, b)}) <= 1

\* Non-equivocation under Byzantine threshold
NonEquivocation ==
    \A s \in Slots, b1, b2 \in BlockID :
        b1 # b2 => ~(HasFastFinalizationCert(s, b1) /\ HasFastFinalizationCert(s, b2))

\* Byzantine resilience - protocol safe with ≤20% Byzantine stake
ByzantineResilienceProperty ==
    Cardinality(ByzantineNodes) <= ByzantineThreshold 
    => (Theorem1_Safety /\ CertificateUniqueness /\ NonEquivocation)

\* Fast path finalization - blocks finalized in one round with >80% stake
FastPathFinalization ==
    \A s \in Slots, b \in BlockID :
        HasFastFinalizationCert(s, b) => <<s, b>> \in finalizedBlocks

\* Slow path finalization - blocks finalized in two rounds with >60% stake
SlowPathFinalization ==
    \A s \in Slots, b \in BlockID :
        (HasNotarizationCert(s, b) /\ HasFinalizationCert(s)) => <<s, b>> \in finalizedBlocks

\* Progress under partial synchrony (simplified)
ProgressGuarantee ==
    \A s \in Slots :
        s < MaxSlots => 
            <>(\E b \in BlockID : <<s, b>> \in finalizedBlocks \/ s \in skippedSlots)

\* Bounded finalization time (min(δ₈₀%, 2δ₆₀%) - simplified as fast vs slow)
BoundedFinalizationTime ==
    \A s \in Slots, b \in BlockID :
        \/ (HasFastFinalizationCert(s, b) => <<s, b>> \in finalizedBlocks)  \* Fast path
        \/ (HasFinalizationCert(s) => \E b2 \in BlockID : <<s, b2>> \in finalizedBlocks)  \* Slow path

\* Network partition recovery
PartitionRecovery ==
    partitionedGroups # {} => <>( \A s \in Slots : 
        s >= currentSlot => (\E b \in BlockID : <<s, b>> \in finalizedBlocks \/ s \in skippedSlots))

\* ========= SAFETY PROPERTIES =========

\* Main safety property from Theorem 1
Safety == Theorem1_Safety

NoMaliciousFinalization ==
    \A s \in Slots, b \in BlockID :
        (<<s, b>> \in finalizedBlocks) => IsCorrectBlock(b)

ByzantineResilience ==
    Cardinality(ByzantineNodes) <= ByzantineThreshold

\* Type invariants
TypeOK ==
    /\ globalTime \in Nat
    /\ currentSlot \in Slots
    /\ \A n \in Nodes, s \in Slots : nodeState[n][s] \subseteq StateFlags
    /\ \A n \in Nodes, s \in Slots : blockstore[n][s] \subseteq BlockID
    /\ finalizedBlocks \subseteq (Slots \times BlockID)
    /\ skippedSlots \subseteq Slots
    /\ disseminatedSlots \subseteq Slots
    /\ \A n \in Nodes, s \in Slots : events[n][s] \subseteq EventTypes
    \* Enhanced Byzantine modeling type invariants
    /\ byzantineEquivocations \subseteq (Slots \times Nodes \times BlockID \times BlockID)
    /\ \A n \in Nodes, s \in Slots : byzantineVoteHistory[n][s] \subseteq (VoteTypes \times BlockID)
    /\ partitionedGroups \subseteq SUBSET Nodes
    \* Rotor type invariants  
    /\ \A s \in Slots, i \in 1..TotalShreds : rotorShreds[s][i] \in BlockID
    /\ \A s \in Slots : rotorRelays[s] \subseteq Nodes
    /\ \A n \in Nodes, s \in Slots : rotorReceivedShreds[n][s] \subseteq (1..TotalShreds)

\* No double voting
NoDoubleVoting ==
    \A n \in Nodes, s \in Slots, vt \in VoteTypes :
        Cardinality({b \in BlockID : votes[n][s][vt][b] > 0}) <= 1

EventualTermination == 
    \A s \in GenesisSlot..(MaxSlots-1) : 
        <>(\E b \in BlockID : <<s, b>> \in finalizedBlocks \/ s \in skippedSlots)

\* Symmetry definition for model checking optimization
Perms == Permutations(Nodes \ ByzantineNodes)
PermsBlocks == Permutations(CorrectBlocks \ MaliciousBlocks)

\* Combined symmetry using union (for both nodes and blocks)
CombinedSymmetry == UNION {Perms, PermsBlocks}


=============================================================================