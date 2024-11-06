-------- MODULE producers --------

EXTENDS Naturals, Sequences, FiniteSets, utilities

\* Definition of a Validator record
Validator == [id: Nat, votingPower: Nat]

CONSTANTS SLOT_COST, PRODUCER_COUNT, BLOCK_HASH, VALIDATORS

ASSUME SLOT_COST > 0
ASSUME PRODUCER_COUNT > 0

(* --algorithm SelectNextProducers

variables
    selectedIDs = << >>,
    IDs = << >>,
    seed = 0,
    i = 0,
    j = 0,
    val,
    nSlots = 0,
    shuffledList = << >>;
    
define
    \* Invariant
    Inv_SelectedIDsCount == Len(selectedIDs) <= PRODUCER_COUNT
end define;
    
begin
check:
    if Len(VALIDATORS) <= PRODUCER_COUNT then
        \* If the number of eligible validators is less than or equal to PRODUCER_COUNT, select all
        selectedIDs := << >>;
        i := 1;
extractIds:
        while i <= Len(VALIDATORS) do
            selectedIDs := Append(selectedIDs, VALIDATORS[i].id);
            i := i + 1;
        end while;
    else
        seed := ExtractSeed(BLOCK_HASH); 
        IDs := << >>;
        i := 1;
createSlots:
        while i <= Len(VALIDATORS) do
            val := VALIDATORS[i];
            nSlots := val.votingPower \div SLOT_COST;
            j := 1;
accumulate:            
            while j <= nSlots do
                IDs := Append(IDs, val.id);
                j := j + 1;
            end while;
            i := i + 1;
        end while;
shuffleIds:
        \* Shuffle the list based on seed
        shuffledList := ShuffleList(IDs, seed);
selectIds:
        \* Select the first PRODUCER_COUNT IDs
        selectedIDs := SubSeq(shuffledList, 1, PRODUCER_COUNT);
    end if;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "9b79c139" /\ chksum(tla) = "3b15ca5")
CONSTANT defaultInitValue
VARIABLES selectedIDs, IDs, seed, i, j, val, nSlots, shuffledList, pc

(* define statement *)
Inv_SelectedIDsCount == Len(selectedIDs) <= PRODUCER_COUNT


vars == << selectedIDs, IDs, seed, i, j, val, nSlots, shuffledList, pc >>

Init == (* Global variables *)
        /\ selectedIDs = << >>
        /\ IDs = << >>
        /\ seed = 0
        /\ i = 0
        /\ j = 0
        /\ val = defaultInitValue
        /\ nSlots = 0
        /\ shuffledList = << >>
        /\ pc = "check"

check == /\ pc = "check"
         /\ IF Len(VALIDATORS) <= PRODUCER_COUNT
               THEN /\ selectedIDs' = << >>
                    /\ i' = 1
                    /\ pc' = "extractIds"
                    /\ UNCHANGED << IDs, seed >>
               ELSE /\ seed' = ExtractSeed(BLOCK_HASH)
                    /\ IDs' = << >>
                    /\ i' = 1
                    /\ pc' = "createSlots"
                    /\ UNCHANGED selectedIDs
         /\ UNCHANGED << j, val, nSlots, shuffledList >>

extractIds == /\ pc = "extractIds"
              /\ IF i <= Len(VALIDATORS)
                    THEN /\ selectedIDs' = Append(selectedIDs, VALIDATORS[i].id)
                         /\ i' = i + 1
                         /\ pc' = "extractIds"
                    ELSE /\ pc' = "Done"
                         /\ UNCHANGED << selectedIDs, i >>
              /\ UNCHANGED << IDs, seed, j, val, nSlots, shuffledList >>

createSlots == /\ pc = "createSlots"
               /\ IF i <= Len(VALIDATORS)
                     THEN /\ val' = VALIDATORS[i]
                          /\ nSlots' = (val'.votingPower \div SLOT_COST)
                          /\ j' = 1
                          /\ pc' = "accumulate"
                     ELSE /\ pc' = "shuffleIds"
                          /\ UNCHANGED << j, val, nSlots >>
               /\ UNCHANGED << selectedIDs, IDs, seed, i, shuffledList >>

accumulate == /\ pc = "accumulate"
              /\ IF j <= nSlots
                    THEN /\ IDs' = Append(IDs, val.id)
                         /\ j' = j + 1
                         /\ pc' = "accumulate"
                         /\ i' = i
                    ELSE /\ i' = i + 1
                         /\ pc' = "createSlots"
                         /\ UNCHANGED << IDs, j >>
              /\ UNCHANGED << selectedIDs, seed, val, nSlots, shuffledList >>

shuffleIds == /\ pc = "shuffleIds"
              /\ shuffledList' = ShuffleList(IDs, seed)
              /\ pc' = "selectIds"
              /\ UNCHANGED << selectedIDs, IDs, seed, i, j, val, nSlots >>

selectIds == /\ pc = "selectIds"
             /\ selectedIDs' = SubSeq(shuffledList, 1, PRODUCER_COUNT)
             /\ pc' = "Done"
             /\ UNCHANGED << IDs, seed, i, j, val, nSlots, shuffledList >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == check \/ extractIds \/ createSlots \/ accumulate \/ shuffleIds
           \/ selectIds
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 



=====
