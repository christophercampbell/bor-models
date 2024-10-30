-------- MODULE producers --------

EXTENDS Integers, Sequences, FiniteSets

\* Definition of a Validator record
Validator == [id: Nat, votingPower: Nat]

CONSTANTS SLOT_COST, PRODUCER_COUNT, BLOCK_HASH, SPAN_ELIGIBLE_VALIDATORS

ASSUME SLOT_COST > 0
ASSUME PRODUCER_COUNT > 0

(* --algorithm SelectNextProducers

variables
    selectedIDs = << >>,
    validatorIndices = << >>,
    seed = 0,
    i = 0,
    j = 0,
    val,
    nSlots = 0,
    shuffledList = << >>;
    
define
    \* Invariant
    Inv_SelectedIDsCount == Len(selectedIDs) <= PRODUCER_COUNT

    ShuffleList(l, s) == l \* figure out later
end define;
    
begin
checkEligible:
    if Len(SPAN_ELIGIBLE_VALIDATORS) <= PRODUCER_COUNT then
        \* If the number of eligible validators is less than or equal to PRODUCER_COUNT, select all
        selectedIDs := << >>;
        i := 1;
extractIds:
        while i <= Len(SPAN_ELIGIBLE_VALIDATORS) do
            selectedIDs := Append(selectedIDs, SPAN_ELIGIBLE_VALIDATORS[i].id);
            i := i + 1;
        end while;
    else
        seed := BLOCK_HASH; 
        validatorIndices := << >>;
        i := 1;
powerToIdx:
        while i <= Len(SPAN_ELIGIBLE_VALIDATORS) do
            val := SPAN_ELIGIBLE_VALIDATORS[i];
            nSlots := val.votingPower \div SLOT_COST;
            j := 1;
accumulate:            
            while j <= nSlots do
                validatorIndices := Append(validatorIndices, val.id);
                j := j + 1;
            end while;
            i := i + 1;
        end while;
shuffle:
        \* Shuffle the list based on seed
        shuffledList := ShuffleList(validatorIndices, seed);
select:
        \* Select the first PRODUCER_COUNT IDs
        selectedIDs := SubSeq(shuffledList, 1, PRODUCER_COUNT);
    end if;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e9b98865" /\ chksum(tla) = "c9567956")
CONSTANT defaultInitValue
VARIABLES selectedIDs, validatorIndices, seed, i, j, val, nSlots, 
          shuffledList, pc

(* define statement *)
Inv_SelectedIDsCount == Len(selectedIDs) <= PRODUCER_COUNT

ShuffleList(l, s) == l


vars == << selectedIDs, validatorIndices, seed, i, j, val, nSlots, 
           shuffledList, pc >>

Init == (* Global variables *)
        /\ selectedIDs = << >>
        /\ validatorIndices = << >>
        /\ seed = 0
        /\ i = 0
        /\ j = 0
        /\ val = defaultInitValue
        /\ nSlots = 0
        /\ shuffledList = << >>
        /\ pc = "checkEligible"

checkEligible == /\ pc = "checkEligible"
                 /\ IF Len(SPAN_ELIGIBLE_VALIDATORS) <= PRODUCER_COUNT
                       THEN /\ selectedIDs' = << >>
                            /\ i' = 1
                            /\ pc' = "extractIds"
                            /\ UNCHANGED << validatorIndices, seed >>
                       ELSE /\ seed' = BLOCK_HASH
                            /\ validatorIndices' = << >>
                            /\ i' = 1
                            /\ pc' = "powerToIdx"
                            /\ UNCHANGED selectedIDs
                 /\ UNCHANGED << j, val, nSlots, shuffledList >>

extractIds == /\ pc = "extractIds"
              /\ IF i <= Len(SPAN_ELIGIBLE_VALIDATORS)
                    THEN /\ selectedIDs' = Append(selectedIDs, SPAN_ELIGIBLE_VALIDATORS[i].id)
                         /\ i' = i + 1
                         /\ pc' = "extractIds"
                    ELSE /\ pc' = "Done"
                         /\ UNCHANGED << selectedIDs, i >>
              /\ UNCHANGED << validatorIndices, seed, j, val, nSlots, 
                              shuffledList >>

powerToIdx == /\ pc = "powerToIdx"
              /\ IF i <= Len(SPAN_ELIGIBLE_VALIDATORS)
                    THEN /\ val' = SPAN_ELIGIBLE_VALIDATORS[i]
                         /\ nSlots' = (val'.votingPower \div SLOT_COST)
                         /\ j' = 1
                         /\ pc' = "accumulate"
                    ELSE /\ pc' = "shuffle"
                         /\ UNCHANGED << j, val, nSlots >>
              /\ UNCHANGED << selectedIDs, validatorIndices, seed, i, 
                              shuffledList >>

accumulate == /\ pc = "accumulate"
              /\ IF j <= nSlots
                    THEN /\ validatorIndices' = Append(validatorIndices, val.id)
                         /\ j' = j + 1
                         /\ pc' = "accumulate"
                         /\ i' = i
                    ELSE /\ i' = i + 1
                         /\ pc' = "powerToIdx"
                         /\ UNCHANGED << validatorIndices, j >>
              /\ UNCHANGED << selectedIDs, seed, val, nSlots, shuffledList >>

shuffle == /\ pc = "shuffle"
           /\ shuffledList' = ShuffleList(validatorIndices, seed)
           /\ pc' = "select"
           /\ UNCHANGED << selectedIDs, validatorIndices, seed, i, j, val, 
                           nSlots >>

select == /\ pc = "select"
          /\ selectedIDs' = SubSeq(shuffledList, 1, PRODUCER_COUNT)
          /\ pc' = "Done"
          /\ UNCHANGED << validatorIndices, seed, i, j, val, nSlots, 
                          shuffledList >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == checkEligible \/ extractIds \/ powerToIdx \/ accumulate \/ shuffle
           \/ select
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=====
