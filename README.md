bor TLA+ model

1. open in TLA+ IDE
1. create a model for `producer` module
1. set values of declared constants in the model view
	- PRODUCER_COUNT <- 3
	- SLOT_COST <- 1
	- BLOCK_HASH <- 42
	- SPAN_ELIGIBLE_VALIDATORS <- `<< [id |-> 1, votingPower |-> 3], [id |-> 2, votingPower |-> 2], [id |-> 3, votingPower |-> 1], [id |-> 4, votingPower |-> 0] >>`
1. select invariants
1. run
