# P Concrete-Machine Equivalence Design

## Goal
Finish the remaining model-engineering layer on PR #1040 without changing the Clay-facing lower-bound target.

## Current paid structure
- `ConcreteTapeMachine.rules` is the literal operational rule table used by Cook–Levin.
- Sequential lookup is implemented by `PNotEqualsNPConcreteTapeRuleTableInterpreterExact`.
- Intrinsic row decomposition plus lookup produces a genuine `WellFormedMachineStep` and carries the decreasing head-margin invariant.
- Cook–Levin run-to-SAT and SAT-to-run are already present on the same concrete machine.

## Immediate closure
Introduce a deterministic-key predicate for rule tables: no two listed rules share the same `(sourceState, readSymbol)` key unless they are the same rule. Prove that under this predicate, any relational `MachineStep` matching the current state/symbol uses the same rule returned by first-match executable lookup. Then prove executable and relational step semantics coincide for intrinsically well-formed rows.

Do not weaken `MachineStep`, and do not introduce a second tape-machine carrier.

## Final representation theorem
After executable/relational equivalence, build or identify a standard deterministic single-tape TM carrier and prove polynomial simulations in both directions with clock transport. Stop model engineering after that theorem.

## Non-goals
- No claim that existing width, Q1, Shannon, observer, or residual arguments prove SAT lower bounds.
- No inhabitant of the universal SAT lower-bound theorem is manufactured.
