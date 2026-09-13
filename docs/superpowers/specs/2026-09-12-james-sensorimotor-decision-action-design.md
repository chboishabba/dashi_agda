# James Sensorimotor Decision/Action Formalisation Design

## Purpose

Formalise Thomas W. James, “Sensorimotor Mechanisms of Decisions and Actions” (Journal of Cognitive Neuroscience 38(6), 1089–1100, 2026; DOI `10.1162/JOCN.a.2484`) using existing DASHI learning, memory, decision, neural-producer, and nonfactorability machinery rather than introducing a parallel decision ontology.

The formalisation is source-bounded. It records James’s proposed sensorimotor/active-sensing architecture and its testable distinctions; it does not promote the paper into proof of metaphysical free will, determinism, or a unique neural implementation.

## Existing owners to reuse

- `DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact`: stored/accessed candidate → accumulator → commitment → actuation, with those operators kept distinct.
- `DASHI.Cognition.PNF.DecisionStateBundleExact`: common fine-grained decision-state carrier including attention, history, commitment, actuation, and `MemoryFibre`.
- `DASHI.Cognition.PNF.DecisionActionFibreMultiplicityExact`: same observed action can coexist with different fine internal states.
- `DASHI.Cognition.PNF.MemoryFibre`: remembered event, valuation, salience, confidence, phase, action weight, retrieval policy, bias, and provenance as separate coordinates.
- `DASHI.Cognition.PNF.LearningUpdateMechanismSeparationExact`: extinction, reconsolidation, and erasure remain distinct.
- `DASHI.Biology.NeuralDecisionProducerBridgeExact`: recurrent neural dynamics are candidate producers rather than the definition of decision semantics.
- `DASHI.Core.IntersectionalNonFactorability`: projection equality does not recover erased fine state without a factorisation witness.

## Architecture

Add one primary owner, `DASHI/Cognition/PNF/JamesSensorimotorDecisionActionExact.agda`.

The primitive carrier is a recurrent physical/sensorimotor episode state:

`environment/body -> sensory state -> task-achieving sensorimotor mechanism -> action -> changed environment/body -> next sensory state`.

Learning/history is carried as an existing `MemoryFibre` coordinate and may be updated by experience. Decision, attention, intention, memory-description, and control are treated as observer/phenomenal descriptions of the evolving carrier; they are not inserted as mandatory causal nodes between sensation and action.

A small cybernetic specialization may expose a `reference`, `controlledVariable`, and `errorSignal` carrier, but this is explicitly a candidate specialization rather than the universal definition of cognition.

## Core theorem/boundary surfaces

The owner must make the following distinctions explicit:

- decision phenomenon != decision mechanism;
- decision phenomenon != executed action;
- observed action does not recover a unique sensorimotor/decision trajectory;
- memory description != physical learning update;
- attention label != attention mechanism;
- correlation between a reported decision and action != decision-causes-action theorem;
- sensorimotor producer != one privileged neural circuit;
- James architecture != proof of metaphysical determinism;
- James architecture != proof of metaphysical libertarian free will.

The owner must also include a finite active-sensing witness in which action changes the subsequent sensory state, and an experience-dependent learning witness in which a `MemoryFibre` update changes future action relevance while preserving remembered-event identity.

## Attribution

The published 2026 paper is the final source-paying manifestation:

- Thomas W. James
- “Sensorimotor Mechanisms of Decisions and Actions”
- Journal of Cognitive Neuroscience 38(6), 1089–1100 (2026)
- DOI `10.1162/JOCN.a.2484`

The 2025 preprint may be retained as an earlier manifestation with DOI `10.20944/preprints202507.0979.v1`, but it must not be conflated with the published object.

Citation imports neither proof nor authority. Source attribution records what claim is being formalised; it does not make the formal claim true by citation alone.

## Files

Create:

- `DASHI/Cognition/PNF/JamesSensorimotorDecisionActionExact.agda`
- `DASHI/Cognition/PNF/JamesSensorimotorDecisionActionRegression.agda`
- `scripts/check_james_sensorimotor_decision_action.py`

Modify:

- the narrow cognition/PNF aggregate that already exports the decision-learning owners (prefer `DASHI/Cognition/PNF/PNFIRLearningEverything.agda` if still canonical on the implementation branch).

Do not create a new global planner, a new memory ontology, or a replacement decision-state bundle.

## Testing and certification

Use TDD. The focused static checker must be written/strengthened first and observed RED before the owner exists. It should assert the owner path, aggregate import, DOI coordinates, active-sensing recurrence, learning/memory bridge, and the key WrongType/non-promotion boundaries.

After implementation, rerun the focused static checker. If an Agda executable or exact-head CI receipt is unavailable, report that kernel certification remains open and do not claim Agda success.
