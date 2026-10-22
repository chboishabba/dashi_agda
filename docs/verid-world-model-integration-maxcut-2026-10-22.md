# VERID laboratory/world-model max-cut (2026-10-22)

## Ownership and scope

Google VERID is an empirical laboratory instance, **not** a new semantics or world-model compiler. Canonical owners:

- `DASHI.WorldModel.ActionConditionedWorldModelCore`: action-sequence-conditioned rollout, task/guard energies, selected-action authority and dependency witnesses.
- `DASHI.WorldModel.PredicateNormalWorldModelCore`: observation -> carrier -> PNF -> Phi/Psi -> candidate action -> rollout. Proposals are not truth.
- `DASHI.WorldModel.ActionRolloutPullbackCore`: invalid dependency pulls back a rollout.
- `DASHI.Core.ConsumerFibreRepairExact`: non-descent witness forces separation by any globally sufficient refinement; separating one collision is not global sufficiency.
- `DASHI.Interop.SLRBoundedResearchIterationControlExact`: research iteration transport never creates semantic authority or evidence payment.
- Generic SensibLaw/ITIR world-model compiler: domain-specific evidence as candidate source adapters, not parallel compiler.

## This cut

`VERIDLabWorldModelInstanceExact.agda` makes the missing safety/conformity/evidence obligations explicit *on top of* the existing `SelectedActionSequence`, proves contact inherits live-dependency/closed-authority, reuses canonical proposal and pullback proofs, and demonstrates that the fail-closed fixture cannot promote or dispatch an action.

This is a **formal contract and negative fixture**, not a robot-driver implementation or a claim that physical-lab operations are certified.

## Open empirical contacts

1. Concrete laboratory `State`, `Action`, `Trajectory` values and capacity/material/geometry guards.
2. Simulation refinement or bounded error measured against instrument behaviour.
3. Versioned state snapshot bound to dispatch, with calibration and authorization receipts.
4. Native observation and execution traces through typed SLRW/SLRO/SLRX contracts, respecting the source-vs-observation distinction.
5. End-to-end experiment: safe simulated transfer, unsafe overflow rejection, stale-state rejection and observed post-state reconciliation.
6. Source attribution and result ceilings: VERID demonstration evidence is not general autonomous biological discovery.

## Reproduction

From repository root with the pinned Agda/stdlib environment:

```sh
agda -i . -i /path/to/agda-stdlib/src DASHI/WorldModel/VERIDLabWorldModelInstanceExact.agda
```

Use the repository's Agda 2.9 parallel-check wrapper if available. No kernel receipt is attached to this GitHub-side change; source-writing is not kernel certification.

## Acceptance

- Existing semantic owners unchanged.
- New negative fixture is kernel-checked.
- Positive laboratory fixture only after its concrete safety/refinement/observation receipts exist.
- No generated candidate source, selected route, closed contact gate or simulator output is promoted as physical truth.

## 2026-10-22 proof-search / experiment max-cut

New `DASHI/WorldModel/VERIDExperimentProofSearchBridgeExact.agda` reuses:
- `SequentialConsumerExperimentPlannerExact.SequentialConsumerPlan`;
- `DiscriminatorSynthesisExact.ExperimentBundle` and `DiscriminatingLanguageExtension`;
- `AristotleActiveExperimentalProofSearchLoopExact.initialIteration`;
- `ProofSearchExperimentalParetoCrossPollinationExact` and `ProofExperimentAction369IntegrationExact` authority boundaries;
- the lab contact from the previous cut, with **separate** simulation vs physical safety/conformity/observation payments.

The finite fixture has two Bool worlds with the same coarse observation. The identity experiment bundle distinguishes them, and `extensionJoinSeparates` rules out equality of the joined observations. This is a symbolic regression, not a calibrated laboratory measurement.

**Digital-ESD cross-pollination, without domain conflation:** The `DigitalESDStudyResultPNFProofSearchExact` source's strongest-paid vs first-unpaid implication and study-specific uncertainty ceilings motivate separately recording model-safe, physically observed, and causally identified claims. No educational population effect or statistical estimate is transferred into physical-lab semantics.

**Remaining priorities:** kernel-check the new modules; finite *positive* governed lab instance; concrete state-version/capacity guards; observation-wire receipts; instrument-specific calibration and benchmark against the same experiment planner without typed repair. Do not mark those as complete based on symbolic non-descent or action-gate declarations.

### Suggested check (Agda 2.9 pinned environment)

```sh
AGDA_BIN="$PWD/scripts/agda29_without_k_wrapper.sh" \
  scripts/run_agda29_parallel_check.sh \
  DASHI/WorldModel/VERIDLabWorldModelInstanceExact.agda \
  DASHI/WorldModel/VERIDExperimentProofSearchBridgeExact.agda
```

Kernel receipt: **not yet obtained in this editing environment**.
