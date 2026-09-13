# Grokking circuit-mechanism temporal-alignment design

## Status

Architectural design for integrating PR #900's circuit-routing receipts into the existing DASHI Grokking programme without promoting the new beta diagnostic directly into `GrokkingMechanismWitness`.

The design keeps three layers distinct:

1. first-passage / accuracy receipts already owned by `DASHI.Learning`;
2. circuit-intervention / conflict-requirement / beta receipts introduced by PR #900;
3. a new temporal-alignment bridge that compares them under matched experimental identity and anti-leakage constraints.

The first target is the existing modular-multiplication family because `Mod97WeightDecayReceipt` already carries seeds, weight-decay coordinates, a fixed 15000-epoch horizon, and horizon-aware `test95` first passage. Actual checkpoint/model-state availability remains a separate acquisition obligation; this design does not infer historical circuit states from final receipts.

## Roadmap placement

`DASHI.Programmes.GrokkingExact` places grokking in the Stage-6/7 calibration and experiment layer. The existing roadmap already identifies `GrokkingMechanismWitness` as an unpaid bridge from measured first passage to the formal crossing-plus-contraction decomposition.

Therefore PR #900 is not a new foundational Grokking theory lane. It becomes a new mechanistic receipt family inside the calibration/experiment layer:

```text
existing first-passage receipt      new circuit-routing receipt
             |                                 |
             v                                 v
       GrokkingObservation      GrokkingCircuitMechanismObservation
             \                                 /
              \                               /
               ------ temporal alignment ------
                           |
                           v
              replicated mechanism candidate
                           |
                           v
             GrokkingMechanismWitness debt
```

A beta transition is evidence about a candidate structural event. It is not, by itself, a crossing proof, contraction proof, MDL proof, or universal grokking mechanism.

## Chosen architecture

Use an independent mechanistic receipt lane plus a temporal-alignment bridge.

Rejected alternatives:

- Extending `GrokkingMechanismWitness` immediately: too strong before replication and temporal ordering are established.
- Keeping PR #900 permanently PNF-local: avoids overpromotion but creates a parallel Grokking programme and defeats the existing roadmap's integration discipline.

The new bridge must be thin. It imports the existing receipt owners rather than moving their semantics.

## Cross-pollination

### RSA / NDim: conflict and requirement closure

Reuse the canonical relation from `RSA260FractalPadicHyperfabricBatchGluingExact`:

```text
conflict | gluingRequirement | independent
```

The Grokking circuit graph must retain the RSA ordering:

```text
classify relations
-> close requirements
-> select conflict-free requirement-closed family
-> validate downstream consumer
```

The finite beta observable remains:

```text
beta(G,R) = max |S|
```

for `S` conflict-free and requirement-closed, with maximality paid by a finite receipt rather than assumed from a claimed number.

### Fly NDim: anti-leakage and held-out discipline

Reuse the Fly structure/function ordering conceptually:

```text
generate candidates
-> restrict to fitting/training carrier
-> build compatibility/conflict relation
-> select family without held-out outcome
-> freeze
-> evaluate held-out outcome
```

For Grokking this becomes:

```text
checkpoint state
-> extract circuit candidates
-> run declared interventions
-> classify conflict/requirement relations
-> freeze extraction/classification rule
-> compute beta trajectory
-> compare against test95 timing
```

Critical firewall:

```text
held-out grokking outcome must not choose the circuit threshold,
intervention threshold, extraction rule, or beta transition rule.
```

A threshold selected retrospectively because it lines up with `test95` does not pay temporal evidence.

The Fly distinction between pair holdout and region holdout also transfers structurally: temporal holdout, seed holdout, and task-family holdout are different validation coordinates. Good alignment within checkpoints from one run does not establish cross-seed or cross-task mechanism stability.

### Existing Grokking operator/COL lane: mechanism boundary

`GrokkingOperatorContract` already separates first passage from the formal decomposition

```text
t_grok = t_cross + t_contract.
```

`GrokkingCOLBridge` already states that an observed accuracy transition is not itself a contraction proof. The new circuit bridge preserves that boundary.

A beta transition may eventually be tested as a candidate marker for:

- pre-crossing structural reorganisation;
- crossing/basin entry;
- post-crossing contraction or cleanup;
- or a non-causal correlate.

No one interpretation is promoted by construction.

### Mod97 receipts: first executable target

`Mod97WeightDecayReceipt` provides a natural first experimental family:

- modulus 97;
- fixed train/test split;
- seeds;
- weight-decay coordinate;
- 15000-epoch horizon;
- horizon-aware `test95`.

The circuit producer should key outputs by the same run identity. If historical checkpoints were not retained, that is acquisition debt, not permission to reconstruct beta from final accuracies.

## New formal surfaces

### `GrokkingCircuitMechanismObservation`

A circuit-side observation for one checkpoint/run identity. Minimum fields:

```text
runIdentity
checkpointEpoch
extractionRuleIdentity
interventionRuleIdentity
relationThresholdIdentity
candidateCount
activeSupport
conflictEdgeCount
requirementEdgeCount
beta
betaMaximalityPaid
heldOutOutcomeNotUsedForSelection
```

The observation is empirical bookkeeping. It does not assert that beta is a mechanism.

### `GrokkingCircuitTrajectoryReceipt`

A finite ordered sequence of circuit observations for one matched run. It records whether the extraction/intervention rules are invariant across checkpoints and whether all promoted beta values have paid maximality receipts.

It must fail closed if the rule changes mid-trajectory.

### Temporal classification

Define a temporal relation between the first paid beta-transition epoch and `test95`:

```text
betaBeforeTest95
betaCoincidentWithTest95
betaAfterTest95
betaTransitionUnobserved
firstPassageRightCensored
notComparable
```

`notComparable` covers mismatched run identity, extraction-rule changes, unpaid beta certificates, or insufficient checkpoint cadence.

The coincidence tolerance must be declared before evaluation and should default to the experiment's checkpoint/measurement cadence, not be tuned per run.

### `GrokkingTemporalAlignmentReceipt`

This bridge holds:

```text
GrokkingObservation
GrokkingCircuitTrajectoryReceipt
temporalClassification
sameRunIdentity
sameHeldOutSplit
sameHorizon
selectionFrozenBeforeOutcomeComparison
alignmentPromotionPaid
```

`alignmentPromotionPaid` does not mean `GrokkingMechanismWitness` is paid. It only means the temporal comparison is admissible under the declared protocol.

## Nulls and falsifiers

The circuit hypothesis must have explicit failure modes.

At minimum compare the observed alignment against:

1. **epoch-label permutation/null timing**: preserve the beta values but break their temporal relation to held-out passage;
2. **seed transfer**: freeze the extraction/classification rule learned or declared independently of the held-out seed, then evaluate another seed;
3. **task/config transfer**: reuse the declared rule across at least another modulus/train fraction/width/optimizer before mechanism promotion;
4. **threshold sensitivity**: predeclare a small threshold grid or robustness interval and report whether the alignment disappears under nearby admissible thresholds;
5. **active-support-only baseline**: test whether beta adds temporal information beyond raw active-support change.

As in the Fly null pipeline, a null replicate must rerun any fitting/selection step that belongs inside the null. It may not reuse a fitted observed-family result when the null is supposed to challenge that selection process.

## Promotion ladder

Use a typed promotion ladder rather than a Bool such as `betaExplainsGrokking`:

```text
circuitReceiptAvailable
-> temporalAlignmentAdmissible
-> withinRunAssociationObserved
-> crossSeedStable
-> crossTaskStable
-> precedesOrCoincidesReplicably
-> beatsDeclaredNulls
-> mechanismCandidate
-> separate proof debt for GrokkingMechanismWitness
```

Important negative rules:

```text
beta increase != held-out improvement
beta-before-test95 != causal mechanism
cross-seed stability != cross-task stability
mechanism candidate != contraction theorem
mechanism candidate != MDL theorem
```

## Runtime producer boundary

The eventual runtime producer should consume actual saved checkpoints plus a fixed intervention/extraction protocol and emit machine-readable receipts. It should not be implemented inside Agda.

Expected runtime stages:

```text
load checkpoint
-> identify candidate units/circuits
-> evaluate single and joint interventions on fixed evaluation carrier
-> classify pair relations
-> close requirements
-> enumerate/certify maximal compatible family for tractable finite carrier
-> emit beta and relation receipts
-> repeat over checkpoint sequence
-> temporal-align with existing first-passage receipt
```

For large candidate sets, exact beta may become combinatorially expensive. The first implementation should remain deliberately small enough for exact finite certification. Approximation/lower-bound machinery is a later tranche and must use a different status than exact beta.

## First implementation tranche

The first implementation after this design is approved should be small and formal-first:

1. add a `DASHI.Learning` temporal-alignment owner that imports the existing Grokking observation contract and the PR #900 circuit receipt surface;
2. add RED regression cases for before/coincident/after/unobserved/not-comparable classifications;
3. enforce same-run identity, fixed extraction rule, paid beta certificates, fixed coincidence tolerance, and anti-leakage;
4. add a synthetic alignment witness only; mark it non-empirical;
5. update `Docs/learning/GrokkingOperatorFormalism.md` and `DASHI.Programmes.GrokkingExact` only enough to register the new Stage-6/7 receipt seam;
6. do not yet build the checkpoint runtime or modify `GrokkingMechanismWitness`.

This keeps the next code tranche bounded. The runtime checkpoint producer becomes the following, separately reviewable tranche.

## Verification

For the formal tranche:

- genuine RED regression before production owner changes;
- focused import/static contract;
- Agda kernel check if a focused workflow is available or can be added without invoking the repository-wide manual `Everything` check;
- no claim of GREEN without a fresh execution receipt.

For the later runtime tranche:

- synthetic fixtures with known pair relations and beta;
- leakage test: perturb held-out outcomes and require extraction/classification/beta to remain unchanged;
- identity test: mismatched seed/config/checkpoint metadata must fail closed;
- null test: selection/fitting is recomputed inside each null where required.

## Success criterion

The architecture is successful when DASHI can state, without overpromotion:

```text
For run R, under a predeclared circuit extraction/intervention protocol,
a paid beta transition occurred at epoch t_beta; test95 occurred at t95;
the temporal relation is X; the relation replicated or failed to replicate
under declared seed/task/null tests.
```

Only after replication should the project decide whether that evidence warrants a concrete adapter into `GrokkingMechanismWitness`.
