# LES research cross-pollination round 3: reusable kernel

## Result

The Animalexic, SeaMeInIt and LES comparisons now expose a stronger commonality than shared provenance or uncertainty vocabulary.  All three are instances of a **reopenable consumer-indexed intervention system**:

```text
observation
  -> fine state / live alternatives
  -> consumer-relative projection
  -> evidence / discrepancy
  -> authority promotion
  -> action or information acquisition
  -> new observation
```

with a side channel

```text
provenance/dependencies -> selective reopening and recomputation.
```

The corresponding generic Agda module is:

- `DASHI.Core.ReopenableConsumerInterventionKernelExact`

and the LES specialization/bridge is:

- `DASHI.Environment.LESResearchCrossPollinationRound3Exact`.

The point of this round is **extraction rather than another application-local framework**.

## 1. Consumer-relative descent

For a fine state `X`, projection `q : X -> Q`, and consumer `c : X -> Y`, the compression is sufficient for that consumer exactly when there exists `cbar : Q -> Y` such that

```text
c = cbar o q.
```

The generic core calls this `ConsumerDescent`.

A `ConsumerDescentDefect` carries two fine states with the same projection but different consumer outputs.  The module proves that such a defect contradicts any claimed descent.

This single theorem pattern covers:

- LES: spatial aggregation/MAUP;
- Animalexic: same behavioural/temporal summary but different semantic consumer;
- SeaMeInIt: same coarse panel/search observation but different downstream manufacturing behaviour;
- ontology lanes: same coarse address but different observer result.

This should therefore be preferred to domain-specific formulations whenever the statement is genuinely only about quotient sufficiency.

## 2. Generic intertwining defect

The round extracts the common commuting square

```text
FineIn --fineMap--> FineOut
  |                    |
projectIn           projectOut
  |                    |
  v                    v
CoarseIn --coarseMap-> CoarseOut
```

into `Intertwiner` and `IntertwiningDefect`.

The LES round-2 `AggregationIntertwiner` and `MAUPDefect` now bridge directly into these generic types, and the generic contradiction theorem re-proves the MAUP incompatibility.

The same object is suitable for:

- multi-fidelity discrepancy;
- causal abstraction defects;
- geometry/coarsening defects;
- aggregation/descent defects;
- fine/coarse simulator mismatch.

Domain modules still choose the metric, tolerance, physical semantics, and admissible projection.  The core only owns the diagram law.

## 3. Active / reopenable / refuted is a common state machine

All three projects need a status richer than active versus false:

```text
active | reopenable | refuted.
```

This is now `AlternativeStatus`, with `LiveAlternativeFamily` carrying provenance, dependencies, pruning policy and residual reopening policy.

The shared law is:

```text
pruned from active computation != refuted.
```

Examples:

- Animalexic: an interpretation or association can be compressed out of the live MHT set without being disproved;
- SeaMeInIt: a beam candidate can be dormant and reopenable rather than dead;
- LES: a plan/scenario/model not on the current frontier can remain scientifically possible.

## 4. Evidence multiplicity must respect provenance roots

Animalexic contributes an especially useful warning to the other projects:

```text
many downstream metrics/receipts from one evidence episode
!=
many independent confirmations.
```

The core therefore separates evidence kind and disposition and adds an `EvidenceIndependenceReceipt` with explicit provenance roots and an independence criterion.

Evidence kinds are intentionally heterogeneous:

```text
proof | measurement | statistical | expert | hypothesis.
```

Evidence dispositions are also explicit:

```text
support | opposition | ignorance | conflict.
```

Dempster-Shafer is one possible implementation of these distinctions, not a mandatory universal calculus.

## 5. Uncertainty is product-typed, not one score

Cross-pollination exposed four recurrently different axes:

```text
epistemic | fidelity | scenario | aleatoric.
```

They now inhabit `TypedUncertainty`.

This prevents statements such as

```text
belief ambiguity == surrogate discrepancy == scenario robustness
```

from becoming accidental implementation assumptions.

A consumer may combine axes, but the combination rule must be declared by that consumer rather than baked into the shared state.

## 6. Authority promotion is separate from evidence accumulation

The shared authority ladder is represented as

```text
computed -> validated -> supported -> authorised -> actionable.
```

The exact labels may be specialized by a domain, but the key boundary is generic:

```text
more evidence does not automatically confer more authority.
```

SeaMeInIt contributes the numerical-certification versus authorization distinction; Animalexic contributes classifier confidence versus semantic authorization; LES contributes model/plan validity versus deployment governance.

`PromotionWitness` therefore records policy, evidence, authority and scope separately.

## 7. Proof-carrying state must also be reopenable

Receipts are stronger when interpreted as proofs of predicates, but a living system additionally needs to know what can invalidate that proof.

`ProofCarryingReopenableState` therefore contains:

- the state;
- a witness of its validity predicate;
- dependency references;
- a typed `ChangeAffects` relation;
- reopening policy;
- provenance.

This is the common abstraction behind:

- LES assimilation followed by selective invalidation;
- Animalexic calibration/evidence changes reopening pose/event/semantic claims;
- SeaMeInIt body/fabric changes reopening ROM/panel/seam claims.

## 8. Bounded completeness is language-relative

SeaMeInIt's behavioural-search analysis and LES planning both need to distinguish search stopping from bounded exhaustion.

`BoundedEnumeration` formalizes:

```text
forall admissible item in the declared bounded language,
item is in the enumerated list.
```

The boundary explicitly refuses:

```text
bounded finite exhaustion => global optimum over an unbounded continuous design space.
```

The same pattern can support:

- SeaMeInIt operator-grammar exhaustion;
- LES bounded intervention-language Pareto completeness;
- Animalexic bounded semantic/hypothesis grammar exhaustion.

## 9. Cross-project feedback map

The useful direction of travel is now:

```text
Animalexic -> LES / SeaMeInIt
  ambiguity as state
  support/opposition/ignorance/conflict
  provenance-root evidence independence
  sparse incremental reopening

SeaMeInIt -> LES / Animalexic
  bounded behavioural exhaustion
  adaptive multi-fidelity discrepancy
  predicate-carrying compliance
  vector-valued defects rather than premature scalarization

LES -> Animalexic / SeaMeInIt
  causal/interventional abstraction
  scenario robustness and deep uncertainty
  assimilation versus dependency invalidation
  hybrid dynamics
  aggregation/non-descent
  governed deployment

DASHI Core -> all
  generic descent/intertwining
  bounded future refinement
  reopenability
  dependency typing
  promotion boundaries.
```

The domains should continue to own their science.  The reusable core owns only the logic of trustworthy abstraction, evidence, reopening, bounded search and authority.

## 10. What this round deliberately does not unify

Shared formal shape does **not** make domain evidence semantically interchangeable.

A curvature defect, animal semantic conflict and nutrient-balance residual are not the same quantity simply because they all inhabit structured residual carriers.

Likewise:

- a causal intervention is not a manufacturing operator;
- a behavioural syllable is not a planning scenario;
- an ecological approval is not an animal-communication promotion;
- a model calibration receipt is not a proof of domain truth.

The project-neutral kernel should therefore remain small and parametric.  Domain adapters must provide the actual predicates, metrics, evidence semantics, admissible actions and authority policies.

## 11. Highest-alpha next reuse

The next generic extractions suggested by this round are:

1. `BoundedActionObservationEquivalence` as the common finite-depth behavioural relation;
2. `AdaptiveFidelityController` coupling discrepancy, uncertainty, cost and materialisation;
3. `AffectedDependencyClosure` with theorem-level selective reopening;
4. `TypedEventTransitionSystem` combining interval/event constraints with hybrid execution;
5. `InformationAction` / value-of-information planning, so all three systems may choose between acting and acquiring evidence.

These are preferable to further project-local receipt duplication because they are already demanded independently by multiple domains.
