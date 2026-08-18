# Observer refinement, future safety, and provenance dynamics

This tranche is stacked on PR #580. That branch already owns the generic `ObserverRefinementLatticeExact`, `FibrePreservingDynamicsExact`, and `SectionedProjectionProvenanceBridgeExact`, so no parallel quotient/observer core is introduced here.

## New exact consequences

`ProvenanceFibreDynamicsReceiptExact` proves:

```text
same surface + same exact reopening receipt -> same fine carrier
```

and therefore:

```text
nontrivial hidden/fibre-preserving motion -> reopening receipt changes.
```

The C3 orbit quotient supplies the smallest exact witness. The p=11 marked supersingular quotient supplies the arithmetic witness: marked Frobenius swaps `a0 <-> a1`, fixes the coarse j-class, and therefore must change the existing `Fine5Residual` coordinate `r0 <-> r1`.

## Static refinement versus future safety

Master already contains `FutureObservationLanguageQuotientExact` and `MinimalSufficientObservationGovernanceExact`. `ObserverRefinementFutureSafetyExact` adds only the missing bridge:

```text
Separating observer -> FutureLanguageSafeProjection
```

and

```text
safe coarse observer + fine refines coarse
-> fine observer safe for the same declared future language.
```

The converse is not claimed. Existing modules already prove that static relevance mass or current-query sufficiency can coexist with future dynamic defects.

## Factorized refinement: the observer analogue of a transfer intertwiner

The incoming YM transfer work on PR #583 reinforced the source-native rule that a compatibility claim should be carried by an equation rather than a Boolean receipt. `ObserverFactorizedRefinementExact` therefore strengthens the extensional relation

```text
Refines coarse fine
```

to an explicit factorization

```text
coarse = factor o fine.
```

Factorized refinements compose and imply the existing kernel-inclusion `Refines` theorem. A factorized refinement still need not be separating; it is a stronger provenance/naturality witness, not a completeness claim.

`RecoverableObserverRefinementTowerExact` welds this to the existing exact recoverable-quotient composition theorem. Every exact recoverable projection has a separating observer

```text
(coarse surface, residual)
```

from which the public coarse surface factors by `proj1`. Successive exact projection stages compose with a product residual, giving a structured refinement tower rather than an ever-widening flat record.

The product type is only a reconstruction coordinate: it does not claim the residual semantics are statistically, causally, or ontologically independent.

## Strictness propagates through later refinements

`ObserverRefinementCompositionExact` proves refinement transitivity and the useful stronger fact:

```text
coarse < middle
middle <= fine
=> coarse < fine.
```

The original collision witness is reused. If the middle observer already distinguished the two states, any finer observer whose equalities imply middle equality must continue to distinguish them.

The same theorem is proved for observer families, and a factorized later stage is handled by first forgetting to the existing `Refines` law.

This gives refinement ladders a persistent falsifier semantics: once a source-native coordinate has demonstrably split a concrete collision, later observer extensions cannot erase that proof. This does not mean the earlier coarse observer was globally invalid for every consumer or future language; strictness is collision-relative evidence.

## Semantic sampling: a real repair theorem

`ResidualSamplingObserverRepairExact` reuses the existing `SemanticSamplingDynamicSafety` regression. The visible Boolean remains an exact sufficient observer for the current query, yet it is future-unsafe because an admissible action can expose the retained residual.

The source-native repair is not to discard that counterexample or jump to a new carrier. It adds exactly the retained residual bit:

```text
visible
<
(visible, residual).
```

This is both a strict and factorized refinement. The pair separates the concrete residual state and is therefore future-language safe, while the original coarse current-query sufficiency and future-unsafety theorems remain intact.

This yields the useful four-way boundary:

```text
current-query sufficient
!= dynamically/future safe
< source-native strict refinement
<= separating/future-safe observer when proved.
```

## Policy naturality is not dynamic safety

`PolicyObserverFactorizationNaturalityExact` transports a coarse intervention policy along a factorized observer by literal composition:

```text
finePolicy = coarsePolicy o factor.
```

It proves the commuting action equation

```text
finePolicy (fine state) = coarsePolicy (coarse state)
```

and proves policy lifts compose along factorized refinement towers.

If the fine observer is independently dynamically safe, the lifted policy inherits the existing `PolicyRelativeSafety` theorem. Dynamic safety remains a premise; action naturality does not manufacture it.

`PolicyNaturalityDynamicSafetyBoundaryRegression` reuses the existing policy demo adversarially. The complete fine state factors perfectly onto the coarse Boolean observation, the always-hold policy lifts with exact action naturality, and the coarse policy is policy-relative safe. Yet the already-existing reveal action still witnesses an unrestricted dynamic defect on the coarse projection.

So the repo now has the exact separation:

```text
policy/action commuting square
!= policy-relative safety
!= unrestricted dynamic/future safety
!= authority legitimacy.
```

## Biology

`DynamicTopologyObserverRefinementExact` reuses the existing graph-development counterexample. Morphology alone collapses states whose hidden junctions lead to different future morphology. Adding the junction coordinate gives a strict refinement and, on that exact two-Boolean state carrier, a separating observer; the generic bridge therefore makes it future-language safe for the declared morphology language.

## Legacy Hecke ladder

`Ontology.Hecke.ObserverRefinementLadderBridgeExact` shows that the older Hecke refinement program was already an observer-refinement search:

```text
collapse time
<
(collapse time, stay refinement)
```

is strict on the exact width1/width3 collision, while the full current saturated `DefectOrbitSummary` still collides. The next sector-histogram / triad-package / correlation work is therefore correctly interpreted as searching for the next source-native splitter of an explicitly nontrivial residual observation fibre. No separation theorem is claimed for the current postulated correlation fallback.

`ObserverRefinementCompositionExact` means any later successful refinement automatically inherits the old collapse-time/stay strictness witness; those earlier falsifiers do not need to be reproved at every richer stage.

## Indexed observers

`IndexedObserverFamilyBridgeExact` packages any finite selected family from

```text
Index -> State -> Value
```

into the generic observer lattice. `ConsumerTransportObserverFamilyCrossPollinationExact` reuses it for both plural policy/task consumers and physical transport observers (microphones/pixels/etc.). Only the static shape is shared: adding an index shrinks the residual observation fibre, but this grants neither plural dynamic safety nor physical fidelity.

## Incoming-PR cross-checks

The live PR surface supplies independent validation and methodological constraints:

- PR #581 independently instantiates exact residual dynamics on the parent/progenitor ontology: public P8810-like surface + relation-vector residual reopens the fine carrier, and legal/disclosure transitions at fixed public slot move the residual. This is a domain-level corroboration of the generic receipt-motion theorem rather than a new generic core.
- PR #583 replaces Boolean transfer compatibility by exact intertwining equations and composition; this directly motivated `ObserverFactorizedRefinementExact` and the policy/action naturality square.
- PR #570's edit-locality work makes unique correspondence itself proof-relevant evidence. It remains relation-valued and eligibility-indexed, so it is deliberately **not** collapsed into an ordinary observer map here. The reusable methodological lesson is to retain theorem-bearing transport evidence rather than a scalar compatibility label.
- PR #577's leading-mode/residual observer is another exact coarse-plus-residual pattern; once stacked compatibility permits, it is a natural additional consumer of the recoverable observer tower without needing another observer abstraction.

## Further high-alpha reuse targets

The same existing machinery now has direct targets in:

- proof-relevant identity fibres: observer separation must remain distinct from authority to assert world identity;
- parent ontology: the independent PR #581 implementation can later consume the generic factorized/future-safety bridges after stack convergence rather than duplicating them;
- policy-relative intervention routing: the naturality layer now exists, so the next source-specific question is which richer observer is actually safe for the declared policy horizon;
- developmental measurement: transcript/phenotype projections can be refined only when a concrete hidden-state collision demands it;
- observer-conditioned transport: finite microphone/pixel families can use residual-fibre monotonicity while minimal/future-safe physical quotients remain separate theorems;
- modular/palette observers: leading-mode observation plus exact residual naturally fits the recoverable refinement tower once the branches share a base.

The governing rule is falsifier-driven:

> Add a new observer after a concrete collision proves the current projection insufficient, then prove exactly which collision is removed—or prove that the richer observer still collapses.

A second rule now sits beside it:

> When a refinement is source-native, prefer an explicit factor/intertwining equation over an unstructured compatibility flag.

And a third:

> Once a collision has been split, carry that strictness witness upward through later refinements instead of rebuilding it from scratch.
