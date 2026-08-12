# ITIR canonical reopenable-evidence specification

## Purpose

This document is the formal reference for the next SensibLaw / ITIR Python and
PostgreSQL implementation sprint.  The objective is not to force runtime code to
look like Agda.  The objective is to make every important runtime shortcut state
exactly which semantic distinction it is allowed to forget, which witness it
must retain, and what authority it does **not** gain.

The historical Wikidata design order remains the semantic spine:

```text
weak text/graph claim
  -> predicate / role binding
  -> soft type pressure
  -> ontology/corpus mismatch residual
  -> typed provenance-bearing carrier
  -> bounded domain projection
  -> reviewable repair/alignment proposal
  -> proof-bearing promotion only where justified.
```

The current formal consolidation adds the missing dynamic condition:

> A projection is safe for a consumer only when distinctions collapsed by that
> projection cannot alter that consumer's valid future inference/action.

This is stronger than present-time query agreement.

## 1. Canonical provenance-bearing quotient

`DASHI.Core.ProvenanceBearingQuotient` extends the existing
`DASHI.Core.FibreRestrictionCore` rather than defining another fibre system.

For a fine carrier `X` and coarse surface `Y`, a supplied exact quotient has:

```text
project : X -> Y
receipt : X -> D
reopen  : Y -> D -> X
reopen(project x, receipt x) = x.
```

`RelevantProvenanceBearingQuotient` permits application-supplied reconstruction
up to a declared relevant equivalence when exact equality is inappropriate.

There is no constructor by which projection or a residual receipt can establish
semantic falsity or truth.  Projection is not erasure.

### Concrete 369 adapter

`DASHI.Physics.Closure.SSP369PolarResidualQuotient` adapts the existing
residual-bearing depth-wheel polar projection:

```text
full ternary phase cell
  -> projected polar cell
   + zero-branch residual retaining depth phase.
```

The residual result reopens exactly to the full nine-state phase carrier.  This
is the canonical semantic interpretation of the apparent `9 -> 6` step: there
is no direct six-state retraction without a zero-trit policy; lossless
projection is `6 + residual`.

## 2. Dynamic quotient safety and terminalisation

`DASHI.Core.AdmissibleReachability` supplies the canonical reflexive/transitive
closure of the existing `TypedDependencyCore.DependentActionSystem`.  Every
step remains proof-bearing through `AdmissibleAction` preconditions and
postconditions.

`DASHI.Core.DynamicalQuotientSafety` defines consumer-relative safety.  For a
projection `pi` and the same admissible action trace `alpha`, safety requires:

```text
pi x = pi y
and x --alpha--> x'
and y --alpha--> y'
-----------------------------------
pi x' = pi y'.
```

A `TerminalisationDefect` is the constructive counter-witness:

```text
pi x = pi y
but after the same admissible trace
pi x' != pi y'.
```

The theorem

```text
terminalisationDefectContradictsSafety
```

proves that a defect and a `DynamicConsumerSafety` certificate cannot coexist.

`DASHI.Core.ProvenanceQuotientDynamics` makes another crucial distinction
explicit: an exact reopening receipt can exist while the coarse projection is
still dynamically unsafe if a consumer runs without that receipt.

### Regression countermodels

`DASHI.Cognition.PNF.TerminalisationDefectRegression` contains three executable
countermodels rather than Boolean boundary declarations:

1. **hidden depth phase** — two phase-different states have the same current
   visible value; one common refinement action makes their visible futures
   diverge;
2. **extinction/action shadow** — actual `MemoryFibre.extinguishActionDominance`
   retains the remembered `EventPNF` but removes current action weight; a later
   action-sensitive probe exposes the hidden distinction;
3. **residual-bearing projection** — two fine states share a coarse visible bit
   but carry different retained residuals; an admissible residual-exposure step
   makes their futures differ.

The general runtime rule is therefore:

```text
currently negligible != semantically absent
outside active beam   != semantically refuted
same current output   != dynamically equivalent.
```

### Reference

Patrick Cousot and Radhia Cousot,
“Abstract interpretation: a unified lattice model for static analysis of
programs by construction or approximation of fixpoints,” POPL 1977,
pp. 238–252. DOI: `10.1145/512950.512973`.

The paper motivates abstraction/concrete-semantics separation.  DASHI's
consumer-relative trace-congruence and terminalisation-defect formulation is an
internal construction, not a theorem attributed to that paper.

## 3. Possibility, accessibility, support and refutation are different axes

`DASHI.Core.PossibilityAccessibilitySupport` gives three independent indexed
propositions:

```text
SemanticallyPossible
ComputationallyAccessible
EvidentiallySupported.
```

No implication is supplied between them.

PNF additionally distinguishes:

```text
SuppressionState
ExecutionRetention
SemanticAdmissibility.
```

Actual refutation requires an evidence-indexed `Refutes evidence candidate`
witness.  Soft reweighting, negative/interfering phase, execution overflow and
pruning have no refutation constructor.

This is the formal target for Python candidate state.  A runtime implementation
should not encode all of these propositions into one mutable enum.

## 4. Bounded execution is a P/Q execution partition, not semantic truncation

`DASHI.Cognition.PNF.BoundedExecutionCarrier` is the canonical bounded-work
surface already shared by proper-name expansion and factor composition.

It records:

```text
possible count
retained count
retained limit
coverage / overflow receipt.
```

The stronger `ReopenableExecutionPartition` additionally supplies:

```text
SemanticallyPossible candidate
Active candidate        -- P
Residual candidate      -- Q
Active -> Possible
Residual -> Possible
Active ∩ Residual = empty
ReopenReceipt for residual candidates.
```

There is no residual-to-refutation path.

`BoundedExecutionAdapters` turns the existing proper-name and factor-composition
execution witnesses into this shared carrier shape without replacing their
runtime-specific theorem names.

`MeasuredReopenableExecutionPartition` can additionally carry an
application-supplied retained/omitted mass split.  No probability measure is
manufactured by the core.

## 5. Support, classification and identity are separate morphisms

`SupportClassificationIdentitySpine` is deliberately an assembly module, not a
new relation implementation.

It reuses:

```text
ParserArgumentSupportWitness      -- structural support / realisation
CandidateClassificationEdge       -- revisable resolved-as/classification
IdentityFibreMember               -- proof-relevant identity.
```

The PNF semantics are:

```text
p --support--> a
x --classified-as--> C
x ==proof==> E
```

with no support-to-identity or classification-to-identity promotion.

`EvidenceClassificationEdge` now carries an explicit classification revision
in addition to factor evidence, provenance and scope.  Reclassification changes
the edge; it does not rewrite occurrence identity.

`ParserArgumentSupportGluing` remains the real parser/name -> argument-bearing
PNF seam.  It reuses the existing generic indexed-gluing proof and requires
multiscale naturality when support is transported across resolution:

```text
S_r(project_P x) = project_A(S_(r+1) x).
```

Identity transport across that seam still requires admitted identity witnesses
at both ends landing on the same canonical entity.

## 6. Predicate participation creates type pressure, not type assertion

`DASHI.Cognition.PNF.TypePressure` formalises the original Wikidata design
intuition directly.

A contribution is indexed by subject and candidate type and carries:

```text
evidence
signedPressure : Z
provenance
scope.
```

Several contributions aggregate by exact integer addition.  The coarse
reinforcing/independent/interfering direction is obtained through the existing
`RelationalBranchInterference.classifySignedInteraction` theorem.

`PredicateRolePressure` is the generic predicate-role form.
`NumericPredicateRolePressure` is the numeric PNF runtime specialization over
`ObjectId`, `FactorId`, `SymbolId` and a signed role pressure.

There is intentionally no theorem

```text
positive type pressure -> asserted type.
```

Pressure may justify a candidate classification or repair proposal; proof-level
typing remains downstream.

## 7. Fine evidence -> coarse phase is one-way

`DASHI.Core.FinePhaseObservation` is the canonical generic observation seam:

```text
Fine --observePhase--> Coarse.
```

`ObservedPhase` carries a proof that the coarse value is actually the observation
of its fine value.  There is no coarse-to-fine reconstruction permission.

The canonical integer instance reuses the existing exact signed-interaction
classifier:

```text
Z -> reinforcing | independent | interfering.
```

`EvidencePhaseObservationAdapter` makes both H3/H6/H9 evidence coordinates and
numeric predicate-role pressure literal instances of this core.

Thus balanced ternary / trinary phase is an observation of fine evidence, not an
independently mutable ontology value.

## 8. Canonical relational horizon 3 -> 6 -> 9

`DASHI.Core.RelationalHorizon369` owns the generic cumulative shape and reuses
the repository's existing exact `Triple` carrier:

```text
H3 A       = Triple A
H6 A B     = H3 A + Triple B
H9 A B C   = H6 A B + Triple C.
```

3/6/9 counts coordinate slots, never candidates or graph branches.

`EvidenceHorizon369` is now an instance of that generic core:

```text
H3 = local structural evidence
H6 = H3 + discourse/temporal evidence
H9 = H6 + external/authority evidence.
```

It retains the existing exact commuting squares with any
`StratifiedResolutionTowerExact.ResolutionTower`:

```text
project6to3(coarsen H6) = coarsen(project6to3 H6)
project9to6(coarsen H9) = coarsen(project9to6 H9).
```

`EvidenceDepthWheelOrthogonality` separately proves that expanding relational
horizon and advancing depth-wheel phase commute because they act on different
coordinates.

Three axes are therefore formally distinct:

```text
fine evidence / coarse sign phase
relational horizon H3/H6/H9
refinement depth phase C3.
```

## 9. Depth-wheel as grade-indexed dynamics

The exact depth-wheel/Cantor/address/ultrametric stack from the depth-wheel lane
is integrated into this branch.

`SSPPrimeLane369DepthWheelCantorBridge` supplies the existing period-three depth
phase and the ungraded phase-dependent endomorphisms:

```text
F0, F1, F2 : X -> X
W = F2 o F1 o F0.
```

`DASHI.Foundations.DepthWheelGradedDynamics` generalises this to a genuinely
grade-indexed carrier:

```text
X0 --F0--> X1 --F1--> X2 --F2--> X0.
```

One complete wheel is grade-preserving.  The existing ungraded wheel embeds as
the constant graded family.

`DepthWheelMemoryGradedAdapter` then proves the existing
`WheelMemoryFibre` is an actual instance: a `ThreePhaseLearningProgram` becomes
a `GradedDepthWheelSystem`, and the underlying phase-zero one-wheel state is
definitionally the existing `runOneLearningWheel` result.

The grade cannot be discarded merely because one wheel closes.  Whether a
consumer may forget it is governed by `DynamicConsumerSafety`.

The existing address wheel remains an ultrametric isometry.  This says the
address action preserves the already-defined ultrametric; it does **not** claim
that depth evolution `W` is contractive.  Contractive/non-expansive depth
dynamics remain a later theorem requiring hypotheses.

## 10. Static semantic sampling is weaker than dynamic safety

`SemanticSamplingLookupGeometry` intentionally formalises only exact present-time
query sufficiency:

```text
fineQuery x = coarseQuery(project x).
```

An `AliasingWitness` records distinct fine states with the same coarse shadow.
This is the disciplined part of the Nyquist analogy; no Shannon/Fourier theorem
for language is asserted.

`SemanticSamplingDynamicSafety` now contains a concrete theorem witness where:

1. the present Boolean query commutes exactly with the coarse projection;
2. the same coarse projection has a `TerminalisationDefect` under a later
   admissible residual-exposure action.

Therefore:

```text
static query sufficiency < dynamic consumer safety.
```

A runtime may stop refinement for a present query under a static sufficiency
certificate, but it may not persist that quotient as future-complete state
without the stronger dynamic proof.

## 11. Lookup geometry remains a runtime contract

`DirectDemandLookup` owns the canonical probe hierarchy:

```text
exact equality/hash-style -> expected constant-budget contract
ordered/B-tree-style      -> logarithmic contract
prefix/partition          -> explicit bounded prefix contract.
```

Agda proves consequences of supplied contracts.  It does not prove PostgreSQL's
planner/index implementation satisfies them without runtime evidence.

`SemanticSamplingLookupGeometry` additionally permits approximate neighbourhood
proposal, but approximate/vector search cannot directly admit identity and must
be followed by exact checking.

## 12. Numeric lexical projections and PostgreSQL retrieval

`LexicalRetrievalProjection` keeps three coordinates distinct:

```text
exact surface SymbolId
parser lemma observation
retrieval lexeme SymbolId(s).
```

PostgreSQL FTS/stemming is therefore a first-class candidate-reduction producer,
not a semantic lemma authority.  Numeric cue words are exact `List SymbolId`
objects after tokenisation; regex has no semantic-authority constructor.

`RetrievalReductionReceipt` measures whether PostgreSQL FTS, numeric cue
machines, or vector proposal actually reduce the candidate frontier.

`NumericTokenStorageReference` separately requires exact encode/decode for any
storage codec and reuses `MultiscaleMDL.ResidualCodec` where a genuine
coarse/fine storage split exists.  Number-theoretic elegance alone does not
select a physical PostgreSQL layout.

## 13. Local chronology before world alignment

`TemporalRoleWorldAlignment` keeps role occupancy local and temporal:

```text
(entity, role, temporal cell, evidence).
```

`ResolvedRoleTimeDemand` now makes local resolution explicit.  A selected local
occupancy is valid when every other locally compatible occupancy has the same
canonical local entity.  No external authority appears in that proof.

Thus Reagan-as-President and Bush-as-President can coexist in different local
time cells, and a title may resolve from the tranche chronology before Wikidata
alignment exists.

External/world alignment remains a later proof-relevant witness using the
existing `externalAlignmentEvidence` + `externalAuthority` path.

## 14. Inductive preference remains a non-proof result

`InductiveDemandPreference` already supplies:

```text
preferred candidate
evidence margin
evidence coverage.
```

It deliberately returns the existing `DemandState openDemand` and has no scalar
identity authority.  This is the home for discourse-level reasoning such as
“only one currently known participant fits the wider story” when no deductive
identity witness yet exists.

## 15. Bounded Wikidata repair endpoint

`WikidataRepairProposal` closes the loop back to the original Wikidata
presentation.

Repair operations are explicitly reviewable proposals:

```text
split entity
underspecify type
remove bad superclass
propose latent type
hold for review.
```

Each proposal retains signed pressure, factor/demand witnesses, residual note,
provenance and scope.  `DomainRepairProjector` emits a
`BoundedExecutionCarrier RepairProposal` rather than an unbounded/global solve.

Neither the proposal nor a positive type-pressure score grants ontology truth.

### Reference

Denny Vrandečić and Markus Krötzsch,
“Wikidata: a free collaborative knowledgebase,” Communications of the ACM
57(10) (2014), 78–85. DOI: `10.1145/2629489`.

This paper describes Wikidata and its collaborative knowledge-base model; the
latent-pressure / bounded-repair semantics here are ITIR/DASHI constructions.

## 16. Existing exact references retained, not universalised

The branch continues to reuse rather than duplicate:

- `NormalizedFibreAveragingExact` for an exact finite P/Q decomposition;
- `GlassesProjectionInvolutionExact` for the exact finite `J P J = Q`,
  `J Q J = P` complementary-view reference;
- `RelationalBranchInterference` for exact signed integer interference;
- `RelationalTernaryPhaseGeometry` for the finite Eisenstein-phase reference;
- `TypedHyperfabricCore` for typed higher-arity incidence;
- `StratifiedResolutionTowerExact` for multiscale quotient towers;
- `MultiscaleMDL` for exact residual codecs and explicit optimality boundaries;
- `IndexedGluing` for exact external/internal representation transport.

None is silently promoted into a universal semantic theorem.

## Runtime laws to implement

The next Python/PostgreSQL sprint should be able to point to these laws almost
one-for-one:

```text
support != identity
classification != identity
pressure != type assertion
retrieval rank != semantic admission
inductive preference != proof
negative phase != refutation
low weight != semantic absence
execution pruning != refutation
bounded output != bounded semantics
reopenable quotient != dynamically safe quotient
present-query sufficiency != future-state sufficiency
H3/H6/H9 horizon != refinement depth
H3/H6/H9 horizon != candidate count
depth phase != evidence phase
local role resolution != world identity
Wikidata repair proposal != ontology truth.
```

The intended execution policy is therefore:

```text
numeric occurrence / factor carrier
  -> cheap PostgreSQL candidate narrowing
  -> provenance-bearing semantic fibre
  -> H3 local evidence
  -> H6 discourse/temporal only if needed
  -> H9 external/authority only if needed
  -> fine signed evidence + derived phase
  -> bounded active P plus reopenable residual Q
  -> inductive preference if useful
  -> proof-bearing identity/type admission only where justified
  -> factor substitution / downstream domain projection.
```

That is the formal contract for the runtime, not a requirement that runtime
objects mirror Agda records mechanically.

## Validation boundary for this branch

The tranche checker enumerates the canonical surfaces and fails closed on
explicit postulates, hole blocks, unsafe termination escapes, and missing
required theorem markers.  The GitHub workflow is intentionally manual-only on
this branch while Actions quota is constrained.

No claim of Agda kernel/typecheck success should be made until the existing
Agda-2.9 checker is run in an environment with the pinned toolchain.
