# ITIR / PNF / Residual Logic Bridge

This note records the bounded bridge between the sibling ITIR/SensibLaw text
surfaces and the DASHI Agda carriers.

For the full normalized chain from runtime receipt emission through residual
joins, pressure, logic carriers, and the Hecke adapter, see
[`ClaimComparisonEngine.md`](./ClaimComparisonEngine.md).
For the downstream classifier design over receipted residual/domain/formula and
Hecke features, see
[`AttractorOrbitClassifier.md`](./AttractorOrbitClassifier.md).

## Runtime Boundary

The ITIR/SensibLaw side has runtime parser and reducer code, but DASHI does not
import that runtime. The safe reading is:

- spaCy is structural substrate only: token, lemma, POS, dependency, head, and
  span evidence.
- `PredicatePNF` is the structured predicate carrier shape promoted by the
  reducer, not a truth oracle.
- residual comparison is a bounded join-lattice over structural agreement, not
  legal truth, route authority, or Wikidata edit authority.
- Real text comparisons must be receipt-driven. Human inspection of a sentence
  is not allowed to assign `WrapperState`, `QualifierState`, role bindings, or
  residual levels.

## Wikidata Structural Coherence Boundary

Wikidata monotone structural coherence is admissible only as a structural
receipt/coherence check over emitted predicate fibres. It may compare whether a
sequence of receipt-backed structural signatures, qualifier states, wrapper
states, provenance fields, and bounded ontology-index references preserves or
sharpens information monotonically. It does not authorize Wikidata edits,
assign truth, select facts, construct live ontology-index artifacts, or promote
residual levels without emitted receipts and an external promotion boundary.

The latest Wikidata formalism should be read as a global-latent structural
coherence theorem shape, not merely as bounded local repair comparison:

```text
global ontology snapshot Omega
  -> typed ontology index and residual/severity carriers
  -> candidate mutations
  -> monotone admission filter severity(after) <= severity(before)
  -> aggregate structural incoherence is non-increasing
  -> finite lattice convergence to a fixed point
```

The bounded QID or review-packet flow is the first product projection of that
larger shape. A completed QID-only tool could project a local slice from the
global index, diagnose pressure, and emit candidate local/upstream mutations
that pass the monotone filter. That still would not be edit authority: the
formal layer certifies structural-coherence improvement, while community or
external governance certifies edit desirability.

Current repo state is behind that endstate. It records residual carriers,
receipt obligations, and non-promoting Wikidata coherence language, but it does
not yet provide concrete Wikidata QID/PID/statement carriers, a live
snapshot-derived ontology index, bounded mutation/filter carriers, or a
QID-only repair bot.

## Fibred PNF Comparison

The PNF residual lattice is not a flat comparison over arbitrary atoms. It is a
family of residual chains indexed by `StructuralSignature`.

- Same-signature comparisons may enter the role, qualifier, and wrapper gates.
- Cross-signature comparisons collapse to `noTypedMeet`; they cannot reach
  `exact` or `partial`.
- `WrapperState` is a pre-filter for exactness. A hedged, attributed, or
  unknown wrapper mismatch cannot be promoted to exact even when the syntactic
  shape is otherwise compatible.
- `performativeEvidence` is a wrapper for public declarations, threats,
  slogans, and negotiating postures. It compares as a wrapper mismatch against
  `directEvidence` and maps to `scopeExceeded6` in the six-level refinement
  when the pipeline emits that wrapper. The formalism does not assign that
  wrapper by surface-text inspection.
- `PredicateIndexSurface` records the shortlisting boundary: candidates are
  selected by structural signature, with a stable fallback reference when no
  candidate fibre is available.

## Agda Surfaces

- `DASHI.Interop.SensibLawResidualLattice` mirrors the four SensibLaw residual
  levels as `ResidualLevel`:
  `exact`, `partial`, `noTypedMeet`, and `contradiction`.
- The same module defines `joinResidual`, proves idempotence, commutativity,
  associativity, upper-bound, least-upper-bound, and preservation into
  `DASHI.Pressure` through `ITIRJoinBridge`.
- The module also defines a minimal `PredicatePNF` record shape with
  `StructuralSignature`, typed role slots, qualifier, wrapper, and provenance.
  This is a carrier shape only; it does not parse text.
- The module defines `PNFEmissionReceipt`, carrying parser profile, reducer
  profile, source span, and emitted atom. `receiptResidual` compares only the
  emitted atoms from two receipts.
- The same module defines `computeResidual`, `SignatureComparison`,
  `WrapperComparison`, and `PredicateIndexSurface`, so the Agda surface records
  the signature-fibred comparison boundary instead of treating residuals as a
  single flat chain.
- It also defines `SixResidualLevel`:
  `exact6`, `partial6`, `underdetermined6`, `noTypedMeet6`,
  `scopeExceeded6`, and `contradiction6`, with join laws and pressure join
  preservation. The wrapper projection sends `performativeEvidence` and
  `wrapperUnknown` to `scopeExceeded6`.
- `DASHI.Algebra.TetralemmaBridge` aligns `LogicTlurey.Stage` and
  `ResidualLevel` through a four-position carrier. It records the topology
  boundary explicitly: `Stage` is cyclic; `ResidualLevel` is an ordered join
  chain. It also embeds `TriTruth` into the residual chain as
  `tri-low -> exact`, `tri-mid -> partial`, and
  `tri-high -> noTypedMeet`. `contradiction` has no preimage in this tone
  embedding; it is cross-claim pressure, not an internally generated
  dialectical tone.
- `DASHI.Algebra.SixfoldLogic` defines `Stage6` and `hexTone : Stage6 ->
  HexTruth`, proving the six-step transport law over `Base369.HexTruth`.
- `Ontology.Hecke.PNFResidualBridge` records the Hecke-side fibre adapter:
  quotient projection equality is a PNF candidate-pool fibre, Hecke defect
  classes embed into `ResidualLevel`, illegal defects map to `contradiction`
  and critical pressure, and the canonical saturated histogram maps to
  `partial` rather than `exact`.
- `DASHI.Interop.PNFResidualConsumerNextObligation` records the current W6
  receipt-bearing consumer obligation. A future consumer must carry paired
  `PNFEmissionReceipt` values, receipt-backed atom projections, a
  receipt-backed residual computation, runtime consumer profile/id, and a
  Hecke candidate-pool receipt. The source diagnostic now lists the missing
  runtime pieces explicitly: consumer profile, runtime receipt id, left and
  right `PNFEmissionReceipt` values, receipt-backed residual computation, and
  Hecke candidate-pool receipt id. The current value is a missing-receipt
  diagnostic only and assigns no wrapper, qualifier, role, residual, or Hecke
  label by inspection.

## Hecke Fibre Adapter

The Hecke bridge is intentionally representation-layer only. Given a
`QuotientInterfaceOn S Class`, the candidate-pool relation is:

```text
SameHeckeCandidatePool q x y =
  QuotientInterfaceOn.proj q x == QuotientInterfaceOn.proj q y
```

A separate `Class -> StructuralSignature` map can then send equal quotient
classes into equal PNF structural signatures. This mirrors the runtime
`PredicateIndex` rule: shortlist by fibre first, then compare inside the fibre.

Defect classes embed as:

| Hecke defect class | PNF residual |
|---|---|
| `stableDefect` | `partial` |
| `illegalDefect` | `contradiction` |
| `otherDefect` | `noTypedMeet` |

The bridge proves that joining any residual with an illegal defect remains
`contradiction`, matching the severity-cannot-be-masked law. It also records
that the current saturated branch is forced-stable/partial, not exact
residual equivalence.

## Case-Study Surface

[`PNFCaseStudiesWatergateIran.md`](./PNFCaseStudiesWatergateIran.md) records
two review-facing conditional fixtures:

- a closed Watergate-style corpus, where receipted emitted atoms can be
  compared inside stable structural-signature fibres;
- a live Iran-war rhetoric corpus, where any performative-wrapper conclusion is
  conditional on the runtime pipeline emitting `performativeEvidence`.

The case-study note cites external reporting only as corpus context. It does
not promote those reports into Agda theorem facts or hand-assigned labels.
It also records already-formal formula spans and interview attribution
transitions as conditional fixtures: the pipeline must emit receipts before
the residual layer can compare them.
An already-formal formula may also be used as an operator-level fixture when a
formula-reader receipt emits a shape such as local expansion,
`f (f x) > f x`. In that case the residual layer can compare the emitted
operator hypothesis, but it still cannot promote the source span into a
real-world `AntiFascistSystem` instance, market-period claim, or actor
classification without a separate model certificate.
The related domain-incommensurability fixture is also documentation-only for
now: if one receipted source span lives in an economic-cost domain and another
lives in a theological, ideological, legal, or otherwise terminal mandate
domain, the current Agda carrier can record cross-signature failure and
`scopeExceeded6`, but it does not yet have a distinct `incommensurable`
constructor for "no common measure bridge was emitted."
The attractor/orbit classifier surface is likewise downstream and
documentation-only: it may consume receipted residual, wrapper, domain, and
Hecke features, but it does not turn those features into trading signals or
causal-source claims without separate validation.

## Anhomomorphic-Logic Context

The physics connection is compatible with Rafael Sorkin's anhomomorphic-logic
reading of the tetralemma: the four alternatives arise naturally when valuation
maps are not required to be Boolean homomorphisms. See Sorkin, "To What Type of
Logic Does the Tetralemma Belong?", Syracuse SURFACE Physics Paper 7:
https://surface.syr.edu/phy/7/

DASHI records this as context, not as a dependency. The Agda bridge only states
the carrier-level fact: a cyclic `Stage` dynamics and a static `ResidualLevel`
chain can share a four-position observation vocabulary while remaining
topologically distinct.

## Non-Claims

- No spaCy parse is treated as an ontology claim.
- No PNF atom is treated as theorem input without an explicit bridge receipt.
- No residual comparison decides policy, routing, legal truth, or Wikidata
  edits.
- No Wikidata monotone structural-coherence result is treated as Wikidata edit
  authority, fact authority, ontology truth, or residual-label authority. It
  requires emitted receipts for structural signatures, qualifiers, wrappers,
  provenance, and any monotone map being claimed.
- No Hecke support/fibre class is treated as a `PredicatePNF`; the bridge only
  aligns candidate-pool and residual-pressure structure.
- No live political claim is promoted from `performativeEvidence` to
  `directEvidence` without an explicit source/profile/span receipt.
- No live political claim is assigned `performativeEvidence` without a pipeline
  receipt that emits that wrapper.
- No formula span is treated as an operator-class proof certificate without a
  receipt plus a model witness for the carrier, operator, observable, and
  obligations being claimed.
- No domain-incommensurability classification is assigned to a live legal,
  theological, political, or market corpus by inspection. It requires emitted
  domain receipts and a model-level absence or failure of a measure bridge.
- No attractor/orbit label is a production classifier output, trade signal, or
  hidden-cause attribution without a checked feature extractor and external
  validation model.
- No state-level political label is identified with a DASHI operator-class
  trace without a separate political/legal taxonomy, receipt corpus, scope
  rule, and validation standard. `FascisticSystem` names an entropy-collapsing
  projection property, not a direct political classification.
- No aggressor or responsibility label is inferred from operator-class traces
  alone. Shared-fibre aggressor claims and cross-fibre responsibility claims
  require a taxonomy, cost/threat/response receipts, provenance for any
  third-party burden claim, and external legal/political/ethical validation.
- No existential-domain or operator-completeness claim is inferred from named
  live events or domain labels. A physical-survival witness fibre requires
  source-span receipts, witness provenance, temporal/wrapper/modality fields,
  a warrant-ordering rule if domains are ranked, and a typed multi-domain
  interaction operator before it can participate in trigger, responsibility,
  or completeness fixtures.
- No enemy-classification operator is assigned to a named scripture,
  theological tradition, or political phrase by inspection. Lineage-fixed,
  behaviour-conditional, invertible, non-invertible, desistance, or
  peace-clause claims require textual/source-span receipts, interpretive
  profile metadata, classifier-input taxonomy, inverse/deactivation semantics,
  and validation before comparison with `FascisticSystem`,
  `AntiFascistSystem`, or `Contraction` surfaces.
- No collapsed classifier is treated as outside the residual formalism merely
  because it destroys distinctions. A one-element or coarser quotient lattice
  is well-formed, and cross-carrier comparison can yield `noTypedMeet`.
  Product-lattice comparison and lift/redifferentiation claims require
  explicit quotient maps, lost-distinction records, receipts, and validation.
- No protected-identity/conduct-axis or three-body lattice model is inferred
  from named religious/legal traditions. Two-axis signatures, product lattices,
  projections, quotient/lift maps, decision-operator routing, church/state
  decoupling, and stable-subproduct claims require source receipts,
  role-binding taxonomies, component meet/join laws, and validation.
- No Basilidean, Gnostic, Sufi, heresiological, or four-body theology claim is
  inferred from an infographic or hostile-source summary. Historical theology
  fixtures require source-critical receipts, wrapper/qualifier profiles for
  adversarial or indirect witnesses, orientation maps, product-lattice
  definitions, operator witnesses, and validation. `Ultrametric.agda` exists;
  what is missing for such a fixture is a domain-specific metric over the
  chosen lattice morphisms.
- No Advaita, Dvaita, Nishkama-karma, Buddhist, Madhyamaka, Jain, or broader
  non-Abrahamic / N-body comparative-lattice claim is inferred from a school
  name, comparative summary, or philosophical keyword. Identity-map,
  permanent-distance, telos-free action, process-dissolution, cessation, or
  perspective-indexed fixtures require school-level source receipts,
  interpretive-profile metadata, carrier definitions, role-binding or process
  translations, perspective meet/join rules where relevant, and validation.
- No Taoist, Confucian, Shinto, Indigenous American, Maori, Aboriginal
  Australian, or other living-lattice claim is inferred from a tradition name,
  comparative summary, public slogan, or cultural keyword. Carrier-substrate,
  natural-flow, relation-matrix, immanent-node, fully connected relation,
  derivation-graph, timeless-bundle, songline/scan-order, metric, or
  fixed-point fixtures require culturally governed source receipts,
  place/community provenance where applicable, restricted-knowledge flags,
  topology-changing carrier definitions, typed morphisms, and validation.
- No feelings-wheel, emotion-taxonomy, vedana/sankhara, mindfulness,
  trauma-collapse, PTSD, emotional-healing, high-Mana, Dreaming-centre, or
  personal-DASHI claim is inferred from a diagram, introspective description,
  forum post, clinical term, or contemplative keyword. Affective-state
  fixtures require a named taxonomy, source or subject/session receipts,
  psychometric or clinical validation status, contemplative-source profiles
  where relevant, typed tone/naming/perspective carriers, and explicit
  clinical non-authority flags.
- No mathematical-atlas claim is inferred from naming a relevant field.
  Category theory, topos theory, HoTT, ergodic theory, information geometry,
  non-well-founded set theory, tropical geometry, renormalization, and
  infinity-categories require typed chart carriers, morphisms from existing
  PNF/residual/operator surfaces, preservation laws, and validation before the
  bridge can emit adjunction, subobject-classifier, path-space, scan-order,
  Fisher/MDL, coinductive, tropical-limit, RG, terminal-object, or
  infinity-topos claims.
- No cross-scale physics / biology / consciousness claim is inferred from
  shared mathematical vocabulary. Quantum measurement, projectors, unitaries,
  RG flows, free energy, Landauer erasure, phase transitions, DNA eigenclasses,
  epigenetic markers, predictive processing, DMN, amygdala/PFC,
  polyvagal-state, IIT Phi, Indigenous relational, or `JFixedPoint` readings
  require typed scale carriers, scale maps, preservation laws, measurement
  protocols, empirical validation, and clinical non-authority flags where
  neural, trauma, affective, or health-related claims are involved.
- No Base369-chain interpretation is inferred from cyclic carriers alone.
  `Base369` supplies formal `TriTruth` / `HexTruth` / `NonaryTruth` cyclic
  surfaces, but claims that these carriers represent named theological,
  actor-count, Theta, capitalist/socialist, strategy-window, resolution, or
  global-attractor structures require typed carrier maps, quotient/seam or
  commutation proofs, operator witnesses, and validation.
- No relational pair-operator claim is inferred from separate actor labels.
  A joint fixed-point, no-fixed-point, or terminal-dominance claim requires a
  product carrier, directed receipts, a coupling/composition law, and a theorem
  connecting component traces to the joint operator.
- No conditional-trigger or latent fixed-point claim is inferred from perceived
  threat narratives. Trigger activation and deactivation require emitted PNF
  receipts, modality/qualifier rules, a trigger connective, a latent fixed
  point in the carrier, and a convergence theorem for the deactivated mode.
- No bot/source join-domain claim is inferred from shared feature inputs. An
  exact meet between market-risk and causal-source PNFs requires a typed
  observation map, orbit-input bijectivity theorem, minimal/canonical operator
  relation, and empirical/causal validation. The current Hecke adapter,
  `CRTPeriod`, and `JFixedPoint` do not supply those obligations.
- No global phase-space or bifurcation claim is inferred from local conflict,
  price, theology, or movement labels. A basin-exit, dominant-attractor,
  reactive-operator, or post-bifurcation claim requires a global state carrier,
  basin metric, perturbation threshold, typed epistemic interaction operator,
  and empirical validation.
- No `SixResidualLevel` value is treated as emitted by runtime SensibLaw until
  the runtime adds those levels and a receipt surface carries them.
- The tetralemma and sixfold carriers are formal alignment surfaces. They do
  not assert external historical, religious, or philosophical equivalence.
- The sixfold carrier does not change `CLOCKPhaseInstance`; the existing clock
  lane remains cyclic `HexTruth`, not dihedral/reversal structure.

## Promotion Gate

The current state is `bridge/adapter`. Promotion requires a consumer theorem
that names which DASHI proof surface receives a `PNFEmissionReceipt` or
residual receipt, plus a receipt preserving parser profile, reducer profile,
span provenance, residual level, structural signature fibre, wrapper state,
and non-authority flags.
