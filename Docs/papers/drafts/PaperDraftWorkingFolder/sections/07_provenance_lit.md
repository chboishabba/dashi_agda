# Appendix: Provenance and Positioning

Status: `docs-only; provenance appendix; fail-closed; non-promoting`

This appendix records provenance and positioning for Paper 1. It is not a new
claim surface. The paper's positive claims remain limited to the repo-backed
theorem, receipt, and obstruction surfaces named in the main draft skeleton.
Historical discussion, chat context, NotebookLM context, JMD material, and
Monster/moonshine-adjacent material are treated as motivation, discovery
context, or source-lattice background only.

## Scope Rule

Paper 1 is a constructive physics-unification paper whose claims are admissible
only when they cite exact DASHI Agda definitions, receipts, or blocker ledgers.
In particular:

- JMD material may explain where a 15-coordinate SSP framing was noticed,
  motivated, or organized.
- JMD material does not prove the DASHI formalization.
- Monster or moonshine-adjacent material may be cited as carrier/provenance
  context where the repo already marks it as such.
- Paper 1 has no Monster moonshine requirement.
- Paper 1 must not claim that JMD proves DASHI physics, physics closure,
  limited SM+GR, GRQFT, empirical validation, or unification.

The live Paper 1 claim inventory is controlled by
`Docs/papers/drafts/Paper1DraftSkeleton.md` and
`Docs/papers/drafts/Paper1InternalFormalMethodsOutline.md`: G2 schema extension, the tracked
G6 route, G3 constructive finite-support subtraction support, and the E8
integer/upstream boundary are the admissible positive or boundary surfaces.

## Positioning

The contribution should be positioned as constructive physics unification with
a fail-closed packaging discipline:
DASHI separates inhabited theorem surfaces from request-only, constructorless,
prototype, historical, and externally-gapped surfaces. This is the paper's
central methodological claim. It is stronger and cleaner than a physics claim:
the repo demonstrates how a formal system can carry exact proof receipts while
also preserving blockers as first-class objects.

The surrounding literature/provenance story is therefore secondary. It can
explain why these surfaces were selected, why the 15 SSP coordinate frame is
natural in this development, and why moonshine language appears in adjacent
repo history. It cannot substitute for a checked theorem or receipt.

## JMD / Monster Boundary

The JMD/Monster boundary should be stated narrowly:

- JMD identified or motivated a 15 SSP coordinate framing relevant to later
  DASHI organization.
- DASHI's typed claims must be cited to DASHI repo surfaces, not to JMD
  narrative provenance.
- The repo already distinguishes a carrier-level Monster/Ogg comparison from a
  stronger moonshine theorem. `Docs/HeckeRepresentationLayer.md` records that
  `Ontology/Hecke/MoonshinePrimeCarrierMatch.agda` proves the intrinsic `SSP`
  carrier matches the canonical 15-prime list
  `2,3,5,7,11,13,17,19,23,29,31,41,47,59,71`, while explicitly rejecting the
  inference that a Hecke-side `forcedStableCount = 15` collapse is identified
  with the Ogg/Monster prime set.
- `README.md` likewise keeps the current moonshine-facing work
  pre-moonshine/non-modular unless a future graded-module or trace bridge is
  supplied. JMD-side regime metadata may be used for occupancy/divergence
  questions, but DASHI-side delta/cone/Fejer/trace tests are separate
  dynamical questions.

Paper 1 should therefore use language such as:

> The 15-coordinate SSP framing has historical provenance in JMD/Monster-facing
> exploration, but the formal claims in this paper are DASHI-local typed
> receipt claims. The Monster/moonshine material is not an assumption of Paper
> 1 and is not used to prove the paper's formal-methods claims.

Avoid language such as:

> JMD proves the DASHI physics program.

> The 15 SSP coordinates establish a Monster moonshine theorem.

> Paper 1 requires Monster moonshine to justify its formal receipt surfaces.

## Source Ledger

The current source ledger for this appendix is:

| Source | Identifier | Use in Paper 1 |
|---|---|---|
| Robust-context thread metadata | Online UUID `6a05676e-f358-83ec-a178-3dcc5f537a9a` | Historical context only; not a theorem citation. |
| Robust-context canonical thread | Canonical ID `edac27557dd34bf9ab9f4563525aecc742c976a1` | Historical context only; not a theorem citation. |
| NotebookLM context | `ee9eb104-2219-45e5-906a-f19ae4ff5a93` | Source/background ledger only. |
| NotebookLM context | `52145000-1ab8-418e-af5b-55a0539f8a26` | Source/background ledger only. |
| NotebookLM context | `5520e3f6-6c61-4735-8c4c-e8bf2198f7a0` | Source/background ledger only. |
| NotebookLM context | `fcb3c21c-3063-469e-9914-a3b589b31933` | Source/background ledger only. |
| NotebookLM context | `0cd1bd14-bff6-4e7d-92df-f56fbd7f142a` | Source/background ledger only. |
| NotebookLM context | `3a220b1e-c9da-4663-8550-444a4b33b0e1` | Source/background ledger only. |
| DASHI draft control | `Docs/papers/drafts/Paper1DraftSkeleton.md` | Governs Paper 1 allowed/forbidden claims. |
| DASHI outline control | `Docs/papers/drafts/Paper1InternalFormalMethodsOutline.md` | Governs Paper 1 scope and blocked surfaces. |
| DASHI Hecke carrier note | `Docs/HeckeRepresentationLayer.md` | Carrier-level 15-prime boundary and non-promotion warning. |
| DASHI repo overview | `README.md` | Current moonshine-facing prototype and JMD regime boundary. |

The robust-context and NotebookLM identifiers are provenance handles, not
paper-grade bibliographic citations by themselves. If the final manuscript
uses them, the bibliography or data-availability note should explain how a
reader can inspect the corresponding archive, export, or notebook state.

## Repo-Backed Receipt Anchor

When this appendix is connected to the main text, the formal references should
route through the paper's existing receipt inventory:

- G2 direction-indexed SFGC schema extension:
  `DASHI.Physics.Closure.G2SFGCGaugeFieldSchemaExtension.canonicalG2SFGCGaugeFieldSchemaExtensionReceipt`
  and `noRemainingG2SFGCSchemaExtensionMissing`.
- G6 tracked cross-lane theorem:
  `DASHI.Physics.Closure.G6CrossLaneCommutingTheorem.canonicalG6OfficialTrackedCrossLaneCommutingTheorem`.
- G6 tracked above-threshold consumer:
  `DASHI.Physics.Closure.G6AboveThresholdIndependence.canonicalG6OfficialTrackedAboveThresholdCoordinateIndependence`.
- G6 old-interface obstruction:
  `DASHI.Physics.Closure.G6CrossLaneCommutingTheorem.g6LaneOperatorUniversalVanishesIdentityObstruction`.
- G3 constructive finite-support subtraction support:
  `DASHI.Physics.Closure.G3P2LimitConvergenceSurface.selectedFiniteSupportOperatorSubtractionCertifiedSupport`,
  `selectedFiniteSupportOperatorSubtractionSupportWitnessFromCertified`, and
  `G3SelectedSubtractionCertifiedSupport`.
- G3 remaining norm-law boundary:
  `DASHI.Physics.Closure.G3P2LimitConvergenceSurface.exactRemainingDifferenceNormLawBlockers`
  and `firstNormIndexMissingAfterDifferenceNormLawSurface =
  missingSelectedOperatorDifferenceNormIndexLaws`.
- E8 integer/upstream boundary:
  `DASHI.Algebra.Trit.E8RootEnumeration.integerIndexedRootsCompleteForTwoSparseShapeTheorem`,
  `DASHI.Algebra.Trit.E8RootEnumeration.canonicalE8RootEnumerationCompletePromotionBoundary`,
  and
  `DASHI.Physics.Closure.LilaE8RootEnumerationNoDuplicatesSurface.canonicalE8UpstreamCompleteReceiptPromotionAudit`.

These anchors are the admissible citation path for Paper 1 claims. JMD,
Monster, robust-context, and NotebookLM entries can explain how the authors got
to these questions; they do not establish the formal claims.

## Citation and Source Gaps

The following gaps should remain visible until closed:

- External literature citations for the formal-methods positioning are not yet
  selected. A final manuscript should cite appropriate work on proof
  assistants, mechanized mathematics, typed certificates, and proof-carrying
  artifacts.
- External citations for Monster moonshine, Ogg primes, and related modular
  representation theory are not yet attached. If mentioned at all, they should
  support only the historical/carrier-language background, not a Paper 1
  theorem.
- The robust-context UUID/canonical-ID pair and NotebookLM IDs are not enough
  for reproducible public citation unless the corresponding archives are
  exported or otherwise made inspectable.
- JMD source material is currently provenance context, not an accepted
  theorem-grade source for DASHI claims. Any final claim that depends on JMD
  must identify the exact source artifact, projection rule, and validation
  route.
- No source in this appendix closes W2, W3, W4, W5, non-flat GR,
  Schwarzschild, continuum scaling, GRQFT, limited SM+GR, empirical authority,
  or full-unification blockers.

The safe final-paper wording is therefore: Paper 1 reports a bounded typed
receipt package and its blocked promotion surfaces. JMD/Monster provenance
helps explain the development path, but the publishable claims stand or fall
on DASHI-local typed receipts.

## Archive Topics To Route, Not Promote

The long blocker archive and NotebookLM source checks surfaced several topics
that were underweighted in earlier paper planning. They should be routed as
follows:

| Topic | Route | Boundary |
|---|---|---|
| 15 SSP / JMD / Monster provenance | Short carrier-background paragraph and this appendix | Attribute the 15 SSP coordinate/provenance input to JMD. Do not claim Monster, moonshine, or modularity closure. |
| Base369 / trit / p-adic carrier intuition | Background or appendix | Expository support for the carrier story only unless a sentence cites exact DASHI Agda surfaces. |
| Hensel lifting / p-adic convergence | Background or mathematical-constructions exposition | Useful for explaining refinement without polarity flip; not a convergence theorem unless repo-backed. |
| UFT-C / lattice logic / SWAR | Compression/semantic-geometry appendix | Implementation/reference machinery, not a performance, proof, or physics claim. |
| Markov-compatible projection | Appendix or discussion | DASHI can be viewed as Markov after history is quotient-lifted into a typed joined state; it is not a classical upstream Markov-chain claim. |
| Orbit-shell / Lorentz-signature family | Future-work appendix | Useful for showing a non-vacuous unification route; not a Paper 1 positive physics result. |
| W5 CT18 observable mismatch | Empirical appendix and exact-gaps table | CT18 diagnostics currently concern a different observable/regime and do not close W5. |
| Wave/unitary lift | Future work only | Avoid implying new quantum mechanics, particle derivation, or speedup. |
| Energy vacua / Standard Model emergence | Future work only | Too broad and too risky for Paper 1 positive scope. |
| DNA/sofic/brain/perception | Future appendix or exclusion | Non-promoting theorem-target material only. |
| Trading/legal/social/cultural material | Exclude from Paper 1 body | Off-thesis for a physics-unification manuscript. |

Older NotebookLM summaries that describe Paper 1 as primarily a
formal-methods collider paper should be treated as risk warnings, not as the
current thesis. The current thesis is physics unification under typed closure
frontiers; formal methods style and proof governance are the publication
discipline.
