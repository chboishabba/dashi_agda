# 4. Formal Core: Carrier Lanes, Inhabited Surfaces, and Exact Blockers

Paper 1 treats the DASHI formal core as a constructive physics-unification
architecture with fail-closed theorem promotion. The lane names used in the
repository are therefore not presented as slogans or completed physical
subtheories. They are typed subproblems: each lane supplies either an inhabited
formal surface, a restricted construction, or an explicit obstruction to a
stronger physical claim.

The four formal lanes used in the main technical body are G2, G3, G6, and
E8/LILA. Together they show how the carrier can host direction-indexed local
geometry, restricted operator filtrations, tracked independence between prime
coordinate lanes, and finite root-enumeration structure. The point is not that
these four receipts complete physics. The point is that a unification program
can state exactly which internal structures are present, which stronger
structures remain missing, and which promotions are forbidden until their
owning receipts are inhabited.

## 4.1 Translation from Lane Names to Mathematical Roles

| Internal label | Mathematical role in the paper | Current positive surface | First fail-closed boundary |
|---|---|---|---|
| G2 | Direction-indexed discrete carrier schema | Direction-indexed SFGC schema adoption for current core-facing consumers | No Maxwell closure or field-equation recovery follows |
| G3 | Restricted finite-support operator filtration | Certified subtraction support for selected constructive finite-support operators | Associated-graded quotient infrastructure remains missing |
| G6 | Tracked cross-lane coordinate independence | Official tracked cross-lane commuting theorem and tracked above-threshold independence | Old universal `LaneOperator` promotion remains blocked |
| E8/LILA | Local finite root-enumeration and upstream-promotion boundary | Integer/two-sparse completeness plus local semantic audit boundary | Upstream `E8RootEnumerationComplete` remains blocked |

This translation table is the paper-facing abstraction layer. The internal
labels are useful for traceability, but the mathematical content is the typed
role, the inhabited surface, and the exact boundary. A reader should be able to
audit every positive sentence in this section against a named Agda receipt or
boundary.

## 4.2 G2: Direction-Indexed Discrete Gauge Schema

The G2 lane supplies the current direction-indexed carrier schema for local
discrete gauge geometry. Mathematically, this should be read as a typed
interface result: the formal carrier has adopted a two-direction local site
schema for the current core-facing consumers. This is the layer at which one
can talk about a structured discrete site, direction labels, and the consumer
side of a local gauge-like schema without already asserting a continuum field
equation.

The positive surface is
`DASHI.Physics.Closure.G2SFGCGaugeFieldSchemaExtension.canonicalG2SFGCGaugeFieldSchemaExtensionReceipt`,
with the no-remaining-missing surface
`DASHI.Physics.Closure.G2SFGCGaugeFieldSchemaExtension.noRemainingG2SFGCSchemaExtensionMissing`.
The admissible paper claim is narrow:

> Direction-indexed SFGC schema adoption is complete for the current
> core-facing consumers.

This matters for the unification architecture because it gives the carrier a
checked local geometric interface rather than leaving "gauge structure" as an
informal analogy. It is a formal site-schema adoption result, not a physical
recovery theorem.

The boundary is equally important. G2 schema adoption does not prove Maxwell
closure, Yang-Mills dynamics, field-equation recovery, empirical calibration,
limited Standard Model plus GR closure, GRQFT closure, or completed
unification. In manuscript terms, G2 may be used to show that the carrier has a
typed local geometry interface; it may not be used to claim that the physical
gauge sector has been derived.

## 4.3 G3: Selected Finite-Support Operators and the Quotient Gap

The G3 lane is the restricted operator-calculus lane. Its role is to build a
controlled finite-support operator surface on which filtration and contraction
language can eventually be made quotient-correct. The current positive result
is not arbitrary operator closure. It is certified subtraction support for a
selected constructive finite-support subtype.

The relevant inhabited surfaces are:

- `DASHI.Physics.Closure.G3P2LimitConvergenceSurface.selectedFiniteSupportOperatorSubtractionCertifiedSupport`
- `DASHI.Physics.Closure.G3P2LimitConvergenceSurface.selectedFiniteSupportOperatorSubtractionSupportWitnessFromCertified`
- `DASHI.Physics.Closure.G3P2LimitConvergenceSurface.G3SelectedSubtractionCertifiedSupport`

The paper-facing statement is:

> For selected constructive finite-support operators, subtraction has certified
> finite-support evidence. This gives a bounded operator class suitable for
> further filtration and norm-law work.

This is real progress toward a contraction story because subtraction support is
one of the basic closure requirements for a filtered operator calculus. It
keeps finite matrix-level reasoning inside a witnessed support boundary rather
than relying on an arbitrary `WaveFunctionOperator` support theorem.

However, the associated-graded quotient is not closed. The paper must
distinguish a filtered prequotient surface from an actual quotient carrier. A
genuine associated graded layer requires classes of the form
`F_n / F_{n-1}` under the current increasing-filtration convention, together
with the kernel-equivalence law:

```text
[x] = [0]  iff  x lies in the denominator filtration piece.
```

Without that equivalence, quotient notation is only a target shape. The missing
infrastructure includes the accepted equivalence modulo the denominator
filtration, the accepted quotient carrier, projection-respects-equivalence, and
the descended norm, bracket, and isomorphism laws needed for a genuine
associated-graded contraction statement.

The current G3 blockers therefore remain substantive:

- arbitrary `WaveFunctionOperator` finite support is blocked at
  `DASHI.Physics.Closure.G3P2LimitConvergenceSurface.missingGlobalFiniteNonzeroMatrixSupportWitness`;
- the norm and valuation laws remain blocked at
  `DASHI.Physics.Closure.G3P2LimitConvergenceSurface.exactRemainingDifferenceNormLawBlockers`;
- the first named missing selected-operator norm-index law remains
  `DASHI.Physics.Closure.G3P2LimitConvergenceSurface.missingSelectedOperatorDifferenceNormIndexLaws`;
- associated-graded quotient closure remains blocked until the quotient
  carrier, kernel-equivalence law, projection-respects-equivalence, and
  descended norm/bracket/isomorphism laws are inhabited.

Consequently, Paper 1 may report selected finite-support subtraction support
and the exact associated-graded quotient gap. It may not claim global
Schrodinger promotion, arbitrary operator finite support, norm-law closure,
rational-difference ultrametric closure, product support, bracket support, or a
completed Galilei contraction theorem.

## 4.4 G6: Official Tracked Cross-Lane Commuting

The G6 lane records cross-lane independence inside the prime-coordinate carrier.
The paper-facing abstraction is simple: when two tracked coordinate actions
operate on independent prime lanes, the official tracked route has a checked
commuting theorem. This is the kind of compositionality a constructive
unification carrier needs. It says that selected lane actions can coexist
without silently interfering with each other.

The positive surface is
`DASHI.Physics.Closure.G6CrossLaneCommutingTheorem.canonicalG6OfficialTrackedCrossLaneCommutingTheorem`.
The tracked above-threshold consumer surface is
`DASHI.Physics.Closure.G6AboveThresholdIndependence.canonicalG6OfficialTrackedAboveThresholdCoordinateIndependence`.

The admissible claim is:

> A nontrivial tracked `GL.FactorVec` lane-action route has an official tracked
> cross-lane commuting theorem, and above-threshold coordinate independence is
> available on the same official tracked route.

This should be presented as a positive compositional theorem for the official
tracked interface. It is stronger than a diagrammatic intuition about
independent coordinates, because it is tied to an inhabited theorem surface.

The old full `LaneOperator` interface is not promoted. Its universal vanished
prime identity law blocks the nontrivial scaling route that the tracked theorem
uses. The relevant obstruction surfaces include
`DASHI.Physics.Closure.G6CrossLaneCommutingTheorem.g6LaneOperatorUniversalVanishesIdentityObstruction`
and the remaining full-G6 blockers recorded by
`DASHI.Physics.Closure.G6CrossLaneCommutingTheorem.G6OfficialTrackedCrossLaneCommutingTheorem.remainingFullG6Blockers`.

The distinction is not editorial. It prevents a true tracked theorem from being
laundered into a stronger universal operator theorem. Paper 1 may claim the
official tracked cross-lane commuting theorem and tracked above-threshold
coordinate independence. It must not claim old universal `LaneOperator`
promotion, full G6 closure, or downstream physics closure from G6 alone.

## 4.5 E8/LILA: Local Completeness and Upstream Promotion Boundary

The E8/LILA lane should be presented as a finite root-enumeration and promotion
boundary, not as a completed E8-to-physics derivation. The positive local
surface concerns integer/two-sparse completeness and local semantic structure.
The stronger upstream completion remains owned by the upstream
`E8RootEnumerationComplete` boundary.

The positive and boundary surfaces are:

- `DASHI.Algebra.Trit.E8RootEnumeration.integerIndexedRootsCompleteForTwoSparseShapeTheorem`
- `DASHI.Algebra.Trit.E8RootEnumeration.canonicalE8RootEnumerationCompletePromotionBoundary`
- `DASHI.Physics.Closure.LilaE8RootEnumerationNoDuplicatesSurface.canonicalE8UpstreamCompleteReceiptPromotionAudit`

The admissible paper claim is:

> Integer completeness and local semantic E8/LILA structure may be reported,
> with upstream completion explicitly blocked.

This lets the manuscript use E8/LILA as a structured finite-enumeration
surface in the formal carrier. It also makes the promotion boundary visible:
local semantic completeness does not automatically construct the upstream
receipt.

The blocked upstream surface is recorded by
`DASHI.Physics.Closure.LilaE8RootEnumerationNoDuplicatesSurface.missingPromotionFromLocalSemanticFiniteCompletenessToUpstreamCompleteReceipt`
and
`DASHI.Physics.Closure.LilaE8RootEnumerationNoDuplicatesSurface.missingUpstreamE8RootEnumerationCompletePromotion`.
The outstanding upstream payload includes the half-indexed even-parity theorem,
the combined indexed-root theorem, enumeration completeness, and the
constructor payload for upstream `E8RootEnumerationComplete`.

Paper 1 may therefore describe local integer completeness and the exact
upstream-promotion audit. It must not claim upstream
`E8RootEnumerationComplete`, E8-derived Standard Model recovery, limited SM+GR,
GRQFT closure, or completed unification from E8 structure.

## 4.6 Why These Four Lanes Belong in a Physics-Unification Paper

The formal core is physics-unification oriented because each lane supplies part
of the architecture needed for a constructive unification program:

- G2 gives the carrier a checked local geometric schema.
- G3 gives the operator side a selected finite-support filtration surface and
  names the exact quotient gap.
- G6 gives the prime-coordinate carrier a checked tracked commuting route.
- E8/LILA gives the finite root-enumeration side a local completeness surface
  while preserving upstream ownership.

Typed governance is not a separate topic placed beside this physics program.
It is the enforcement mechanism that keeps the unification claim honest. The
same formal system that records an inhabited schema or theorem also records the
missing quotient, blocked operator interface, upstream promotion gap, and
forbidden physical inference. That is the constructive posture of Paper 1: the
unification architecture is advanced through inhabited surfaces, while the
frontier remains typed rather than rhetorical.

## 4.7 Formal-Core Claim Boundary

The formal core supports the following positive inventory and no more:

| Lane | Paper-positive claim | Not claimed |
|---|---|---|
| G2 | Direction-indexed SFGC schema adoption for current core-facing consumers | Maxwell closure, gauge dynamics recovery, empirical calibration |
| G3 | Selected finite-support subtraction support | Associated-graded quotient closure, global Schrodinger promotion, arbitrary operator support |
| G6 | Official tracked cross-lane commuting and tracked above-threshold independence | Old universal `LaneOperator` promotion, full G6 closure |
| E8/LILA | Integer/two-sparse completeness plus local/upstream promotion audit | Upstream `E8RootEnumerationComplete`, E8-to-physics promotion |

All later physical interpretations must pass through their own surfaces:
accepted W3 empirical authority, W4/W5 convention authority, W4 physical
calibration, GR non-flat adapter receipts, stress-energy construction,
continuum scaling, and empirical validation receipts. None of those are
supplied by the four formal-core lanes alone.

## 4.8 Missing References and Uncertain Wording

- I did not find an existing `22_formal_core_draft.md`; this file is a new
  lane-owned draft.
- This draft cites the current claim-ledger and gate-status surfaces for the
  four required lanes. It does not independently revalidate the Agda modules.
- The phrase "G2 discrete gauge schema" is used as a schema/interface phrase,
  not as a field-equation or Maxwell-closure claim. The integrator should keep
  that qualifier if the section is shortened.
- The G3 quotient denominator is described using the current
  increasing-filtration convention `F_n / F_{n-1}`. If the final manuscript
  switches to a descending-filtration convention, the denominator wording
  should be adjusted while preserving the same kernel-equivalence obligation.
- The E8/LILA subsection deliberately avoids saying "E8 complete"; it says
  local integer/two-sparse completeness and upstream promotion blocked.

## 4.9 Compact O/R/C/S/L/P/G/F Summary

O: Worker Lane 2 drafted the formal-core manuscript lane; the parent
orchestrator owns integration.

R: The draft presents G2, G3, G6, and E8/LILA as physics-unification formal
surfaces with exact positive claims and exact blockers.

C: Read `ClaimLedger.md`, `03_formal_core.md`, `09_abstraction_layer.md`,
`10_g3_graded_quotient_gap.md`, `Docs/CurrentGateStatus.md`, and `README.md`.
Wrote only `Docs/PaperDraftWorkingFolder/sections/22_formal_core_draft.md`.

S: Existing source material was ledger-style and repo-internal; this draft
normalizes it into paper-facing prose for external readers.

L: Each lane is ordered as internal label, mathematical abstraction, allowed
claim, and blocked promotion.

P: Integrate this as the main technical-body draft or use it to replace the
current terse formal-core section after the other paper lanes return.

G: The required constraints are preserved: G2 is schema adoption, not Maxwell
closure; G3 is selected finite-support subtraction support plus
associated-graded quotient gap; G6 is tracked theorem positive while old
`LaneOperator` remains blocked; E8/LILA is local/integer boundary positive
while upstream promotion remains blocked.

F: Remaining gaps are substantive, not editorial: G3 quotient infrastructure,
old G6 interface migration or law split, upstream E8 completion, and all W3,
W4/W5, GR, calibration, and empirical authority surfaces remain outside this
lane's positive claim inventory.
