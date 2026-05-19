# 3. Formal Core

This section records the internal theorem and receipt surface used by the
paper. The scope is deliberately narrow: a statement is treated as positive
only when it is tied inline to a named Agda module and surface. Constructorless
authority types, request templates, local shadows, and upstream-owned receipts
are reported as boundaries rather than promoted results.

## 3.1 G2 Direction-Indexed SFGC Schema Extension

The current core-facing G2 schema-extension claim is a schema-adoption claim,
not a field-equation or downstream recovery claim. Direction-indexed SFGC
schema adoption is complete for the current core-facing consumers at
`DASHI.Physics.Closure.G2SFGCGaugeFieldSchemaExtension.canonicalG2SFGCGaugeFieldSchemaExtensionReceipt`,
with the no-remaining-missing surface
`DASHI.Physics.Closure.G2SFGCGaugeFieldSchemaExtension.noRemainingG2SFGCSchemaExtensionMissing`.

The result should therefore be read as a typed interface update: the core
consumer side has adopted the direction-indexed SFGC schema, while legacy
right-only names remain compatibility surfaces. It does not imply Maxwell
recovery, G2 field-equation closure, limited SM+GR promotion, GRQFT promotion,
or unification.

## 3.2 G6 Tracked Cross-Lane Commuting

The paper-usable G6 result is the official tracked route. A nontrivial tracked
`GL.FactorVec` lane-action route has an official cross-lane commuting theorem
at
`DASHI.Physics.Closure.G6CrossLaneCommutingTheorem.canonicalG6OfficialTrackedCrossLaneCommutingTheorem`.
Above-threshold coordinate independence is available only on that official
tracked route at
`DASHI.Physics.Closure.G6AboveThresholdIndependence.canonicalG6OfficialTrackedAboveThresholdCoordinateIndependence`.

The old full `LaneOperator` interface is not promoted by this section. Its
obstruction is recorded at
`DASHI.Physics.Closure.G6CrossLaneCommutingTheorem.g6LaneOperatorUniversalVanishesIdentityObstruction`,
and the official tracked theorem records the remaining full-interface blockers
at
`DASHI.Physics.Closure.G6CrossLaneCommutingTheorem.G6OfficialTrackedCrossLaneCommutingTheorem.remainingFullG6Blockers`.
The boundary is substantive: the old interface's universal vanished-prime
identity law prevents using that interface as the nontrivial full-promotion
route. The admissible claim is tracked commuting and tracked above-threshold
coordinate independence, not old full `LaneOperator` promotion.

## 3.3 G3 Constructive Finite-Support Subtraction

The G3 positive surface is restricted to constructive finite-support selected
operators. Certified support for subtraction of that subtype is present at
`DASHI.Physics.Closure.G3P2LimitConvergenceSurface.selectedFiniteSupportOperatorSubtractionCertifiedSupport`.
The corresponding support witness is available from the certified surface at
`DASHI.Physics.Closure.G3P2LimitConvergenceSurface.selectedFiniteSupportOperatorSubtractionSupportWitnessFromCertified`,
and the certified-support record is
`DASHI.Physics.Closure.G3P2LimitConvergenceSurface.G3SelectedSubtractionCertifiedSupport`.

This is not a claim about arbitrary `WaveFunctionOperator` finite support.
The global arbitrary-operator support boundary remains
`DASHI.Physics.Closure.G3P2LimitConvergenceSurface.missingGlobalFiniteNonzeroMatrixSupportWitness`.
The valuation and norm-law portion remains blocked at
`DASHI.Physics.Closure.G3P2LimitConvergenceSurface.exactRemainingDifferenceNormLawBlockers`;
the first named missing law after the subtraction-support surface is
`DASHI.Physics.Closure.G3P2LimitConvergenceSurface.missingSelectedOperatorDifferenceNormIndexLaws`.

Consequently, this section does not claim witness-independent norm symmetry,
rational-difference ultrametric closure, p2 rescaling or min-shift closure,
finite-support product support, bracket support, or global Schrodinger
promotion. The constructive result is subtraction support for the selected
finite-support subtype, with the remaining norm and valuation laws left as
typed blockers.

## 3.4 E8 Integer Completeness and Local-to-Upstream Boundary

The E8 material is included as a local/upstream boundary, not as upstream
completion. Integer completeness for the two-sparse shape is present at
`DASHI.Algebra.Trit.E8RootEnumeration.integerIndexedRootsCompleteForTwoSparseShapeTheorem`.
The promotion boundary tying the local semantic finite surface to the upstream
receipt obstruction is recorded at
`DASHI.Algebra.Trit.E8RootEnumeration.canonicalE8RootEnumerationCompletePromotionBoundary`.
The upstream-complete promotion audit is recorded at
`DASHI.Physics.Closure.LilaE8RootEnumerationNoDuplicatesSurface.canonicalE8UpstreamCompleteReceiptPromotionAudit`.

The upstream completion itself is not claimed. The remaining upstream blocker
is
`DASHI.Physics.Closure.LilaE8RootEnumerationNoDuplicatesSurface.missingPromotionFromLocalSemanticFiniteCompletenessToUpstreamCompleteReceipt`,
reported under the upstream-completion boundary as
`DASHI.Physics.Closure.LilaE8RootEnumerationNoDuplicatesSurface.missingUpstreamE8RootEnumerationCompletePromotion`.
The outstanding upstream payload includes
`DASHI.Algebra.Trit.E8RootEnumeration.halfIndexedRootsCompleteForEvenParityShapeTheorem`,
`DASHI.Algebra.Trit.E8RootEnumeration.combinedIndexedRootsCompleteForE8ShapeTheorem`,
`DASHI.Algebra.Trit.E8RootEnumeration.enumerationIsComplete`, and the
constructor payload for upstream `E8RootEnumerationComplete`.

Thus the paper may describe integer completeness and the local semantic
finite-to-upstream obstruction wiring. It must not claim upstream
`E8RootEnumerationComplete`, downstream E8-to-physics promotion, limited
SM+GR, GRQFT closure, or unification from E8 structure.

## 3.5 Boundary Ledger

The formal core excludes the following as positive claims:

- Old full G6 `LaneOperator` promotion, blocked by
  `DASHI.Physics.Closure.G6CrossLaneCommutingTheorem.g6LaneOperatorUniversalVanishesIdentityObstruction`
  and
  `DASHI.Physics.Closure.G6CrossLaneCommutingTheorem.G6OfficialTrackedCrossLaneCommutingTheorem.remainingFullG6Blockers`.
- Arbitrary `WaveFunctionOperator` finite support, blocked at
  `DASHI.Physics.Closure.G3P2LimitConvergenceSurface.missingGlobalFiniteNonzeroMatrixSupportWitness`.
- G3 norm-law closure, blocked at
  `DASHI.Physics.Closure.G3P2LimitConvergenceSurface.exactRemainingDifferenceNormLawBlockers`
  and
  `DASHI.Physics.Closure.G3P2LimitConvergenceSurface.missingSelectedOperatorDifferenceNormIndexLaws`.
- Upstream E8 completion, blocked at
  `DASHI.Physics.Closure.LilaE8RootEnumerationNoDuplicatesSurface.missingPromotionFromLocalSemanticFiniteCompletenessToUpstreamCompleteReceipt`
  and
  `DASHI.Physics.Closure.LilaE8RootEnumerationNoDuplicatesSurface.missingUpstreamE8RootEnumerationCompletePromotion`.
- W2 natural p2-convergence promotion, because
  `DASHI.Physics.Closure.NaturalP2ConvergencePromotionObligation.NaturalP2ConvergencePromotionAuthorityToken`
  remains the required authority-token boundary.
- W3 accepted empirical authority, because
  `DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken`
  remains the required authority-token boundary.
- W4/W5 Drell-Yan convention authority and W4 physical calibration, because
  `DASHI.Physics.Closure.W4ZAdequacyReceipt.AcceptedDYLuminosityConventionAuthority`
  remains the required convention-authority boundary.
- Non-flat GR, sourced discrete Einstein tensor claims, Schwarzschild
  recovery, continuum scaling, limited SM+GR, GRQFT closure, and full
  unification; these remain outside the formal-core positive surface and
  require their own inhabited receipts or authority tokens before they can be
  stated as results.

## 3.6 Citation Gaps

No citation gap is known for the four positive surfaces used in this section:
G2 direction-indexed schema adoption, G6 official tracked commuting and
tracked above-threshold independence, G3 constructive finite-support
subtraction support, and E8 integer/local-to-upstream boundary all cite exact
module/surface names inline.

Known citation mismatch: `Docs/Paper1DraftSkeleton.md` names
`G6OfficialTrackedCrossLaneCommutingTheorem.obstructionForOldLaneOperator`,
but read-only inspection found the current Agda record field as
`DASHI.Physics.Closure.G6CrossLaneCommutingTheorem.G6OfficialTrackedCrossLaneCommutingTheorem.remainingFullG6Blockers`.
This section cites the current field and keeps the old-interface point as an
obstruction, not as a positive tracked theorem.

Potential manuscript integration gap: if the final paper text wants to make a
positive claim about any GR adapter, W2/W3/W4/W5 authority, old G6
`LaneOperator`, arbitrary `WaveFunctionOperator`, upstream E8 completion,
Maxwell recovery, physics calibration, limited SM+GR, GRQFT, or unification
surface, this section currently has no positive citation for it and should
continue to treat it as blocked.
