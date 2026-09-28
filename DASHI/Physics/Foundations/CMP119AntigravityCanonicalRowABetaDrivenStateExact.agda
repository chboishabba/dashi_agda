{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowABetaDrivenStateExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowARegionParametersExact as Region
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCanonicalYM4StateExact as Canonical
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Source
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4RGInvariantRegionPhysicalGapExact as RG

------------------------------------------------------------------------
-- SAME-OBJECT S4a STATE CONSTRUCTOR
--
-- The preferred antigravity/CMP119 beta-driven state is built directly with
-- the canonical Row-A coupling cap.  Callers provide the physically meaningful
-- inequality
--
--   history gamma <= canonical Row-A gamma,
--
-- rather than an unrelated repository cap plus a later equality proof.
------------------------------------------------------------------------

record CanonicalRowABetaDrivenCoordinates
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (inputs : BetaFlow.BetaDrivenCompleteDensityInputs {trajectory} {split})
    (rowA : RowA.FiniteQuarticResponseConstants)
    (smallFieldCap largeFieldCap covarianceCap : ℚ) : Set₁ where
  field
    historyGammaBelowCanonicalRowA :
      History.gamma (BetaFlow.betaHistory inputs)
      ≤ RowA.canonicalQuarticResponseGamma rowA

    smallFieldCoordinate : Nat → ℚ
    largeFieldCoordinate : Nat → ℚ
    covarianceCoordinate : Nat → ℚ
    latticeDecayCoordinate : Nat → ℚ
    inverseSpacingCoordinate : Nat → ℚ

    section2SmallFieldBound : ∀ scale →
      Source.Section2ConditionsAndBounds
        (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale
        (Source.densityAt (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale) →
      smallFieldCoordinate scale ≤ smallFieldCap

    section2LargeFieldBound : ∀ scale →
      Source.Section2ConditionsAndBounds
        (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale
        (Source.densityAt (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale) →
      largeFieldCoordinate scale ≤ largeFieldCap

    section2CovarianceBound : ∀ scale →
      Source.Section2ConditionsAndBounds
        (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale
        (Source.densityAt (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale) →
      covarianceCoordinate scale ≤ covarianceCap

    section2DecayNonnegative : ∀ scale →
      Source.Section2ConditionsAndBounds
        (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale
        (Source.densityAt (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale) →
      0ℚ ≤ latticeDecayCoordinate scale

    sourceInverseSpacingNonnegative : ∀ scale →
      0ℚ ≤ inverseSpacingCoordinate scale

open CanonicalRowABetaDrivenCoordinates public

preferredParameters :
  (rowA : RowA.FiniteQuarticResponseConstants) →
  (smallFieldCap largeFieldCap covarianceCap : ℚ) →
  RG.YM4RGRegionParameters
preferredParameters rowA smallFieldCap largeFieldCap covarianceCap =
  Region.canonicalRowARegionParameters
    rowA smallFieldCap largeFieldCap covarianceCap

asBetaDrivenCanonicalCoordinates :
  ∀ {trajectory split inputs rowA smallFieldCap largeFieldCap covarianceCap} →
  CanonicalRowABetaDrivenCoordinates
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap →
  Canonical.BetaDrivenCanonicalSection2Coordinates
    {trajectory = trajectory} {split = split}
    inputs
    (preferredParameters rowA smallFieldCap largeFieldCap covarianceCap)
asBetaDrivenCanonicalCoordinates dataSet = record
  { Canonical.BetaDrivenCanonicalSection2Coordinates.gammaInsideRepositoryCap =
      historyGammaBelowCanonicalRowA dataSet
  ; Canonical.BetaDrivenCanonicalSection2Coordinates.smallFieldCoordinate =
      smallFieldCoordinate dataSet
  ; Canonical.BetaDrivenCanonicalSection2Coordinates.largeFieldCoordinate =
      largeFieldCoordinate dataSet
  ; Canonical.BetaDrivenCanonicalSection2Coordinates.covarianceCoordinate =
      covarianceCoordinate dataSet
  ; Canonical.BetaDrivenCanonicalSection2Coordinates.latticeDecayCoordinate =
      latticeDecayCoordinate dataSet
  ; Canonical.BetaDrivenCanonicalSection2Coordinates.inverseSpacingCoordinate =
      inverseSpacingCoordinate dataSet
  ; Canonical.BetaDrivenCanonicalSection2Coordinates.section2SmallFieldBound =
      section2SmallFieldBound dataSet
  ; Canonical.BetaDrivenCanonicalSection2Coordinates.section2LargeFieldBound =
      section2LargeFieldBound dataSet
  ; Canonical.BetaDrivenCanonicalSection2Coordinates.section2CovarianceBound =
      section2CovarianceBound dataSet
  ; Canonical.BetaDrivenCanonicalSection2Coordinates.section2DecayNonnegative =
      section2DecayNonnegative dataSet
  ; Canonical.BetaDrivenCanonicalSection2Coordinates.sourceInverseSpacingNonnegative =
      sourceInverseSpacingNonnegative dataSet
  }

preferredRepositoryCapIsCanonicalRowA :
  (rowA : RowA.FiniteQuarticResponseConstants) →
  (smallFieldCap largeFieldCap covarianceCap : ℚ) →
  RG.couplingCap
    (preferredParameters rowA smallFieldCap largeFieldCap covarianceCap)
  ≡ RowA.canonicalQuarticResponseGamma rowA
preferredRepositoryCapIsCanonicalRowA rowA smallFieldCap largeFieldCap covarianceCap =
  refl

postHocRepositoryCapEqualityRequired : Bool
postHocRepositoryCapEqualityRequired = false

postHocRepositoryCapEqualityRequiredIsFalse :
  postHocRepositoryCapEqualityRequired ≡ false
postHocRepositoryCapEqualityRequiredIsFalse = refl
