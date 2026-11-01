module DASHI.Physics.YangMills.Balaban1989BetaHistoryToCanonicalCompleteDensityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Make the beta-produced coupling history and the CMP119/CMP122 complete-density
-- state literally the SAME state coordinate.  The running-coupling field of
-- the canonical repository state is definitionally the couplingAt function
-- from the finite beta history.  Therefore the beta theorem supplies the
-- coupling cap while the remaining five coordinates come from the same
-- Sect.-2 density bounds.  There is no parallel RG trajectory to reconcile.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Source
import DASHI.Physics.YangMills.Balaban1989CanonicalYM4StateFromSection2Exact as Canonical
import DASHI.Physics.YangMills.Balaban1989CompleteDensityToYM4RegionExact as Complete
import DASHI.Physics.YangMills.BalabanYM4RGInvariantRegionPhysicalGapExact as RG

record BetaHistorySection2Coordinates
    {Coupling Density : Set}
    {flow : Source.Balaban1989EffectiveDensityFlow Coupling Density}
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (parameters : RG.YM4RGRegionParameters) : Set₁ where
  field
    betaHistory : History.BetaSplitInverseSquareTerminalHistoryData trajectory split

    -- Every source scale represented by this finite complete-density flow is
    -- one of the active beta-history scales.
    sourceScaleActive : ∀ scale → History.ActiveScale betaHistory scale

    -- The source's small-coupling threshold is inside the repository cap.
    gammaInsideRepositoryCap :
      History.gamma betaHistory ≤ RG.couplingCap parameters

    smallFieldCoordinate : Nat → ℚ
    largeFieldCoordinate : Nat → ℚ
    covarianceCoordinate : Nat → ℚ
    latticeDecayCoordinate : Nat → ℚ
    inverseSpacingCoordinate : Nat → ℚ

    section2SmallFieldBound : ∀ scale →
      Source.Section2ConditionsAndBounds flow scale (Source.densityAt flow scale) →
      smallFieldCoordinate scale ≤ RG.smallFieldCap parameters

    section2LargeFieldBound : ∀ scale →
      Source.Section2ConditionsAndBounds flow scale (Source.densityAt flow scale) →
      largeFieldCoordinate scale ≤ RG.largeFieldCap parameters

    section2CovarianceBound : ∀ scale →
      Source.Section2ConditionsAndBounds flow scale (Source.densityAt flow scale) →
      covarianceCoordinate scale ≤ RG.covarianceCap parameters

    section2DecayNonnegative : ∀ scale →
      Source.Section2ConditionsAndBounds flow scale (Source.densityAt flow scale) →
      0ℚ ≤ latticeDecayCoordinate scale

    sourceInverseSpacingNonnegative : ∀ scale →
      0ℚ ≤ inverseSpacingCoordinate scale

open BetaHistorySection2Coordinates public

betaCouplingAt :
  ∀ {Coupling Density flow trajectory split parameters} →
  BetaHistorySection2Coordinates
    {Coupling} {Density} {flow} {trajectory} {split} parameters →
  Nat → ℚ
betaCouplingAt dataSet = History.couplingAt (betaHistory dataSet)

betaHistoryGivesRepositoryCouplingCap :
  ∀ {Coupling Density flow trajectory split parameters}
    (dataSet : BetaHistorySection2Coordinates
      {Coupling} {Density} {flow} {trajectory} {split} parameters)
    scale →
  betaCouplingAt dataSet scale ≤ RG.couplingCap parameters
betaHistoryGivesRepositoryCouplingCap dataSet scale =
  ℚP.≤-trans
    (History.smallCouplingAtEveryActiveScale
      (betaHistory dataSet) scale (sourceScaleActive dataSet scale))
    (gammaInsideRepositoryCap dataSet)

canonicalCoordinatesFromBetaHistory :
  ∀ {Coupling Density flow trajectory split parameters} →
  BetaHistorySection2Coordinates
    {Coupling} {Density} {flow} {trajectory} {split} parameters →
  Canonical.Section2CanonicalYM4Coordinates {flow = flow} parameters
canonicalCoordinatesFromBetaHistory dataSet = record
  { Canonical.Section2CanonicalYM4Coordinates.couplingCoordinate =
      betaCouplingAt dataSet
  ; Canonical.Section2CanonicalYM4Coordinates.smallFieldCoordinate =
      smallFieldCoordinate dataSet
  ; Canonical.Section2CanonicalYM4Coordinates.largeFieldCoordinate =
      largeFieldCoordinate dataSet
  ; Canonical.Section2CanonicalYM4Coordinates.covarianceCoordinate =
      covarianceCoordinate dataSet
  ; Canonical.Section2CanonicalYM4Coordinates.latticeDecayCoordinate =
      latticeDecayCoordinate dataSet
  ; Canonical.Section2CanonicalYM4Coordinates.inverseSpacingCoordinate =
      inverseSpacingCoordinate dataSet
  ; Canonical.Section2CanonicalYM4Coordinates.section2FormCouplingBound =
      λ scale _ → betaHistoryGivesRepositoryCouplingCap dataSet scale
  ; Canonical.Section2CanonicalYM4Coordinates.section2SmallFieldBound =
      section2SmallFieldBound dataSet
  ; Canonical.Section2CanonicalYM4Coordinates.section2LargeFieldBound =
      section2LargeFieldBound dataSet
  ; Canonical.Section2CanonicalYM4Coordinates.section2CovarianceBound =
      section2CovarianceBound dataSet
  ; Canonical.Section2CanonicalYM4Coordinates.section2DecayNonnegative =
      section2DecayNonnegative dataSet
  ; Canonical.Section2CanonicalYM4Coordinates.sourceInverseSpacingNonnegative =
      sourceInverseSpacingNonnegative dataSet
  }

canonicalStateRunningCouplingIsBetaHistory :
  ∀ {Coupling Density flow trajectory split parameters}
    (dataSet : BetaHistorySection2Coordinates
      {Coupling} {Density} {flow} {trajectory} {split} parameters)
    scale →
  RG.runningCoupling
    (Canonical.canonicalYM4State
      (canonicalCoordinatesFromBetaHistory dataSet) scale)
  ≡ History.couplingAt (betaHistory dataSet) scale
canonicalStateRunningCouplingIsBetaHistory dataSet scale = refl

betaHistoryAndSourceTheoremGiveLiteralInvariantRegion :
  ∀ {Coupling Density flow trajectory split parameters}
    (dataSet : BetaHistorySection2Coordinates
      {Coupling} {Density} {flow} {trajectory} {split} parameters)
    (theorem1 : Source.Balaban1989Theorem1Witness flow)
    scale →
  RG.InYM4RGInvariantRegion parameters
    (Canonical.canonicalYM4State
      (canonicalCoordinatesFromBetaHistory dataSet) scale)
betaHistoryAndSourceTheoremGiveLiteralInvariantRegion dataSet theorem1 =
  Canonical.sourceTheoremGivesCanonicalYM4InvariantRegion
    (canonicalCoordinatesFromBetaHistory dataSet) theorem1

balabanBetaHistorySameStateCouplingLevel : ProofLevel
balabanBetaHistorySameStateCouplingLevel = machineChecked

balabanBetaHistoryToCanonicalCompleteDensityLevel : ProofLevel
balabanBetaHistoryToCanonicalCompleteDensityLevel = machineChecked
