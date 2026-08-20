module DASHI.Physics.YangMills.Balaban1989BetaDrivenCanonicalYM4StateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
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
-- Complete the same-state composition:
--
--   finite beta history
--      -> beta-driven CMP122 effective-density flow
--      -> canonical Section-2 scalar coordinates
--      -> repository YM4RGState.
--
-- The running-coupling coordinate is definitionally the CMP122 source coupling,
-- which is definitionally the beta-history coupling.  The other five state
-- coordinates are extracted from the SAME Section-2 density.  Therefore the
-- published complete-density theorem yields repository invariant-region
-- membership without a second coupling history or an independently supplied
-- coupling-cap implication.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Source
import DASHI.Physics.YangMills.Balaban1989CanonicalYM4StateFromSection2Exact as Canonical
import DASHI.Physics.YangMills.BalabanYM4RGInvariantRegionPhysicalGapExact as RG

record BetaDrivenCanonicalSection2Coordinates
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    (inputs : BetaFlow.BetaDrivenCompleteDensityInputs {trajectory} {split})
    (parameters : RG.YM4RGRegionParameters) : Set₁ where
  field
    gammaInsideRepositoryCap :
      History.gamma (BetaFlow.betaHistory inputs) ≤ RG.couplingCap parameters

    smallFieldCoordinate : Nat → ℚ
    largeFieldCoordinate : Nat → ℚ
    covarianceCoordinate : Nat → ℚ
    latticeDecayCoordinate : Nat → ℚ
    inverseSpacingCoordinate : Nat → ℚ

    section2SmallFieldBound : ∀ scale →
      Source.Section2ConditionsAndBounds
        (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale
        (Source.densityAt (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale) →
      smallFieldCoordinate scale ≤ RG.smallFieldCap parameters

    section2LargeFieldBound : ∀ scale →
      Source.Section2ConditionsAndBounds
        (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale
        (Source.densityAt (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale) →
      largeFieldCoordinate scale ≤ RG.largeFieldCap parameters

    section2CovarianceBound : ∀ scale →
      Source.Section2ConditionsAndBounds
        (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale
        (Source.densityAt (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale) →
      covarianceCoordinate scale ≤ RG.covarianceCap parameters

    section2DecayNonnegative : ∀ scale →
      Source.Section2ConditionsAndBounds
        (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale
        (Source.densityAt (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale) →
      0ℚ ≤ latticeDecayCoordinate scale

    sourceInverseSpacingNonnegative : ∀ scale →
      0ℚ ≤ inverseSpacingCoordinate scale

open BetaDrivenCanonicalSection2Coordinates public

canonicalCoordinates :
  ∀ {trajectory split inputs parameters} →
  BetaDrivenCanonicalSection2Coordinates
    {trajectory} {split} inputs parameters →
  Canonical.Section2CanonicalYM4Coordinates
    {flow = BetaFlow.betaDrivenCompleteDensityFlow inputs} parameters
canonicalCoordinates {inputs = inputs} dataSet = record
  { Canonical.Section2CanonicalYM4Coordinates.couplingCoordinate =
      History.couplingAt (BetaFlow.betaHistory inputs)
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
      λ scale _ →
        ℚP.≤-trans
          (BetaFlow.sourceSmallnessIsDerivedFromBetaHistory inputs scale)
          (gammaInsideRepositoryCap dataSet)
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

canonicalRunningCouplingIsSourceAndBeta :
  ∀ {trajectory split inputs parameters}
    (dataSet : BetaDrivenCanonicalSection2Coordinates
      {trajectory} {split} inputs parameters)
    scale →
  RG.runningCoupling
    (Canonical.canonicalYM4State (canonicalCoordinates dataSet) scale)
  ≡ Source.couplingAt (BetaFlow.betaDrivenCompleteDensityFlow inputs) scale
canonicalRunningCouplingIsSourceAndBeta dataSet scale = refl

betaDrivenCMP122TheoremGivesRepositoryInvariantRegion :
  ∀ {trajectory split inputs parameters}
    (dataSet : BetaDrivenCanonicalSection2Coordinates
      {trajectory} {split} inputs parameters)
    (theorem1 : Source.Balaban1989Theorem1Witness
      (BetaFlow.betaDrivenCompleteDensityFlow inputs))
    scale →
  RG.InYM4RGInvariantRegion parameters
    (Canonical.canonicalYM4State (canonicalCoordinates dataSet) scale)
betaDrivenCMP122TheoremGivesRepositoryInvariantRegion dataSet theorem1 =
  Canonical.sourceTheoremGivesCanonicalYM4InvariantRegion
    (canonicalCoordinates dataSet) theorem1

balabanBetaDrivenCanonicalStateLevel : ProofLevel
balabanBetaDrivenCanonicalStateLevel = machineChecked

balabanBetaDrivenCMP122ToRepositoryRegionLevel : ProofLevel
balabanBetaDrivenCMP122ToRepositoryRegionLevel = machineChecked
