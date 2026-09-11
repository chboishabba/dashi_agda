{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanAmplitudeAwareModeSelectedSubgapRound341Exact where

------------------------------------------------------------------------
-- ROUND341 / AMPLITUDE-AWARE MODE-SELECTED SUBGAP CONTRADICTION
--
-- R301 specialized the fast clustering envelope to
--
--     (1/4) * (1/2)^t.
--
-- The underlying R294 geometric-dominance theorem is already parameterized by
-- an arbitrary nonnegative fast amplitude.  The spectral consumer therefore
-- does not need the unit/configured Step-V normalization.  A finite observable-
-- dependent amplitude survives unchanged:
--
--     Corr_selected(O,t) <= C(O) * (1/2)^t,   C(O) >= 0.
--
-- This owner is only the least-privilege compiler.  It creates no clustering
-- estimate and no spectral decomposition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (fst; snd)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanQuantitativeSubgapSpectralCoreRound301Exact as R301
import DASHI.Physics.YangMills.BalabanSubgapGeometricSeparationRound294Exact as R294
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

AmplitudeSelectedCorrelationUpper :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)} →
  (decomposition : R300.PositiveSpectralComponentDecomposition
    dataSet extension tests quantitative family) →
  (fastAmplitude : TestObservable → ℚ) → Set
AmplitudeSelectedCorrelationUpper
    {dataSet = dataSet} {extension = extension} {tests = tests}
    decomposition fastAmplitude =
  ∀ observable time →
    R278.connectedCovarianceMagnitude extension
      (Gram.continuumMeasure dataSet)
      (R278.left tests (R300.indexFor decomposition observable time))
      (R278.right tests (R300.indexFor decomposition observable time))
    ≤ fastAmplitude observable * Power.rationalPower Geo.half time

noPositiveSubgapModeFromAmplitudeUpper :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family} →
  R294.RationalGeometricDominance →
  (rates : R301.ModeIndexedSubgapRateSemantics
    dataSet extension tests quantitative family decomposition) →
  (fastAmplitude : TestObservable → ℚ) →
  (∀ observable → 0ℚ ≤ fastAmplitude observable) →
  AmplitudeSelectedCorrelationUpper decomposition fastAmplitude →
  ∀ energy (mode : R297.SubgapMode family energy) →
  R301.PositiveEnergy rates energy →
  R301.StrictlyBelow rates energy (R301.gapCandidate rates) →
  Gap.Empty
noPositiveSubgapModeFromAmplitudeUpper
    {family = family} {decomposition = decomposition}
    dominance rates fastAmplitude fastAmplitudeNonnegative upper
    energy mode positive below =
  let
    observable =
      R297.modeObservableFromActualNonzeroFamily family energy mode
    weight = R300.selectedOverlapWeight decomposition energy mode
    ratio = R300.subgapRatio decomposition energy mode
    witness = R294.eventuallySlowDominatesFast dominance
      (fastAmplitude observable) weight ratio
      (fastAmplitudeNonnegative observable)
      (R300.selectedOverlapWeightPositive decomposition energy mode)
      (R301.positiveSubgapHasSlowerRatio rates energy mode positive below)
      (R301.subgapRatioStrictlyBelowOne rates energy mode)
    time = fst witness
    upperStrictlyBelowLower = snd witness
    lowerBelowCorrelation =
      R300.spectralComponentBelowCorrelation decomposition energy mode time
    correlationBelowUpper = upper observable time
  in
  R294.strictSandwichImpossible
    lowerBelowCorrelation correlationBelowUpper upperStrictlyBelowLower

record Round341Boundary : Set where
  constructor round341-boundary
  field
    quarterAmplitudeMandatoryForSubgapContradiction : Bool
    quarterAmplitudeMandatoryForSubgapContradictionIsFalse :
      quarterAmplitudeMandatoryForSubgapContradiction ≡ false

    arbitraryFiniteNonnegativeFastAmplitudeSupported : Bool
    arbitraryFiniteNonnegativeFastAmplitudeSupportedIsTrue :
      arbitraryFiniteNonnegativeFastAmplitudeSupported ≡ true

    fastDecayRatioStillHalf : Bool
    fastDecayRatioStillHalfIsTrue : fastDecayRatioStillHalf ≡ true

    newYMAnalyticEstimateIntroduced : Bool
    newYMAnalyticEstimateIntroducedIsFalse :
      newYMAnalyticEstimateIntroduced ≡ false

canonicalRound341Boundary : Round341Boundary
canonicalRound341Boundary =
  round341-boundary false refl true refl true refl false refl

round341AmplitudeAwareSubgapCompilerLevel : ProofLevel
round341AmplitudeAwareSubgapCompilerLevel = machineChecked

round341GeometricDominanceAuthorityLevel : ProofLevel
round341GeometricDominanceAuthorityLevel = R294.round294RationalGeometricDominanceLevel

round341PhysicalRateSemanticsLevel : ProofLevel
round341PhysicalRateSemanticsLevel = R301.round301PhysicalEnergyToDecayOrderingLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
