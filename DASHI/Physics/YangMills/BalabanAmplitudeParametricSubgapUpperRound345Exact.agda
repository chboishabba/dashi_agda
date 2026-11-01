{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanAmplitudeParametricSubgapUpperRound345Exact where

------------------------------------------------------------------------
-- ROUND345 / REMOVE THE FIXED-1/4 FAST-AMPLITUDE OVERPAYMENT
--
-- R301 specialized the continuum clustering upper to
--
--       (1/4) * (1/2)^t.
--
-- That amplitude is sufficient but is not required by the spectral
-- contradiction.  R294's source-independent geometric-dominance theorem is
-- already parametric in an arbitrary nonnegative fast amplitude.  Therefore a
-- source-native CMP116 bound
--
--       A_H * (1/2)^t
--
-- is enough for the same positive-subgap contradiction for every finite
-- nonnegative A_H.  In particular A_H = (1/4) C_H needs C_H >= 0, not C_H <= 1.
--
-- This owner changes only the consumer interface.  It does not manufacture the
-- physical spectral decomposition, the energy-to-decay ordering, or a source
-- clustering theorem.
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
import DASHI.Physics.YangMills.BalabanSubgapGeometricSeparationRound293Exact as R293
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanQuantitativeSubgapSpectralCoreRound301Exact as R301
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

AmplitudeParametricContinuumSelectedCorrelationUpper :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)} →
  (decomposition : R300.PositiveSpectralComponentDecomposition
    dataSet extension tests quantitative family) →
  ℚ → Set
AmplitudeParametricContinuumSelectedCorrelationUpper
    {dataSet = dataSet} {extension = extension} {tests = tests}
    decomposition fastAmplitude =
  ∀ observable time →
    R278.connectedCovarianceMagnitude extension
      (Gram.continuumMeasure dataSet)
      (R278.left tests (R300.indexFor decomposition observable time))
      (R278.right tests (R300.indexFor decomposition observable time))
    ≤ fastAmplitude * Power.rationalPower Geo.half time

noPositiveSubgapModeFromAmplitudeParametricUpper :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family} →
  R293.RationalGeometricDominance →
  (rates : R301.ModeIndexedSubgapRateSemantics
    dataSet extension tests quantitative family decomposition) →
  (fastAmplitude : ℚ) →
  0ℚ ≤ fastAmplitude →
  AmplitudeParametricContinuumSelectedCorrelationUpper
    decomposition fastAmplitude →
  ∀ energy (mode : R297.SubgapMode family energy) →
  R301.PositiveEnergy rates energy →
  R301.StrictlyBelow rates energy (R301.gapCandidate rates) →
  Gap.Empty
noPositiveSubgapModeFromAmplitudeParametricUpper
    {family = family} {decomposition = decomposition}
    dominance rates fastAmplitude fastAmplitudeNN upper
    energy mode positive below =
  let
    observable =
      R297.modeObservableFromActualNonzeroFamily family energy mode
    weight = R300.selectedOverlapWeight decomposition energy mode
    ratio = R300.subgapRatio decomposition energy mode
    witness = R293.eventuallySlowDominatesFast dominance
      fastAmplitude weight ratio
      fastAmplitudeNN
      (R300.selectedOverlapWeightPositive decomposition energy mode)
      (R301.positiveSubgapHasSlowerRatio rates energy mode positive below)
      (R301.subgapRatioStrictlyBelowOne rates energy mode)
    time = fst witness
    upperStrictlyBelowLower = snd witness
    lowerBelowCorrelation =
      R300.spectralComponentBelowCorrelation decomposition energy mode time
    correlationBelowUpper = upper observable time
  in
  R293.strictSandwichImpossible
    lowerBelowCorrelation correlationBelowUpper upperStrictlyBelowLower

------------------------------------------------------------------------
-- Compatibility: R301's historical quarter-amplitude upper is one instance.
------------------------------------------------------------------------

fixedQuarterFastAmplitudeMandatory : Bool
fixedQuarterFastAmplitudeMandatory = false

fixedQuarterFastAmplitudeMandatoryIsFalse :
  fixedQuarterFastAmplitudeMandatory ≡ false
fixedQuarterFastAmplitudeMandatoryIsFalse = refl

arbitraryNonnegativeFastAmplitudeAccepted : Bool
arbitraryNonnegativeFastAmplitudeAccepted = true

arbitraryNonnegativeFastAmplitudeAcceptedIsTrue :
  arbitraryNonnegativeFastAmplitudeAccepted ≡ true
arbitraryNonnegativeFastAmplitudeAcceptedIsTrue = refl

hessianConstantAtMostOneRequiredBySpectralContradiction : Bool
hessianConstantAtMostOneRequiredBySpectralContradiction = false

hessianConstantAtMostOneRequiredBySpectralContradictionIsFalse :
  hessianConstantAtMostOneRequiredBySpectralContradiction ≡ false
hessianConstantAtMostOneRequiredBySpectralContradictionIsFalse = refl

record Round345Boundary : Set where
  constructor round345-boundary
  field
    fixedQuarterAmplitudeIndependentLeaf : Bool
    fixedQuarterAmplitudeIndependentLeafIsFalse :
      fixedQuarterAmplitudeIndependentLeaf ≡ false

    finiteNonnegativeFastAmplitudeSuffices : Bool
    finiteNonnegativeFastAmplitudeSufficesIsTrue :
      finiteNonnegativeFastAmplitudeSuffices ≡ true

    physicalSpectralDecompositionStillProofBearing : Bool
    physicalSpectralDecompositionStillProofBearingIsTrue :
      physicalSpectralDecompositionStillProofBearing ≡ true

    energyToDecayOrderingStillProofBearing : Bool
    energyToDecayOrderingStillProofBearingIsTrue :
      energyToDecayOrderingStillProofBearing ≡ true

canonicalRound345Boundary : Round345Boundary
canonicalRound345Boundary =
  round345-boundary false refl true refl true refl true refl

round345AmplitudeParametricSpectralCompilerLevel : ProofLevel
round345AmplitudeParametricSpectralCompilerLevel = machineChecked

round345SameHamiltonianPositiveSpectralDecompositionLevel : ProofLevel
round345SameHamiltonianPositiveSpectralDecompositionLevel =
  R301.round301SameHamiltonianPositiveSpectralDecompositionLevel

round345PhysicalEnergyToDecayOrderingLevel : ProofLevel
round345PhysicalEnergyToDecayOrderingLevel =
  R301.round301PhysicalEnergyToDecayOrderingLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
