{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanQuantitativeSubgapSpectralCoreRound301Exact where

------------------------------------------------------------------------
-- ROUND301 / DIRECT MODE-INDEXED SUBGAP CONTRADICTION
--
-- The first draft tried to compile R300 back into the historical R288 interface
--
--   subgapSpectralEnvelope : Energy -> Observable -> Time -> Bound.
--
-- That interface is too broad for the canonical spectral argument.  The lower
-- component is naturally indexed by an alleged subgap MODE and the observable
-- is then chosen from that mode by positive-time cyclicity.  There is no honest
-- Observable -> mode inverse, so do not invent one.
--
-- Instead consume exactly what the terminal contradiction needs:
--
--   continuum upper at the cyclic observable,
--   exact positive spectral component lower from R300,
--   1/2 < q_E < 1 for every alleged positive subgap mode,
--   standard rational geometric domination.
--
-- Then one finite time gives
--
--   lower <= correlation <= upper < lower,
--
-- contradiction.  The old arbitrary-observable subgap-envelope object is a
-- derived presentation, not primitive proof debt on this route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (fst; snd)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _*_; _≤_; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanSubgapGeometricSeparationRound293Exact as R293
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record ModeIndexedSubgapRateSemantics
    {Measure TestObservable Energy Vector : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (quantitative : R299.QuantitativePositiveTimeVacuumCyclicity
      TestObservable Vector)
    (family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative))
    (decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family) : Set₁ where
  field
    gapCandidate : Energy
    PositiveEnergy : Energy → Set
    StrictlyBelow : Energy → Energy → Set

    positiveSubgapHasSlowerRatio :
      ∀ energy (mode : R297.SubgapMode family energy) →
      PositiveEnergy energy →
      StrictlyBelow energy gapCandidate →
      Geo.half < R300.subgapRatio decomposition energy mode

    subgapRatioStrictlyBelowOne :
      ∀ energy (mode : R297.SubgapMode family energy) →
      R300.subgapRatio decomposition energy mode < 1ℚ

open ModeIndexedSubgapRateSemantics public

ContinuumSelectedCorrelationUpper :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)} →
  R300.PositiveSpectralComponentDecomposition
    dataSet extension tests quantitative family → Set
ContinuumSelectedCorrelationUpper {dataSet = dataSet} {extension = extension}
    {tests = tests} decomposition =
  ∀ observable time →
    R278.connectedCovarianceMagnitude extension
      (Gram.continuumMeasure dataSet)
      (R278.left tests (R300.indexFor decomposition observable time))
      (R278.right tests (R300.indexFor decomposition observable time))
    ≤ Shell.quarter * Power.rationalPower Geo.half time

noPositiveSubgapModeFromPositiveComponent :
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
  (rates : ModeIndexedSubgapRateSemantics
    dataSet extension tests quantitative family decomposition) →
  ContinuumSelectedCorrelationUpper decomposition →
  ∀ energy (mode : R297.SubgapMode family energy) →
  PositiveEnergy rates energy →
  StrictlyBelow rates energy (gapCandidate rates) →
  Gap.Empty
noPositiveSubgapModeFromPositiveComponent
    {family = family} {decomposition = decomposition}
    dominance rates upper energy mode positive below =
  let
    observable =
      R297.modeObservableFromActualNonzeroFamily family energy mode
    weight = R300.selectedOverlapWeight decomposition energy mode
    ratio = R300.subgapRatio decomposition energy mode
    witness = R293.eventuallySlowDominatesFast dominance
      Shell.quarter weight ratio
      R274.quarterNonnegative
      (R300.selectedOverlapWeightPositive decomposition energy mode)
      (positiveSubgapHasSlowerRatio rates energy mode positive below)
      (subgapRatioStrictlyBelowOne rates energy mode)
    time = fst witness
    upperStrictlyBelowLower = snd witness
    lowerBelowCorrelation =
      R300.spectralComponentBelowCorrelation decomposition energy mode time
    correlationBelowUpper = upper observable time
  in
  R293.strictSandwichImpossible
    lowerBelowCorrelation correlationBelowUpper upperStrictlyBelowLower

record Round301Boundary : Set where
  constructor round301-boundary
  field
    arbitraryObservableSubgapEnvelopePrimitive : Bool
    arbitraryObservableSubgapEnvelopePrimitiveIsFalse :
      arbitraryObservableSubgapEnvelopePrimitive ≡ false

    separatePositiveOverlapAmplitudeLeaf : Bool
    separatePositiveOverlapAmplitudeLeafIsFalse :
      separatePositiveOverlapAmplitudeLeaf ≡ false

    separateSpectralLowerInequalityLeaf : Bool
    separateSpectralLowerInequalityLeafIsFalse :
      separateSpectralLowerInequalityLeaf ≡ false

    opaqueSeparatingTimeLeaf : Bool
    opaqueSeparatingTimeLeafIsFalse : opaqueSeparatingTimeLeaf ≡ false

    sameHamiltonianSpectralDecompositionStillPhysical : Bool
    sameHamiltonianSpectralDecompositionStillPhysicalIsTrue :
      sameHamiltonianSpectralDecompositionStillPhysical ≡ true

    energyToDecayOrderingStillPhysical : Bool
    energyToDecayOrderingStillPhysicalIsTrue :
      energyToDecayOrderingStillPhysical ≡ true

canonicalRound301Boundary : Round301Boundary
canonicalRound301Boundary =
  round301-boundary false refl false refl false refl false refl true refl true refl

round301ModeIndexedSubgapContradictionCompilerLevel : ProofLevel
round301ModeIndexedSubgapContradictionCompilerLevel = machineChecked

round301SameHamiltonianPositiveSpectralDecompositionLevel : ProofLevel
round301SameHamiltonianPositiveSpectralDecompositionLevel =
  R300.round300SameHamiltonianPositiveSpectralDecompositionLevel

round301PhysicalEnergyToDecayOrderingLevel : ProofLevel
round301PhysicalEnergyToDecayOrderingLevel = conditional
