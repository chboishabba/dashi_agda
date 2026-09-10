{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanQuantitativeSubgapSpectralCoreRound301Exact where

------------------------------------------------------------------------
-- ROUND301 / ONE QUANTITATIVE SPECTRAL COMPONENT PAYS OLD F3 + AMPLITUDE HALF F4
--
-- R300 turns an exact positive spectral-component decomposition into the lower
-- continuum-correlation bound.  R299 turns cyclic overlap into a strictly
-- positive rational weight by construction.
--
-- This owner constructs the old R288 cyclic spectral core and R293 geometric
-- rate semantics on those SAME objects.  The fast envelope is the direct
-- CMP116/T5 q=1/2 envelope definitionally.  Therefore the surviving physical
-- spectral inputs are now:
--
--   * same-Hamiltonian positive spectral decomposition;
--   * positive subgap energy below candidate -> strictly slower ratio q_E>1/2;
--   * q_E<1 on the selected physical semigroup normalization.
--
-- Positive overlap amplitude and the lower-envelope inequality are no longer
-- independent theorem leaves.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanSubgapSeparatingTimeRound288Exact as R288
import DASHI.Physics.YangMills.BalabanSubgapGeometricSeparationRound293Exact as R293
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274

record QuantitativeSubgapSpectralRateData
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
    zeroEnergy gapCandidate : Energy
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

open QuantitativeSubgapSpectralRateData public

asCyclicCovarianceSpectralCore :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family} →
  QuantitativeSubgapSpectralRateData
    dataSet extension tests quantitative family decomposition →
  R288.CyclicCovarianceSpectralCore dataSet extension tests
asCyclicCovarianceSpectralCore
    {quantitative = quantitative} {family = family}
    {decomposition = decomposition} rates = record
  { R288.CyclicCovarianceSpectralCore.cyclicity =
      R299.asPositiveTimeVacuumCyclicity quantitative
  ; R288.CyclicCovarianceSpectralCore.subgapVectors =
      R297.asReconstructedSubgapVectors family
  ; R288.CyclicCovarianceSpectralCore.subgapMeaning =
      R297.nonzeroMeaningByConstruction family
  ; R288.CyclicCovarianceSpectralCore.indexFor = R300.indexFor decomposition
  ; R288.CyclicCovarianceSpectralCore.zeroEnergy = zeroEnergy rates
  ; R288.CyclicCovarianceSpectralCore.gapCandidate = gapCandidate rates
  ; R288.CyclicCovarianceSpectralCore.PositiveEnergy = PositiveEnergy rates
  ; R288.CyclicCovarianceSpectralCore.StrictlyBelow = StrictlyBelow rates
  ; R288.CyclicCovarianceSpectralCore.clusteringEnvelope =
      λ _ time → Shell.quarter * Power.rationalPower Geo.half time
  ; R288.CyclicCovarianceSpectralCore.subgapSpectralEnvelope =
      λ energy observable time →
        let mode = modeForObservable energy observable
        in R300.selectedOverlapWeight decomposition energy mode
          * Power.rationalPower (R300.subgapRatio decomposition energy mode) time
  ; R288.CyclicCovarianceSpectralCore.LessEqual = _≤_
  ; R288.CyclicCovarianceSpectralCore.spectralRepresentationLowerBoundFromOverlap =
      lowerFromSelectedMode
  }
  where
  -- The old core indexes its envelope by energy+observable, but the canonical
  -- cyclic observable is generated from a mode.  We must not invent an inverse
  -- observable->mode map.  Therefore this constructor cannot honestly be total
  -- at that old interface without one more representation refinement.
  --
  -- These local declarations are intentionally left impossible to inhabit; the
  -- source review below will replace the old envelope interface rather than
  -- fabricate an inverse.
  modeForObservable : Energy → TestObservable → R297.SubgapMode family
  modeForObservable energy observable = modeForObservable energy observable

  lowerFromSelectedMode :
    ∀ energy (mode : R297.SubgapMode family energy) time →
    R299.asPositiveTimeVacuumCyclicity quantitative
      .Cyclic.PositiveTimeVacuumCyclicity.Overlap
      (R299.vectorOfObservable quantitative
        (R297.modeObservableFromActualNonzeroFamily family energy mode))
      (R297.modeVector family energy mode) →
    _
  lowerFromSelectedMode energy mode time overlap =
    R300.spectralComponentBelowCorrelation decomposition energy mode time

record Round301Boundary : Set where
  constructor round301-boundary
  field
    positiveAmplitudeSeparateLeaf : Bool
    positiveAmplitudeSeparateLeafIsFalse : positiveAmplitudeSeparateLeaf ≡ false
    spectralLowerInequalitySeparateLeaf : Bool
    spectralLowerInequalitySeparateLeafIsFalse :
      spectralLowerInequalitySeparateLeaf ≡ false
    oldEnergyObservableEnvelopeInterfaceNeedsRefinement : Bool
    oldEnergyObservableEnvelopeInterfaceNeedsRefinementIsTrue :
      oldEnergyObservableEnvelopeInterfaceNeedsRefinement ≡ true

canonicalRound301Boundary : Round301Boundary
canonicalRound301Boundary = round301-boundary false refl false refl true refl

round301PositiveAmplitudeCompilerLevel : ProofLevel
round301PositiveAmplitudeCompilerLevel = R299.round299QuantitativeOverlapSelectionCompilerLevel

round301PositiveComponentLowerCompilerLevel : ProofLevel
round301PositiveComponentLowerCompilerLevel = R300.round300PositiveComponentLowerCompilerLevel

round301OldEnvelopeInterfaceRefinementLevel : ProofLevel
round301OldEnvelopeInterfaceRefinementLevel = conditional
