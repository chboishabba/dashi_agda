{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSubgapSeparatingTimeRound288Exact where

------------------------------------------------------------------------
-- ROUND288 / THE SPECTRAL CONTRADICTION NEEDS ONE SEPARATING TIME
--
-- The historical spectrum ABI stores a large implication saying that a slower
-- positive subgap envelope and the faster clustering envelope cannot coexist
-- for all times.  The actual contradiction consumer is smaller.
--
-- Given a proposed positive subgap mode below the candidate gap, it suffices to
-- exhibit one time at which:
--
--   subgapSpectralEnvelope <= connectedCorrelation <= clusteringEnvelope
--
-- is impossible.
--
-- This owner makes that witness explicit.  A later exponential/geometric
-- separation theorem can produce the time; no full asymptotic-analysis package
-- is required by the mass-gap consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanCyclicContinuumCovarianceSpectrumRound287Exact as R287
import DASHI.Physics.YangMills.BalabanClayT5OSReconstructionCyclicityExact as Cyclic
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record SubgapSeparatingTimeData
    {Measure TestObservable Scalar Energy Vector : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (source : R287.CyclicContinuumCovarianceSpectrumData dataSet extension tests)
    : Set₁ where
  field
    separatingTime :
      ∀ energy (mode : Cyclic.SubgapMode (R287.subgapVectors source) energy) →
      R287.PositiveEnergy source energy →
      R287.StrictlyBelow source energy (R287.gapCandidate source) → Nat

    lowerAndUpperAtSeparatingTimeContradict :
      ∀ energy (mode : Cyclic.SubgapMode (R287.subgapVectors source) energy)
        (positive : R287.PositiveEnergy source energy)
        (below : R287.StrictlyBelow source energy (R287.gapCandidate source)) →
      let time = separatingTime energy mode positive below
          observable =
            Cyclic.modeObservableFromCyclicity
              (R287.subgapMeaning source) energy mode
          correlation =
            R278.connectedCovarianceMagnitude extension
              (Gram.continuumMeasure dataSet)
              (R278.left tests (R287.indexFor source observable time))
              (R278.right tests (R287.indexFor source observable time))
      in
      R287.LessEqual source
        (R287.subgapSpectralEnvelope source energy observable time)
        correlation →
      R287.LessEqual source
        correlation
        (R287.clusteringEnvelope source observable time) →
      Gap.Empty

open SubgapSeparatingTimeData public

slowFastContradictionFromSeparatingTime :
  ∀ {Measure TestObservable Scalar Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {source : R287.CyclicContinuumCovarianceSpectrumData dataSet extension tests} →
  SubgapSeparatingTimeData dataSet extension tests source →
  ∀ energy (mode : Cyclic.SubgapMode (R287.subgapVectors source) energy) →
  R287.PositiveEnergy source energy →
  R287.StrictlyBelow source energy (R287.gapCandidate source) →
  (∀ time →
    R287.LessEqual source
      (R287.subgapSpectralEnvelope source energy
        (Cyclic.modeObservableFromCyclicity (R287.subgapMeaning source) energy mode)
        time)
      (R278.connectedCovarianceMagnitude extension
        (Gram.continuumMeasure dataSet)
        (R278.left tests
          (R287.indexFor source
            (Cyclic.modeObservableFromCyclicity
              (R287.subgapMeaning source) energy mode) time))
        (R278.right tests
          (R287.indexFor source
            (Cyclic.modeObservableFromCyclicity
              (R287.subgapMeaning source) energy mode) time)))) →
  (∀ time →
    R287.LessEqual source
      (R278.connectedCovarianceMagnitude extension
        (Gram.continuumMeasure dataSet)
        (R278.left tests
          (R287.indexFor source
            (Cyclic.modeObservableFromCyclicity
              (R287.subgapMeaning source) energy mode) time))
        (R278.right tests
          (R287.indexFor source
            (Cyclic.modeObservableFromCyclicity
              (R287.subgapMeaning source) energy mode) time)))
      (R287.clusteringEnvelope source
        (Cyclic.modeObservableFromCyclicity (R287.subgapMeaning source) energy mode)
        time)) →
  Gap.Empty
slowFastContradictionFromSeparatingTime separation energy mode positive below
    lower upper =
  lowerAndUpperAtSeparatingTimeContradict separation energy mode positive below
    (lower (separatingTime separation energy mode positive below))
    (upper (separatingTime separation energy mode positive below))

record Round288Boundary : Set where
  constructor round288-boundary
  field
    wholeAsymptoticContradictionPrimitive : Bool
    wholeAsymptoticContradictionPrimitiveIsFalse :
      wholeAsymptoticContradictionPrimitive ≡ false

    oneSeparatingTimeSuffices : Bool
    oneSeparatingTimeSufficesIsTrue : oneSeparatingTimeSuffices ≡ true

    separationTimeConstructionStillMathematical : Bool
    separationTimeConstructionStillMathematicalIsTrue :
      separationTimeConstructionStillMathematical ≡ true

canonicalRound288Boundary : Round288Boundary
canonicalRound288Boundary =
  round288-boundary false refl true refl true refl

round288SeparatingTimeCompilerLevel : ProofLevel
round288SeparatingTimeCompilerLevel = machineChecked

round288PhysicalSeparatingTimeLevel : ProofLevel
round288PhysicalSeparatingTimeLevel = conditional
