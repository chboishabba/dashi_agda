{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact where

------------------------------------------------------------------------
-- ROUND281 / BUILD THE SPECTRUM ON THE CONTINUUM COVARIANCE CARRIER
--
-- R279 exposed a post-hoc semantic weld
--
--   continuum expectation covariance magnitude
--     == reconstructed-spectrum connected correlation.
--
-- That equality is unnecessary if the reconstructed spectrum is constructed on
-- the SAME continuum covariance carrier in the first place.  This owner keeps
-- all genuine spectral content explicit while defining `connectedCorrelation`
-- directly from R278's continuum covariance magnitude.
--
-- Therefore the covariance/spectrum identity is definitional (`refl`), not a
-- separate physical theorem.  This does NOT manufacture the spectral lower
-- representation, subgap overlap, rate comparison, or positivity of the gap
-- candidate; those remain fields of the source/spectral producer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record ContinuumCovarianceSpectrumData
    {Measure TestObservable Scalar SpectralObservable Energy : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    : Set₁ where
  field
    indexFor : SpectralObservable → Nat → R278.Index tests

    zeroEnergy gapCandidate : Energy
    PositiveEnergy : Energy → Set
    StrictlyBelow : Energy → Energy → Set

    clusteringEnvelope : SpectralObservable → Nat → Scalar
    subgapSpectralEnvelope : Energy → SpectralObservable → Nat → Scalar
    LessEqual : Scalar → Scalar → Set

    SubgapMode : Energy → Set
    modeObservable : ∀ energy → SubgapMode energy → SpectralObservable

    spectralRepresentationLowerBound : ∀ energy mode time →
      LessEqual
        (subgapSpectralEnvelope energy (modeObservable energy mode) time)
        (R278.connectedCovarianceMagnitude extension
          (Gram.continuumMeasure dataSet)
          (R278.left tests (indexFor (modeObservable energy mode) time))
          (R278.right tests (indexFor (modeObservable energy mode) time)))

    slowSubgapEnvelopeContradictsFastClustering : ∀ energy mode →
      PositiveEnergy energy → StrictlyBelow energy gapCandidate →
      (∀ time →
        LessEqual
          (subgapSpectralEnvelope energy (modeObservable energy mode) time)
          (R278.connectedCovarianceMagnitude extension
            (Gram.continuumMeasure dataSet)
            (R278.left tests (indexFor (modeObservable energy mode) time))
            (R278.right tests (indexFor (modeObservable energy mode) time)))) →
      (∀ time →
        LessEqual
          (R278.connectedCovarianceMagnitude extension
            (Gram.continuumMeasure dataSet)
            (R278.left tests (indexFor (modeObservable energy mode) time))
            (R278.right tests (indexFor (modeObservable energy mode) time)))
          (clusteringEnvelope (modeObservable energy mode) time)) →
      Gap.Empty

open ContinuumCovarianceSpectrumData public

asReconstructedClusteringSpectrum :
  ∀ {Measure TestObservable Scalar SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet} →
  ContinuumCovarianceSpectrumData dataSet extension tests →
  Gap.ReconstructedClusteringSpectrum SpectralObservable Energy Scalar
asReconstructedClusteringSpectrum {dataSet = dataSet} {extension = extension}
    {tests = tests} source = record
  { Gap.ReconstructedClusteringSpectrum.zeroEnergy = zeroEnergy source
  ; Gap.ReconstructedClusteringSpectrum.gapCandidate = gapCandidate source
  ; Gap.ReconstructedClusteringSpectrum.PositiveEnergy = PositiveEnergy source
  ; Gap.ReconstructedClusteringSpectrum.StrictlyBelow = StrictlyBelow source
  ; Gap.ReconstructedClusteringSpectrum.connectedCorrelation =
      λ observable time →
        R278.connectedCovarianceMagnitude extension
          (Gram.continuumMeasure dataSet)
          (R278.left tests (indexFor source observable time))
          (R278.right tests (indexFor source observable time))
  ; Gap.ReconstructedClusteringSpectrum.clusteringEnvelope = clusteringEnvelope source
  ; Gap.ReconstructedClusteringSpectrum.subgapSpectralEnvelope = subgapSpectralEnvelope source
  ; Gap.ReconstructedClusteringSpectrum.LessEqual = LessEqual source
  ; Gap.ReconstructedClusteringSpectrum.SubgapMode = SubgapMode source
  ; Gap.ReconstructedClusteringSpectrum.modeObservable = modeObservable source
  ; Gap.ReconstructedClusteringSpectrum.spectralRepresentationLowerBound =
      spectralRepresentationLowerBound source
  ; Gap.ReconstructedClusteringSpectrum.slowSubgapEnvelopeContradictsFastClustering =
      slowSubgapEnvelopeContradictsFastClustering source
  }

continuumCovarianceIsSpectrumCorrelation :
  ∀ {Measure TestObservable Scalar SpectralObservable Energy}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    (source : ContinuumCovarianceSpectrumData dataSet extension tests)
    observable time →
  R278.connectedCovarianceMagnitude extension
    (Gram.continuumMeasure dataSet)
    (R278.left tests (indexFor source observable time))
    (R278.right tests (indexFor source observable time))
  ≡ Gap.connectedCorrelation
      (asReconstructedClusteringSpectrum source) observable time
continuumCovarianceIsSpectrumCorrelation source observable time = refl

record Round281Boundary : Set where
  constructor round281-boundary
  field
    postHocContinuumSpectrumEqualityRequired : Bool
    postHocContinuumSpectrumEqualityRequiredIsFalse :
      postHocContinuumSpectrumEqualityRequired ≡ false

    continuumCorrelationChosenFromExactCovariance : Bool
    continuumCorrelationChosenFromExactCovarianceIsTrue :
      continuumCorrelationChosenFromExactCovariance ≡ true

    spectralLowerRepresentationManufactured : Bool
    spectralLowerRepresentationManufacturedIsFalse :
      spectralLowerRepresentationManufactured ≡ false

    subgapOverlapManufactured : Bool
    subgapOverlapManufacturedIsFalse : subgapOverlapManufactured ≡ false

    positiveGapManufactured : Bool
    positiveGapManufacturedIsFalse : positiveGapManufactured ≡ false

canonicalRound281Boundary : Round281Boundary
canonicalRound281Boundary =
  round281-boundary false refl true refl false refl false refl false refl

round281ContinuumCovarianceSpectrumConstructorLevel : ProofLevel
round281ContinuumCovarianceSpectrumConstructorLevel = machineChecked

-- Physical spectral work remaining on this constructor: provide the actual
-- reconstructed subgap semantics/lower envelope and the slow-vs-fast rate
-- contradiction on the same continuum covariance observable family.
round281PhysicalSpectralRepresentationAndRateInputsLevel : ProofLevel
round281PhysicalSpectralRepresentationAndRateInputsLevel = conditional
