{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralWilsonP3SameOSCorrelationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281

------------------------------------------------------------------------
-- ROUTE-S P3 / SAME OS CORRELATION
--
-- R281 already removes the post-hoc covariance/spectrum equality: its
-- ReconstructedClusteringSpectrum is constructed with connectedCorrelation
-- definitionally equal to the selected continuum connected covariance.
--
-- Consequently P3 does NOT require a new theorem
--
--   continuum covariance = spectrum correlation.
--
-- The only physical same-object theorem is that this exact R281 spectrum is the
-- reconstructed spectral object of the actual H_OS produced by the selected OS
-- reconstruction.
------------------------------------------------------------------------

record OSIndexedContinuumCovarianceSpectrum
    {Measure TestObservable Scalar SpectralObservable Energy : Set}
    {Observable Point : Set}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system)
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    : Set₁ where
  field
    source :
      R281.ContinuumCovarianceSpectrumData
        {SpectralObservable = SpectralObservable}
        {Energy = Energy}
        dataSet extension tests

    SpectrumOfReconstructedHamiltonian :
      OS.Hamiltonian reconstruction →
      Gap.ReconstructedClusteringSpectrum SpectralObservable Energy Scalar →
      Set

    spectrumOfReconstructedHamiltonian :
      SpectrumOfReconstructedHamiltonian
        (OS.hamiltonian reconstruction)
        (R281.asReconstructedClusteringSpectrum source)

open OSIndexedContinuumCovarianceSpectrum public

sameOSCorrelationIsContinuumCovariance :
  ∀ {Measure TestObservable Scalar SpectralObservable Energy Observable Point}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    {reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable Scalar}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    (indexed :
      OSIndexedContinuumCovarianceSpectrum
        {SpectralObservable = SpectralObservable}
        {Energy = Energy}
        reconstruction dataSet extension tests)
    observable time →
  R278.connectedCovarianceMagnitude extension
    (Gram.continuumMeasure dataSet)
    (R278.left tests
      (R281.indexFor (source indexed) observable time))
    (R278.right tests
      (R281.indexFor (source indexed) observable time))
  ≡ Gap.connectedCorrelation
      (R281.asReconstructedClusteringSpectrum (source indexed))
      observable time
sameOSCorrelationIsContinuumCovariance indexed observable time =
  R281.continuumCovarianceIsSpectrumCorrelation
    (source indexed) observable time

------------------------------------------------------------------------
-- Frontier reduction.
------------------------------------------------------------------------

postHocCorrelationIdentityStillPhysical : Bool
postHocCorrelationIdentityStillPhysical = false

postHocCorrelationIdentityStillPhysicalIsFalse :
  postHocCorrelationIdentityStillPhysical ≡ false
postHocCorrelationIdentityStillPhysicalIsFalse = refl

sameReconstructedHamiltonianSpectrumStillPhysical : Bool
sameReconstructedHamiltonianSpectrumStillPhysical = true

sameReconstructedHamiltonianSpectrumStillPhysicalIsTrue :
  sameReconstructedHamiltonianSpectrumStillPhysical ≡ true
sameReconstructedHamiltonianSpectrumStillPhysicalIsTrue = refl

p3CorrelationIdentityCompilerLevel : ProofLevel
p3CorrelationIdentityCompilerLevel =
  R281.round281ContinuumCovarianceSpectrumConstructorLevel

p3SameReconstructedHamiltonianSpectrumLevel : ProofLevel
p3SameReconstructedHamiltonianSpectrumLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
