{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsABCConstructiveCoreExact where

------------------------------------------------------------------------
-- THEOREM-BEARING A/B/C CORE
--
-- A: represented positive normalized continuum cylinder measure
-- B: reconstructed positive transfer-gap core
-- C: same-family local operator / quantitative OPE / stress package
--
-- This is not itself Clay evidence: literal all-group same-family welding,
-- accepted OS/Wightman reconstruction, nontriviality and the remaining physical
-- source identifications must still be supplied.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCylinderExpectationLimitMeasureExact as A
import DASHI.Physics.YangMills.BalabanCMP116PublishedSelectedGapProducerExact as B
import DASHI.Physics.YangMills.BalabanCMP116R281SourceResponseSameObjectRound342Exact as R342
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanSameFamilyCompositeOPEStressCompilerExact as C
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local

record ABCConstructiveCore
    (CylinderObservable ContinuumMeasure : Set)
    (cylinderData : A.CylinderExpectationLimitData CylinderObservable)
    {Measure TestObservable SpectralObservable Energy : Set}
    {measureData : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension measureData}
    (base : R318.UnlocalizedT5StateFamilyJPresentation measureData extension)
    (tests : R278.SelectedConnectedCovarianceTests measureData)
    (spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      measureData extension tests)
    (Scale Volume Root ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian : Set) : Set₂ where
  field
    representedMeasure :
      A.CylinderMeasureRepresentation
        CylinderObservable ContinuumMeasure cylinderData

    transferGap :
      Gap.PositiveTransferGapCore
        (R281.asReconstructedClusteringSpectrum spectrumSource)

    localPackage :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian

open ABCConstructiveCore public

constructABC :
  ∀ {CylinderObservable ContinuumMeasure}
    {cylinderData : A.CylinderExpectationLimitData CylinderObservable}
    {Measure TestObservable SpectralObservable Energy}
    {measureData : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension measureData}
    {base : R318.UnlocalizedT5StateFamilyJPresentation measureData extension}
    {tests : R278.SelectedConnectedCovarianceTests measureData}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      measureData extension tests}
    {Scale Volume Root ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian} →
  A.CylinderMeasureRepresentationAuthority
    CylinderObservable ContinuumMeasure →
  B.PublishedSelectedCMP116Producer base tests spectrumSource →
  R342.SelectedLimitUpperClosure {dataSet = measureData} →
  Gap.PositiveEnergy
    (R281.asReconstructedClusteringSpectrum spectrumSource)
    (Gap.gapCandidate (R281.asReconstructedClusteringSpectrum spectrumSource)) →
  C.SameFamilyCompositeOPEStressInputs
    Scale Volume Root ContinuumFamily CurvaturePolynomial LocalOperator Position
    OPECoefficient StressTensor Hamiltonian →
  ABCConstructiveCore
    CylinderObservable ContinuumMeasure cylinderData
    base tests spectrumSource
    Scale Volume Root ContinuumFamily CurvaturePolynomial LocalOperator Position
    OPECoefficient StressTensor Hamiltonian
constructABC
    {cylinderData = cylinderData}
    measureAuthority bProducer limitClosure positiveGap cInputs = record
  { ABCConstructiveCore.representedMeasure =
      A.represent measureAuthority cylinderData
  ; ABCConstructiveCore.transferGap =
      B.publishedSelectedCMP116BuildsPositiveTransferGap
        bProducer limitClosure positiveGap
  ; ABCConstructiveCore.localPackage =
      C.compileContinuumLocalOperatorOPEStressTensor cInputs
  }

abcConstructiveCoreCompilerLevel : ProofLevel
abcConstructiveCoreCompilerLevel = machineChecked
