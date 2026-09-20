{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ApplicationToClusteringExact where

------------------------------------------------------------------------
-- B / REMOVE DUPLICATED L4 PREMISE
--
-- LiteralRealCMP116Application already proves that the selected CMP116
-- differentiated magnitude is the finite connected covariance of the SAME
-- normalized CMP119 measure.  The clustering record previously accepted that
-- identity again as an independent field.
--
-- This adapter makes L4 compiler-owned.  The remaining B inputs are exactly:
--
--   * the physical envelope/rate calibration;
--   * closed order under the selected real limit.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealTwoJSourceExact as TwoJ
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ApplicationExact as Application
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ClusteringExact as Clustering
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record LiteralRealCMP116PhysicalCalibration
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
     Scale Volume Root SourceDirection Index : Set}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    {S}
    {a :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    {group : G}
    {twoJ :
      TwoJ.LiteralRealTwoJSourceMeaning
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum SourceDirection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} a group}
    {source :
      CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root SourceDirection ℝ}
    (application :
      Application.LiteralRealCMP116Application
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Scale Volume Root SourceDirection Index
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} a group twoJ source) : Set₁ where
  field
    physicalUpper : Index → ℝ

    sourceEnvelopeBelowPhysicalUpper :
      ∀ cutoff index →
      CMP116.sourceEnvelope source
        (Application.scaleAt application cutoff)
        (Application.volumeAt application cutoff)
        (CMP116.sourceRoot source
          (Application.scaleAt application cutoff)
          (Application.volumeAt application cutoff)
          (Cumulant.sourceDirectionOf
            (TwoJ.meaning twoJ)
            (Application.left application index))
          (Cumulant.sourceDirectionOf
            (TwoJ.meaning twoJ)
            (Application.right application index)))
        (CMP116.sourceDistance source
          (Cumulant.sourceDirectionOf
            (TwoJ.meaning twoJ)
            (Application.left application index))
          (Cumulant.sourceDirectionOf
            (TwoJ.meaning twoJ)
            (Application.right application index)))
      ≤ℝ physicalUpper index

    orderLimit : Clustering.RealUpperClosedLimit sequenceLimit

open LiteralRealCMP116PhysicalCalibration public

asClusteringInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection Index
      sequenceLimit limitLaws quotient division S a group twoJ source}
    (application :
      Application.LiteralRealCMP116Application
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Scale Volume Root SourceDirection Index
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} a group twoJ source)
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    (calibration : LiteralRealCMP116PhysicalCalibration application) →
  Clustering.LiteralRealCMP116ClusteringInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    Scale Volume Root SourceDirection Index
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} a covarianceLaws group source
asClusteringInputs application covarianceLaws calibration = record
  { Clustering.LiteralRealCMP116ClusteringInputs.left =
      Application.left application
  ; Clustering.LiteralRealCMP116ClusteringInputs.right =
      Application.right application
  ; Clustering.LiteralRealCMP116ClusteringInputs.sourceLeft =
      λ index →
        Cumulant.sourceDirectionOf
          (TwoJ.meaning _)
          (Application.left application index)
  ; Clustering.LiteralRealCMP116ClusteringInputs.sourceRight =
      λ index →
        Cumulant.sourceDirectionOf
          (TwoJ.meaning _)
          (Application.right application index)
  ; Clustering.LiteralRealCMP116ClusteringInputs.scaleAt =
      Application.scaleAt application
  ; Clustering.LiteralRealCMP116ClusteringInputs.volumeAt =
      Application.volumeAt application
  ; Clustering.LiteralRealCMP116ClusteringInputs.selectedPairAdmissible =
      Application.selectedPairAdmissible application
  ; Clustering.LiteralRealCMP116ClusteringInputs.sourceMagnitudeIsFinitePhysicalCovariance =
      Application.sourceMagnitudeIsFinitePhysicalCovariance
        application covarianceLaws
  ; Clustering.LiteralRealCMP116ClusteringInputs.physicalUpper =
      physicalUpper calibration
  ; Clustering.LiteralRealCMP116ClusteringInputs.sourceEnvelopeBelowPhysicalUpper =
      sourceEnvelopeBelowPhysicalUpper calibration
  ; Clustering.LiteralRealCMP116ClusteringInputs.orderLimit =
      orderLimit calibration
  }

literalRealCMP116L4ToClusteringAdapterLevel : ProofLevel
literalRealCMP116L4ToClusteringAdapterLevel = machineChecked

-- After this adapter, the finite source-coordinate/covariance identification is
-- not an independent clustering premise.
literalRealCMP116RemainingPhysicalCalibrationLevel : ProofLevel
literalRealCMP116RemainingPhysicalCalibrationLevel = conditional
