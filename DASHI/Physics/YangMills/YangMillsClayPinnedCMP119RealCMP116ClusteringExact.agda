{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ClusteringExact where

------------------------------------------------------------------------
-- LITERAL CMP116 ON THE SAME REAL CMP119 COVARIANCE
--
-- Selected source response = finite real connected covariance at each cutoff.
-- Published CMP116 localization then bounds that exact covariance, and closed
-- order passes the bound to the SAME continuum covariance.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record RealUpperClosedLimit
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError) : Set₁ where
  field
    upperClosed :
      (sequence : Nat → ℝ) (target upper : ℝ) →
      RealLimit.Converges sequenceLimit sequence target →
      (∀ cutoff → sequence cutoff ≤ℝ upper) →
      target ≤ℝ upper

open RealUpperClosedLimit public

record LiteralRealCMP116ClusteringInputs
    (CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     HilbertSpace Hamiltonian VacuumState
     Scale Volume Root SourceDirection Index : Set)
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
    (a :
      A.PinnedCMP119OSAxiomInputs
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    (group : CompactSimpleGroup)
    (source :
      CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root SourceDirection ℝ) : Set₂ where
  field
    left right : Index → Configuration → ℝ

    sourceLeft sourceRight : Index → SourceDirection

    scaleAt : Nat → Scale
    volumeAt : Nat → Volume

    selectedPairAdmissible : ∀ cutoff index →
      CMP116.AdmissibleSourcePair source
        (scaleAt cutoff) (volumeAt cutoff)
        (sourceLeft index) (sourceRight index)

    -- L4: the published differentiated response is the literal finite real
    -- connected covariance magnitude on the same CMP119 measure.
    sourceMagnitudeIsFinitePhysicalCovariance :
      ∀ cutoff index →
      CMP116.differentiatedMagnitude source
        (scaleAt cutoff) (volumeAt cutoff)
        (sourceLeft index) (sourceRight index)
      ≡
      R278.connectedCovarianceMagnitude
        (Cov.realCovarianceExtension a covarianceLaws group)
        (Gram.measureSequence
          (Carrier.cmp119PhysicalMeasureConvergenceData a group)
          cutoff)
        (left index) (right index)

    physicalUpper : Index → ℝ

    -- L5: source tree/localization coordinates are calibrated to the desired
    -- physical Euclidean upper.  All source exponential/distance algebra feeds
    -- this single comparison.
    sourceEnvelopeBelowPhysicalUpper :
      ∀ cutoff index →
      CMP116.sourceEnvelope source
        (scaleAt cutoff) (volumeAt cutoff)
        (CMP116.sourceRoot source
          (scaleAt cutoff) (volumeAt cutoff)
          (sourceLeft index) (sourceRight index))
        (CMP116.sourceDistance source
          (sourceLeft index) (sourceRight index))
      ≤ℝ physicalUpper index

    orderLimit : RealUpperClosedLimit sequenceLimit

open LiteralRealCMP116ClusteringInputs public

finitePhysicalCovarianceBelowUpper :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection Index
      sequenceLimit limitLaws quotient division S a covarianceLaws group source}
    (inputs :
      LiteralRealCMP116ClusteringInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Scale Volume Root SourceDirection Index
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} a covarianceLaws group source)
    cutoff index →
  R278.connectedCovarianceMagnitude
    (Cov.realCovarianceExtension a covarianceLaws group)
    (Gram.measureSequence
      (Carrier.cmp119PhysicalMeasureConvergenceData a group)
      cutoff)
    (left inputs index) (right inputs index)
  ≤ℝ
  physicalUpper inputs index
finitePhysicalCovarianceBelowUpper
    {source = source} inputs cutoff index =
  let
    sourceBound =
      CMP116.sourceDifferentiatedLocalization source
        (scaleAt inputs cutoff)
        (volumeAt inputs cutoff)
        (sourceLeft inputs index)
        (sourceRight inputs index)
        (selectedPairAdmissible inputs cutoff index)

    calibrated =
      sourceEnvelopeBelowPhysicalUpper inputs cutoff index
  in
  subst
    (λ lower → lower ≤ℝ physicalUpper inputs index)
    (sourceMagnitudeIsFinitePhysicalCovariance inputs cutoff index)
    (CMP116.orderTransitive source sourceBound calibrated)

continuumPhysicalCovarianceBelowUpper :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection Index
      sequenceLimit limitLaws quotient division S a covarianceLaws group source}
    (inputs :
      LiteralRealCMP116ClusteringInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Scale Volume Root SourceDirection Index
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} a covarianceLaws group source)
    index →
  R278.connectedCovarianceMagnitude
    (Cov.realCovarianceExtension a covarianceLaws group)
    (Gram.continuumMeasure
      (Carrier.cmp119PhysicalMeasureConvergenceData a group))
    (left inputs index) (right inputs index)
  ≤ℝ
  physicalUpper inputs index
continuumPhysicalCovarianceBelowUpper
    {a = a} {covarianceLaws = covarianceLaws} {group = group}
    inputs index =
  RealUpperClosedLimit.upperClosed
    (orderLimit inputs)
    (λ cutoff →
      R278.connectedCovarianceMagnitude
        (Cov.realCovarianceExtension a covarianceLaws group)
        (Gram.measureSequence
          (Carrier.cmp119PhysicalMeasureConvergenceData a group)
          cutoff)
        (left inputs index) (right inputs index))
    (R278.connectedCovarianceMagnitude
      (Cov.realCovarianceExtension a covarianceLaws group)
      (Gram.continuumMeasure
        (Carrier.cmp119PhysicalMeasureConvergenceData a group))
      (left inputs index) (right inputs index))
    (physicalUpper inputs index)
    (Cov.selectedRealConnectedCovarianceConverges
      a covarianceLaws group
      _ (left inputs) (right inputs) index)
    (λ cutoff →
      finitePhysicalCovarianceBelowUpper inputs cutoff index)

literalRealCMP116FinitePhysicalApplicationLevel : ProofLevel
literalRealCMP116FinitePhysicalApplicationLevel = conditional

literalRealCMP116PhysicalRateCalibrationLevel : ProofLevel
literalRealCMP116PhysicalRateCalibrationLevel = conditional

literalRealCMP116ContinuumClusteringCompilerLevel : ProofLevel
literalRealCMP116ContinuumClusteringCompilerLevel = machineChecked

realUpperClosedLimitAuthorityLevel : ProofLevel
realUpperClosedLimitAuthorityLevel = standardImported
