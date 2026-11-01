{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116PhysicalUpperExact where

------------------------------------------------------------------------
-- PREFERRED LITERAL REAL CMP116 CONTINUUM UPPER
--
-- L4 is compiled from normalized two-J source calculus + selected J coordinate.
-- The only remaining source-specific analytic input here is L5:
--
--   published source envelope <= desired physical Euclidean upper.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealTwoJSourceExact as TwoJ
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ApplicationExact as App
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ClusteringExact as Cluster
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record LiteralRealCMP116PhysicalUpperInputs
    (CompactSimpleGroup Spacetime Configuration Position
     CurvaturePolynomial LocalOperator OPECoefficient StressTensor
     Hilbert Hamiltonian Vacuum
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
        Hilbert Hamiltonian Vacuum
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    (group : CompactSimpleGroup)
    (twoJ :
      TwoJ.LiteralRealTwoJSourceMeaning
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        Hilbert Hamiltonian Vacuum SourceDirection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} a group)
    (source :
      CMP116.PublishedCMP116DifferentiatedLocalization
        Scale Volume Root SourceDirection ℝ)
    (application :
      App.LiteralRealCMP116Application
        CompactSimpleGroup Spacetime Configuration Position
        CurvaturePolynomial LocalOperator OPECoefficient StressTensor
        Hilbert Hamiltonian Vacuum
        Scale Volume Root SourceDirection Index
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} a group twoJ source) : Set₂ where
  field
    physicalUpper : Index → ℝ

    sourceEnvelopeBelowPhysicalUpper :
      ∀ cutoff index →
      CMP116.sourceEnvelope source
        (App.scaleAt application cutoff)
        (App.volumeAt application cutoff)
        (CMP116.sourceRoot source
          (App.scaleAt application cutoff)
          (App.volumeAt application cutoff)
          (Cumulant.sourceDirectionOf
            (TwoJ.meaning twoJ)
            (App.left application index))
          (Cumulant.sourceDirectionOf
            (TwoJ.meaning twoJ)
            (App.right application index)))
        (CMP116.sourceDistance source
          (Cumulant.sourceDirectionOf
            (TwoJ.meaning twoJ)
            (App.left application index))
          (Cumulant.sourceDirectionOf
            (TwoJ.meaning twoJ)
            (App.right application index)))
      DASHI.Foundations.RealAnalysisAxioms.≤ℝ
      physicalUpper index

    orderLimit : Cluster.RealUpperClosedLimit sequenceLimit

open LiteralRealCMP116PhysicalUpperInputs public

asClusteringInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection Index
      sequenceLimit limitLaws quotient division S
      a covarianceLaws group twoJ source application} →
  LiteralRealCMP116PhysicalUpperInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    Scale Volume Root SourceDirection Index
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} a covarianceLaws group twoJ source application →
  Cluster.LiteralRealCMP116ClusteringInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    Scale Volume Root SourceDirection Index
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} a covarianceLaws group source
asClusteringInputs
    {twoJ = twoJ} {application = application}
    inputs = record
  { Cluster.LiteralRealCMP116ClusteringInputs.left =
      App.left application
  ; Cluster.LiteralRealCMP116ClusteringInputs.right =
      App.right application
  ; Cluster.LiteralRealCMP116ClusteringInputs.sourceLeft =
      λ index →
        Cumulant.sourceDirectionOf
          (TwoJ.meaning twoJ)
          (App.left application index)
  ; Cluster.LiteralRealCMP116ClusteringInputs.sourceRight =
      λ index →
        Cumulant.sourceDirectionOf
          (TwoJ.meaning twoJ)
          (App.right application index)
  ; Cluster.LiteralRealCMP116ClusteringInputs.scaleAt =
      App.scaleAt application
  ; Cluster.LiteralRealCMP116ClusteringInputs.volumeAt =
      App.volumeAt application
  ; Cluster.LiteralRealCMP116ClusteringInputs.selectedPairAdmissible =
      App.selectedPairAdmissible application
  ; Cluster.LiteralRealCMP116ClusteringInputs.sourceMagnitudeIsFinitePhysicalCovariance =
      App.sourceMagnitudeIsFinitePhysicalCovariance
        application covarianceLaws
  ; Cluster.LiteralRealCMP116ClusteringInputs.physicalUpper =
      physicalUpper inputs
  ; Cluster.LiteralRealCMP116ClusteringInputs.sourceEnvelopeBelowPhysicalUpper =
      sourceEnvelopeBelowPhysicalUpper inputs
  ; Cluster.LiteralRealCMP116ClusteringInputs.orderLimit =
      orderLimit inputs
  }

continuumPhysicalCovarianceBelowUpper :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection Index
      sequenceLimit limitLaws quotient division S
      a covarianceLaws group twoJ source application}
    (inputs :
      LiteralRealCMP116PhysicalUpperInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Scale Volume Root SourceDirection Index
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} a covarianceLaws group twoJ source application)
    index →
  let clustering = asClusteringInputs inputs
  in
  R278.connectedCovarianceMagnitude
    (Cov.realCovarianceExtension a covarianceLaws group)
    (Gram.continuumMeasure
      (Carrier.cmp119PhysicalMeasureConvergenceData
        a group))
    (App.left application index)
    (App.right application index)
  DASHI.Foundations.RealAnalysisAxioms.≤ℝ
  physicalUpper inputs index
continuumPhysicalCovarianceBelowUpper inputs =
  Cluster.continuumPhysicalCovarianceBelowUpper
    (asClusteringInputs inputs)

literalRealCMP116PhysicalUpperCompilerLevel : ProofLevel
literalRealCMP116PhysicalUpperCompilerLevel = machineChecked

-- After L4 compilation, this is the only physical decay calibration at this
-- layer.  Its source exponent/distance algebra is separately compiler-owned.
literalRealCMP116PhysicalUpperCalibrationLevel : ProofLevel
literalRealCMP116PhysicalUpperCalibrationLevel = conditional
