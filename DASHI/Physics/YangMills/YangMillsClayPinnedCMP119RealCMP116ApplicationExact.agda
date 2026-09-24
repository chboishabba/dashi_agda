{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ApplicationExact where

------------------------------------------------------------------------
-- CMP116 SOURCE COORDINATE -> LITERAL REAL CMP119 COVARIANCE
--
-- The normalized two-J cumulant identity is compiler-owned.  L4 is reduced to
-- one source-coordinate statement:
--
--   published differentiated magnitude
--     = | literal mixed J-log derivative |
--
-- on the selected physical J directions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; absℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealTwoJSourceExact as TwoJ
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record LiteralRealCMP116Application
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
        Scale Volume Root SourceDirection ℝ) : Set₂ where
  field
    left right : Index → Configuration → ℝ

    scaleAt : Nat → Scale
    volumeAt : Nat → Volume

    selectedPairAdmissible : ∀ cutoff index →
      CMP116.AdmissibleSourcePair source
        (scaleAt cutoff) (volumeAt cutoff)
        (Cumulant.sourceDirectionOf (TwoJ.meaning twoJ) (left index))
        (Cumulant.sourceDirectionOf (TwoJ.meaning twoJ) (right index))

    -- Sole L4 source-coordinate payment.
    sourceMagnitudeIsLiteralMixedLogMagnitude :
      ∀ cutoff index →
      CMP116.differentiatedMagnitude source
        (scaleAt cutoff) (volumeAt cutoff)
        (Cumulant.sourceDirectionOf (TwoJ.meaning twoJ) (left index))
        (Cumulant.sourceDirectionOf (TwoJ.meaning twoJ) (right index))
      ≡
      absℝ
        (Cumulant.literalMixedSecondLogDerivative
          (TwoJ.meaning twoJ)
          (Cumulant.sourceDirectionOf (TwoJ.meaning twoJ) (left index))
          (Cumulant.sourceDirectionOf (TwoJ.meaning twoJ) (right index))
          cutoff)

open LiteralRealCMP116Application public

sourceMagnitudeIsFinitePhysicalCovariance :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection Index
      sequenceLimit limitLaws quotient division S a group twoJ source}
    (application :
      LiteralRealCMP116Application
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Scale Volume Root SourceDirection Index
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} a group twoJ source)
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    cutoff index →
  CMP116.differentiatedMagnitude source
    (scaleAt application cutoff) (volumeAt application cutoff)
    (Cumulant.sourceDirectionOf (TwoJ.meaning twoJ) (left application index))
    (Cumulant.sourceDirectionOf (TwoJ.meaning twoJ) (right application index))
  ≡
  R278.connectedCovarianceMagnitude
    (Cov.realCovarianceExtension a covarianceLaws group)
    (Gram.measureSequence
      (Carrier.cmp119PhysicalMeasureConvergenceData a group)
      cutoff)
    (left application index) (right application index)
sourceMagnitudeIsFinitePhysicalCovariance
    {a = a} {group = group} {twoJ = twoJ}
    application covarianceLaws cutoff index =
  trans
    (sourceMagnitudeIsLiteralMixedLogMagnitude
      application cutoff index)
    (TwoJ.finiteLiteralMixedLogMagnitudeIsPhysicalCovariance
      twoJ cutoff
      (left application index)
      (right application index))

literalRealCMP116L4CompilerLevel : ProofLevel
literalRealCMP116L4CompilerLevel = machineChecked

literalCMP116SelectedJCoordinateLevel : ProofLevel
literalCMP116SelectedJCoordinateLevel = conditional
