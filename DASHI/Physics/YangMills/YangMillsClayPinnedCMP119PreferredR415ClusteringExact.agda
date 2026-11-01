{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119PreferredR415ClusteringExact where

------------------------------------------------------------------------
-- B / LITERAL REAL CMP116 APPLICATION + PREFERRED R415 -> CLUSTERING INPUT
------------------------------------------------------------------------

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealTwoJSourceExact as TwoJ
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanCMP116PreferredR415SourceExact as Preferred
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ApplicationExact as Application
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ApplicationToClusteringExact as Adapter
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119PreferredR415OrderedRealExact as R415Real
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116MarkedExpansionOrderedUpperExact as Upper
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ClusteringExact as Clustering
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PreferredR415ApplicationCalibration
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
     Scale Volume Root SourceDirection Index Domain Term Operator : Set}
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
        {S = S} a group twoJ source)
    (expReal : ℝ → ℝ)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (preferred : Index → Preferred.PreferredR415Source Domain Term Operator)
    : Set₂ where
  field
    realCalibration :
      R415Real.PreferredR415OrderedRealCalibration
        Domain Term Operator Scale Volume Root SourceDirection Index
        source
        (λ index →
          Cumulant.sourceDirectionOf
            (TwoJ.meaning twoJ)
            (Application.left application index))
        (λ index →
          Cumulant.sourceDirectionOf
            (TwoJ.meaning twoJ)
            (Application.right application index))
        (Application.scaleAt application)
        (Application.volumeAt application)
        expReal embedding preferred

    orderLimit :
      Clustering.RealUpperClosedLimit sequenceLimit

open PreferredR415ApplicationCalibration public

asPhysicalCalibration :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection Index Domain Term Operator
      sequenceLimit limitLaws quotient division S a group twoJ source
      application expReal embedding preferred}
    (calibration :
      PreferredR415ApplicationCalibration
        {G = G} {X = X} {Configuration = Configuration}
        {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {StressTensor = StressTensor} {Hilbert = Hilbert}
        {Hamiltonian = Hamiltonian} {Vacuum = Vacuum}
        {Scale = Scale} {Volume = Volume} {Root = Root}
        {SourceDirection = SourceDirection} {Index = Index}
        {Domain = Domain} {Term = Term} {Operator = Operator}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division} {S = S}
        {a = a} {group = group} {twoJ = twoJ} {source = source}
        application expReal embedding preferred) →
  Adapter.LiteralRealCMP116PhysicalCalibration application
asPhysicalCalibration calibration = record
  { Adapter.LiteralRealCMP116PhysicalCalibration.physicalUpper =
      Upper.physicalExponentialUpper
        (R415Real.asOrderedInputs
          (realCalibration calibration))
  ; Adapter.LiteralRealCMP116PhysicalCalibration.sourceEnvelopeBelowPhysicalUpper =
      R415Real.preferredR415OrderedPhysicalUpper
        (realCalibration calibration)
  ; Adapter.LiteralRealCMP116PhysicalCalibration.orderLimit =
      orderLimit calibration
  }

asClusteringInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection Index Domain Term Operator
      sequenceLimit limitLaws quotient division S a group twoJ source
      application expReal embedding preferred}
    (covarianceLaws : Cov.CanonicalRealCovarianceLimitLaws sequenceLimit)
    (calibration :
      PreferredR415ApplicationCalibration
        {G = G} {X = X} {Configuration = Configuration}
        {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {StressTensor = StressTensor} {Hilbert = Hilbert}
        {Hamiltonian = Hamiltonian} {Vacuum = Vacuum}
        {Scale = Scale} {Volume = Volume} {Root = Root}
        {SourceDirection = SourceDirection} {Index = Index}
        {Domain = Domain} {Term = Term} {Operator = Operator}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division} {S = S}
        {a = a} {group = group} {twoJ = twoJ} {source = source}
        application expReal embedding preferred) →
  Clustering.LiteralRealCMP116ClusteringInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    Scale Volume Root SourceDirection Index
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws} {quotient = quotient} {division = division}
    {S = S} a covarianceLaws group source
asClusteringInputs {application = application}
    covarianceLaws calibration =
  Adapter.asClusteringInputs
    application covarianceLaws
    (asPhysicalCalibration calibration)

preferredR415ApplicationToClusteringCompilerLevel : ProofLevel
preferredR415ApplicationToClusteringCompilerLevel = machineChecked

literalPreferredR415ApplicationClusteringLevel : ProofLevel
literalPreferredR415ApplicationClusteringLevel = conditional
