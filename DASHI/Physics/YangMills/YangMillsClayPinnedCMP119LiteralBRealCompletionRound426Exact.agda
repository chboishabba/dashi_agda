{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119LiteralBRealCompletionRound426Exact where

------------------------------------------------------------------------
-- B / ROUND426: PREFERRED R415 -> SAME CMP119 CONTINUUM COVARIANCE UPPER
--
-- R425 produces the preferred literal selected source.  The existing ordered
-- real calibration needs only the one-sided B4/B5 comparisons.  This owner
-- makes the whole downstream route one compiler call:
--
--   preferred R415
--     -> sourceEnvelope <= selected boundary
--     -> selected residual weight <= physical exponential
--     -> finite connected covariance
--     -> SAME continuum connected covariance.
------------------------------------------------------------------------

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealTwoJSourceExact as TwoJ
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanCMP116PreferredR415SourceExact as Preferred
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ApplicationExact as Application
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119PreferredR415ClusteringExact as PreferredClustering
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ClusteringExact as Clustering
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCovarianceExact as Cov
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record LiteralCMP116BRealCompletion
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
    covarianceLaws :
      Cov.CanonicalRealCovarianceLimitLaws sequenceLimit

    calibration :
      PreferredClustering.PreferredR415ApplicationCalibration
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
        application expReal embedding preferred

open LiteralCMP116BRealCompletion public

clusteringInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection Index Domain Term Operator
      sequenceLimit limitLaws quotient division S a group twoJ source
      application expReal embedding preferred}
    (completion :
      LiteralCMP116BRealCompletion
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
    {S = S} a (covarianceLaws completion) group source
clusteringInputs completion =
  PreferredClustering.asClusteringInputs
    (covarianceLaws completion)
    (calibration completion)

continuumCovarianceBelowPreferredPhysicalUpper :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Scale Volume Root SourceDirection Index Domain Term Operator
      sequenceLimit limitLaws quotient division S a group twoJ source
      application expReal embedding preferred}
    (completion :
      LiteralCMP116BRealCompletion
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
        application expReal embedding preferred)
    index →
  let inputs = clusteringInputs completion
  in
  R278.connectedCovarianceMagnitude
    (Cov.realCovarianceExtension a (covarianceLaws completion) group)
    (Gram.continuumMeasure
      (Carrier.cmp119PhysicalMeasureConvergenceData a group))
    (Clustering.left inputs index)
    (Clustering.right inputs index)
  DASHI.Foundations.RealAnalysisAxioms.≤ℝ
  Clustering.physicalUpper inputs index
continuumCovarianceBelowPreferredPhysicalUpper completion =
  Clustering.continuumPhysicalCovarianceBelowUpper
    (clusteringInputs completion)

round426PreferredBContinuumCompilerLevel : ProofLevel
round426PreferredBContinuumCompilerLevel = machineChecked

-- The only new physical input at this stage is the ordered-real B4/B5
-- calibration already exposed by PreferredR415ApplicationCalibration.
literalRound426PreferredBRealCalibrationLevel : ProofLevel
literalRound426PreferredBRealCalibrationLevel = conditional
