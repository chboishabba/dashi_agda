{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsLiteralCMP119ExponentialMomentTheoremExact where

------------------------------------------------------------------------
-- T5 theorem-bearing constructor.
--
-- The sole quantitative input is the exponential-moment producer on the exact
-- literal CMP119 measure sequence.  Polynomial moments, reflected-product
-- bounds and the OS0/OS5 uniform-integrability consequences stay downstream in
-- the existing T5/R560 compiler chain.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.YangMillsLiteralCMP119QuantitativeMomentsRound559Exact as R559
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

literalCMP119ExponentialMomentTheorem :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    {S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Agda.Builtin.Nat.Nat Configuration
          DASHI.Foundations.RealAnalysisAxioms.ℝ
          (Configuration → DASHI.Foundations.RealAnalysisAxioms.ℝ)
          Position CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          HilbertSpace Hamiltonian VacuumState)}
    {inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    {group : G} →
  T5.ExponentialMomentProducer
    (Gram.operations
      (Carrier.cmp119PhysicalMeasureConvergenceData inputs group))
    (Gram.measureSequence
      (Carrier.cmp119PhysicalMeasureConvergenceData inputs group))
    (Gram.RenormalizedObservable
      (Carrier.cmp119PhysicalMeasureConvergenceData inputs group)) →
  R559.LiteralCMP119QuantitativeMomentSource
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S inputs group
literalCMP119ExponentialMomentTheorem moments = record
  { R559.LiteralCMP119QuantitativeMomentSource.moments = moments
  }
