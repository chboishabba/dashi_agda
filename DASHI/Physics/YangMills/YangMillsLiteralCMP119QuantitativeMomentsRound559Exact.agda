{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsLiteralCMP119QuantitativeMomentsRound559Exact where

------------------------------------------------------------------------
-- GOAL-1 T5 / ROUND559:
-- PUT THE QUANTITATIVE MOMENT PRODUCER ON THE LITERAL CMP119 FAMILY ITSELF
--
-- R514 accepts an abstract T5 PhysicalExpectationProducerData and then asks for
-- a sameFiniteExpectation equality to the literal CMP119 family.
--
-- The pinned CMP119 covariance carrier already chooses:
--
--   measureSequence cutoff observable
--     := Limit.finiteExpectation literalFamily cutoff observable.
--
-- Therefore the preferred quantitative source should be an exponential-moment
-- producer on THAT exact measure sequence.  Polynomial and exponential finite
-- bounds then apply to the literal CMP119 expectations definitionally; no
-- post-hoc T5 <-> CMP119 expectation equality survives.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CovarianceCarrierExact as Carrier
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record LiteralCMP119QuantitativeMomentSource
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          HilbertSpace Hamiltonian VacuumState))
    (inputs :
      A.PinnedCMP119OSAxiomInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (group : G)
    : Set₂ where
  field
    moments :
      T5.ExponentialMomentProducer
        (Gram.operations
          (Carrier.cmp119PhysicalMeasureConvergenceData inputs group))
        (Gram.measureSequence
          (Carrier.cmp119PhysicalMeasureConvergenceData inputs group))
        (Gram.RenormalizedObservable
          (Carrier.cmp119PhysicalMeasureConvergenceData inputs group))

open LiteralCMP119QuantitativeMomentSource public

literalFiniteMomentBound :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S inputs group}
    (source :
      LiteralCMP119QuantitativeMomentSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S inputs group)
    degree observable cutoff →
  T5.LessEqual (moments source)
    (Limit.finiteExpectation
      (A.family inputs group)
      cutoff
      (T5.powerObservable (moments source) degree
        (T5.absoluteObservable (moments source) observable)))
    (T5.multiply (moments source)
      (T5.factorial (moments source) degree)
      (T5.divide (moments source)
        (T5.exponentialMomentBound (moments source) observable)
        (T5.lambda (moments source))))
literalFiniteMomentBound source degree observable cutoff =
  T5.singleScaleInsertionMomentBound
    (moments source)
    degree observable tt cutoff

literalFiniteExponentialBound :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S inputs group}
    (source :
      LiteralCMP119QuantitativeMomentSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S inputs group)
    observable cutoff →
  T5.LessEqual (moments source)
    (Limit.finiteExpectation
      (A.family inputs group)
      cutoff
      (T5.exponentialObservable
        (moments source)
        (T5.lambda (moments source))
        (T5.absoluteObservable (moments source) observable)))
    (T5.exponentialMomentBound (moments source) observable)
literalFiniteExponentialBound source observable cutoff =
  T5.exponentialMomentUniformBound
    (moments source)
    observable tt cutoff

round559LiteralCMP119MomentTransportLevel : ProofLevel
round559LiteralCMP119MomentTransportLevel = machineChecked

round559SameFiniteExpectationAttachmentRequired : Bool
round559SameFiniteExpectationAttachmentRequired = false

-- Genuine physical quantitative theorem: construct the exponential-moment
-- producer on the literal CMP119 sequence.
literalRound559CMP119ExponentialMomentProducerLevel : ProofLevel
literalRound559CMP119ExponentialMomentProducerLevel = conditional
