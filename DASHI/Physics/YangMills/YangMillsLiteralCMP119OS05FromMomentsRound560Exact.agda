{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsLiteralCMP119OS05FromMomentsRound560Exact where

------------------------------------------------------------------------
-- GOAL-1 T5/A4/A5 / ROUND560:
-- LITERAL CMP119 MOMENT SOURCE -> CANONICAL OS0/OS5 LIMIT DATA
--
-- R559 places the exponential-moment producer on the literal CMP119 finite
-- expectation sequence itself.  Therefore the finite regularity/growth
-- predicates can be defined directly from those source bounds, with no
-- same-family equality premise.
--
-- Only the standard closure of those concrete finite predicates to the
-- canonical limit remains as functional-analysis authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ; _,_; _×_)
open import Agda.Builtin.Unit using (tt)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OS05CanonicalLimitExact as OS05
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsLiteralCMP119QuantitativeMomentsRound559Exact as R559
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record LiteralCMP119OS05ClosureAuthority
    (Configuration : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    (family :
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division)
    (FiniteRegularity FiniteGrowthControl :
      OS05.ExpectationFunctional Configuration → Set)
    : Set₂ where
  field
    ContinuumRegularity :
      OS05.ExpectationFunctional Configuration → Set

    ContinuumGrowthControl :
      OS05.ExpectationFunctional Configuration → Set

    regularityClosedUnderCanonicalLimit :
      (∀ cutoff →
        FiniteRegularity
          (Limit.finiteExpectation family cutoff)) →
      ContinuumRegularity
        (Limit.limitExpectation family)

    growthClosedUnderCanonicalLimit :
      (∀ cutoff →
        FiniteGrowthControl
          (Limit.finiteExpectation family cutoff)) →
      ContinuumGrowthControl
        (Limit.limitExpectation family)

open LiteralCMP119OS05ClosureAuthority public

FiniteMomentRegularity :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S inputs group}
    (source :
      R559.LiteralCMP119QuantitativeMomentSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S inputs group) →
  OS05.ExpectationFunctional Configuration → Set
FiniteMomentRegularity {inputs = inputs} {group = group} source expectation =
  Σ Nat
    (λ cutoff →
      (∀ observable →
        expectation observable
        ≡ Limit.finiteExpectation (A.family inputs group) cutoff observable)
      ×
      (∀ degree observable →
        T5.LessEqual (R559.moments source)
          (expectation
            (T5.powerObservable
              (R559.moments source)
              degree
              (T5.absoluteObservable
                (R559.moments source)
                observable)))
          (T5.multiply (R559.moments source)
            (T5.factorial (R559.moments source) degree)
            (T5.divide (R559.moments source)
              (T5.exponentialMomentBound
                (R559.moments source) observable)
              (T5.lambda (R559.moments source))))))

FiniteExponentialGrowth :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S inputs group}
    (source :
      R559.LiteralCMP119QuantitativeMomentSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S inputs group) →
  OS05.ExpectationFunctional Configuration → Set
FiniteExponentialGrowth {inputs = inputs} {group = group} source expectation =
  Σ Nat
    (λ cutoff →
      (∀ observable →
        expectation observable
        ≡ Limit.finiteExpectation (A.family inputs group) cutoff observable)
      ×
      (∀ observable →
        T5.LessEqual (R559.moments source)
          (expectation
            (T5.exponentialObservable
              (R559.moments source)
              (T5.lambda (R559.moments source))
              (T5.absoluteObservable
                (R559.moments source)
                observable)))
          (T5.exponentialMomentBound
            (R559.moments source) observable)))

finiteMomentRegularity :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S inputs group}
    (source :
      R559.LiteralCMP119QuantitativeMomentSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S inputs group)
    cutoff →
  FiniteMomentRegularity source
    (Limit.finiteExpectation (A.family inputs group) cutoff)
finiteMomentRegularity source cutoff =
  cutoff ,
    ( (λ observable → refl)
    , (λ degree observable →
        R559.literalFiniteMomentBound
          source degree observable cutoff)
    )

finiteExponentialGrowth :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S inputs group}
    (source :
      R559.LiteralCMP119QuantitativeMomentSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S inputs group)
    cutoff →
  FiniteExponentialGrowth source
    (Limit.finiteExpectation (A.family inputs group) cutoff)
finiteExponentialGrowth source cutoff =
  cutoff ,
    ( (λ observable → refl)
    , (λ observable →
        R559.literalFiniteExponentialBound
          source observable cutoff)
    )

asCanonicalOS05 :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
      sequenceLimit limitLaws quotient division S inputs group}
    (source :
      R559.LiteralCMP119QuantitativeMomentSource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor HilbertSpace Hamiltonian VacuumState
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S inputs group)
    (closure :
      LiteralCMP119OS05ClosureAuthority
        Configuration
        (A.family inputs group)
        (FiniteMomentRegularity source)
        (FiniteExponentialGrowth source)) →
  OS05.CanonicalCMP119OS05LimitData
    Configuration
    (A.family inputs group)
asCanonicalOS05 source closure = record
  { OS05.CanonicalCMP119OS05LimitData.FiniteRegularity =
      FiniteMomentRegularity source
  ; OS05.CanonicalCMP119OS05LimitData.ContinuumRegularity =
      ContinuumRegularity closure
  ; OS05.CanonicalCMP119OS05LimitData.FiniteGrowthControl =
      FiniteExponentialGrowth source
  ; OS05.CanonicalCMP119OS05LimitData.ContinuumGrowthControl =
      ContinuumGrowthControl closure
  ; OS05.CanonicalCMP119OS05LimitData.finiteRegularity =
      finiteMomentRegularity source
  ; OS05.CanonicalCMP119OS05LimitData.finiteGrowthControl =
      finiteExponentialGrowth source
  ; OS05.CanonicalCMP119OS05LimitData.regularityClosedUnderCanonicalLimit =
      regularityClosedUnderCanonicalLimit closure
  ; OS05.CanonicalCMP119OS05LimitData.growthClosedUnderCanonicalLimit =
      growthClosedUnderCanonicalLimit closure
  }

round560FiniteOS05FromLiteralMomentsLevel : ProofLevel
round560FiniteOS05FromLiteralMomentsLevel = machineChecked

round560SameFamilyExpectationAttachmentRequired : Bool
round560SameFamilyExpectationAttachmentRequired = false

round560CanonicalClosureAuthorityLevel : ProofLevel
round560CanonicalClosureAuthorityLevel = standardImported

literalRound560CMP119MomentSourceLevel : ProofLevel
literalRound560CMP119MomentSourceLevel =
  R559.literalRound559CMP119ExponentialMomentProducerLevel
