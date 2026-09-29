{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsConcreteQuantitativeOS05Round514Exact where

------------------------------------------------------------------------
-- GOAL-1 A4/A5 / ROUND514:
-- CONCRETE FINITE REGULARITY/GROWTH FROM THE QUANTITATIVE T5 PRODUCER
--
-- R500 leaves two "quantitative bounds imply finite predicate" fields because
-- the finite predicates were arbitrary.  Here we choose the concrete finite
-- predicates to be exactly the source quantities the T5 producer proves:
--
--   finite regularity:
--     all polynomial insertion moments obey the uniform factorial/exponential
--     bound on every renormalized observable;
--
--   finite growth:
--     the exponential moment itself obeys the uniform source bound.
--
-- The SAME-family attachment identifies the T5 diagonal expectation with the
-- literal CMP119 finite expectation.  After that identification, both finite
-- predicates are compiler output.  No additional analytic estimate is used.
--
-- This module deliberately does NOT manufacture the continuum OS0/OS5
-- interpretation.  The selected standard closure/OS semantics remain a
-- separate authority.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OS05CanonicalLimitExact as OS05
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record ConcreteQuantitativeOS05Inputs
    (Configuration Measure : Set)
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
    : Set₂ where
  field
    quantitative :
      T5.PhysicalExpectationProducerData
        Measure (Configuration → ℝ) ℝ

    sameFiniteExpectation :
      ∀ cutoff observable →
      Gram.expectation
        (T5.operations (T5.thermodynamic quantitative))
        (T5.diagonalMeasure quantitative cutoff)
        observable
      ≡
      Limit.finiteExpectation family cutoff observable

open ConcreteQuantitativeOS05Inputs public

quantitativeExpectation :
  ∀ {Configuration Measure sequenceLimit limitLaws quotient division family} →
  ConcreteQuantitativeOS05Inputs
    Configuration Measure
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {quotient = quotient}
    {division = division}
    family →
  Nat → OS05.ExpectationFunctional Configuration
quantitativeExpectation inputs cutoff =
  Gram.expectation
    (T5.operations (T5.thermodynamic (quantitative inputs)))
    (T5.diagonalMeasure (quantitative inputs) cutoff)

------------------------------------------------------------------------
-- Concrete finite predicates.
------------------------------------------------------------------------

FiniteMomentRegularity :
  ∀ {Configuration Measure sequenceLimit limitLaws quotient division family} →
  ConcreteQuantitativeOS05Inputs
    Configuration Measure
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {quotient = quotient}
    {division = division}
    family →
  OS05.ExpectationFunctional Configuration → Set
FiniteMomentRegularity inputs expectation =
  Σ Nat
    (λ cutoff →
      (∀ observable →
        expectation observable
        ≡ quantitativeExpectation inputs cutoff observable)
      ×
      (∀ degree observable →
        T5.RenormalizedObservable
          (T5.thermodynamic (quantitative inputs))
          observable →
        T5.LessEqual (T5.moments (quantitative inputs))
          (expectation
            (T5.powerObservable
              (T5.moments (quantitative inputs))
              degree
              (T5.absoluteObservable
                (T5.moments (quantitative inputs))
                observable)))
          (T5.multiply (T5.moments (quantitative inputs))
            (T5.factorial (T5.moments (quantitative inputs)) degree)
            (T5.divide (T5.moments (quantitative inputs))
              (T5.exponentialMomentBound
                (T5.moments (quantitative inputs))
                observable)
              (T5.lambda (T5.moments (quantitative inputs)))))))

FiniteExponentialGrowth :
  ∀ {Configuration Measure sequenceLimit limitLaws quotient division family} →
  ConcreteQuantitativeOS05Inputs
    Configuration Measure
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {quotient = quotient}
    {division = division}
    family →
  OS05.ExpectationFunctional Configuration → Set
FiniteExponentialGrowth inputs expectation =
  Σ Nat
    (λ cutoff →
      (∀ observable →
        expectation observable
        ≡ quantitativeExpectation inputs cutoff observable)
      ×
      (∀ observable →
        T5.RenormalizedObservable
          (T5.thermodynamic (quantitative inputs))
          observable →
        T5.LessEqual (T5.moments (quantitative inputs))
          (expectation
            (T5.exponentialObservable
              (T5.moments (quantitative inputs))
              (T5.lambda (T5.moments (quantitative inputs)))
              (T5.absoluteObservable
                (T5.moments (quantitative inputs))
                observable)))
          (T5.exponentialMomentBound
            (T5.moments (quantitative inputs))
            observable)))

------------------------------------------------------------------------
-- The two former analytic implication leaves.
------------------------------------------------------------------------

finiteMomentRegularity :
  ∀ {Configuration Measure sequenceLimit limitLaws quotient division family}
    (inputs :
      ConcreteQuantitativeOS05Inputs
        Configuration Measure
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family)
    cutoff →
  FiniteMomentRegularity inputs
    (Limit.finiteExpectation family cutoff)
finiteMomentRegularity inputs cutoff =
  cutoff ,
    ( (λ observable →
        sym (sameFiniteExpectation inputs cutoff observable))
    , (λ degree observable admissible →
        subst
          (λ value →
            T5.LessEqual (T5.moments (quantitative inputs))
              value
              (T5.multiply (T5.moments (quantitative inputs))
                (T5.factorial (T5.moments (quantitative inputs)) degree)
                (T5.divide (T5.moments (quantitative inputs))
                  (T5.exponentialMomentBound
                    (T5.moments (quantitative inputs))
                    observable)
                  (T5.lambda (T5.moments (quantitative inputs))))))
          (sameFiniteExpectation inputs cutoff
            (T5.powerObservable
              (T5.moments (quantitative inputs))
              degree
              (T5.absoluteObservable
                (T5.moments (quantitative inputs))
                observable)))
          (T5.singleScaleInsertionMomentBound
            (T5.moments (quantitative inputs))
            degree observable admissible cutoff))
    )

finiteExponentialGrowth :
  ∀ {Configuration Measure sequenceLimit limitLaws quotient division family}
    (inputs :
      ConcreteQuantitativeOS05Inputs
        Configuration Measure
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        family)
    cutoff →
  FiniteExponentialGrowth inputs
    (Limit.finiteExpectation family cutoff)
finiteExponentialGrowth inputs cutoff =
  cutoff ,
    ( (λ observable →
        sym (sameFiniteExpectation inputs cutoff observable))
    , (λ observable admissible →
        subst
          (λ value →
            T5.LessEqual (T5.moments (quantitative inputs))
              value
              (T5.exponentialMomentBound
                (T5.moments (quantitative inputs))
                observable))
          (sameFiniteExpectation inputs cutoff
            (T5.exponentialObservable
              (T5.moments (quantitative inputs))
              (T5.lambda (T5.moments (quantitative inputs)))
              (T5.absoluteObservable
                (T5.moments (quantitative inputs))
                observable)))
          (T5.exponentialMomentUniformBound
            (T5.moments (quantitative inputs))
            observable admissible cutoff))
    )

round514FiniteMomentRegularityCompilerLevel : ProofLevel
round514FiniteMomentRegularityCompilerLevel = machineChecked

round514FiniteExponentialGrowthCompilerLevel : ProofLevel
round514FiniteExponentialGrowthCompilerLevel = machineChecked

-- Only the same-family expectation attachment remains before these concrete
-- finite predicates are available.
literalRound514AdditionalFiniteRegularityEstimateLevel : ProofLevel
literalRound514AdditionalFiniteRegularityEstimateLevel = machineChecked

literalRound514AdditionalFiniteGrowthEstimateLevel : ProofLevel
literalRound514AdditionalFiniteGrowthEstimateLevel = machineChecked

-- Final continuum OS0/OS5 interpretation/closure is intentionally separate.
literalRound514ContinuumOS05InterpretationLevel : ProofLevel
literalRound514ContinuumOS05InterpretationLevel = conditional
