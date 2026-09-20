{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsLiteralCylinderOSReflectionPositiveExact where

------------------------------------------------------------------------
-- NORMALIZED CMP119 CYLINDER LIMIT + FINITE WILSON RP -> CONTINUUM OS2
--
-- Work on the common expectation-functional measure carrier
--
--     Measure = Observable -> ℝ.
--
-- Finite physical measures are represented by their normalized expectations;
-- the continuum measure is the normalized cylinder limit expectation.  Thus
-- finite and continuum reflected Gram forms live on one carrier definitionally.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Normalized
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS

record CylinderOSObservableAlgebra (Observable : Set) : Set₁ where
  field
    reflectObservable : Observable → Observable
    multiplyObservable : Observable → Observable → Observable

open CylinderOSObservableAlgebra public

ExpectationMeasure : Set → Set
ExpectationMeasure Observable = Observable → ℝ

expectationOperations :
  ∀ {Observable} →
  CylinderOSObservableAlgebra Observable →
  Gram.PhysicalOSOperations
    (ExpectationMeasure Observable) Observable ℝ
expectationOperations observableAlgebra = record
  { Gram.PhysicalOSOperations.zero = 0ℝ
  ; Gram.PhysicalOSOperations.add = _+ℝ_
  ; Gram.PhysicalOSOperations.multiply = _*ℝ_
  ; Gram.PhysicalOSOperations.conjugate = λ scalar → scalar
  ; Gram.PhysicalOSOperations.reflectObservable =
      reflectObservable observableAlgebra
  ; Gram.PhysicalOSOperations.multiplyObservable =
      multiplyObservable observableAlgebra
  ; Gram.PhysicalOSOperations.expectation =
      λ measure observable → measure observable
  }

finiteExpectationMeasure :
  ∀ {Observable algebra quotient division}
    (source :
      Normalized.NormalizedCylinderSourceData
        Observable algebra quotient division) →
  Nat → ExpectationMeasure Observable
finiteExpectationMeasure source cutoff =
  Normalized.finiteNormalized source cutoff

continuumExpectationMeasure :
  ∀ {Observable algebra quotient division}
    (source :
      Normalized.NormalizedCylinderSourceData
        Observable algebra quotient division) →
  ExpectationMeasure Observable
continuumExpectationMeasure source =
  Normalized.continuumNormalized source

record LiteralCylinderOSReflectionPositivityInputs
    {Observable : Set}
    {sequenceLimit}
    (limitLaws :
      RealLimit.CanonicalRealLimitLaws sequenceLimit)
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Normalized.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    (source :
      Normalized.NormalizedCylinderSourceData
        Observable
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient division)
    (observableAlgebra :
      CylinderOSObservableAlgebra Observable) : Set₁ where
  field
    finiteReflectionPositive :
      ∀ cutoff
        (family : Gram.PhysicalOSFiniteTestFamily Observable ℝ) →
      0ℝ ≤ℝ
        Gram.physicalReflectedGramQuadraticForm
          (expectationOperations observableAlgebra)
          (finiteExpectationMeasure source cutoff)
          family

open LiteralCylinderOSReflectionPositivityInputs public

gramEntryConverges :
  ∀ {Observable sequenceLimit}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Normalized.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    {source :
      Normalized.NormalizedCylinderSourceData
        Observable
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient division}
    {observableAlgebra :
      CylinderOSObservableAlgebra Observable}
    (inputs :
      LiteralCylinderOSReflectionPositivityInputs
        limitLaws source observableAlgebra)
    left right →
  RealLimit.Converges sequenceLimit
    (λ cutoff →
      Gram.physicalReflectedGramEntry
        (expectationOperations observableAlgebra)
        (finiteExpectationMeasure source cutoff)
        left right)
    (Gram.physicalReflectedGramEntry
      (expectationOperations observableAlgebra)
      (continuumExpectationMeasure source)
      left right)
gramEntryConverges
    {limitLaws = limitLaws}
    {source = source}
    {observableAlgebra = observableAlgebra}
    inputs left right =
  let
    observable =
      multiplyObservable observableAlgebra
        (reflectObservable observableAlgebra
          (Gram.observable left))
        (Gram.observable right)

    coefficient =
      Gram.coefficient left *ℝ Gram.coefficient right

    expectationConverges =
      Normalized.normalizedConverges source observable
  in
  Gram.multiplyConstantConverges
    (RealLimit.canonicalGramScalarConvergence limitLaws)
    coefficient
    (λ cutoff →
      finiteExpectationMeasure source cutoff observable)
    (continuumExpectationMeasure source observable)
    expectationConverges

gramQuadraticFormConverges :
  ∀ {Observable sequenceLimit}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Normalized.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    {source :
      Normalized.NormalizedCylinderSourceData
        Observable
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient division}
    {observableAlgebra :
      CylinderOSObservableAlgebra Observable}
    (inputs :
      LiteralCylinderOSReflectionPositivityInputs
        limitLaws source observableAlgebra)
    (family : Gram.PhysicalOSFiniteTestFamily Observable ℝ) →
  RealLimit.Converges sequenceLimit
    (λ cutoff →
      Gram.physicalReflectedGramQuadraticForm
        (expectationOperations observableAlgebra)
        (finiteExpectationMeasure source cutoff)
        family)
    (Gram.physicalReflectedGramQuadraticForm
      (expectationOperations observableAlgebra)
      (continuumExpectationMeasure source)
      family)
gramQuadraticFormConverges
    {limitLaws = limitLaws}
    {source = source}
    {observableAlgebra = observableAlgebra}
    inputs family =
  Gram.finiteSumCommutesWithLimit
    (RealLimit.canonicalGramScalarConvergence limitLaws)
    (Gram.tests family)
    (λ left cutoff →
      Gram.sumList _ 0ℝ (Gram.tests family)
        (λ right →
          Gram.physicalReflectedGramEntry
            (expectationOperations observableAlgebra)
            (finiteExpectationMeasure source cutoff)
            left right))
    (λ left →
      Gram.sumList _ 0ℝ (Gram.tests family)
        (λ right →
          Gram.physicalReflectedGramEntry
            (expectationOperations observableAlgebra)
            (continuumExpectationMeasure source)
            left right))
    (λ left →
      Gram.finiteSumCommutesWithLimit
        (RealLimit.canonicalGramScalarConvergence limitLaws)
        (Gram.tests family)
        (λ right cutoff →
          Gram.physicalReflectedGramEntry
            (expectationOperations observableAlgebra)
            (finiteExpectationMeasure source cutoff)
            left right)
        (λ right →
          Gram.physicalReflectedGramEntry
            (expectationOperations observableAlgebra)
            (continuumExpectationMeasure source)
            left right)
        (λ right →
          gramEntryConverges inputs left right))

asOSGramLimitData :
  ∀ {Observable sequenceLimit}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Normalized.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    {source :
      Normalized.NormalizedCylinderSourceData
        Observable
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient division}
    {observableAlgebra :
      CylinderOSObservableAlgebra Observable} →
  LiteralCylinderOSReflectionPositivityInputs
    limitLaws source observableAlgebra →
  OS.OSGramLimitData
    (ExpectationMeasure Observable)
    (Gram.PhysicalOSFiniteTestFamily Observable ℝ)
    ℝ
asOSGramLimitData
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {source = source}
    {observableAlgebra = observableAlgebra}
    inputs = record
  { OS.OSGramLimitData.finiteSchwinger =
      finiteExpectationMeasure source
  ; OS.OSGramLimitData.continuumSchwinger =
      continuumExpectationMeasure source
  ; OS.OSGramLimitData.reflectedGramQuadraticForm =
      λ measure family →
        Gram.physicalReflectedGramQuadraticForm
          (expectationOperations observableAlgebra)
          measure family
  ; OS.OSGramLimitData.scalarLimit = record
      { DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact.SequentialLimit.limit =
          RealLimit.Seq.limit sequenceLimit
      ; DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact.SequentialLimit.Converges =
          RealLimit.Converges sequenceLimit
      ; DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact.SequentialLimit.sequenceConvergesToLimit =
          λ sequence → Agda.Builtin.Equality.refl
      }
  ; OS.OSGramLimitData.Nonnegative =
      λ scalar → 0ℝ ≤ℝ scalar
  ; OS.OSGramLimitData.gramQuadraticFormConverges =
      gramQuadraticFormConverges inputs
  ; OS.OSGramLimitData.finiteGramNonnegative =
      finiteReflectionPositive inputs
  ; OS.OSGramLimitData.nonnegativeConeClosed =
      λ sequence target converges pointwise →
        helper
          (RealLimit.nonnegativeLimitClosed
            limitLaws sequence pointwise)
          converges
  }
  where
  helper :
    ∀ {left right : ℝ} →
    0ℝ ≤ℝ left → left ≡ right → 0ℝ ≤ℝ right
  helper proof Agda.Builtin.Equality.refl = proof

literalContinuumReflectionPositive :
  ∀ {Observable sequenceLimit}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Normalized.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    {source :
      Normalized.NormalizedCylinderSourceData
        Observable
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient division}
    {observableAlgebra :
      CylinderOSObservableAlgebra Observable}
    (inputs :
      LiteralCylinderOSReflectionPositivityInputs
        limitLaws source observableAlgebra) →
  OS.GramReflectionPositive
    (asOSGramLimitData inputs)
    (continuumExpectationMeasure source)
literalContinuumReflectionPositive inputs =
  OS.continuumReflectionPositiveFromGramTopology
    (asOSGramLimitData inputs)

literalCylinderGramConvergenceCompilerLevel : ProofLevel
literalCylinderGramConvergenceCompilerLevel = machineChecked

literalCylinderContinuumOS2CompilerLevel : ProofLevel
literalCylinderContinuumOS2CompilerLevel = machineChecked

-- The only physical input at this OS2 layer is finite Wilson reflection
-- positivity for the literal normalized finite expectations.
literalFiniteWilsonReflectionPositivityLevel : ProofLevel
literalFiniteWilsonReflectionPositivityLevel = conditional
