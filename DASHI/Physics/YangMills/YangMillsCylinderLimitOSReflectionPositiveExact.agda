{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact where

------------------------------------------------------------------------
-- ANY REAL CYLINDER LIMIT + FINITE REFLECTION POSITIVITY -> CONTINUUM OS2
------------------------------------------------------------------------

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit

record CylinderOSAlgebra (Observable : Set) : Set₁ where
  field
    reflectObservable : Observable → Observable
    multiplyObservable : Observable → Observable → Observable

open CylinderOSAlgebra public

ExpectationMeasure : Set → Set
ExpectationMeasure Observable = Observable → ℝ

operations :
  ∀ {Observable} →
  CylinderOSAlgebra Observable →
  Gram.PhysicalOSOperations
    (ExpectationMeasure Observable) Observable ℝ
operations observableAlgebra = record
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

record CylinderLimitOSInputs
    {Observable : Set}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (cylinder :
      Cylinder.ScalarCylinderExpectationLimitData
        Observable ℝ
        (RealLimit.canonicalCylinderAlgebra limitLaws))
    (observableAlgebra : CylinderOSAlgebra Observable) : Set₁ where
  field
    finiteReflectionPositive :
      ∀ cutoff
        (family : Gram.PhysicalOSFiniteTestFamily Observable ℝ) →
      0ℝ ≤ℝ
        Gram.physicalReflectedGramQuadraticForm
          (operations observableAlgebra)
          (λ observable →
            Cylinder.finiteExpectation cylinder cutoff observable)
          family

open CylinderLimitOSInputs public

entryConverges :
  ∀ {Observable sequenceLimit}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {cylinder :
      Cylinder.ScalarCylinderExpectationLimitData
        Observable ℝ
        (RealLimit.canonicalCylinderAlgebra limitLaws)}
    {observableAlgebra : CylinderOSAlgebra Observable}
    (inputs :
      CylinderLimitOSInputs limitLaws cylinder observableAlgebra)
    left right →
  RealLimit.Converges sequenceLimit
    (λ cutoff →
      Gram.physicalReflectedGramEntry
        (operations observableAlgebra)
        (λ observable →
          Cylinder.finiteExpectation cylinder cutoff observable)
        left right)
    (Gram.physicalReflectedGramEntry
      (operations observableAlgebra)
      (Cylinder.limitExpectation cylinder)
      left right)
entryConverges
    {limitLaws = limitLaws}
    {cylinder = cylinder}
    {observableAlgebra = observableAlgebra}
    inputs left right =
  Gram.multiplyConstantConverges
    (RealLimit.canonicalGramScalarConvergence limitLaws)
    (Gram.coefficient left *ℝ Gram.coefficient right)
    (λ cutoff →
      Cylinder.finiteExpectation cylinder cutoff
        (multiplyObservable observableAlgebra
          (reflectObservable observableAlgebra
            (Gram.observable left))
          (Gram.observable right)))
    (Cylinder.limitExpectation cylinder
      (multiplyObservable observableAlgebra
        (reflectObservable observableAlgebra
          (Gram.observable left))
        (Gram.observable right)))
    (Cylinder.selectedConverges cylinder
      (multiplyObservable observableAlgebra
        (reflectObservable observableAlgebra
          (Gram.observable left))
        (Gram.observable right)))

quadraticFormConverges :
  ∀ {Observable sequenceLimit}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {cylinder :
      Cylinder.ScalarCylinderExpectationLimitData
        Observable ℝ
        (RealLimit.canonicalCylinderAlgebra limitLaws)}
    {observableAlgebra : CylinderOSAlgebra Observable}
    (inputs :
      CylinderLimitOSInputs limitLaws cylinder observableAlgebra)
    family →
  RealLimit.Converges sequenceLimit
    (λ cutoff →
      Gram.physicalReflectedGramQuadraticForm
        (operations observableAlgebra)
        (λ observable →
          Cylinder.finiteExpectation cylinder cutoff observable)
        family)
    (Gram.physicalReflectedGramQuadraticForm
      (operations observableAlgebra)
      (Cylinder.limitExpectation cylinder)
      family)
quadraticFormConverges
    {limitLaws = limitLaws}
    {cylinder = cylinder}
    {observableAlgebra = observableAlgebra}
    inputs family =
  Gram.finiteSumCommutesWithLimit
    (RealLimit.canonicalGramScalarConvergence limitLaws)
    (Gram.tests family)
    (λ left cutoff →
      Gram.sumList _ 0ℝ (Gram.tests family)
        (λ right →
          Gram.physicalReflectedGramEntry
            (operations observableAlgebra)
            (λ observable →
              Cylinder.finiteExpectation cylinder cutoff observable)
            left right))
    (λ left →
      Gram.sumList _ 0ℝ (Gram.tests family)
        (λ right →
          Gram.physicalReflectedGramEntry
            (operations observableAlgebra)
            (Cylinder.limitExpectation cylinder)
            left right))
    (λ left →
      Gram.finiteSumCommutesWithLimit
        (RealLimit.canonicalGramScalarConvergence limitLaws)
        (Gram.tests family)
        (λ right cutoff →
          Gram.physicalReflectedGramEntry
            (operations observableAlgebra)
            (λ observable →
              Cylinder.finiteExpectation cylinder cutoff observable)
            left right)
        (λ right →
          Gram.physicalReflectedGramEntry
            (operations observableAlgebra)
            (Cylinder.limitExpectation cylinder)
            left right)
        (λ right → entryConverges inputs left right))

asOSGramLimitData :
  ∀ {Observable sequenceLimit}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {cylinder :
      Cylinder.ScalarCylinderExpectationLimitData
        Observable ℝ
        (RealLimit.canonicalCylinderAlgebra limitLaws)}
    {observableAlgebra : CylinderOSAlgebra Observable} →
  CylinderLimitOSInputs limitLaws cylinder observableAlgebra →
  OS.OSGramLimitData
    (ExpectationMeasure Observable)
    (Gram.PhysicalOSFiniteTestFamily Observable ℝ)
    ℝ
asOSGramLimitData
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {cylinder = cylinder}
    {observableAlgebra = observableAlgebra}
    inputs = record
  { OS.OSGramLimitData.finiteSchwinger =
      λ cutoff observable →
        Cylinder.finiteExpectation cylinder cutoff observable
  ; OS.OSGramLimitData.continuumSchwinger =
      Cylinder.limitExpectation cylinder
  ; OS.OSGramLimitData.reflectedGramQuadraticForm =
      λ measure family →
        Gram.physicalReflectedGramQuadraticForm
          (operations observableAlgebra) measure family
  ; OS.OSGramLimitData.scalarLimit = record
      { Limit.SequentialLimit.limit = Seq.limit sequenceLimit
      ; Limit.SequentialLimit.Converges =
          RealLimit.Converges sequenceLimit
      ; Limit.SequentialLimit.sequenceConvergesToLimit =
          λ sequence → Agda.Builtin.Equality.refl
      }
  ; OS.OSGramLimitData.Nonnegative =
      λ scalar → 0ℝ ≤ℝ scalar
  ; OS.OSGramLimitData.gramQuadraticFormConverges =
      quadraticFormConverges inputs
  ; OS.OSGramLimitData.finiteGramNonnegative =
      finiteReflectionPositive inputs
  ; OS.OSGramLimitData.nonnegativeConeClosed =
      λ sequence target converges pointwise →
        transportNonnegative
          (RealLimit.nonnegativeLimitClosed
            limitLaws sequence pointwise)
          converges
  }
  where
  transportNonnegative :
    ∀ {left right : ℝ} →
    0ℝ ≤ℝ left → left Agda.Builtin.Equality.≡ right → 0ℝ ≤ℝ right
  transportNonnegative proof Agda.Builtin.Equality.refl = proof

continuumReflectionPositive :
  ∀ {Observable sequenceLimit}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {cylinder :
      Cylinder.ScalarCylinderExpectationLimitData
        Observable ℝ
        (RealLimit.canonicalCylinderAlgebra limitLaws)}
    {observableAlgebra : CylinderOSAlgebra Observable}
    (inputs :
      CylinderLimitOSInputs limitLaws cylinder observableAlgebra) →
  OS.GramReflectionPositive
    (asOSGramLimitData inputs)
    (Cylinder.limitExpectation cylinder)
continuumReflectionPositive inputs =
  OS.continuumReflectionPositiveFromGramTopology
    (asOSGramLimitData inputs)

cylinderGramConvergenceCompilerLevel : ProofLevel
cylinderGramConvergenceCompilerLevel = machineChecked

cylinderContinuumOS2CompilerLevel : ProofLevel
cylinderContinuumOS2CompilerLevel = machineChecked

finiteWilsonReflectionPositivityInputLevel : ProofLevel
finiteWilsonReflectionPositivityInputLevel = conditional
