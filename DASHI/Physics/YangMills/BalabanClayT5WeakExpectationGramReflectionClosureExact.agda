{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5WeakExpectationGramReflectionClosureExact where

------------------------------------------------------------------------
-- WEAK EXPECTATION TOPOLOGY -> GENERIC COMPLETE FINITE-GRAM RP CLOSURE
--
-- Reflection positivity for a measure is quantified over every finite positive-
-- time test family.  Each corresponding Gram quadratic form is a finite sum of
-- reflected-product expectations.  Therefore arbitrary-sequence RP closure is
-- not an independent physical theorem once the selected measure topology is
-- known to control those reflected-product expectations and the scalar
-- nonnegative cone is closed.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5WeakExpectationPropertyClosureExact as Weak

record WeakGramScalarAlgebra
    {Measure Test Scalar : Set}
    {measureLimit : Limit.SequentialLimit Measure}
    (topology : Weak.WeakExpectationTopology Measure Test Scalar measureLimit)
    : Set₁ where
  field
    zero : Scalar
    add multiply : Scalar → Scalar → Scalar
    conjugate : Scalar → Scalar

    addConverges : ∀ firstSequence firstLimit secondSequence secondLimit →
      Weak.ScalarConverges topology firstSequence firstLimit →
      Weak.ScalarConverges topology secondSequence secondLimit →
      Weak.ScalarConverges topology
        (λ n → add (firstSequence n) (secondSequence n))
        (add firstLimit secondLimit)

    multiplyConstantConverges : ∀ coefficient sequence target →
      Weak.ScalarConverges topology sequence target →
      Weak.ScalarConverges topology
        (λ n → multiply coefficient (sequence n))
        (multiply coefficient target)

    Nonnegative : Scalar → Set
    nonnegativeClosed : ∀ sequence target →
      Weak.ScalarConverges topology sequence target →
      (∀ n → Nonnegative (sequence n)) →
      Nonnegative target

open WeakGramScalarAlgebra public

record WeakReflectedTestSemantics
    {Measure Test Scalar : Set}
    {measureLimit : Limit.SequentialLimit Measure}
    (topology : Weak.WeakExpectationTopology Measure Test Scalar measureLimit)
    (algebra : WeakGramScalarAlgebra topology) : Set₁ where
  field
    reflectTest : Test → Test
    multiplyTest : Test → Test → Test
    reflectedProductsAdmissible : ∀ left right →
      Weak.AdmissibleTest topology
        (multiplyTest (reflectTest left) right)

open WeakReflectedTestSemantics public

finiteSumConverges :
  ∀ {Measure Test Scalar A}
    {measureLimit : Limit.SequentialLimit Measure}
    {topology : Weak.WeakExpectationTopology Measure Test Scalar measureLimit}
    (algebra : WeakGramScalarAlgebra topology)
    (items : List A)
    (sequence : A → Nat → Scalar)
    (target : A → Scalar) →
  (∀ item → Weak.ScalarConverges topology (sequence item) (target item)) →
  Weak.ScalarConverges topology
    (λ n → Gram.sumList (add algebra) (zero algebra) items
      (λ item → sequence item n))
    (Gram.sumList (add algebra) (zero algebra) items target)
finiteSumConverges {topology = topology} algebra [] sequence target pointwise =
  Weak.scalarConstantConverges topology (zero algebra)
finiteSumConverges {topology = topology} algebra (item ∷ items)
  sequence target pointwise =
  addConverges algebra
    (sequence item) (target item)
    (λ n → Gram.sumList (add algebra) (zero algebra) items
      (λ tail → sequence tail n))
    (Gram.sumList (add algebra) (zero algebra) items target)
    (pointwise item)
    (finiteSumConverges algebra items sequence target pointwise)

gramEntry :
  ∀ {Measure Test Scalar}
    {measureLimit : Limit.SequentialLimit Measure}
    {topology : Weak.WeakExpectationTopology Measure Test Scalar measureLimit} →
  (algebra : WeakGramScalarAlgebra topology) →
  WeakReflectedTestSemantics topology algebra →
  Measure →
  Gram.PhysicalPositiveTimeCylinderTest Test Scalar →
  Gram.PhysicalPositiveTimeCylinderTest Test Scalar →
  Scalar
gramEntry {topology = topology} algebra semantics measure left right =
  multiply algebra
    (multiply algebra
      (conjugate algebra (Gram.coefficient left))
      (Gram.coefficient right))
    (Weak.expectation topology measure
      (multiplyTest semantics
        (reflectTest semantics (Gram.observable left))
        (Gram.observable right)))

gramQuadraticForm :
  ∀ {Measure Test Scalar}
    {measureLimit : Limit.SequentialLimit Measure}
    {topology : Weak.WeakExpectationTopology Measure Test Scalar measureLimit} →
  (algebra : WeakGramScalarAlgebra topology) →
  WeakReflectedTestSemantics topology algebra →
  Measure → Gram.PhysicalOSFiniteTestFamily Test Scalar → Scalar
gramQuadraticForm algebra semantics measure family =
  Gram.sumList (add algebra) (zero algebra) (Gram.tests family)
    (λ left →
      Gram.sumList (add algebra) (zero algebra) (Gram.tests family)
        (λ right → gramEntry algebra semantics measure left right))

gramEntryConverges :
  ∀ {Measure Test Scalar}
    {measureLimit : Limit.SequentialLimit Measure}
    {topology : Weak.WeakExpectationTopology Measure Test Scalar measureLimit}
    (algebra : WeakGramScalarAlgebra topology)
    (semantics : WeakReflectedTestSemantics topology algebra)
    sequence target →
  Limit.Converges measureLimit sequence target →
  ∀ left right →
  Weak.ScalarConverges topology
    (λ n → gramEntry algebra semantics (sequence n) left right)
    (gramEntry algebra semantics target left right)
gramEntryConverges {topology = topology} algebra semantics
  sequence target convergence left right =
  multiplyConstantConverges algebra
    (multiply algebra
      (conjugate algebra (Gram.coefficient left))
      (Gram.coefficient right))
    (λ n → Weak.expectation topology (sequence n)
      (multiplyTest semantics
        (reflectTest semantics (Gram.observable left))
        (Gram.observable right)))
    (Weak.expectation topology target
      (multiplyTest semantics
        (reflectTest semantics (Gram.observable left))
        (Gram.observable right)))
    (Weak.expectationContinuous topology sequence target
      (multiplyTest semantics
        (reflectTest semantics (Gram.observable left))
        (Gram.observable right))
      convergence
      (reflectedProductsAdmissible semantics
        (Gram.observable left) (Gram.observable right)))

gramQuadraticFormConverges :
  ∀ {Measure Test Scalar}
    {measureLimit : Limit.SequentialLimit Measure}
    {topology : Weak.WeakExpectationTopology Measure Test Scalar measureLimit}
    (algebra : WeakGramScalarAlgebra topology)
    (semantics : WeakReflectedTestSemantics topology algebra)
    sequence target →
  Limit.Converges measureLimit sequence target →
  ∀ family →
  Weak.ScalarConverges topology
    (λ n → gramQuadraticForm algebra semantics (sequence n) family)
    (gramQuadraticForm algebra semantics target family)
gramQuadraticFormConverges algebra semantics sequence target convergence family =
  finiteSumConverges algebra (Gram.tests family)
    (λ left n →
      Gram.sumList (add algebra) (zero algebra) (Gram.tests family)
        (λ right → gramEntry algebra semantics (sequence n) left right))
    (λ left →
      Gram.sumList (add algebra) (zero algebra) (Gram.tests family)
        (λ right → gramEntry algebra semantics target left right))
    (λ left →
      finiteSumConverges algebra (Gram.tests family)
        (λ right n → gramEntry algebra semantics (sequence n) left right)
        (λ right → gramEntry algebra semantics target left right)
        (λ right →
          gramEntryConverges algebra semantics sequence target convergence
            left right))

GramReflectionPositive :
  ∀ {Measure Test Scalar}
    {measureLimit : Limit.SequentialLimit Measure}
    {topology : Weak.WeakExpectationTopology Measure Test Scalar measureLimit} →
  (algebra : WeakGramScalarAlgebra topology) →
  WeakReflectedTestSemantics topology algebra → Measure → Set
GramReflectionPositive algebra semantics measure =
  ∀ family → Nonnegative algebra (gramQuadraticForm algebra semantics measure family)

gramReflectionClosedFromWeakExpectation :
  ∀ {Measure Test Scalar}
    {measureLimit : Limit.SequentialLimit Measure}
    {topology : Weak.WeakExpectationTopology Measure Test Scalar measureLimit}
    (algebra : WeakGramScalarAlgebra topology)
    (semantics : WeakReflectedTestSemantics topology algebra) →
  ∀ sequence target →
  Limit.Converges measureLimit sequence target →
  (∀ n → GramReflectionPositive algebra semantics (sequence n)) →
  GramReflectionPositive algebra semantics target
gramReflectionClosedFromWeakExpectation algebra semantics
  sequence target convergence finiteRP family =
  nonnegativeClosed algebra
    (λ n → gramQuadraticForm algebra semantics (sequence n) family)
    (gramQuadraticForm algebra semantics target family)
    (gramQuadraticFormConverges algebra semantics sequence target convergence family)
    (λ n → finiteRP n family)

weakExpectationGramReflectionClosureCompilerLevel : ProofLevel
weakExpectationGramReflectionClosureCompilerLevel = machineChecked

-- No new Yang--Mills estimate is introduced here.  The remaining physical seam
-- is that the actual reflected-product cylinder tests belong to the same weak
-- test class used to define the selected measure topology.
reflectedProductWeakTestClassMeaningLevel : ProofLevel
reflectedProductWeakTestClassMeaningLevel = conditional
