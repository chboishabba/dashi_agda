{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5SelectedWeakGramReflectionClosureExact where

------------------------------------------------------------------------
-- SELECTED-CONVERGENCE COMPLETE FINITE-GRAM RP CLOSURE
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Selected
import DASHI.Physics.YangMills.BalabanClayT5SelectedWeakExpectationClosureExact as Weak

record SelectedWeakGramScalarAlgebra
    {Measure Test Scalar : Set}
    {measureConvergence : Selected.SequentialConvergence Measure}
    (topology : Weak.SelectedWeakExpectationTopology
      Measure Test Scalar measureConvergence) : Set₁ where
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

open SelectedWeakGramScalarAlgebra public

record SelectedWeakReflectedTestSemantics
    {Measure Test Scalar : Set}
    {measureConvergence : Selected.SequentialConvergence Measure}
    (topology : Weak.SelectedWeakExpectationTopology
      Measure Test Scalar measureConvergence)
    (algebra : SelectedWeakGramScalarAlgebra topology) : Set₁ where
  field
    reflectTest : Test → Test
    multiplyTest : Test → Test → Test
    reflectedProductsAdmissible : ∀ left right →
      Weak.AdmissibleTest topology
        (multiplyTest (reflectTest left) right)

open SelectedWeakReflectedTestSemantics public

finiteSumConverges :
  ∀ {Measure Test Scalar A}
    {measureConvergence : Selected.SequentialConvergence Measure}
    {topology : Weak.SelectedWeakExpectationTopology
      Measure Test Scalar measureConvergence}
    (algebra : SelectedWeakGramScalarAlgebra topology)
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
    {measureConvergence : Selected.SequentialConvergence Measure}
    {topology : Weak.SelectedWeakExpectationTopology
      Measure Test Scalar measureConvergence} →
  (algebra : SelectedWeakGramScalarAlgebra topology) →
  SelectedWeakReflectedTestSemantics topology algebra →
  Measure →
  Gram.PhysicalPositiveTimeCylinderTest Test Scalar →
  Gram.PhysicalPositiveTimeCylinderTest Test Scalar → Scalar
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
    {measureConvergence : Selected.SequentialConvergence Measure}
    {topology : Weak.SelectedWeakExpectationTopology
      Measure Test Scalar measureConvergence} →
  (algebra : SelectedWeakGramScalarAlgebra topology) →
  SelectedWeakReflectedTestSemantics topology algebra →
  Measure → Gram.PhysicalOSFiniteTestFamily Test Scalar → Scalar
gramQuadraticForm algebra semantics measure family =
  Gram.sumList (add algebra) (zero algebra) (Gram.tests family)
    (λ left →
      Gram.sumList (add algebra) (zero algebra) (Gram.tests family)
        (λ right → gramEntry algebra semantics measure left right))

gramEntryConverges :
  ∀ {Measure Test Scalar}
    {measureConvergence : Selected.SequentialConvergence Measure}
    {topology : Weak.SelectedWeakExpectationTopology
      Measure Test Scalar measureConvergence}
    (algebra : SelectedWeakGramScalarAlgebra topology)
    (semantics : SelectedWeakReflectedTestSemantics topology algebra)
    sequence target →
  Selected.Converges measureConvergence sequence target →
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
    {measureConvergence : Selected.SequentialConvergence Measure}
    {topology : Weak.SelectedWeakExpectationTopology
      Measure Test Scalar measureConvergence}
    (algebra : SelectedWeakGramScalarAlgebra topology)
    (semantics : SelectedWeakReflectedTestSemantics topology algebra)
    sequence target →
  Selected.Converges measureConvergence sequence target →
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
        (λ right → gramEntryConverges algebra semantics sequence target convergence
          left right))

GramReflectionPositive :
  ∀ {Measure Test Scalar}
    {measureConvergence : Selected.SequentialConvergence Measure}
    {topology : Weak.SelectedWeakExpectationTopology
      Measure Test Scalar measureConvergence} →
  (algebra : SelectedWeakGramScalarAlgebra topology) →
  SelectedWeakReflectedTestSemantics topology algebra → Measure → Set
GramReflectionPositive algebra semantics measure =
  ∀ family → Nonnegative algebra (gramQuadraticForm algebra semantics measure family)

gramReflectionClosed :
  ∀ {Measure Test Scalar}
    {measureConvergence : Selected.SequentialConvergence Measure}
    {topology : Weak.SelectedWeakExpectationTopology
      Measure Test Scalar measureConvergence}
    (algebra : SelectedWeakGramScalarAlgebra topology)
    (semantics : SelectedWeakReflectedTestSemantics topology algebra) →
  ∀ sequence target →
  Selected.Converges measureConvergence sequence target →
  (∀ n → GramReflectionPositive algebra semantics (sequence n)) →
  GramReflectionPositive algebra semantics target
gramReflectionClosed algebra semantics sequence target convergence finiteRP family =
  nonnegativeClosed algebra
    (λ n → gramQuadraticForm algebra semantics (sequence n) family)
    (gramQuadraticForm algebra semantics target family)
    (gramQuadraticFormConverges algebra semantics sequence target convergence family)
    (λ n → finiteRP n family)

selectedWeakGramReflectionClosureLevel : ProofLevel
selectedWeakGramReflectionClosureLevel = machineChecked

selectedReflectedProductTestClassMeaningLevel : ProofLevel
selectedReflectedProductTestClassMeaningLevel = conditional
