{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5WeakExpectationPropertyClosureExact where

------------------------------------------------------------------------
-- WEAK EXPECTATION TOPOLOGY -> NORMALIZATION / POSITIVITY / GAUGE CLOSURE
--
-- The historical continuum closure asks for three unrelated sequential-closure
-- laws on an abstract Measure carrier.  On the usual weak measure topology they
-- are all consequences of one semantic fact: admissible test expectations are
-- continuous under measure convergence, together with Hausdorff/closed-cone
-- properties of the scalar convergence relation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit

record WeakExpectationTopology
    (Measure Test Scalar : Set)
    (measureLimit : Limit.SequentialLimit Measure) : Set₁ where
  field
    expectation : Measure → Test → Scalar
    AdmissibleTest : Test → Set

    ScalarConverges : (Nat → Scalar) → Scalar → Set
    scalarConstantConverges : ∀ value →
      ScalarConverges (λ _ → value) value
    scalarConvergenceCongruent : ∀ first second target →
      (∀ n → first n ≡ second n) →
      ScalarConverges first target →
      ScalarConverges second target
    scalarLimitUnique : ∀ sequence first second →
      ScalarConverges sequence first →
      ScalarConverges sequence second →
      first ≡ second

    expectationContinuous : ∀ sequence target test →
      Limit.Converges measureLimit sequence target →
      AdmissibleTest test →
      ScalarConverges
        (λ n → expectation (sequence n) test)
        (expectation target test)

open WeakExpectationTopology public

record WeakMeasurePropertySemantics
    {Measure Test Scalar : Set}
    {measureLimit : Limit.SequentialLimit Measure}
    (topology : WeakExpectationTopology Measure Test Scalar measureLimit)
    (Gauge : Set) : Set₁ where
  field
    unitTest : Test
    one : Scalar
    unitAdmissible : AdmissibleTest topology unitTest

    PositiveTest : Test → Set
    Nonnegative : Scalar → Set
    positiveTestsAdmissible : ∀ test → PositiveTest test →
      AdmissibleTest topology test
    nonnegativeClosed : ∀ sequence target →
      ScalarConverges topology sequence target →
      (∀ n → Nonnegative (sequence n)) →
      Nonnegative target

    gaugeAct : Gauge → Test → Test
    GaugeTest : Test → Set
    gaugeTestsAdmissible : ∀ test → GaugeTest test →
      AdmissibleTest topology test
    gaugeActsAdmissibly : ∀ gauge test → GaugeTest test →
      AdmissibleTest topology (gaugeAct gauge test)

open WeakMeasurePropertySemantics public

Normalized :
  ∀ {Measure Test Scalar} {measureLimit : Limit.SequentialLimit Measure}
    {topology : WeakExpectationTopology Measure Test Scalar measureLimit}
    {Gauge : Set} →
  WeakMeasurePropertySemantics topology Gauge → Measure → Set
Normalized {topology = topology} semantics measure =
  expectation topology measure (unitTest semantics) ≡ one semantics

Positive :
  ∀ {Measure Test Scalar} {measureLimit : Limit.SequentialLimit Measure}
    {topology : WeakExpectationTopology Measure Test Scalar measureLimit}
    {Gauge : Set} →
  WeakMeasurePropertySemantics topology Gauge → Measure → Set
Positive {topology = topology} semantics measure =
  ∀ test → PositiveTest semantics test →
  Nonnegative semantics (expectation topology measure test)

GaugeInvariant :
  ∀ {Measure Test Scalar} {measureLimit : Limit.SequentialLimit Measure}
    {topology : WeakExpectationTopology Measure Test Scalar measureLimit}
    {Gauge : Set} →
  WeakMeasurePropertySemantics topology Gauge → Measure → Set
GaugeInvariant {topology = topology} semantics measure =
  ∀ gauge test → GaugeTest semantics test →
  expectation topology measure (gaugeAct semantics gauge test)
  ≡ expectation topology measure test

normalizedClosedFromWeakExpectation :
  ∀ {Measure Test Scalar Gauge}
    {measureLimit : Limit.SequentialLimit Measure}
    {topology : WeakExpectationTopology Measure Test Scalar measureLimit}
    (semantics : WeakMeasurePropertySemantics topology Gauge) →
  ∀ sequence target →
  Limit.Converges measureLimit sequence target →
  (∀ n → Normalized semantics (sequence n)) →
  Normalized semantics target
normalizedClosedFromWeakExpectation {topology = topology} semantics
  sequence target convergence finiteNormalized =
  scalarLimitUnique topology
    (λ n → expectation topology (sequence n) (unitTest semantics))
    (expectation topology target (unitTest semantics))
    (one semantics)
    (expectationContinuous topology sequence target (unitTest semantics)
      convergence (unitAdmissible semantics))
    (scalarConvergenceCongruent topology
      (λ _ → one semantics)
      (λ n → expectation topology (sequence n) (unitTest semantics))
      (one semantics)
      (λ n → finiteNormalized n)
      (scalarConstantConverges topology (one semantics)))

positiveClosedFromWeakExpectation :
  ∀ {Measure Test Scalar Gauge}
    {measureLimit : Limit.SequentialLimit Measure}
    {topology : WeakExpectationTopology Measure Test Scalar measureLimit}
    (semantics : WeakMeasurePropertySemantics topology Gauge) →
  ∀ sequence target →
  Limit.Converges measureLimit sequence target →
  (∀ n → Positive semantics (sequence n)) →
  Positive semantics target
positiveClosedFromWeakExpectation {topology = topology} semantics
  sequence target convergence finitePositive test positiveTest =
  nonnegativeClosed semantics
    (λ n → expectation topology (sequence n) test)
    (expectation topology target test)
    (expectationContinuous topology sequence target test convergence
      (positiveTestsAdmissible semantics test positiveTest))
    (λ n → finitePositive n test positiveTest)

gaugeInvariantClosedFromWeakExpectation :
  ∀ {Measure Test Scalar Gauge}
    {measureLimit : Limit.SequentialLimit Measure}
    {topology : WeakExpectationTopology Measure Test Scalar measureLimit}
    (semantics : WeakMeasurePropertySemantics topology Gauge) →
  ∀ sequence target →
  Limit.Converges measureLimit sequence target →
  (∀ n → GaugeInvariant semantics (sequence n)) →
  GaugeInvariant semantics target
gaugeInvariantClosedFromWeakExpectation {topology = topology} semantics
  sequence target convergence finiteGauge gauge test gaugeTest =
  scalarLimitUnique topology
    (λ n → expectation topology (sequence n) (gaugeAct semantics gauge test))
    (expectation topology target (gaugeAct semantics gauge test))
    (expectation topology target test)
    (expectationContinuous topology sequence target
      (gaugeAct semantics gauge test) convergence
      (gaugeActsAdmissibly semantics gauge test gaugeTest))
    (scalarConvergenceCongruent topology
      (λ n → expectation topology (sequence n) test)
      (λ n → expectation topology (sequence n) (gaugeAct semantics gauge test))
      (expectation topology target test)
      (λ n → finiteGauge n gauge test gaugeTest)
      (expectationContinuous topology sequence target test convergence
        (gaugeTestsAdmissible semantics test gaugeTest)))

weakExpectationPropertyClosureCompilerLevel : ProofLevel
weakExpectationPropertyClosureCompilerLevel = machineChecked

-- The physical seam is now one topology/semantics identification: the selected
-- measure convergence must control expectations on the declared test class.
selectedMeasureWeakExpectationTopologyLevel : ProofLevel
selectedMeasureWeakExpectationTopologyLevel = conditional

scalarHausdorffAndPositiveConeClosureLevel : ProofLevel
scalarHausdorffAndPositiveConeClosureLevel = standardImported
