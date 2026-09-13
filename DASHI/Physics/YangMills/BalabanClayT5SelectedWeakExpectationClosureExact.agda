{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5SelectedWeakExpectationClosureExact where

------------------------------------------------------------------------
-- SELECTED-CONVERGENCE WEAK EXPECTATION CLOSURE
--
-- Preferred T2/T3 compiler on the ordinary convergence relation.  It derives
-- normalization, positivity, action invariance, and extracted-cluster test
-- agreement without any total limit operator.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as Subsequence
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Selected

record SelectedWeakExpectationTopology
    (Measure Test Scalar : Set)
    (measureConvergence : Selected.SequentialConvergence Measure) : Set₁ where
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
    scalarConvergenceRestrictsToSubsequence :
      ∀ sequence target →
      ScalarConverges sequence target →
      (subsequence : Subsequence.SubsequenceWitness sequence) →
      ScalarConverges (Subsequence.values subsequence) target

    expectationContinuous : ∀ sequence target test →
      Selected.Converges measureConvergence sequence target →
      AdmissibleTest test →
      ScalarConverges
        (λ n → expectation (sequence n) test)
        (expectation target test)

open SelectedWeakExpectationTopology public

record SelectedWeakMeasurePropertySemantics
    {Measure Test Scalar : Set}
    {measureConvergence : Selected.SequentialConvergence Measure}
    (topology : SelectedWeakExpectationTopology
      Measure Test Scalar measureConvergence)
    (Action : Set) : Set₁ where
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

    act : Action → Test → Test
    ActionTest : Test → Set
    actionTestsAdmissible : ∀ test → ActionTest test →
      AdmissibleTest topology test
    actionPreservesAdmissibility : ∀ action test → ActionTest test →
      AdmissibleTest topology (act action test)

open SelectedWeakMeasurePropertySemantics public

Normalized :
  ∀ {Measure Test Scalar Action measureConvergence topology} →
  SelectedWeakMeasurePropertySemantics
    {Measure} {Test} {Scalar} {measureConvergence} topology Action →
  Measure → Set
Normalized {topology = topology} semantics measure =
  expectation topology measure (unitTest semantics) ≡ one semantics

Positive :
  ∀ {Measure Test Scalar Action measureConvergence topology} →
  SelectedWeakMeasurePropertySemantics
    {Measure} {Test} {Scalar} {measureConvergence} topology Action →
  Measure → Set
Positive {topology = topology} semantics measure =
  ∀ test → PositiveTest semantics test →
  Nonnegative semantics (expectation topology measure test)

ActionInvariant :
  ∀ {Measure Test Scalar Action measureConvergence topology} →
  SelectedWeakMeasurePropertySemantics
    {Measure} {Test} {Scalar} {measureConvergence} topology Action →
  Measure → Set
ActionInvariant {topology = topology} semantics measure =
  ∀ action test → ActionTest semantics test →
  expectation topology measure (act semantics action test)
  ≡ expectation topology measure test

normalizedClosed :
  ∀ {Measure Test Scalar Action}
    {measureConvergence : Selected.SequentialConvergence Measure}
    {topology : SelectedWeakExpectationTopology
      Measure Test Scalar measureConvergence}
    (semantics : SelectedWeakMeasurePropertySemantics topology Action) →
  ∀ sequence target →
  Selected.Converges measureConvergence sequence target →
  (∀ n → Normalized semantics (sequence n)) →
  Normalized semantics target
normalizedClosed {topology = topology} semantics
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
      (λ n → sym (finiteNormalized n))
      (scalarConstantConverges topology (one semantics)))

positiveClosed :
  ∀ {Measure Test Scalar Action}
    {measureConvergence : Selected.SequentialConvergence Measure}
    {topology : SelectedWeakExpectationTopology
      Measure Test Scalar measureConvergence}
    (semantics : SelectedWeakMeasurePropertySemantics topology Action) →
  ∀ sequence target →
  Selected.Converges measureConvergence sequence target →
  (∀ n → Positive semantics (sequence n)) →
  Positive semantics target
positiveClosed {topology = topology} semantics
  sequence target convergence finitePositive test positiveTest =
  nonnegativeClosed semantics
    (λ n → expectation topology (sequence n) test)
    (expectation topology target test)
    (expectationContinuous topology sequence target test convergence
      (positiveTestsAdmissible semantics test positiveTest))
    (λ n → finitePositive n test positiveTest)

actionInvariantClosed :
  ∀ {Measure Test Scalar Action}
    {measureConvergence : Selected.SequentialConvergence Measure}
    {topology : SelectedWeakExpectationTopology
      Measure Test Scalar measureConvergence}
    (semantics : SelectedWeakMeasurePropertySemantics topology Action) →
  ∀ sequence target →
  Selected.Converges measureConvergence sequence target →
  (∀ n → ActionInvariant semantics (sequence n)) →
  ActionInvariant semantics target
actionInvariantClosed {topology = topology} semantics
  sequence target convergence finiteInvariant action test actionTest =
  scalarLimitUnique topology
    (λ n → expectation topology (sequence n) (act semantics action test))
    (expectation topology target (act semantics action test))
    (expectation topology target test)
    (expectationContinuous topology sequence target
      (act semantics action test) convergence
      (actionPreservesAdmissibility semantics action test actionTest))
    (scalarConvergenceCongruent topology
      (λ n → expectation topology (sequence n) test)
      (λ n → expectation topology (sequence n) (act semantics action test))
      (expectation topology target test)
      (λ n → sym (finiteInvariant n action test actionTest))
      (expectationContinuous topology sequence target test convergence
        (actionTestsAdmissible semantics test actionTest)))

scalarSubsequenceWitness :
  ∀ {Measure Test Scalar}
    {measureConvergence : Selected.SequentialConvergence Measure}
    (topology : SelectedWeakExpectationTopology
      Measure Test Scalar measureConvergence)
    {sequence : Nat → Measure}
    (test : Test) →
  Subsequence.SubsequenceWitness sequence →
  Subsequence.SubsequenceWitness
    (λ n → expectation topology (sequence n) test)
scalarSubsequenceWitness topology test subsequence = record
  { indices = Subsequence.indices subsequence
  ; StrictlyIncreasing = Subsequence.StrictlyIncreasing subsequence
  ; indicesStrictlyIncreasing = Subsequence.indicesStrictlyIncreasing subsequence
  }

record SelectedClusterExtraction
    (Measure : Set)
    (measureConvergence : Selected.SequentialConvergence Measure)
    (sequence : Nat → Measure) : Set₁ where
  field
    extractFurther :
      (subsequence : Subsequence.SubsequenceWitness sequence) →
      Subsequence.SubsequenceWitness (Subsequence.values subsequence)
    clusterLimit : Subsequence.SubsequenceWitness sequence → Measure
    extractedConverges :
      (subsequence : Subsequence.SubsequenceWitness sequence) →
      Selected.Converges measureConvergence
        (Subsequence.values (extractFurther subsequence))
        (clusterLimit subsequence)

open SelectedClusterExtraction public

record SelectedTargetExpectationConvergence
    {Measure Test Scalar : Set}
    {measureConvergence : Selected.SequentialConvergence Measure}
    (topology : SelectedWeakExpectationTopology
      Measure Test Scalar measureConvergence)
    (sequence : Nat → Measure)
    (target : Measure) : Set₁ where
  field
    selectedExpectationsConverge : ∀ test →
      AdmissibleTest topology test →
      ScalarConverges topology
        (λ n → expectation topology (sequence n) test)
        (expectation topology target test)

open SelectedTargetExpectationConvergence public

extractedClusterAgreesOnAdmissibleTest :
  ∀ {Measure Test Scalar}
    {measureConvergence : Selected.SequentialConvergence Measure}
    {topology : SelectedWeakExpectationTopology
      Measure Test Scalar measureConvergence}
    {sequence : Nat → Measure}
    {target : Measure} →
  SelectedClusterExtraction Measure measureConvergence sequence →
  SelectedTargetExpectationConvergence topology sequence target →
  (subsequence : Subsequence.SubsequenceWitness sequence) →
  (test : Test) →
  AdmissibleTest topology test →
  expectation topology
    (clusterLimit _ subsequence) test
  ≡ expectation topology target test
extractedClusterAgreesOnAdmissibleTest
  {topology = topology} extraction targetConvergence
  subsequence test admissible =
  let
    scalarSub = scalarSubsequenceWitness topology test subsequence
    further = extractFurther extraction subsequence
    scalarFurther = scalarSubsequenceWitness topology test further

    fullConvergence =
      selectedExpectationsConverge targetConvergence test admissible
    firstRestriction =
      scalarConvergenceRestrictsToSubsequence topology
        _ _ fullConvergence scalarSub
    secondRestriction =
      scalarConvergenceRestrictsToSubsequence topology
        _ _ firstRestriction scalarFurther
    clusterConvergence =
      expectationContinuous topology
        (Subsequence.values further)
        (clusterLimit extraction subsequence)
        test
        (extractedConverges extraction subsequence)
        admissible
  in
  scalarLimitUnique topology
    _
    (expectation topology (clusterLimit extraction subsequence) test)
    (expectation topology target test)
    clusterConvergence
    secondRestriction

selectedWeakExpectationPropertyClosureLevel : ProofLevel
selectedWeakExpectationPropertyClosureLevel = machineChecked

selectedWeakTopologyClusterAgreementLevel : ProofLevel
selectedWeakTopologyClusterAgreementLevel = machineChecked

selectedWeakExpectationTopologyMeaningLevel : ProofLevel
selectedWeakExpectationTopologyMeaningLevel = conditional
