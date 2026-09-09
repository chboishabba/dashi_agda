{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5WeakTopologyClusterCylinderAgreementExact where

------------------------------------------------------------------------
-- WEAK EXPECTATION TOPOLOGY -> EXTRACTED CLUSTER CYLINDER AGREEMENT
--
-- Once the selected scalar expectations converge to the target, a convergent
-- extracted measure subsequence cannot acquire different cylinder expectations:
-- scalar convergence restricts to subsequences, weak measure convergence gives
-- convergence to the cluster expectation, and Hausdorff uniqueness identifies
-- the two scalar limits.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as Compact
import DASHI.Physics.YangMills.BalabanClayT5WeakExpectationPropertyClosureExact as Weak

scalarSubsequenceWitness :
  ∀ {Measure Test Scalar}
    {measureLimit : Limit.SequentialLimit Measure}
    (topology : Weak.WeakExpectationTopology Measure Test Scalar measureLimit)
    {sequence : Nat → Measure}
    (test : Test) →
  Compact.SubsequenceWitness sequence →
  Compact.SubsequenceWitness
    (λ n → Weak.expectation topology (sequence n) test)
scalarSubsequenceWitness topology test subsequence = record
  { indices = Compact.indices subsequence
  ; StrictlyIncreasing = Compact.StrictlyIncreasing subsequence
  ; indicesStrictlyIncreasing = Compact.indicesStrictlyIncreasing subsequence
  }

record ScalarSubsequenceStability
    {Measure Test Scalar : Set}
    {measureLimit : Limit.SequentialLimit Measure}
    (topology : Weak.WeakExpectationTopology Measure Test Scalar measureLimit)
    : Set₁ where
  field
    scalarConvergenceRestrictsToSubsequence :
      ∀ sequence target →
      Weak.ScalarConverges topology sequence target →
      (subsequence : Compact.SubsequenceWitness sequence) →
      Weak.ScalarConverges topology (Compact.values subsequence) target

open ScalarSubsequenceStability public

record SelectedClusterExtraction
    (Measure : Set)
    (measureLimit : Limit.SequentialLimit Measure)
    (sequence : Nat → Measure) : Set₁ where
  field
    extractFurther :
      (subsequence : Compact.SubsequenceWitness sequence) →
      Compact.SubsequenceWitness (Compact.values subsequence)
    clusterLimit : Compact.SubsequenceWitness sequence → Measure
    extractedConverges :
      (subsequence : Compact.SubsequenceWitness sequence) →
      Limit.Converges measureLimit
        (Compact.values (extractFurther subsequence))
        (clusterLimit subsequence)

open SelectedClusterExtraction public

record SelectedTargetExpectationConvergence
    {Measure Test Scalar : Set}
    {measureLimit : Limit.SequentialLimit Measure}
    (topology : Weak.WeakExpectationTopology Measure Test Scalar measureLimit)
    (sequence : Nat → Measure)
    (target : Measure) : Set₁ where
  field
    selectedExpectationsConverge : ∀ test →
      Weak.AdmissibleTest topology test →
      Weak.ScalarConverges topology
        (λ n → Weak.expectation topology (sequence n) test)
        (Weak.expectation topology target test)

open SelectedTargetExpectationConvergence public

extractedClusterAgreesOnAdmissibleTest :
  ∀ {Measure Test Scalar}
    {measureLimit : Limit.SequentialLimit Measure}
    {topology : Weak.WeakExpectationTopology Measure Test Scalar measureLimit}
    {sequence : Nat → Measure}
    {target : Measure} →
  ScalarSubsequenceStability topology →
  SelectedClusterExtraction Measure measureLimit sequence →
  SelectedTargetExpectationConvergence topology sequence target →
  (subsequence : Compact.SubsequenceWitness sequence) →
  (test : Test) →
  Weak.AdmissibleTest topology test →
  Weak.expectation topology
    (clusterLimit _ subsequence) test
  ≡ Weak.expectation topology target test
extractedClusterAgreesOnAdmissibleTest
  {topology = topology} stability extraction targetConvergence
  subsequence test admissible =
  let
    scalarSub = scalarSubsequenceWitness topology test subsequence
    further = extractFurther extraction subsequence
    scalarFurther =
      scalarSubsequenceWitness topology test further

    fullConvergence =
      selectedExpectationsConverge targetConvergence test admissible
    firstRestriction =
      scalarConvergenceRestrictsToSubsequence stability
        _ _ fullConvergence scalarSub
    secondRestriction =
      scalarConvergenceRestrictsToSubsequence stability
        _ _ firstRestriction scalarFurther
    clusterConvergence =
      Weak.expectationContinuous topology
        (Compact.values further)
        (clusterLimit extraction subsequence)
        test
        (extractedConverges extraction subsequence)
        admissible
  in
  Weak.scalarLimitUnique topology
    _
    (Weak.expectation topology (clusterLimit extraction subsequence) test)
    (Weak.expectation topology target test)
    clusterConvergence
    secondRestriction

weakTopologyClusterCylinderAgreementCompilerLevel : ProofLevel
weakTopologyClusterCylinderAgreementCompilerLevel = machineChecked

scalarSubsequenceStabilityLevel : ProofLevel
scalarSubsequenceStabilityLevel = standardImported

-- Physical content is reduced to the already-selected expectation convergence
-- and the same weak expectation topology used by the property-closure compiler.
selectedTargetExpectationConvergenceLevel : ProofLevel
selectedTargetExpectationConvergenceLevel = conditional
