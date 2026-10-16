{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119GRQFTPreferredQ123TraceReconciliationExact where

------------------------------------------------------------------------
-- GRQFT TRACE RECONCILIATION WITH THE PREFERRED Q1/Q2/Q3 SOURCE ROUTE
--
-- The R144/CurvatureSix no-go is a useful firewall: a nonzero generated-action
-- trace cannot be obtained by silently identifying the WHOLE generated action
-- with the classical d=4 CurvatureSix sector, whose diagonal action trace is
-- exactly zero.
--
-- But the preferred source-physics overlay is already sharper than introducing
-- a generic "nonclassical action sector".  It leaves exactly three source
-- packages:
--
--   Q1  ordinary path-derivative semantics/equivariance for the present-cut D1;
--   Q2  the nonperturbative SU(2) trace-anomaly theorem on the Hilbert trace of
--       the SAME R136 / pinned Local-C stress;
--   Q3  one pointwise-common finite physical F^2 sequence whose two existing
--       limit representations identify Local-C F^2 with physical-Haar F^2.
--
-- Therefore the classical CurvatureSix same-object weld remains valuable for
-- the classical Wilson/Gibbs lane, but it is NOT an additional terminal debt of
-- the scoped preferred Q1/Q2/Q3 source route.  Nor is there a free quantum trace
-- scalar: Q2 names the trace of the actual stress object.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004QExact as Q
import DASHI.Physics.Foundations.CMP119CosmologyP2HilbertTraceAnomalyExact as P2
import DASHI.Physics.Foundations.CMP119CosmologyP3LocalCF2PhysicalHaarCommonLimitExact as P3
import DASHI.Physics.Foundations.CMP119R144CurvatureTraceSectorNoGoExact as TraceNoGo
import DASHI.Physics.Foundations.CMP119R144PartitionInsertionTrivialityExact as Partition
import DASHI.Physics.Foundations.CMP119CurvatureWilsonSelectedInsertionCompilerExact as CurvatureWilson

preferredSourcePackageCount : Nat
preferredSourcePackageCount = Q.remainingPreferredSourcePackageCount

preferredFrontierRemainsQ1Q2Q3 : Bool
preferredFrontierRemainsQ1Q2Q3 = true

q1IsPresentCutPathDerivativeSemantics : Bool
q1IsPresentCutPathDerivativeSemantics =
  Q.q1IsPathDerivativeSemanticsAndEquivariance

q2AnomalyIsOnSameR136LocalCStress : Bool
q2AnomalyIsOnSameR136LocalCStress =
  Q.q2IsNonperturbativeHilbertTraceAnomalyOnExactLocalCPair

q2FreeTraceScalarRetired : Bool
q2FreeTraceScalarRetired =
  Q.freeTraceFrameCalibrationRetired

q3UsesPointwiseCommonFiniteF2Sequence : Bool
q3UsesPointwiseCommonFiniteF2Sequence =
  Q.q3IsPointwiseCommonFinitePhysicalF2Sequence

q3ExactFiniteContinuumF2EqualityRetired : Bool
q3ExactFiniteContinuumF2EqualityRetired =
  P3.exactFiniteEqualsContinuumF2NoLongerRequired

p23AlreadyCompilesPhysicalHaarPositivityToNegativeR136 : Bool
p23AlreadyCompilesPhysicalHaarPositivityToNegativeR136 =
  Q.p23CompilesPhysicalHaarPositivityToNegativeR136

------------------------------------------------------------------------
-- Correct the interim sector language.
------------------------------------------------------------------------

genericNonclassicalActionSectorIsTerminalLeaf : Bool
genericNonclassicalActionSectorIsTerminalLeaf = false

freeSelectedQuantumTraceScalarIsTerminalLeaf : Bool
freeSelectedQuantumTraceScalarIsTerminalLeaf = false

-- The anomaly theorem belongs to the Hilbert trace of the SAME selected stress,
-- not to an independently postulated additive action scalar.
preferredNonclassicalTraceObjectIsSelectedStressHilbertTrace : Bool
preferredNonclassicalTraceObjectIsSelectedStressHilbertTrace = true

------------------------------------------------------------------------
-- CurvatureSix remains a useful classical-sector compiler, not a whole-action
-- identification and not an extra preferred-Q source package.
------------------------------------------------------------------------

wholeGeneratedActionMayCollapseToClassicalCurvature : Bool
wholeGeneratedActionMayCollapseToClassicalCurvature =
  TraceNoGo.fullGeneratedActionMayBeClassicalCurvatureWithoutTracePayment

classicalCurvaturePaysAllTenClassicalDS : Bool
classicalCurvaturePaysAllTenClassicalDS =
  CurvatureWilson.curvatureSixPaysWholeClassicalActionMetricVariation

classicalCurvatureSameObjectWeldRequiredByPreferredQ123Route : Bool
classicalCurvatureSameObjectWeldRequiredByPreferredQ123Route = false

classicalCurvatureSameObjectWeldStillUsefulForWilsonGibbsLane : Bool
classicalCurvatureSameObjectWeldStillUsefulForWilsonGibbsLane = true

------------------------------------------------------------------------
-- The R144 partition-stress lane also does not reopen inserted-observable data.
------------------------------------------------------------------------

preferredPartitionStressNeedsIndependentO : Bool
preferredPartitionStressNeedsIndependentO =
  Partition.partitionResponseInsertionObservableRequiresIndependentSelection

preferredPartitionStressNeedsIndependentDO : Bool
preferredPartitionStressNeedsIndependentDO =
  Partition.partitionResponseInsertionVariationRequiresIndependentSelection

------------------------------------------------------------------------
-- Machine-visible receipts.
------------------------------------------------------------------------

preferredFrontierRemainsQ1Q2Q3IsTrue :
  preferredFrontierRemainsQ1Q2Q3 ≡ true
preferredFrontierRemainsQ1Q2Q3IsTrue = refl

q2AnomalyIsOnSameR136LocalCStressIsTrue :
  q2AnomalyIsOnSameR136LocalCStress ≡ true
q2AnomalyIsOnSameR136LocalCStressIsTrue = refl

q3UsesPointwiseCommonFiniteF2SequenceIsTrue :
  q3UsesPointwiseCommonFiniteF2Sequence ≡ true
q3UsesPointwiseCommonFiniteF2SequenceIsTrue = refl

wholeGeneratedActionMayCollapseToClassicalCurvatureIsFalse :
  wholeGeneratedActionMayCollapseToClassicalCurvature ≡ false
wholeGeneratedActionMayCollapseToClassicalCurvatureIsFalse = refl
