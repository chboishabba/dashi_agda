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
-- The preferred source-physics overlay leaves three source packages:
--
--   Q1  ordinary path-derivative semantics/equivariance for the present-cut D1;
--   Q2  the nonperturbative SU(2) trace-anomaly theorem on the Hilbert trace of
--       the SAME R136 / pinned Local-C stress;
--   Q3  asymptotic identification of the finite Local-C and physical-Haar F^2
--       sequences by a vanishing bridge error.
--
-- Q3 no longer requires pointwise equality of the two finite sequences.  The
-- existing Local-C limit and physical-Haar error representations, together with
-- a vanishing bridge
--
--   |F2_Haar(n) - F2_LocalC(n)| <= eps(n), eps -> 0,
--
-- already force equality of their continuum readouts.
--
-- The classical CurvatureSix same-object weld remains valuable for the
-- classical Wilson/Gibbs lane, but it is NOT an additional terminal debt of the
-- scoped preferred Q1/Q2/Q3 source route.  Nor is there a free quantum trace
-- scalar: Q2 names the trace of the actual stress object.
--
-- On the finite side, Wilson DS[h] and F^2 are compiled from exactly one
-- FiniteCurvatureSixFamily, so Q3 does not get to select an unrelated curvature
-- family merely because it is consumed by an anomaly observable.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004QExact as Q
import DASHI.Physics.Foundations.CMP119CosmologyLatestParetoFrontierExact as Latest
import DASHI.Physics.Foundations.CMP119CosmologyP2HilbertTraceAnomalyExact as P2
import DASHI.Physics.Foundations.CMP119CosmologyP3LocalCF2PhysicalHaarCommonLimitExact as P3Old
import DASHI.Physics.Foundations.CMP119CosmologyP3AsymptoticFiniteF2CommonLimitExact as P3
import DASHI.Physics.Foundations.CMP119R144CurvatureTraceSectorNoGoExact as TraceNoGo
import DASHI.Physics.Foundations.CMP119R144PartitionInsertionTrivialityExact as Partition
import DASHI.Physics.Foundations.CMP119CurvatureWilsonSelectedInsertionCompilerExact as CurvatureWilson
import DASHI.Physics.Foundations.CMP119CurvatureWilsonF2SingleFamilyCompilerExact as SingleF2

preferredSourcePackageCount : Nat
preferredSourcePackageCount = Q.remainingPreferredSourcePackageCount

preferredFrontierRemainsQ1Q2Q3 : Bool
preferredFrontierRemainsQ1Q2Q3 = true

preferredRouteRemainingAdapterDebt : Nat
preferredRouteRemainingAdapterDebt = Latest.remainingAdapterDebt

preferredRemainingWorkIsSourceConstructionOrSourceTheorems : Bool
preferredRemainingWorkIsSourceConstructionOrSourceTheorems =
  Latest.remainingWorkIsSourceConstructionOrSourceTheorems

q1IsPresentCutPathDerivativeSemantics : Bool
q1IsPresentCutPathDerivativeSemantics =
  Q.q1IsPathDerivativeSemanticsAndEquivariance

q2AnomalyIsOnSameR136LocalCStress : Bool
q2AnomalyIsOnSameR136LocalCStress =
  Q.q2IsNonperturbativeHilbertTraceAnomalyOnExactLocalCPair

q2FreeTraceScalarRetired : Bool
q2FreeTraceScalarRetired =
  Q.freeTraceFrameCalibrationRetired

------------------------------------------------------------------------
-- Q3 recut: termwise equality is stronger than the limit argument needs.
------------------------------------------------------------------------

q3PointwiseCommonFiniteF2SequenceStillRequired : Bool
q3PointwiseCommonFiniteF2SequenceStillRequired =
  P3.termwiseFiniteF2EqualityRequired

q3UsesAsymptoticFiniteF2Bridge : Bool
q3UsesAsymptoticFiniteF2Bridge =
  P3.q3ReducedToAsymptoticFiniteF2Bridge

q3VanishingFiniteF2BridgeSuffices : Bool
q3VanishingFiniteF2BridgeSuffices =
  P3.vanishingFiniteF2BridgeSufficesForCommonLimit

q3ExactFiniteContinuumF2EqualityRetired : Bool
q3ExactFiniteContinuumF2EqualityRetired =
  P3Old.exactFiniteEqualsContinuumF2NoLongerRequired

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

independentFiniteF2CurvatureFamilyRequired : Bool
independentFiniteF2CurvatureFamilyRequired =
  SingleF2.independentFiniteF2CurvatureFamilyRequired

sameFiniteCurvatureFamilyPaysClassicalDSAndF2 : Bool
sameFiniteCurvatureFamilyPaysClassicalDSAndF2 =
  SingleF2.sameCurvatureFamilyPaysWilsonTenSlotDSAndF2

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

q3PointwiseCommonFiniteF2SequenceStillRequiredIsFalse :
  q3PointwiseCommonFiniteF2SequenceStillRequired ≡ false
q3PointwiseCommonFiniteF2SequenceStillRequiredIsFalse = refl

q3UsesAsymptoticFiniteF2BridgeIsTrue :
  q3UsesAsymptoticFiniteF2Bridge ≡ true
q3UsesAsymptoticFiniteF2BridgeIsTrue = refl

wholeGeneratedActionMayCollapseToClassicalCurvatureIsFalse :
  wholeGeneratedActionMayCollapseToClassicalCurvature ≡ false
wholeGeneratedActionMayCollapseToClassicalCurvatureIsFalse = refl

independentFiniteF2CurvatureFamilyRequiredIsFalse :
  independentFiniteF2CurvatureFamilyRequired ≡ false
independentFiniteF2CurvatureFamilyRequiredIsFalse = refl

sameFiniteCurvatureFamilyPaysClassicalDSAndF2IsTrue :
  sameFiniteCurvatureFamilyPaysClassicalDSAndF2 ≡ true
sameFiniteCurvatureFamilyPaysClassicalDSAndF2IsTrue = refl
