{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound208Exact where

------------------------------------------------------------------------
-- ROUND208: T2/T3 COLLAPSE ONTO ONE WEAK-EXPECTATION TOPOLOGY SEAM
--
-- The selected quantitative T5 producer already carries expectation convergence
-- for its bounded-observable class.  Once the actual measure convergence is
-- identified with a weak topology on a determining admissible test class:
--
--   * extracted cluster cylinder agreement follows by subsequence restriction
--     and scalar limit uniqueness;
--   * normalization, positivity and gauge invariance are sequentially closed by
--     the same expectation-continuity theorem.
--
-- Thus four historical physical leaves are not independent Yang--Mills
-- estimates.  The shared physical seam is the topology/test-class meaning.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound207Exact as R207
import DASHI.Physics.YangMills.BalabanClayT5MomentCompactContainmentExact as Moment
import DASHI.Physics.YangMills.BalabanClayT5WeakExpectationPropertyClosureExact as Weak
import DASHI.Physics.YangMills.BalabanClayT5WeakTopologyClusterCylinderAgreementExact as Cluster
import DASHI.Physics.YangMills.BalabanClayT5CylinderDeterminingClusterUniquenessExact as Cylinder
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf208 : Set where
  -- T1 remains the first global analytic wall.
  physicalGlobalMomentCompactContainment : T5PreferredContinuumLeaf208

  -- Shared T2/T3 topology semantics.  This identifies the selected convergence
  -- with weak expectation convergence on a determining class containing the
  -- unit, positive and gauge-transformed tests used by the legacy predicates.
  physicalWeakExpectationTopologyAndTestClassMeaning : T5PreferredContinuumLeaf208

  -- T4 remains only because the historical broad closure carrier demands the
  -- generic arbitrary-sequence RP closure law, stronger than selected-target RP.
  physicalGenericGramReflectionSequentialClosure : T5PreferredContinuumLeaf208

  -- T5 continuum Schwinger semantics remain split rather than bundled.
  physicalContinuumEuclideanCovariance : T5PreferredContinuumLeaf208
  physicalContinuumSymmetry : T5PreferredContinuumLeaf208
  physicalContinuumTemperedness : T5PreferredContinuumLeaf208
  physicalContinuumRegularity : T5PreferredContinuumLeaf208
  physicalContinuumClustering : T5PreferredContinuumLeaf208
  physicalGramReflectionToSchwingerReflectionMeaning : T5PreferredContinuumLeaf208

preferredT5ContinuumCut208 : List T5PreferredContinuumLeaf208
preferredT5ContinuumCut208 =
  physicalGlobalMomentCompactContainment ∷
  physicalWeakExpectationTopologyAndTestClassMeaning ∷
  physicalGenericGramReflectionSequentialClosure ∷
  physicalContinuumEuclideanCovariance ∷
  physicalContinuumSymmetry ∷
  physicalContinuumTemperedness ∷
  physicalContinuumRegularity ∷
  physicalContinuumClustering ∷
  physicalGramReflectionToSchwingerReflectionMeaning ∷ []

typedMomentToUniformTightnessCompilerLevel : ProofLevel
typedMomentToUniformTightnessCompilerLevel =
  Moment.typedMomentToUniformTightnessCompilerLevel

weakExpectationPropertyClosureCompilerLevel : ProofLevel
weakExpectationPropertyClosureCompilerLevel =
  Weak.weakExpectationPropertyClosureCompilerLevel

weakTopologyClusterCylinderAgreementCompilerLevel : ProofLevel
weakTopologyClusterCylinderAgreementCompilerLevel =
  Cluster.weakTopologyClusterCylinderAgreementCompilerLevel

cylinderDeterminingClusterUniquenessCompilerLevel : ProofLevel
cylinderDeterminingClusterUniquenessCompilerLevel =
  Cylinder.cylinderDeterminingClusterUniquenessCompilerLevel

scalarSubsequenceStabilityLevel : ProofLevel
scalarSubsequenceStabilityLevel = Cluster.scalarSubsequenceStabilityLevel

scalarHausdorffAndPositiveConeClosureLevel : ProofLevel
scalarHausdorffAndPositiveConeClosureLevel =
  Weak.scalarHausdorffAndPositiveConeClosureLevel

data T1PrerequisiteStatus208 : Set where
  missingGlobalMomentCompactContainment : T1PrerequisiteStatus208
  readyForGlobalUniformTightnessCompiler : T1PrerequisiteStatus208

preferredCurrentT1Status208 : T1PrerequisiteStatus208
preferredCurrentT1Status208 = missingGlobalMomentCompactContainment

data T23PrerequisiteStatus208 : Set where
  missingWeakExpectationTopologyAndTestClassMeaning : T23PrerequisiteStatus208
  readyForClusterAndPropertyClosureCompilers : T23PrerequisiteStatus208

preferredCurrentT23Status208 : T23PrerequisiteStatus208
preferredCurrentT23Status208 = missingWeakExpectationTopologyAndTestClassMeaning

round207GlobalTightnessCorrectionRetained : ProofLevel
round207GlobalTightnessCorrectionRetained = R207.currentYMTerminalCutsetRound207Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound208Level : ProofLevel
currentYMTerminalCutsetRound208Level = machineChecked

literalPreferredT5ContinuumLeaf208Level : ProofLevel
literalPreferredT5ContinuumLeaf208Level = conditional
