{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound209Exact where

------------------------------------------------------------------------
-- ROUND209: T2/T3/T4 SHARE ONE WEAK-TOPOLOGY / TEST-CLASS SEAM
--
-- The weak-expectation topology now compiles:
--   * extracted cluster cylinder agreement;
--   * normalization, positivity and gauge-invariance closure;
--   * generic complete finite-family reflected-Gram RP closure.
--
-- Thus the historical T2/T3/T4 leaves are all representations of one common
-- measure-topology fact rather than independent Yang--Mills estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound208Exact as R208
import DASHI.Physics.YangMills.BalabanClayT5MomentCompactContainmentExact as Moment
import DASHI.Physics.YangMills.BalabanClayT5WeakExpectationPropertyClosureExact as Weak
import DASHI.Physics.YangMills.BalabanClayT5WeakTopologyClusterCylinderAgreementExact as Cluster
import DASHI.Physics.YangMills.BalabanClayT5WeakExpectationGramReflectionClosureExact as GramClosure
import DASHI.Physics.YangMills.BalabanClayT5CylinderDeterminingClusterUniquenessExact as Cylinder
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf209 : Set where
  -- T1 remains the first genuinely global analytic theorem.
  physicalGlobalMomentCompactContainment : T5PreferredContinuumLeaf209

  -- T2/T3/T4 shared semantics: the actual measure convergence is weak on one
  -- determining class containing unit, positive, gauge-transformed and
  -- reflected-product cylinder tests.
  physicalWeakExpectationTopologyAndCompleteTestClassMeaning :
    T5PreferredContinuumLeaf209

  -- Remaining continuum Schwinger semantics.
  physicalContinuumEuclideanCovariance : T5PreferredContinuumLeaf209
  physicalContinuumSymmetry : T5PreferredContinuumLeaf209
  physicalContinuumTemperedness : T5PreferredContinuumLeaf209
  physicalContinuumRegularity : T5PreferredContinuumLeaf209
  physicalContinuumClustering : T5PreferredContinuumLeaf209
  physicalGramReflectionToSchwingerReflectionMeaning : T5PreferredContinuumLeaf209

preferredT5ContinuumCut209 : List T5PreferredContinuumLeaf209
preferredT5ContinuumCut209 =
  physicalGlobalMomentCompactContainment ∷
  physicalWeakExpectationTopologyAndCompleteTestClassMeaning ∷
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

weakExpectationGramReflectionClosureCompilerLevel : ProofLevel
weakExpectationGramReflectionClosureCompilerLevel =
  GramClosure.weakExpectationGramReflectionClosureCompilerLevel

cylinderDeterminingClusterUniquenessCompilerLevel : ProofLevel
cylinderDeterminingClusterUniquenessCompilerLevel =
  Cylinder.cylinderDeterminingClusterUniquenessCompilerLevel

data T1PrerequisiteStatus209 : Set where
  missingGlobalMomentCompactContainment : T1PrerequisiteStatus209
  readyForGlobalUniformTightnessCompiler : T1PrerequisiteStatus209

preferredCurrentT1Status209 : T1PrerequisiteStatus209
preferredCurrentT1Status209 = missingGlobalMomentCompactContainment

data T234PrerequisiteStatus209 : Set where
  missingWeakExpectationTopologyAndCompleteTestClassMeaning :
    T234PrerequisiteStatus209
  readyForClusterPropertyAndGramClosureCompilers : T234PrerequisiteStatus209

preferredCurrentT234Status209 : T234PrerequisiteStatus209
preferredCurrentT234Status209 =
  missingWeakExpectationTopologyAndCompleteTestClassMeaning

round208WeakTopologyReductionRetained : ProofLevel
round208WeakTopologyReductionRetained = R208.currentYMTerminalCutsetRound208Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound209Level : ProofLevel
currentYMTerminalCutsetRound209Level = machineChecked

literalPreferredT5ContinuumLeaf209Level : ProofLevel
literalPreferredT5ContinuumLeaf209Level = conditional
