{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound198Exact where

------------------------------------------------------------------------
-- ROUND198: SPLIT MOMENT COMPACT CONTAINMENT INTO ITS TWO PHYSICAL SEAMS
--
-- Round197 left one broad physical leaf: typed moment bound -> compact
-- containment. The typed moment inequality is already owned, and generic
-- Markov/sublevel reasoning is standard. What remains physically is exactly:
--
--   (1) same-object coercivity of the observable integrated by diagonalMeasure;
--   (2) compactness/admissibility of its sublevel witnesses in the selected
--       measure topology.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound197Exact as R197
import DASHI.Physics.YangMills.BalabanClayT5CoerciveMomentMarkovContainmentExact as Coercive
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf198 : Set where
  physicalCoerciveMomentObservableSameObject : T5PreferredContinuumLeaf198
  physicalCoerciveSublevelCompactness : T5PreferredContinuumLeaf198
  physicalEveryExtractedClusterPointIsTarget : T5PreferredContinuumLeaf198
  physicalMeasurePropertySequentialClosure : T5PreferredContinuumLeaf198
  physicalGramReflectionMeasureTopologyClosure : T5PreferredContinuumLeaf198
  physicalContinuumSchwingerAxioms : T5PreferredContinuumLeaf198

preferredT5ContinuumCut198 : List T5PreferredContinuumLeaf198
preferredT5ContinuumCut198 =
  physicalCoerciveMomentObservableSameObject ∷
  physicalCoerciveSublevelCompactness ∷
  physicalEveryExtractedClusterPointIsTarget ∷
  physicalMeasurePropertySequentialClosure ∷
  physicalGramReflectionMeasureTopologyClosure ∷
  physicalContinuumSchwingerAxioms ∷ []

markovCompactContainmentAuthorityLevel : ProofLevel
markovCompactContainmentAuthorityLevel =
  Coercive.markovCompactContainmentAuthorityLevel

coerciveMomentContainmentCompilerLevel : ProofLevel
coerciveMomentContainmentCompilerLevel =
  Coercive.coerciveMomentMarkovContainmentCompilerLevel

physicalCoerciveMomentObservableSameObjectLevel : ProofLevel
physicalCoerciveMomentObservableSameObjectLevel =
  Coercive.physicalCoerciveMomentObservableSameObjectLevel

physicalCoerciveSublevelCompactnessLevel : ProofLevel
physicalCoerciveSublevelCompactnessLevel =
  Coercive.physicalCoerciveSublevelCompactnessLevel

data T1PrerequisiteStatus198 : Set where
  missingCoerciveObservableSameObject : T1PrerequisiteStatus198
  missingCoerciveSublevelCompactness : T1PrerequisiteStatus198
  readyForMarkovContainmentCompiler : T1PrerequisiteStatus198

preferredCurrentT1Status198 : T1PrerequisiteStatus198
preferredCurrentT1Status198 = missingCoerciveObservableSameObject

round197CutRetainedForCompatibility : ProofLevel
round197CutRetainedForCompatibility =
  R197.currentYMTerminalCutsetRound197Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound198Level : ProofLevel
currentYMTerminalCutsetRound198Level = machineChecked

literalPreferredT5ContinuumLeaf198Level : ProofLevel
literalPreferredT5ContinuumLeaf198Level = conditional
