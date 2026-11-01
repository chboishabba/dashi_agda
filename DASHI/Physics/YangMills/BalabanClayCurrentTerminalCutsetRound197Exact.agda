{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound197Exact where

------------------------------------------------------------------------
-- ROUND197: REFINE SELECTED-SEQUENCE UNIFORM TIGHTNESS TO THE ACTUAL
-- COMPACT-CONTAINMENT INTERPRETATION OF ALREADY-OWNED TYPED MOMENT BOUNDS
--
-- Round196 made one selected-sequence uniform-tightness certificate the first
-- T1 leaf.  The quantitative expectation producer already supplies an actual
-- cutoff-indexed moment inequality on that selected diagonal measure sequence.
-- The remaining physical content is therefore only the theorem that the chosen
-- coercive moment observable controls escape from an admissible compact set.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound196Exact as R196
import DASHI.Physics.YangMills.BalabanClayT5MomentCompactContainmentExact as Moment
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf197 : Set where
  physicalMomentCompactContainment : T5PreferredContinuumLeaf197
  physicalEveryExtractedClusterPointIsTarget : T5PreferredContinuumLeaf197
  physicalMeasurePropertySequentialClosure : T5PreferredContinuumLeaf197
  physicalGramReflectionMeasureTopologyClosure : T5PreferredContinuumLeaf197
  physicalContinuumSchwingerAxioms : T5PreferredContinuumLeaf197

preferredT5ContinuumCut197 : List T5PreferredContinuumLeaf197
preferredT5ContinuumCut197 =
  physicalMomentCompactContainment ∷
  physicalEveryExtractedClusterPointIsTarget ∷
  physicalMeasurePropertySequentialClosure ∷
  physicalGramReflectionMeasureTopologyClosure ∷
  physicalContinuumSchwingerAxioms ∷ []

-- Typed moment inequalities themselves come from the existing physical
-- expectation producer; no new numerical moment theorem is scheduled here.
typedMomentToUniformTightnessCompilerLevel : ProofLevel
typedMomentToUniformTightnessCompilerLevel =
  Moment.typedMomentToUniformTightnessCompilerLevel

momentCompactContainmentProducerLevel : ProofLevel
momentCompactContainmentProducerLevel =
  Moment.physicalMomentCompactContainmentLevel

data T1PrerequisiteStatus197 : Set where
  missingMomentCompactContainment : T1PrerequisiteStatus197
  readyForUniformTightnessCompiler : T1PrerequisiteStatus197

preferredCurrentT1Status197 : T1PrerequisiteStatus197
preferredCurrentT1Status197 = missingMomentCompactContainment

round196CutRetainedForCompatibility : ProofLevel
round196CutRetainedForCompatibility =
  R196.currentYMTerminalCutsetRound196Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound197Level : ProofLevel
currentYMTerminalCutsetRound197Level = machineChecked

literalPreferredT5ContinuumLeaf197Level : ProofLevel
literalPreferredT5ContinuumLeaf197Level = conditional
