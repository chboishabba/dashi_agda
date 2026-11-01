{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound196Exact where

------------------------------------------------------------------------
-- ROUND196: REMOVE THE UNIVERSAL-SUBSEQUENCE TIGHTNESS LEAF
--
-- Round195 exposed
--
--   forall literal subsequences s, Tight(mu_s)
--
-- as the first physical T1 prerequisite.  On the preferred uniform-tightness
-- formulation this is stronger than necessary as a primitive search leaf: one
-- epsilon-dependent compact witness controls the whole selected sequence and
-- therefore controls every restriction of that sequence automatically.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound195Exact as R195
import DASHI.Physics.YangMills.BalabanClayT5UniformTightnessSubsequenceInheritanceExact as Uniform
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf196 : Set where
  physicalSelectedSequenceUniformTightness : T5PreferredContinuumLeaf196
  physicalEveryExtractedClusterPointIsTarget : T5PreferredContinuumLeaf196
  physicalMeasurePropertySequentialClosure : T5PreferredContinuumLeaf196
  physicalGramReflectionMeasureTopologyClosure : T5PreferredContinuumLeaf196
  physicalContinuumSchwingerAxioms : T5PreferredContinuumLeaf196

preferredT5ContinuumCut196 : List T5PreferredContinuumLeaf196
preferredT5ContinuumCut196 =
  physicalSelectedSequenceUniformTightness ∷
  physicalEveryExtractedClusterPointIsTarget ∷
  physicalMeasurePropertySequentialClosure ∷
  physicalGramReflectionMeasureTopologyClosure ∷
  physicalContinuumSchwingerAxioms ∷ []

-- The universal-subsequence quantifier is compiler output now.
uniformTightnessRestrictionCompilerLevel : ProofLevel
uniformTightnessRestrictionCompilerLevel =
  Uniform.uniformTightnessSubsequenceRestrictionLevel

selectedSequenceUniformTightnessProducerLevel : ProofLevel
selectedSequenceUniformTightnessProducerLevel =
  Uniform.selectedPhysicalSequenceUniformTightnessLevel

-- Proof-search diagnosis: the next physical theorem is one uniform-tightness
-- certificate on the selected diagonal sequence, not a theorem separately
-- quantified over arbitrary subsequences.
data T1PrerequisiteStatus196 : Set where
  missingSelectedSequenceUniformTightness : T1PrerequisiteStatus196
  readyForSubsequenceRestriction : T1PrerequisiteStatus196

preferredCurrentT1Status196 : T1PrerequisiteStatus196
preferredCurrentT1Status196 = missingSelectedSequenceUniformTightness

round195CutRetainedForCompatibility : ProofLevel
round195CutRetainedForCompatibility =
  R195.currentYMTerminalCutsetRound195Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound196Level : ProofLevel
currentYMTerminalCutsetRound196Level = machineChecked

literalPreferredT5ContinuumLeaf196Level : ProofLevel
literalPreferredT5ContinuumLeaf196Level = conditional
