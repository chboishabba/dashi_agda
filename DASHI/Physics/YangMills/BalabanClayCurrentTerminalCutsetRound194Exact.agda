{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound194Exact where

------------------------------------------------------------------------
-- ROUND194: REFINE THE MEASURE-LIMIT LEAF
--
-- Round193 left four preferred T5 continuum analytic classes. The first,
-- physicalMeasureLimitConvergence, is itself not primitive: on the preferred
-- topology route it is compiled from literal relative sequential compactness
-- plus uniqueness of every cluster point, using the standard compact-unique
-- convergence theorem.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound193Exact as R193
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as CompactUnique
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf : Set where
  physicalRelativeSequentialCompactness : T5PreferredContinuumLeaf
  physicalUniqueClusterPoint : T5PreferredContinuumLeaf
  physicalMeasurePropertySequentialClosure : T5PreferredContinuumLeaf
  physicalGramReflectionMeasureTopologyClosure : T5PreferredContinuumLeaf
  physicalContinuumSchwingerAxioms : T5PreferredContinuumLeaf

preferredT5ContinuumCut : List T5PreferredContinuumLeaf
preferredT5ContinuumCut =
  physicalRelativeSequentialCompactness ∷
  physicalUniqueClusterPoint ∷
  physicalMeasurePropertySequentialClosure ∷
  physicalGramReflectionMeasureTopologyClosure ∷
  physicalContinuumSchwingerAxioms ∷ []

fullMeasureConvergenceCompilerLevel : ProofLevel
fullMeasureConvergenceCompilerLevel =
  CompactUnique.compactUniqueFullSequenceCompilerLevel

compactUniqueAuthorityLevel : ProofLevel
compactUniqueAuthorityLevel =
  CompactUnique.compactUniqueFullConvergenceAuthorityLevel

relativeSequentialCompactnessProducerLevel : ProofLevel
relativeSequentialCompactnessProducerLevel =
  CompactUnique.physicalRelativeSequentialCompactnessLevel

uniqueClusterPointProducerLevel : ProofLevel
uniqueClusterPointProducerLevel =
  CompactUnique.physicalUniqueClusterPointLevel

round193PreferredCutRetainedForCompatibility : ProofLevel
round193PreferredCutRetainedForCompatibility =
  R193.currentYMTerminalCutsetRound193Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound194Level : ProofLevel
currentYMTerminalCutsetRound194Level = machineChecked

literalPreferredT5ContinuumLeafLevel : ProofLevel
literalPreferredT5ContinuumLeafLevel = conditional
