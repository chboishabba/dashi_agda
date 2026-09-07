{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound200Exact where

------------------------------------------------------------------------
-- ROUND200: REMOVE DIAGONAL-MEASURE SAME-OBJECT AS A PHYSICAL LEAF
--
-- The preferred expectation producer now defines the selected diagonal measure
-- literally as finiteVolumeMeasure cutoff (diagonalVolume cutoff).  Therefore
-- the Round199 same-object weld and expectation transport are `refl` on the
-- preferred route.  The first physical T1 prerequisite moves forward to the
-- coercive-observable same-object theorem.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound199Exact as R199
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Preferred
import DASHI.Physics.YangMills.BalabanClayT5CoerciveMomentMarkovContainmentExact as Coercive
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf200 : Set where
  physicalCoerciveObservableSameObject : T5PreferredContinuumLeaf200
  physicalCoerciveSublevelCompactness : T5PreferredContinuumLeaf200
  physicalEveryExtractedClusterPointIsTarget : T5PreferredContinuumLeaf200
  physicalMeasurePropertySequentialClosure : T5PreferredContinuumLeaf200
  physicalGramReflectionMeasureTopologyClosure : T5PreferredContinuumLeaf200
  physicalContinuumSchwingerAxioms : T5PreferredContinuumLeaf200

preferredT5ContinuumCut200 : List T5PreferredContinuumLeaf200
preferredT5ContinuumCut200 =
  physicalCoerciveObservableSameObject ∷
  physicalCoerciveSublevelCompactness ∷
  physicalEveryExtractedClusterPointIsTarget ∷
  physicalMeasurePropertySequentialClosure ∷
  physicalGramReflectionMeasureTopologyClosure ∷
  physicalContinuumSchwingerAxioms ∷ []

preferredDiagonalExpectationProducerCompilerLevel : ProofLevel
preferredDiagonalExpectationProducerCompilerLevel =
  Preferred.preferredDiagonalExpectationProducerCompilerLevel

preferredDiagonalFiniteVolumeSameObjectLevel : ProofLevel
preferredDiagonalFiniteVolumeSameObjectLevel =
  Preferred.preferredDiagonalFiniteVolumeSameObjectLevel

coerciveMomentMarkovContainmentCompilerLevel : ProofLevel
coerciveMomentMarkovContainmentCompilerLevel =
  Coercive.coerciveMomentMarkovContainmentCompilerLevel

physicalCoerciveObservableSameObjectProducerLevel : ProofLevel
physicalCoerciveObservableSameObjectProducerLevel =
  Coercive.physicalCoerciveMomentObservableSameObjectLevel

physicalCoerciveSublevelCompactnessProducerLevel : ProofLevel
physicalCoerciveSublevelCompactnessProducerLevel =
  Coercive.physicalCoerciveSublevelCompactnessLevel

data T1PrerequisiteStatus200 : Set where
  missingCoerciveObservableSameObject : T1PrerequisiteStatus200
  missingCoerciveSublevelCompactness : T1PrerequisiteStatus200
  readyForMarkovUniformTightnessCompiler : T1PrerequisiteStatus200

preferredCurrentT1Status200 : T1PrerequisiteStatus200
preferredCurrentT1Status200 = missingCoerciveObservableSameObject

round199CutRetainedForCompatibility : ProofLevel
round199CutRetainedForCompatibility = R199.currentYMTerminalCutsetRound199Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound200Level : ProofLevel
currentYMTerminalCutsetRound200Level = machineChecked

literalPreferredT5ContinuumLeaf200Level : ProofLevel
literalPreferredT5ContinuumLeaf200Level = conditional
