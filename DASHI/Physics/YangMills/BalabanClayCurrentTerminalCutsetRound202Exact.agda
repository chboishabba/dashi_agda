{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound202Exact where

------------------------------------------------------------------------
-- ROUND202: CHOOSE THE PHYSICAL COERCIVE OBSERVABLE AS THE MOMENT OBSERVABLE
--
-- The marked/exponential-moment machinery is quantified over every admissible
-- Observable.  Hence the preferred route does not need a post-hoc theorem that
-- an arbitrary moment observable equals the physical coercive observable: use
-- the physical value itself.  The Round201 equality leaf becomes `refl`.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound201Exact as R201
import DASHI.Physics.YangMills.BalabanClayT5PreferredPhysicalCoerciveMomentBridgeExact as Preferred
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf202 : Set where
  physicalCoerciveObservableRenormalized : T5PreferredContinuumLeaf202
  physicalCoerciveObservableNonnegative : T5PreferredContinuumLeaf202
  physicalCoerciveObservableCoercivity : T5PreferredContinuumLeaf202
  physicalCoerciveSublevelCompactness : T5PreferredContinuumLeaf202
  physicalEveryExtractedClusterPointIsTarget : T5PreferredContinuumLeaf202
  physicalMeasurePropertySequentialClosure : T5PreferredContinuumLeaf202
  physicalGramReflectionMeasureTopologyClosure : T5PreferredContinuumLeaf202
  physicalContinuumSchwingerAxioms : T5PreferredContinuumLeaf202

preferredT5ContinuumCut202 : List T5PreferredContinuumLeaf202
preferredT5ContinuumCut202 =
  physicalCoerciveObservableRenormalized ∷
  physicalCoerciveObservableNonnegative ∷
  physicalCoerciveObservableCoercivity ∷
  physicalCoerciveSublevelCompactness ∷
  physicalEveryExtractedClusterPointIsTarget ∷
  physicalMeasurePropertySequentialClosure ∷
  physicalGramReflectionMeasureTopologyClosure ∷
  physicalContinuumSchwingerAxioms ∷ []

preferredMomentObservableSameObjectLevel : ProofLevel
preferredMomentObservableSameObjectLevel =
  Preferred.preferredMomentObservableSameObjectLevel

physicalCoerciveObservableRenormalizationProducerLevel : ProofLevel
physicalCoerciveObservableRenormalizationProducerLevel =
  Preferred.physicalCoerciveObservableRenormalizationLevel

physicalCoerciveObservableNonnegativityProducerLevel : ProofLevel
physicalCoerciveObservableNonnegativityProducerLevel =
  Preferred.physicalCoerciveObservableNonnegativityLevel

physicalCoerciveObservableCoercivityProducerLevel : ProofLevel
physicalCoerciveObservableCoercivityProducerLevel =
  Preferred.physicalCoerciveObservableCoercivityLevel

physicalCoerciveSublevelCompactnessProducerLevel : ProofLevel
physicalCoerciveSublevelCompactnessProducerLevel =
  Preferred.physicalCoerciveSublevelCompactnessLevel

data T1PrerequisiteStatus202 : Set where
  missingPhysicalCoerciveObservableRenormalization : T1PrerequisiteStatus202
  missingPhysicalCoerciveObservableNonnegativity : T1PrerequisiteStatus202
  missingPhysicalCoercivity : T1PrerequisiteStatus202
  missingCoerciveSublevelCompactness : T1PrerequisiteStatus202
  readyForMarkovUniformTightnessCompiler : T1PrerequisiteStatus202

preferredCurrentT1Status202 : T1PrerequisiteStatus202
preferredCurrentT1Status202 = missingPhysicalCoerciveObservableRenormalization

round201CutRetainedForCompatibility : ProofLevel
round201CutRetainedForCompatibility = R201.currentYMTerminalCutsetRound201Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound202Level : ProofLevel
currentYMTerminalCutsetRound202Level = machineChecked

literalPreferredT5ContinuumLeaf202Level : ProofLevel
literalPreferredT5ContinuumLeaf202Level = conditional
