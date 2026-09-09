{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound201Exact where

------------------------------------------------------------------------
-- ROUND201: SAME-OBJECT MEANS EQUALITY, NOT A COERCIVITY PREDICATE
--
-- Round200 removed the diagonal-measure weld by preferred construction.  The
-- next frontier must still distinguish two facts that older surfaces blurred:
--
--   1. the literal moment observable equals the independently physical
--      coercive observable;
--   2. that independently physical observable is coercive in the selected
--      topology.
--
-- Equality transports coercivity mechanically.  Neither fact may stand in for
-- the other.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound200Exact as R200
import DASHI.Physics.YangMills.BalabanClayT5CoerciveMomentMarkovContainmentExact as Coercive
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf201 : Set where
  physicalMomentObservableEqualsCoerciveObservable : T5PreferredContinuumLeaf201
  physicalCoerciveObservableCoercivity : T5PreferredContinuumLeaf201
  physicalCoerciveSublevelCompactness : T5PreferredContinuumLeaf201
  physicalEveryExtractedClusterPointIsTarget : T5PreferredContinuumLeaf201
  physicalMeasurePropertySequentialClosure : T5PreferredContinuumLeaf201
  physicalGramReflectionMeasureTopologyClosure : T5PreferredContinuumLeaf201
  physicalContinuumSchwingerAxioms : T5PreferredContinuumLeaf201

preferredT5ContinuumCut201 : List T5PreferredContinuumLeaf201
preferredT5ContinuumCut201 =
  physicalMomentObservableEqualsCoerciveObservable ∷
  physicalCoerciveObservableCoercivity ∷
  physicalCoerciveSublevelCompactness ∷
  physicalEveryExtractedClusterPointIsTarget ∷
  physicalMeasurePropertySequentialClosure ∷
  physicalGramReflectionMeasureTopologyClosure ∷
  physicalContinuumSchwingerAxioms ∷ []

coerciveObservableEqualityTransportLevel : ProofLevel
coerciveObservableEqualityTransportLevel =
  Coercive.coerciveObservableEqualityTransportLevel

coerciveMomentMarkovContainmentCompilerLevel : ProofLevel
coerciveMomentMarkovContainmentCompilerLevel =
  Coercive.coerciveMomentMarkovContainmentCompilerLevel

physicalMomentObservableSameObjectProducerLevel : ProofLevel
physicalMomentObservableSameObjectProducerLevel =
  Coercive.physicalCoerciveMomentObservableSameObjectLevel

physicalCoerciveObservableCoercivityProducerLevel : ProofLevel
physicalCoerciveObservableCoercivityProducerLevel =
  Coercive.physicalCoerciveObservableCoercivityLevel

physicalCoerciveSublevelCompactnessProducerLevel : ProofLevel
physicalCoerciveSublevelCompactnessProducerLevel =
  Coercive.physicalCoerciveSublevelCompactnessLevel

data T1PrerequisiteStatus201 : Set where
  missingMomentObservableEquality : T1PrerequisiteStatus201
  missingPhysicalCoercivity : T1PrerequisiteStatus201
  missingCoerciveSublevelCompactness : T1PrerequisiteStatus201
  readyForMarkovUniformTightnessCompiler : T1PrerequisiteStatus201

preferredCurrentT1Status201 : T1PrerequisiteStatus201
preferredCurrentT1Status201 = missingMomentObservableEquality

round200CutRetainedForCompatibility : ProofLevel
round200CutRetainedForCompatibility = R200.currentYMTerminalCutsetRound200Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound201Level : ProofLevel
currentYMTerminalCutsetRound201Level = machineChecked

literalPreferredT5ContinuumLeaf201Level : ProofLevel
literalPreferredT5ContinuumLeaf201Level = conditional
