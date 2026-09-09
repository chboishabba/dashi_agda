{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound193Exact where

------------------------------------------------------------------------
-- ROUND193: ELIMINATE THE T5 GRAM/MEASURE SAME-OBJECT LEAF
--
-- Round192 exposed five analytic producer classes above the mature quantitative
-- T5 machinery.  One of them was still an artefact of choosing OS-Gram data
-- independently from the expectation producer and then asking for equality.
--
-- The preferred route now constructs the OS-Gram carrier directly from the
-- expectation producer.  Its finite measure sequence and continuum candidate
-- are definitionally identical to the selected diagonal quantitative sequence.
-- Therefore the post-hoc Gram/measure same-object leaf is not primitive.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound192Exact as R192
import DASHI.Physics.YangMills.BalabanClayT5PreferredOSGramFromExpectationExact as PreferredGram
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumAnalyticProducer : Set where
  physicalMeasureLimitConvergence : T5PreferredContinuumAnalyticProducer
  physicalMeasurePropertySequentialClosure : T5PreferredContinuumAnalyticProducer
  physicalGramReflectionMeasureTopologyClosure : T5PreferredContinuumAnalyticProducer
  physicalContinuumSchwingerAxioms : T5PreferredContinuumAnalyticProducer

preferredT5ContinuumAnalyticCut : List T5PreferredContinuumAnalyticProducer
preferredT5ContinuumAnalyticCut =
  physicalMeasureLimitConvergence ∷
  physicalMeasurePropertySequentialClosure ∷
  physicalGramReflectionMeasureTopologyClosure ∷
  physicalContinuumSchwingerAxioms ∷ []

-- The fifth Round192 leaf is removed by construction on the preferred route.
gramMeasureSameObjectCompilerLevel : ProofLevel
gramMeasureSameObjectCompilerLevel =
  PreferredGram.physicalGramMeasureSameObjectCompilerLevel

preferredOSGramConstructionLevel : ProofLevel
preferredOSGramConstructionLevel =
  PreferredGram.physicalOSGramFromExpectationCompilerLevel

round192FiveLeafCutRetainedForCompatibility : ProofLevel
round192FiveLeafCutRetainedForCompatibility =
  R192.currentYMTerminalCutsetRound192Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound193Level : ProofLevel
currentYMTerminalCutsetRound193Level = machineChecked

literalPreferredT5ContinuumAnalyticProducerLevel : ProofLevel
literalPreferredT5ContinuumAnalyticProducerLevel = conditional
