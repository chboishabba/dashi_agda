{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound192Exact where

------------------------------------------------------------------------
-- ROUND192: REFINE THE T5 TERMINAL CUT THROUGH THE QUANTITATIVE CLOSURE COMPILER
--
-- Round191 synchronized the global YM frontier.  Round192 makes one further
-- least-privilege reduction: the broad `FiniteToContinuumOSClosure` object is
-- no longer a primitive search leaf once the mature quantitative T5 package is
-- present.  It is compiled from five analytic producer classes below.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound191Exact as R191
import DASHI.Physics.YangMills.BalabanClayT5QuantitativeContinuumClosureCompilerExact as Closure
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

-- These are the theorem-bearing analytic classes above the already-owned
-- quantitative tail/moment/compactness and OS-Gram reductions.
data T5ContinuumAnalyticProducer : Set where
  physicalMeasureLimitConvergence : T5ContinuumAnalyticProducer
  physicalMeasurePropertySequentialClosure : T5ContinuumAnalyticProducer
  physicalGramMeasureSameObject : T5ContinuumAnalyticProducer
  physicalGramReflectionMeasureTopologyClosure : T5ContinuumAnalyticProducer
  physicalContinuumSchwingerAxioms : T5ContinuumAnalyticProducer

preferredT5ContinuumAnalyticCut : List T5ContinuumAnalyticProducer
preferredT5ContinuumAnalyticCut =
  physicalMeasureLimitConvergence ∷
  physicalMeasurePropertySequentialClosure ∷
  physicalGramMeasureSameObject ∷
  physicalGramReflectionMeasureTopologyClosure ∷
  physicalContinuumSchwingerAxioms ∷ []

-- The old broad closure leaf is therefore a compiler target, not a primitive
-- theorem search surface.
quantitativeClosureCompilerLevel : ProofLevel
quantitativeClosureCompilerLevel = Closure.quantitativeContinuumClosureCompilerLevel

measureLimitProducerLevel : ProofLevel
measureLimitProducerLevel = Closure.physicalMeasureLimitConvergenceLevel

measurePropertyClosureProducerLevel : ProofLevel
measurePropertyClosureProducerLevel =
  Closure.physicalMeasurePropertySequentialClosureLevel

gramMeasureIdentityProducerLevel : ProofLevel
gramMeasureIdentityProducerLevel = Closure.physicalGramMeasureSameObjectLevel

gramMeasureTopologyClosureProducerLevel : ProofLevel
gramMeasureTopologyClosureProducerLevel =
  Closure.physicalGramReflectionMeasureTopologyClosureLevel

continuumSchwingerAxiomProducerLevel : ProofLevel
continuumSchwingerAxiomProducerLevel =
  Closure.physicalContinuumSchwingerAxiomInputsLevel

-- Global synchronization remains fail-closed.  Refining the producer cut does
-- not flip any mathematical promotion coordinate.
finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

round191GlobalCutStillCanonical : ProofLevel
round191GlobalCutStillCanonical = R191.currentYMTerminalCutsetRound191Level

currentYMTerminalCutsetRound192Level : ProofLevel
currentYMTerminalCutsetRound192Level = machineChecked

literalT5ContinuumAnalyticProducerLevel : ProofLevel
literalT5ContinuumAnalyticProducerLevel = conditional
