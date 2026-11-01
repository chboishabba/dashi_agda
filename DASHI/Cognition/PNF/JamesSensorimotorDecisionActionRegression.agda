module DASHI.Cognition.PNF.JamesSensorimotorDecisionActionRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.JamesSensorimotorDecisionActionExact as James
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Decision

------------------------------------------------------------------------
-- Focused regression: the James owner must retain active-sensing recurrence,
-- experience-dependent learning with remembered-event preservation,
-- lossy action projection, and metaphysical non-promotion.
------------------------------------------------------------------------

record JamesSensorimotorRegression (memory : Memory.MemoryFibre) : Set where
  constructor jamesSensorimotorRegression
  field
    supportFeedbackAfterAction :
      James.sensory
        (James.activeSensingStep
          (James.sensorimotorEpisode
            James.neutralEnvironment
            James.neutralBody
            James.neutralSensation
            James.supportSensorimotor
            Decision.supportAction
            memory))
      ≡ James.supportFeedback

    learningPreservesRememberedEvent :
      Memory.rememberedEvent (James.learningThroughActiveSensing memory)
      ≡ Memory.rememberedEvent memory

    sameActionStillDoesNotRecoverMechanism :
      James.sensorimotorProjection (James.supportMechanismEpisode memory)
      ≡ James.sensorimotorProjection (James.counterMechanismEpisode memory) → ⊥

    determinismNotPromoted :
      James.paperProvesDeterminism James.canonicalJamesWrongTypeBoundary
      ≡ false

open JamesSensorimotorRegression public

canonicalJamesSensorimotorRegression :
  (memory : Memory.MemoryFibre) → JamesSensorimotorRegression memory
canonicalJamesSensorimotorRegression memory =
  jamesSensorimotorRegression
    (James.supportActionChangesNextSensation memory)
    (James.activeSensingLearningPreservesRememberedEvent memory)
    (James.sensorimotorStatesStillDiffer memory)
    James.jamesDoesNotProveDeterminism
