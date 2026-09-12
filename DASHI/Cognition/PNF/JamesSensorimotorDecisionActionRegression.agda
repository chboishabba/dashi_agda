module DASHI.Cognition.PNF.JamesSensorimotorDecisionActionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.JamesSensorimotorDecisionActionExact as James
import DASHI.Cognition.PNF.MemoryFibre as Memory

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
            James.neutralSensation
            James.supportSensorimotor
            James.Decision.supportAction
            memory))
      ≡ James.supportFeedback

    learningPreservesRememberedEvent :
      Memory.rememberedEvent (James.learningThroughActiveSensing memory)
      ≡ Memory.rememberedEvent memory

    sameActionStillDoesNotRecoverMechanism :
      James.sensorimotorProjection (James.supportMechanismEpisode memory)
      ≡ James.sensorimotorProjection (James.counterMechanismEpisode memory) → ⊥

    determinismNotPromoted :
      James.JamesWrongTypeBoundary.paperProvesDeterminism
        James.canonicalJamesWrongTypeBoundary
      ≡ Agda.Builtin.Bool.false

open JamesSensorimotorRegression public

canonicalJamesSensorimotorRegression :
  (memory : Memory.MemoryFibre) → JamesSensorimotorRegression memory
canonicalJamesSensorimotorRegression memory =
  jamesSensorimotorRegression
    (James.supportActionChangesNextSensation memory)
    (James.activeSensingLearningPreservesRememberedEvent memory)
    (James.sensorimotorStatesStillDiffer memory)
    James.jamesDoesNotProveDeterminism
