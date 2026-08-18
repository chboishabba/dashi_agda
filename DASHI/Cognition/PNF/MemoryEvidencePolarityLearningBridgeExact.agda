module DASHI.Cognition.PNF.MemoryEvidencePolarityLearningBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Cognition.PNF.MemoryFibre as Memory

------------------------------------------------------------------------
-- Evidence revision need not erase remembered-event identity.
--
-- The existing PNF learning algebra already proves that revaluation,
-- habituation, extinction and phase realignment preserve remembered semantic
-- content.  This bridge adds only an orthogonal evidence-polarity coordinate:
-- the appraisal of a remembered claim may change while the remembered event
-- remains the same versioned carrier.
------------------------------------------------------------------------

record PolarityAnnotatedLearningStep : Set where
  constructor polarityAnnotatedLearningStep
  field
    learningReceipt : Learning.LearningReceipt
    beforePolarity : Four.PolarAssessment
    afterPolarity : Four.PolarAssessment
    rememberedEventPreserved :
      Memory.rememberedEvent (Learning.after learningReceipt)
      ≡ Memory.rememberedEvent (Learning.before learningReceipt)

open PolarityAnnotatedLearningStep public

revaluationPolarityStep :
  Memory.MemoryFibre →
  Nat →
  Four.PolarAssessment →
  Four.PolarAssessment →
  PolarityAnnotatedLearningStep
revaluationPolarityStep memory value beforeEvidence afterEvidence =
  polarityAnnotatedLearningStep
    (Learning.revaluationReceipt memory value)
    beforeEvidence
    afterEvidence
    (Memory.revaluePreservesRememberedEvent memory value)

extinctionPolarityStep :
  Memory.MemoryFibre →
  Four.PolarAssessment →
  Four.PolarAssessment →
  PolarityAnnotatedLearningStep
extinctionPolarityStep memory beforeEvidence afterEvidence =
  polarityAnnotatedLearningStep
    (Learning.extinctionReceipt memory)
    beforeEvidence
    afterEvidence
    (Memory.extinctionPreservesRememberedEvent memory)

record MemoryEvidencePolarityBoundary : Set where
  field
    evidenceRevisionRequiresMemoryErasureClaimed : Bool
    extinctionErasesRememberedEventClaimed : Bool
    appraisalAndRememberedIdentitySeparated : Bool
    priorMemoryRetentionCompatible : Bool

canonicalMemoryEvidencePolarityBoundary : MemoryEvidencePolarityBoundary
canonicalMemoryEvidencePolarityBoundary = record
  { evidenceRevisionRequiresMemoryErasureClaimed = false
  ; extinctionErasesRememberedEventClaimed = false
  ; appraisalAndRememberedIdentitySeparated = true
  ; priorMemoryRetentionCompatible = true
  }
