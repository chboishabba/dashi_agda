module DASHI.Philosophy.ReflexivePowerUp where

open import Agda.Primitive using (Set₁)

------------------------------------------------------------------------
-- 1.0 knowledge: experience held inside an implicit frame.

record FirstOrderKnowledge (X : Set) : Set where
  constructor firstOrderKnowledge
  field
    experience :
      X

open FirstOrderKnowledge public

------------------------------------------------------------------------
-- 1.1 knowledge: the experience plus a representation of its frame,
-- observer position, residuals, and possible interventions.
--
-- This is reflected situatedness, not omniscience.

record ReflexiveKnowledge
       (X Frame Residual Intervention : Set) : Set₁ where
  constructor reflexiveKnowledge
  field
    experience :
      X

    frameOf :
      X →
      Frame

    representedFrame :
      Frame

    observerPosition :
      Frame

    residual :
      Residual

    possibleIntervention :
      Intervention

    noViewFromNowhere :
      Set

open ReflexiveKnowledge public

powerUp :
  ∀ {X Frame Residual Intervention : Set} →
  (x : X) →
  (frame : X → Frame) →
  Frame →
  Residual →
  Intervention →
  Set →
  ReflexiveKnowledge X Frame Residual Intervention
powerUp x frame position r intervention humility =
  reflexiveKnowledge
    x
    frame
    (frame x)
    position
    r
    intervention
    humility

------------------------------------------------------------------------
-- Recursive humility: the critical frame can itself become an object of
-- criticism.

record RevisableReflexiveKnowledge
       (X Frame MetaFrame Residual Intervention : Set) : Set₁ where
  field
    reflexive :
      ReflexiveKnowledge X Frame Residual Intervention

    frameOfFrame :
      Frame →
      MetaFrame

    representedMetaFrame :
      MetaFrame

    revisionWitness :
      Set

open RevisableReflexiveKnowledge public

------------------------------------------------------------------------
-- Distress is a situated mismatch signal.  It does not identify a unique
-- cause and does not automatically decide whether person or system is right.

record SituatedDistressSignal
       (Person Environment History Body Signal Interpretation : Set) : Set₁ where
  field
    person :
      Person

    environment :
      Environment

    history :
      History

    body :
      Body

    signal :
      Signal

    candidateInterpretation :
      Interpretation

    signalIsNotNoise :
      Set

    noUniqueCauseInferred :
      Set

    noAutomaticClinicalOrPoliticalPromotion :
      Set

open SituatedDistressSignal public
