module DASHI.Moonshine.Base369Monster3BSingleActionProducerBidiExact where

------------------------------------------------------------------------
-- SINGLE-PRODUCER BIDI CUT
--
-- The previous capstone accepted two inputs:
--
--   phaseResolved : ActualMonster3BPhaseResolvedSector
--   recognition   : ActualZetaSectorRecognition chosenZetaSector.
--
-- For repo recovery this is unnecessarily weak.  Once a literal actual state
-- carrier and central/normalizer action are recovered, the chosen zeta sector
-- can be taken to be the literal dependent eigenspace itself.  Its inclusion
-- and recovery maps are identities.  Phase resolution is therefore compiler
-- output from the action producer, not an independent scientific object.
--
-- The one remaining producer must attach the Weyl/model recognition to that
-- SAME literal eigenspace.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Recognition
import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Action

record ActualMonster3BSingleActionProducer : Set₁ where
  field
    State Normalizer : Set
    normalizerAction : Inertia.CentralNormalizerAction State Normalizer

    recognition :
      Recognition.ActualZetaSectorRecognition
        (Inertia.CentralEigenspace
          (Inertia.phaseAction normalizerAction)
          Inertia.phaseZeta)

open ActualMonster3BSingleActionProducer public

literalZetaSector : ActualMonster3BSingleActionProducer → Set
literalZetaSector source =
  Inertia.CentralEigenspace
    (Inertia.phaseAction (normalizerAction source))
    Inertia.phaseZeta

phaseResolvedFromSingleProducer :
  (source : ActualMonster3BSingleActionProducer) →
  Inertia.ActualMonster3BPhaseResolvedSector
phaseResolvedFromSingleProducer source =
  record
    { State = State source
    ; Normalizer = Normalizer source
    ; normalizerAction = normalizerAction source
    ; chosenZetaSector = literalZetaSector source
    ; includeChosenZeta = λ state → state
    ; recoverChosenZeta = λ state → state
    ; recoverAfterInclude = λ state → refl
    ; includeAfterRecover = λ state → refl
    }

actualActionRecognitionFromSingleProducer :
  ActualMonster3BSingleActionProducer →
  Action.ActualMonster3BActionRecognition
actualActionRecognitionFromSingleProducer source =
  record
    { phaseResolved = phaseResolvedFromSingleProducer source
    ; recognition = recognition source
    }

------------------------------------------------------------------------
-- Boundary / search consequences.
------------------------------------------------------------------------

record SingleActionProducerBoundary : Set where
  constructor single-action-producer-boundary
  field
    chosenZetaSectorIsLiteralEigenspace : Bool
    phaseResolvedRecordIsCompilerOutput : Bool
    separatePhaseSectorRecoverySearchNeeded : Bool
    recognitionMustUseSameLiteralEigenspace : Bool
    dimensionOrCharacterEqualitySufficesForRecognition : Bool
    actualSingleProducerInhabitedHere : Bool

canonicalSingleActionProducerBoundary : SingleActionProducerBoundary
canonicalSingleActionProducerBoundary =
  single-action-producer-boundary
    true true false true false false
