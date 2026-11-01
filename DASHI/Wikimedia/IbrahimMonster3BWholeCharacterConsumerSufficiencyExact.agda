module DASHI.Wikimedia.IbrahimMonster3BWholeCharacterConsumerSufficiencyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Refinement
import DASHI.Wikimedia.IbrahimMonster3BWholeCharacterIsotypicBypassExact as Whole
import DASHI.Wikimedia.IbrahimMonster3BConstituentAttachmentSnowballExact as Constituent

------------------------------------------------------------------------
-- MONSTER WHOLE-CHARACTER CONSUMER-SUFFICIENCY BIDI BRIDGE
--
-- Cross-pollinated structure with the RSA action-observer lane:
--
--   1. choose the declared consumer;
--   2. ask whether a coarse observer is sufficient;
--   3. if yes, do not require a richer representation merely for completeness;
--   4. if no, retain a consumer-relevant collision and add only a residual that
--      separates that failed fibre.
--
-- Here the candidate coarse observer is the whole restricted character and the
-- declared consumer is the H_zeta-isotypic representation class.  The proposed
-- Lean producer would certify that this coarse information is sufficient under
-- the semisimple/simple hypotheses.  If that producer fails, the literal
-- constituent route supplies a richer residual witness.
--
-- This does not say that the character is sufficient for the later concrete
-- X6 x Fin90 basis/action consumer.  That consumer is strictly stronger and
-- remains separately unpaid.
------------------------------------------------------------------------

refinementBoundary : Refinement.ConsumerIndexedResidualRefinementBoundary
refinementBoundary = Refinement.canonicalConsumerIndexedResidualRefinementBoundary

wholeBoundary : Whole.WholeCharacterIsotypicBypassBoundary
wholeBoundary = Whole.canonicalWholeCharacterIsotypicBypassBoundary

constituentBoundary : Constituent.ConstituentAttachmentFrontier
constituentBoundary = Constituent.currentConstituentAttachmentFrontier

------------------------------------------------------------------------
-- WrongType boundaries.
------------------------------------------------------------------------

data WholeCharacterSufficiencyCreatesConcreteBasisActionRecognition : Set where
data FailedWholeCharacterProbeRequiresWorldCompleteReconstruction : Set where
data OEISCreatesMonsterConsumerSufficiency : Set where
data CharacterConsumerSufficiencyTransfersToEveryConsumer : Set where

wholeCharacterSufficiencyDoesNotCreateConcreteRecognition :
  WholeCharacterSufficiencyCreatesConcreteBasisActionRecognition -> ⊥
wholeCharacterSufficiencyDoesNotCreateConcreteRecognition ()

failedProbeDoesNotRequireWorldCompleteReconstruction :
  FailedWholeCharacterProbeRequiresWorldCompleteReconstruction -> ⊥
failedProbeDoesNotRequireWorldCompleteReconstruction ()

oeisDoesNotCreateMonsterConsumerSufficiency :
  OEISCreatesMonsterConsumerSufficiency -> ⊥
oeisDoesNotCreateMonsterConsumerSufficiency ()

consumerSufficiencyDoesNotTransferUniversally :
  CharacterConsumerSufficiencyTransfersToEveryConsumer -> ⊥
consumerSufficiencyDoesNotTransferUniversally ()

record MonsterWholeCharacterConsumerSufficiencyBoundary : Set where
  constructor monster-whole-character-consumer-sufficiency-boundary
  field
    consumerIndexedResidualRefinementReused : Bool
    wholeCharacterMayBeSufficientForIsotypicConsumer : Bool
    failureMustReturnConsumerRelevantResidual : Bool
    literalConstituentFallbackRetained : Bool
    wholeCharacterLeanProducerPaid : Bool
    wholeCharacterSufficiencyCreatesConcreteBasisActionRecognition : Bool
    characterSufficiencyTransfersToEveryConsumer : Bool
    oeisCreatesConsumerSufficiency : Bool
    nextResidual : String
open MonsterWholeCharacterConsumerSufficiencyBoundary public

canonicalMonsterWholeCharacterConsumerSufficiencyBoundary :
  MonsterWholeCharacterConsumerSufficiencyBoundary
canonicalMonsterWholeCharacterConsumerSufficiencyBoundary =
  monster-whole-character-consumer-sufficiency-boundary
    true
    true
    true
    true
    false
    false
    false
    false
    "treat the whole-character Lean theorem as a consumer-sufficiency probe, not a world-completeness theorem. Attempt only the FDRep-to-group-algebra adapter needed to show the H_zeta-isotypic consumer factors through the whole character under the declared semisimple/simple hypotheses. If that attempt yields a concrete obstruction, retain it as the residual that justifies the richer literal-constituent route. Even a successful isotypic theorem does not pay the later X6 x Fin90/Base369 basis-action consumer."
