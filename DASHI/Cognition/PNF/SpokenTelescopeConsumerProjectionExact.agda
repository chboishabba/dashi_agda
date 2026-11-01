module DASHI.Cognition.PNF.SpokenTelescopeConsumerProjectionExact where

------------------------------------------------------------------------
-- SPOKEN-WORD / PNF CONSUMER PROJECTION EXAMPLE
--
-- "I saw John with the telescope" has two retained parses:
--   instrumentParse  : the speaker used the telescope;
--   possessionParse  : John had the telescope.
--
-- Both parses answer "who was seen?" identically, but they answer "who had
-- the telescope?" differently.  A later discourse action can therefore expose
-- a distinction that an earlier consumer was licensed to ignore.
--
-- This is a finite semantic regression model.  It does not claim that these
-- two parses exhaust natural-language interpretation in the world.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Core.DynamicProjectionCompositionExact as Dynamic

------------------------------------------------------------------------
-- Fine represented carrier.
------------------------------------------------------------------------

data Participant : Set where
  speaker : Participant
  john : Participant

data TelescopeParse : Set where
  instrumentParse : TelescopeParse
  possessionParse : TelescopeParse

data ParseProvenance : Set where
  syntacticAttachmentResidual : ParseProvenance

data QueryStage : Set where
  askWhoSeen : QueryStage
  askTelescopeHolder : QueryStage

record SpokenPNFState : Set where
  constructor spokenPNFState
  field
    parse : TelescopeParse
    provenance : ParseProvenance
    queryStage : QueryStage

open SpokenPNFState public

instrumentState possessionState : SpokenPNFState
instrumentState =
  spokenPNFState instrumentParse syntacticAttachmentResidual askWhoSeen
possessionState =
  spokenPNFState possessionParse syntacticAttachmentResidual askWhoSeen

whoSeen : TelescopeParse → Participant
whoSeen instrumentParse = john
whoSeen possessionParse = john

telescopeHolder : TelescopeParse → Participant
telescopeHolder instrumentParse = speaker
telescopeHolder possessionParse = john

whoSeenProjection : SpokenPNFState → Participant
whoSeenProjection state = whoSeen (parse state)

telescopeHolderProjection : SpokenPNFState → Participant
telescopeHolderProjection state = telescopeHolder (parse state)

whoSeenConsumerMayCollapseCurrentParse :
  whoSeenProjection instrumentState ≡ whoSeenProjection possessionState
whoSeenConsumerMayCollapseCurrentParse = refl

telescopeHolderConsumerMustDistinguish :
  telescopeHolderProjection instrumentState
  ≡ telescopeHolderProjection possessionState → ⊥
telescopeHolderConsumerMustDistinguish ()

------------------------------------------------------------------------
-- Dynamic discourse observation.
------------------------------------------------------------------------

data SpokenObservation : Set where
  seenAnswer : Participant → SpokenObservation
  holderAnswer : Participant → SpokenObservation

observeForCurrentQuestion : SpokenPNFState → SpokenObservation
observeForCurrentQuestion state with queryStage state
... | askWhoSeen = seenAnswer (whoSeen (parse state))
... | askTelescopeHolder = holderAnswer (telescopeHolder (parse state))

data DiscourseAction : Set where
  continueToHolderQuestion : DiscourseAction

advanceDiscourse : DiscourseAction → SpokenPNFState → SpokenPNFState
advanceDiscourse continueToHolderQuestion state =
  spokenPNFState
    (parse state)
    (provenance state)
    askTelescopeHolder

spokenDynamics : Dynamic.ActionDynamics SpokenPNFState DiscourseAction
spokenDynamics = Dynamic.actionDynamics advanceDiscourse

sameObservationAtWhoQuestion :
  observeForCurrentQuestion instrumentState
  ≡ observeForCurrentQuestion possessionState
sameObservationAtWhoQuestion = refl

futureObservationSeparatesParses :
  observeForCurrentQuestion
    (Dynamic.runTrace spokenDynamics
      (continueToHolderQuestion ∷ []) instrumentState)
  ≡
  observeForCurrentQuestion
    (Dynamic.runTrace spokenDynamics
      (continueToHolderQuestion ∷ []) possessionState)
  → ⊥
futureObservationSeparatesParses ()

------------------------------------------------------------------------
-- Reopenable residual: the coarse "John was seen" answer plus the retained
-- parse coordinate reconstructs the represented semantic branch.
------------------------------------------------------------------------

reopenFromSeenAnswer : Participant → TelescopeParse → SpokenPNFState
reopenFromSeenAnswer answer parseChoice =
  spokenPNFState parseChoice syntacticAttachmentResidual askWhoSeen

parseResidualReopensInstrument :
  reopenFromSeenAnswer
    (whoSeenProjection instrumentState)
    instrumentParse
  ≡ instrumentState
parseResidualReopensInstrument = refl

parseResidualReopensPossession :
  reopenFromSeenAnswer
    (whoSeenProjection possessionState)
    possessionParse
  ≡ possessionState
parseResidualReopensPossession = refl

------------------------------------------------------------------------
-- Authority boundary: equality for one bounded consumer is not a universal
-- semantic identity theorem.
------------------------------------------------------------------------

data WhoSeenEqualityPromotesFullSemanticIdentity : Set where

whoSeenEqualityCannotPromoteFullIdentity :
  WhoSeenEqualityPromotesFullSemanticIdentity → ⊥
whoSeenEqualityCannotPromoteFullIdentity ()
