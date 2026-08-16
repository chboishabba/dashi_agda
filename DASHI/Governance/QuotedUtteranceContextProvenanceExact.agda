module DASHI.Governance.QuotedUtteranceContextProvenanceExact where

------------------------------------------------------------------------
-- QUOTED UTTERANCE / CONTEXT / LATER CLARIFICATION
--
-- Worked case: Hasan Piker's 2019 "America deserved 9/11" statement.
--
-- Contemporaneous reporting / source trail:
-- Sean Burch,
-- "Young Turks' Hasan Piker Says Comment That US 'Deserved 9/11' Was
-- 'Inappropriate'", TheWrap, 23 August 2019. No DOI asserted.
-- The report records the original livestream statement and Piker's subsequent
-- description of his wording as inappropriate / imprecise and attempted
-- satire in an interview with Cenk Uygur.
--
-- Reuters,
-- "UK blocks visits by left-wing US commentators Cenk Uygur and Hasan Piker",
-- 1 June 2026. No DOI asserted.
-- Bounded role: later independent reporting that the 2019 statement occurred
-- and was subsequently characterized by Piker as inappropriate.
--
-- The formal rule is symmetric: context/clarification does not erase a literal
-- utterance, while the literal utterance alone does not establish every wider
-- proposition about speaker motive, intended victim target, ideology, or
-- endorsement of violence.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.AmalekProvenanceRoleBinding as Amalek

record QuoteReceipt : Set where
  constructor quoteReceipt
  field
    speaker : String
    utterance : String
    date : String
    setting : String
    source : String

open QuoteReceipt public

record ContextReceipt : Set where
  constructor contextReceipt
  field
    speakerOrSource : String
    date : String
    contextualReading : String
    source : String

open ContextReceipt public

hasan2019Quote : QuoteReceipt
hasan2019Quote = quoteReceipt
  "Hasan Piker"
  "America deserved 9/11"
  "2019-08"
  "Twitch livestream while criticizing U.S. foreign policy and Dan Crenshaw"
  "contemporaneous reporting including TheWrap, 2019-08-23; no DOI asserted"

hasan2019Clarification : ContextReceipt
hasan2019Clarification = contextReceipt
  "Hasan Piker"
  "2019-08-22/23"
  "said the wording was inappropriate/imprecise and described the remark as a poor attempt at satire in a TYT interview; foreign-policy critique remained part of his explanation"
  "Sean Burch, TheWrap, 2019-08-23; no DOI asserted"

hasanLaterIndependentReceipt : ContextReceipt
hasanLaterIndependentReceipt = contextReceipt
  "Reuters"
  "2026-06-01"
  "independent later report records the 2019 statement and that Piker subsequently said it was inappropriate"
  "Reuters, UK blocks visits by left-wing US commentators Cenk Uygur and Hasan Piker; no DOI asserted"

------------------------------------------------------------------------
-- Semantic non-promotions.
------------------------------------------------------------------------

data LiteralQuotePromotesCivilianVictimDesert : Set where

data LiteralQuotePromotesSpeakerMotive : Set where

data ClarificationErasesOriginalUtterance : Set where

data AssociationWithSpeakerPromotesQuoteEndorsement : Set where

quoteDoesNotByItselfPromoteVictimDesert :
  LiteralQuotePromotesCivilianVictimDesert → ⊥
quoteDoesNotByItselfPromoteVictimDesert ()

quoteDoesNotByItselfPromoteMotive : LiteralQuotePromotesSpeakerMotive → ⊥
quoteDoesNotByItselfPromoteMotive ()

clarificationDoesNotEraseOriginal : ClarificationErasesOriginalUtterance → ⊥
clarificationDoesNotEraseOriginal ()

associationDoesNotPromoteEndorsement :
  AssociationWithSpeakerPromotesQuoteEndorsement → ⊥
associationDoesNotPromoteEndorsement ()

------------------------------------------------------------------------
-- Cross-pollination with Amalek role-binding: quoted language, contextual
-- reading, identity assignment and downstream command/policy transport are
-- different authorities.  A provocative phrase does not get to bypass those
-- same provenance gates merely because it is politically salient.
------------------------------------------------------------------------

amalekRoleBindingBoundary : Amalek.AmalekBoundary
amalekRoleBindingBoundary = Amalek.canonicalAmalekBoundary

record QuotedUtteranceBoundary : Set where
  constructor quotedUtteranceBoundary
  field
    literalUtterancePreserved : Bool
    contextPreserved : Bool
    laterClarificationPreserved : Bool
    clarificationErasesQuote : Bool
    quoteAloneEstablishesMotive : Bool
    quoteAloneEstablishesVictimDesertClaim : Bool
    politicalAssociationEstablishesEndorsement : Bool

canonicalQuotedUtteranceBoundary : QuotedUtteranceBoundary
canonicalQuotedUtteranceBoundary =
  quotedUtteranceBoundary true true true false false false false
