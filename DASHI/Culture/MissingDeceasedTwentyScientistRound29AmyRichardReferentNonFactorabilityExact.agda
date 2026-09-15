module DASHI.Culture.MissingDeceasedTwentyScientistRound29AmyRichardReferentNonFactorabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Culture.MissingDeceasedTwentyScientistRound28AmyNASACandidateWeldExact as R28

------------------------------------------------------------------------
-- ROUND 29: AMY -> RICHARD REFERENT NON-FACTORABILITY
--
-- The official HAL5 deck pays a strong candidate predicate intersection:
-- Richard Eskridge is explicitly on Amy's team and is labelled a co-founder,
-- CTO, retired NASA engineer and scientist.  NASA TM 20205010911 separately
-- pays R.H. Eskridge authorship and MSFC provenance.  Amy's later reproduced
-- statement, however, refers only to an unnamed "member of our team" and an
-- unnamed NASA-reviewed paper.  Matching all exposed predicates is therefore
-- a candidate-generation surface, not a literal referent-identity receipt.
------------------------------------------------------------------------

hal5DeckSource : Attribution.AttributedSource
hal5DeckSource = Attribution.mkNoDOISource
  "Amy Eskridge / Huntsville Alabama L5 Society"
  "A Historical Perspective on Anti-Gravity Technology"
  "HAL5 December 2018 presentation deck"
  "2018"
  "https://www.hal5.org/PDF/HAL5-Dec2018-Talk-AntiGravity.pdf"
  Attribution.communitySource
  "primary event deck for the bounded team-role claims: Richard Eskridge appears on the team surface and is separately labelled CTO, co-founder, retired NASA engineer and scientist"
  Attribution.publicAttribution

hal5DeckSnowball : Snowball.SourceRoleSnowballReceipt hal5DeckSource
hal5DeckSnowball = Snowball.canonicalSourceRoleSnowballReceipt hal5DeckSource

record RichardCandidatePredicateReceipt : Set where
  constructor richard-candidate-predicate-receipt
  field
    teamSource : Attribution.AttributedSource
    nasaSource : Attribution.AttributedSource
    teamMembershipPaid : Bool
    retiredNASAIdentityPaid : Bool
    nasaReportAuthorshipPaid : Bool
    msfcProvenancePaid : Bool
    candidatePredicateIntersection : Bool
    unnamedReferentIdentity : Bool
    exactPaperIdentity : Bool
    sameObjectSemantics : Bool
    pays : String
    doesNotPay : String

open RichardCandidatePredicateReceipt public

richardCandidateReceipt : RichardCandidatePredicateReceipt
richardCandidateReceipt = richard-candidate-predicate-receipt
  hal5DeckSource
  R28.nasaTMSource
  true
  true
  true
  true
  true
  false
  false
  false
  "Richard is a source-backed member of Amy's 2018 team surface, a retired NASA engineer/scientist, and the R.H. Eskridge author of the later MSFC Technical Memorandum candidate"
  "that Amy's unnamed 2020 team-member referent was Richard, that her unnamed paper was TM 20205010911, Institute participation in SAA8-1519855, H2, H3, suppression, or event causation"

richardTeamMembershipPaid : Bool
richardTeamMembershipPaid = true

richardRetiredNASAIdentityPaid : Bool
richardRetiredNASAIdentityPaid = true

richardNASAReportAuthorshipPaid : Bool
richardNASAReportAuthorshipPaid = true

candidatePredicateIntersectionPaid : Bool
candidatePredicateIntersectionPaid = true

unnamedReferentIdentityPaid : Bool
unnamedReferentIdentityPaid = false

sameObjectSemanticsPaid : Bool
sameObjectSemanticsPaid = false

------------------------------------------------------------------------
-- Predicate matching does not factor to referent identity.
--
-- The same visible candidate-predicate surface is consistent with a world in
-- which Richard is Amy's unnamed referent and a world in which another team
-- member is.  Without an additional identity-bearing receipt the referent query
-- cannot factor through candidate matching alone.
------------------------------------------------------------------------

data ReferentWorld : Set where
  richardIsReferent otherTeamMemberIsReferent : ReferentWorld

data CandidatePredicateObservation : Set where
  matchingCandidatePredicates : CandidatePredicateObservation

data ReferentQuery : Set where
  identifyUnnamedTeamMember : ReferentQuery

data ReferentAnswer : Set where
  richardAnswer otherMemberAnswer : ReferentAnswer

projectCandidatePredicates : ReferentWorld → CandidatePredicateObservation
projectCandidatePredicates _ = matchingCandidatePredicates

answerReferent : ReferentQuery → ReferentWorld → ReferentAnswer
answerReferent identifyUnnamedTeamMember richardIsReferent = richardAnswer
answerReferent identifyUnnamedTeamMember otherTeamMemberIsReferent = otherMemberAnswer

referentSemantics : Query.QuerySemantics ReferentWorld ReferentQuery ReferentAnswer
referentSemantics = Query.querySemantics answerReferent

referentIdentityQueryDefect :
  Query.QueryAdequacyDefect
    projectCandidatePredicates
    referentSemantics
    identifyUnnamedTeamMember
referentIdentityQueryDefect =
  Query.queryAdequacyDefect
    richardIsReferent
    otherTeamMemberIsReferent
    refl
    (λ ())

predicateMatchCannotDetermineUnnamedReferent :
  Query.AdequateFor
    projectCandidatePredicates
    referentSemantics
    identifyUnnamedTeamMember →
  ⊥
predicateMatchCannotDetermineUnnamedReferent =
  Query.queryAdequacyDefectBlocksFactorisation referentIdentityQueryDefect

predicateIntersectionIsCandidateNotIdentity : Bool
predicateIntersectionIsCandidateNotIdentity = true

unnamedReferenceRequiresIdentityBearingReceipt : Bool
unnamedReferenceRequiresIdentityBearingReceipt = true

round29H2PaidCount : Nat
round29H2PaidCount = 0

round29H3PaidCount : Nat
round29H3PaidCount = 0

round29Pareto : String
round29Pareto = "Richard Eskridge is now the strongest source-backed candidate for Amy's unnamed former-NASA team-member referent because HAL5 pays team membership and retired-NASA identity while NTRS pays R.H. Eskridge authorship/MSFC provenance. The remaining discriminator is literal identity-bearing evidence: Amy's original 2020 message/email, NASA review metadata, report title/number, SAA number, POAMS/V3 reference, or equivalent same-object key. Predicate fit alone cannot promote the referent or paper identity."