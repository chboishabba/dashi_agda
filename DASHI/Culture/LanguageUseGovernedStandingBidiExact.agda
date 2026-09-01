module DASHI.Culture.LanguageUseGovernedStandingBidiExact where

------------------------------------------------------------------------
-- LANGUAGE USE x GOVERNED STANDING BIDI
--
-- Source discipline:
--   later-Wittgenstein use/practice material is one source-bounded comparison
--   surface; Indigenous situated-authority/permission/obligation machinery is
--   another.  The product formalism and finite collision theorems are DASHI
--   constructions and are attributed to neither source tradition.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.GovernedObservationProvenanceExact as Governed
import DASHI.Culture.WittgensteinUsePracticeSourceBridgeExact as Wittgenstein
import DASHI.Culture.WitchRelationalAttributionDialogueBidiExact as Dialogue
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as Indigenous
import DASHI.Culture.PhilosophyClaimProvenanceHistoryBidiExact as Philosophy

------------------------------------------------------------------------
-- 1. A situated linguistic act keeps use and governance coordinates distinct.
------------------------------------------------------------------------

data UseClass : Set where
  devotionalUse explanatoryUse classificatoryUse quotedUse reclaimedUse : UseClass

data SpeakerStanding : Set where
  selfStanding participantStanding custodialStanding historianStanding
  institutionalStanding externalObserverStanding unresolvedStanding : SpeakerStanding

data DisclosurePermission : Set where
  publicDisclosure restrictedDisclosure noDisclosureReceipt unresolvedDisclosure
  : DisclosurePermission

data InterpretiveObligation : Set where
  ordinaryAttribution preserveContestability preserveSourceContext
  reciprocalObligation unresolvedObligation : InterpretiveObligation

record GovernedLanguageAct : Set where
  constructor governed-language-act
  field
    words : String
    useClass : UseClass
    standing : SpeakerStanding
    permission : DisclosurePermission
    obligation : InterpretiveObligation
    provenance : String

open GovernedLanguageAct public

------------------------------------------------------------------------
-- 2. Same words/use can coexist with different governed standing.
------------------------------------------------------------------------

data GovernedUseState : Set where
  authorisedParticipantUse externalObserverUse : GovernedUseState

data SameWordsAndUseSurface : Set where sameWordsSameUse : SameWordsAndUseSurface

data StandingCode : Set where participantCode observerCode : StandingCode

data PermissionCode : Set where restrictedCode publicCode : PermissionCode

data ObligationCode : Set where reciprocalCode ordinaryCode : ObligationCode

wordsAndUse : GovernedUseState → SameWordsAndUseSurface
wordsAndUse _ = sameWordsSameUse

standingCode : GovernedUseState → StandingCode
standingCode authorisedParticipantUse = participantCode
standingCode externalObserverUse = observerCode

permissionCode : GovernedUseState → PermissionCode
permissionCode authorisedParticipantUse = restrictedCode
permissionCode externalObserverUse = publicCode

obligationCode : GovernedUseState → ObligationCode
obligationCode authorisedParticipantUse = reciprocalCode
obligationCode externalObserverUse = ordinaryCode

standingDiffers : standingCode authorisedParticipantUse ≡ standingCode externalObserverUse → ⊥
standingDiffers ()

permissionDiffers : permissionCode authorisedParticipantUse ≡ permissionCode externalObserverUse → ⊥
permissionDiffers ()

obligationDiffers : obligationCode authorisedParticipantUse ≡ obligationCode externalObserverUse → ⊥
obligationDiffers ()

sameWordsAndUseCannotRecoverStanding : INF.FactorsThrough wordsAndUse standingCode → ⊥
sameWordsAndUseCannotRecoverStanding =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness authorisedParticipantUse externalObserverUse refl standingDiffers)

sameWordsAndUseCannotRecoverPermission : INF.FactorsThrough wordsAndUse permissionCode → ⊥
sameWordsAndUseCannotRecoverPermission =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness authorisedParticipantUse externalObserverUse refl permissionDiffers)

sameWordsAndUseCannotRecoverObligation : INF.FactorsThrough wordsAndUse obligationCode → ⊥
sameWordsAndUseCannotRecoverObligation =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness authorisedParticipantUse externalObserverUse refl obligationDiffers)

------------------------------------------------------------------------
-- 3. Direct reuse of the merged Indigenous situated-proposition theorems.
------------------------------------------------------------------------

indigenousPropositionStillCannotRecoverAuthority :
  INF.FactorsThrough Indigenous.extractedProposition Indigenous.authority → ⊥
indigenousPropositionStillCannotRecoverAuthority = Indigenous.propositionCannotRecoverAuthority

indigenousPropositionStillCannotRecoverPermission :
  INF.FactorsThrough Indigenous.extractedProposition Indigenous.permission → ⊥
indigenousPropositionStillCannotRecoverPermission = Indigenous.propositionCannotRecoverPermission

indigenousPropositionStillCannotRecoverObligation :
  INF.FactorsThrough Indigenous.extractedProposition Indigenous.obligation → ⊥
indigenousPropositionStillCannotRecoverObligation = Indigenous.propositionCannotRecoverObligation

------------------------------------------------------------------------
-- 4. Governed-observer consequence uses the canonical collision carrier.
------------------------------------------------------------------------

standingCollision : Consumer.ConsumerRelevantCollision wordsAndUse standingCode
standingCollision =
  Consumer.consumer-relevant-collision
    authorisedParticipantUse externalObserverUse refl standingDiffers

standingCollisionBlocksGovernedSufficiency :
  ∀ {Value Provenance Epistemic Permission Obligation : Set}
    {value : GovernedUseState → Value}
    {provenance : GovernedUseState → Provenance}
    {epistemic : GovernedUseState → Epistemic}
    {permission : GovernedUseState → Permission}
    {obligation : GovernedUseState → Obligation} →
  Governed.GovernedConsumerSufficiency
    wordsAndUse value provenance epistemic standingCode permission obligation → ⊥
standingCollisionBlocksGovernedSufficiency =
  Governed.authorityCollisionBlocksGovernedSufficiency standingCollision

------------------------------------------------------------------------
-- 5. Relational attribution remains independently typed.
------------------------------------------------------------------------

relationalPredicateStillCannotRecoverMode :
  INF.FactorsThrough Dialogue.predicateSurface Dialogue.modeCode → ⊥
relationalPredicateStillCannotRecoverMode = Dialogue.samePredicateCannotRecoverRelationalMode

------------------------------------------------------------------------
-- 6. No-promotion gates.
------------------------------------------------------------------------

data UsePromotesStanding : Set where
data UsePromotesPermission : Set where
data UsePromotesObligation : Set where
data SelfIdentificationPromotesCommunityAuthority : Set where
data PublicStoryPromotesRestrictedInterpretation : Set where
data WittgensteinPromotesIndigenousGovernance : Set where
data IndigenousKnowledgePromotesWittgensteinTheory : Set where

useDoesNotPromoteStanding : UsePromotesStanding → ⊥
useDoesNotPromoteStanding ()
useDoesNotPromotePermission : UsePromotesPermission → ⊥
useDoesNotPromotePermission ()
useDoesNotPromoteObligation : UsePromotesObligation → ⊥
useDoesNotPromoteObligation ()
selfIdentificationDoesNotPromoteCommunityAuthority : SelfIdentificationPromotesCommunityAuthority → ⊥
selfIdentificationDoesNotPromoteCommunityAuthority ()
publicStoryDoesNotPromoteRestrictedInterpretation : PublicStoryPromotesRestrictedInterpretation → ⊥
publicStoryDoesNotPromoteRestrictedInterpretation ()
wittgensteinDoesNotPromoteIndigenousGovernance : WittgensteinPromotesIndigenousGovernance → ⊥
wittgensteinDoesNotPromoteIndigenousGovernance ()
indigenousKnowledgeDoesNotPromoteWittgensteinTheory : IndigenousKnowledgePromotesWittgensteinTheory → ⊥
indigenousKnowledgeDoesNotPromoteWittgensteinTheory ()

------------------------------------------------------------------------
-- 7. Canonical weld and boundary.
------------------------------------------------------------------------

record LanguageUseGovernedStandingWeld : Set where
  constructor language-use-governed-standing-weld
  field
    wittgensteinBoundary : Wittgenstein.WittgensteinUsePracticeBoundary
    philosophyBoundary : Philosophy.PhilosophyClaimProvenanceHistoryBoundary
    governedBoundary : Governed.GovernedObservationProvenanceBoundary
    sameUseStandingNonfactorability : INF.FactorsThrough wordsAndUse standingCode → ⊥
    sameUsePermissionNonfactorability : INF.FactorsThrough wordsAndUse permissionCode → ⊥
    sameUseObligationNonfactorability : INF.FactorsThrough wordsAndUse obligationCode → ⊥
    sourceTraditionsRemainDistinct : Bool
    finiteTheoremsRemainDASHIConstructions : Bool

canonicalLanguageUseGovernedStandingWeld : LanguageUseGovernedStandingWeld
canonicalLanguageUseGovernedStandingWeld =
  language-use-governed-standing-weld
    Wittgenstein.canonicalWittgensteinUsePracticeBoundary
    Philosophy.canonicalPhilosophyClaimProvenanceHistoryBoundary
    Governed.canonicalGovernedObservationProvenanceBoundary
    sameWordsAndUseCannotRecoverStanding
    sameWordsAndUseCannotRecoverPermission
    sameWordsAndUseCannotRecoverObligation
    true true

record LanguageUseGovernedStandingBoundary : Set where
  constructor language-use-governed-standing-boundary
  field
    sameWordsAndUseDetermineStanding : Bool
    sameWordsAndUseDeterminePermission : Bool
    sameWordsAndUseDetermineObligation : Bool
    lexicalSelfDescriptionDeterminesCommunityAuthority : Bool
    hearingPublicStoryGrantsRestrictedInterpretation : Bool
    WittgensteinUseEqualsIndigenousGovernance : Bool
    IndigenousSituatedKnowledgeEqualsWittgensteinTheory : Bool
    governedStandingNeedsIndependentCoordinates : Bool
    sourceAttributionSurvivesSynthesis : Bool

canonicalLanguageUseGovernedStandingBoundary : LanguageUseGovernedStandingBoundary
canonicalLanguageUseGovernedStandingBoundary =
  language-use-governed-standing-boundary false false false false false false false true true
