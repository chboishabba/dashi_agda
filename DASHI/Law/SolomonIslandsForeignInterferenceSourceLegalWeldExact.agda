module DASHI.Law.SolomonIslandsForeignInterferenceSourceLegalWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SolomonIslandsForeignInterferenceAttributionExact as Base
import DASHI.Law.SolomonIslandsDomesticAuthorityExact as Domestic
import DASHI.Law.SolomonIslandsDefeatMotionProvenanceExact as Defeat
import DASHI.Law.LegalAuthorityCitationExact as Legal

------------------------------------------------------------------------
-- SOURCE / LEGAL WELD
--
-- The evidence lane and authority lane meet only through explicit consumer
-- coordinates.  A source-supported fact does not become a legal conclusion;
-- a legal proposition does not manufacture the missing facts needed to fit it.
------------------------------------------------------------------------

record SourceLegalForeignInterferenceFibre : Set where
  constructor source-legal-foreign-interference-fibre
  field
    abcAuthenticatedMessage : Base.EventAtom
    oppositionDefeatMotionAttribution : String
    constitutionalNoConfidenceAuthority : Legal.LegalCitation
    leadershipIntegrityAuthority : Legal.LegalCitation
    officialWithdrawalAuthority : Legal.LegalCitation
    diplomaticNonInterferenceAuthority : Legal.LegalCitation
    customaryNonInterventionAuthority : Legal.LegalCitation
    sovereignEqualityAuthority : Legal.LegalCitation

open SourceLegalForeignInterferenceFibre public

currentSourceLegalFibre : SourceLegalForeignInterferenceFibre
currentSourceLegalFibre = source-legal-foreign-interference-fibre
  Base.australianDiplomaticCommunicationExists
  "Opposition publicly attributes 'stand together to defeat this Motion' language to a subsequent message; sender/authentication remain unresolved"
  Domestic.constitutionSection34
  Domestic.constitutionSection94
  Domestic.parliamentWithdrawalRecord
  Base.viennaDiplomaticRelationsArticle41
  Base.nicaraguaNonInterventionPara205
  Base.unCharterSovereignEquality

------------------------------------------------------------------------
-- Minimum legal discriminator.
--
-- This is deliberately a question surface, not a verdict.  It reflects the
-- existing Mabo discipline: identify the exact legal proposition and prove the
-- factual hinge before promotion.
------------------------------------------------------------------------

record NonInterventionFitCoordinates : Set where
  constructor non-intervention-fit-coordinates
  field
    protectedDomesticChoiceIdentified : Bool
    protectedDomesticChoiceIdentifiedIsTrue : protectedDomesticChoiceIdentified ≡ true
    allegedForeignConductIdentified : Bool
    allegedForeignConductIdentifiedIsTrue : allegedForeignConductIdentified ≡ true
    exactRequestByForeignActorAuthenticated : Bool
    exactRequestByForeignActorAuthenticatedIsFalse :
      exactRequestByForeignActorAuthenticated ≡ false
    coerciveCharacterEstablished : Bool
    coerciveCharacterEstablishedIsFalse : coerciveCharacterEstablished ≡ false
    diplomaticArticle41FitEstablished : Bool
    diplomaticArticle41FitEstablishedIsFalse :
      diplomaticArticle41FitEstablished ≡ false
    finalWrongfulnessEstablished : Bool
    finalWrongfulnessEstablishedIsFalse : finalWrongfulnessEstablished ≡ false

open NonInterventionFitCoordinates public

currentNonInterventionFit : NonInterventionFitCoordinates
currentNonInterventionFit = non-intervention-fit-coordinates
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl

------------------------------------------------------------------------
-- Why the first two coordinates are now paid.
------------------------------------------------------------------------

protectedDomesticChoiceBasis : String
protectedDomesticChoiceBasis =
  "Constitution s 34 identifies the no-confidence mechanism as a Solomon Islands parliamentary process decided by members of Parliament"

allegedForeignConductBasis : String
allegedForeignConductBasis =
  "ABC authenticated a diplomatic communication concerning treaty/funding progress and holding steady; Opposition separately attributes defeat-motion language to a subsequent message"

------------------------------------------------------------------------
-- No legal bootstrapping.
------------------------------------------------------------------------

data ConstitutionalProcessPlusForeignContactImpliesCoercion : Set where
data Article41TextPlusAllegationImpliesBreach : Set where
data NicaraguaTestPlusTimingImpliesWrongfulIntervention : Set where

constitutionAndContactDoNotAutoEstablishCoercion :
  ConstitutionalProcessPlusForeignContactImpliesCoercion → ⊥
constitutionAndContactDoNotAutoEstablishCoercion ()

article41AndAllegationDoNotAutoEstablishBreach :
  Article41TextPlusAllegationImpliesBreach → ⊥
article41AndAllegationDoNotAutoEstablishBreach ()

nicaraguaAndTimingDoNotAutoEstablishWrongfulIntervention :
  NicaraguaTestPlusTimingImpliesWrongfulIntervention → ⊥
nicaraguaAndTimingDoNotAutoEstablishWrongfulIntervention ()

------------------------------------------------------------------------
-- Current shortest residual.
------------------------------------------------------------------------

record SourceLegalResidual : Set where
  constructor source-legal-residual
  field
    domesticConstitutionalProcessMapped : Bool
    domesticConstitutionalProcessMappedIsTrue :
      domesticConstitutionalProcessMapped ≡ true
    domesticLeadershipIntegrityMapped : Bool
    domesticLeadershipIntegrityMappedIsTrue :
      domesticLeadershipIntegrityMapped ≡ true
    officialWithdrawalChronologyMapped : Bool
    officialWithdrawalChronologyMappedIsTrue :
      officialWithdrawalChronologyMapped ≡ true
    oppositionDefeatMotionSentenceMapped : Bool
    oppositionDefeatMotionSentenceMappedIsTrue :
      oppositionDefeatMotionSentenceMapped ≡ true
    originalDefeatMotionArtifactAuthenticated : Bool
    originalDefeatMotionArtifactAuthenticatedIsFalse :
      originalDefeatMotionArtifactAuthenticated ≡ false
    australianSenderOfDefeatMotionSentenceEstablished : Bool
    australianSenderOfDefeatMotionSentenceEstablishedIsFalse :
      australianSenderOfDefeatMotionSentenceEstablished ≡ false
    coercionHingePaid : Bool
    coercionHingePaidIsFalse : coercionHingePaid ≡ false
    nextExactProducer : String

open SourceLegalResidual public

currentSourceLegalResidual : SourceLegalResidual
currentSourceLegalResidual = source-legal-residual
  true refl
  true refl
  true refl
  true refl
  false refl
  false refl
  false refl
  "original/authenticated defeat-motion message chain with sender/recipient/timestamp provenance; only after that, analyse conditionality or coercion against VCDR Article 41 and Nicaragua paragraph 205"
