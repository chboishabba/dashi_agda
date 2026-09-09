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
-- coordinates.  The current evidence supports an Australian High Commission
-- treaty/funding communication to Sade and a separately reported Sade ->
-- coalition political exhortation.  It does not establish a direct Australian
-- instruction to defeat the motion.
------------------------------------------------------------------------

record SourceLegalForeignInterferenceFibre : Set where
  constructor source-legal-foreign-interference-fibre
  field
    abcAuthenticatedMessage : Base.EventAtom
    downstreamDefeatMotionAttribution : String
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
  "Opposition publishes defeat-motion language; AAP separately reports the downstream political message as Sade's own coalition-directed message following his forwarding of the Australian High Commission update"
  Domestic.constitutionSection34
  Domestic.constitutionSection94
  Domestic.parliamentWithdrawalRecord
  Base.viennaDiplomaticRelationsArticle41
  Base.nicaraguaNonInterventionPara205
  Base.unCharterSovereignEquality

------------------------------------------------------------------------
-- Minimum legal discriminator.
------------------------------------------------------------------------

record NonInterventionFitCoordinates : Set where
  constructor non-intervention-fit-coordinates
  field
    protectedDomesticChoiceIdentified : Bool
    protectedDomesticChoiceIdentifiedIsTrue : protectedDomesticChoiceIdentified ≡ true
    australianTreatyFundingCommunicationIdentified : Bool
    australianTreatyFundingCommunicationIdentifiedIsTrue :
      australianTreatyFundingCommunicationIdentified ≡ true
    downstreamDomesticPoliticalUseReported : Bool
    downstreamDomesticPoliticalUseReportedIsTrue :
      downstreamDomesticPoliticalUseReported ≡ true
    exactRequestByAustralianActorAuthenticated : Bool
    exactRequestByAustralianActorAuthenticatedIsFalse :
      exactRequestByAustralianActorAuthenticated ≡ false
    australianConditionalityEstablished : Bool
    australianConditionalityEstablishedIsFalse :
      australianConditionalityEstablished ≡ false
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
  true refl
  false refl
  false refl
  false refl
  false refl
  false refl

protectedDomesticChoiceBasis : String
protectedDomesticChoiceBasis =
  "Constitution s 34 identifies the no-confidence mechanism as a Solomon Islands parliamentary process decided by members of Parliament"

currentCommunicationBasis : String
currentCommunicationBasis =
  "ABC authenticates the High Commission treaty/funding communication to Sade; AAP reporting identifies Sade as forwarding that update and separately sending his own coalition-directed political message"

------------------------------------------------------------------------
-- No legal bootstrapping.
------------------------------------------------------------------------

data DomesticRelayImpliesAustralianInstruction : Set where
data BenefitCommunicationImpliesConditionality : Set where
data Article41TextPlusRelayImpliesBreach : Set where
data NicaraguaTestPlusTimingImpliesWrongfulIntervention : Set where

domesticRelayDoesNotBecomeAustralianInstruction :
  DomesticRelayImpliesAustralianInstruction → ⊥
domesticRelayDoesNotBecomeAustralianInstruction ()

benefitCommunicationDoesNotAutoEstablishConditionality :
  BenefitCommunicationImpliesConditionality → ⊥
benefitCommunicationDoesNotAutoEstablishConditionality ()

article41AndRelayDoNotAutoEstablishBreach :
  Article41TextPlusRelayImpliesBreach → ⊥
article41AndRelayDoNotAutoEstablishBreach ()

nicaraguaAndTimingDoNotAutoEstablishWrongfulIntervention :
  NicaraguaTestPlusTimingImpliesWrongfulIntervention → ⊥
nicaraguaAndTimingDoNotAutoEstablishWrongfulIntervention ()

------------------------------------------------------------------------
-- Current shortest residual after sender correction.
------------------------------------------------------------------------

record SourceLegalResidual : Set where
  constructor source-legal-residual
  field
    domesticConstitutionalProcessMapped : Bool
    domesticConstitutionalProcessMappedIsTrue :
      domesticConstitutionalProcessMapped ≡ true
    officialWithdrawalChronologyMapped : Bool
    officialWithdrawalChronologyMappedIsTrue :
      officialWithdrawalChronologyMapped ≡ true
    australianUpstreamMessageMapped : Bool
    australianUpstreamMessageMappedIsTrue : australianUpstreamMessageMapped ≡ true
    sadeDownstreamPoliticalMessageMappedByReport : Bool
    sadeDownstreamPoliticalMessageMappedByReportIsTrue :
      sadeDownstreamPoliticalMessageMappedByReport ≡ true
    exactThreadTopologyPrimaryAuthenticated : Bool
    exactThreadTopologyPrimaryAuthenticatedIsFalse :
      exactThreadTopologyPrimaryAuthenticated ≡ false
    australianConditionalityPaid : Bool
    australianConditionalityPaidIsFalse : australianConditionalityPaid ≡ false
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
  "original/authenticated WhatsApp chain with forwarding markers, sender/recipient/timestamps and adjacency; then test whether Australia conditioned funding/treaty benefits on government survival or requested political use against the no-confidence motion"
