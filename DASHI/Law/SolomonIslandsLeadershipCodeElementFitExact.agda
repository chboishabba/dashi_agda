module DASHI.Law.SolomonIslandsLeadershipCodeElementFitExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.LegalAuthorityCitationExact as Legal
import DASHI.Law.SolomonIslandsDomesticLegalCoverageExact as Coverage
import DASHI.Law.SolomonIslandsDefeatMotionProvenanceExact as Provenance

------------------------------------------------------------------------
-- LEADERSHIP-CODE ELEMENT FIT
--
-- Primary authority: Attorney-General authorised reprint of the Leadership
-- Code (Further Provisions) Act 1999, current as at 5 February 2024.
--
-- This module does not infer misconduct from political advantage or public
-- development funding.  It isolates the statutory elements that would have to
-- be paid by facts before those characterisations become available.
------------------------------------------------------------------------

leadershipCodeSection11PersonalBenefit : Legal.LegalCitation
leadershipCodeSection11PersonalBenefit = Legal.legal-citation
  Legal.legislation
  Legal.bindingPrimaryAuthority
  "Solomon Islands"
  "Attorney-General's Chambers, Solomon Islands"
  "Leadership Code (Further Provisions) Act 1999"
  1999
  (Legal.statutoryCitation "Leadership Code (Further Provisions) Act 1999, s 11(1)-(2); authorised reprint current 5 February 2024")
  "section 11(1)-(2)"
  "a Leader commits misconduct if the Leader directly or indirectly asks or accepts, for the Leader or an associate, a benefit in relation to official action or by reason of office; the section also reaches improper use of name or official position for the benefit of self or another person"
  false refl

leadershipCodeSection12FinancialInterest : Legal.LegalCitation
leadershipCodeSection12FinancialInterest = Legal.legal-citation
  Legal.legislation
  Legal.bindingPrimaryAuthority
  "Solomon Islands"
  "Attorney-General's Chambers, Solomon Islands"
  "Leadership Code (Further Provisions) Act 1999"
  1999
  (Legal.statutoryCitation "Leadership Code (Further Provisions) Act 1999, s 12(1)-(3); authorised reprint current 5 February 2024")
  "section 12(1)-(3)"
  "specified shareholdings, investments, positions or financial interests of a Leader, spouse or child amount to misconduct when they could reasonably create a conflict of interest or compromise discharge of official duties, subject to statutory approval/divestment provisions"
  false refl

leadershipCodeSection16ConflictDefinition : Legal.LegalCitation
leadershipCodeSection16ConflictDefinition = Legal.legal-citation
  Legal.legislation
  Legal.bindingPrimaryAuthority
  "Solomon Islands"
  "Attorney-General's Chambers, Solomon Islands"
  "Leadership Code (Further Provisions) Act 1999"
  1999
  (Legal.statutoryCitation "Leadership Code (Further Provisions) Act 1999, s 16; authorised reprint current 5 February 2024")
  "section 16"
  "conflict of interest is framed as a choice between a Leader's personal interests and obligations as Leader; the Commission considers decision influence, office reputation, possible financial gain or other benefit to the Leader, and development value to Solomon Islands"
  false refl

leadershipCodeSection17Bribery : Legal.LegalCitation
leadershipCodeSection17Bribery = Legal.legal-citation
  Legal.legislation
  Legal.bindingPrimaryAuthority
  "Solomon Islands"
  "Attorney-General's Chambers, Solomon Islands"
  "Leadership Code (Further Provisions) Act 1999"
  1999
  (Legal.statutoryCitation "Leadership Code (Further Provisions) Act 1999, s 17(1)-(3); authorised reprint current 5 February 2024")
  "section 17(1)-(3)"
  "a Leader commits misconduct by asking for, receiving, obtaining, agreeing or attempting to obtain property, benefit or favour in consideration of official action being influenced or because of past official action; a person commits an offence by offering, giving or attempting to give property, benefit or favour as consideration, inducement or reward for a Leader doing or forbearing an act in that capacity"
  false refl

leadershipCodeSection20OfficialInformation : Legal.LegalCitation
leadershipCodeSection20OfficialInformation = Legal.legal-citation
  Legal.legislation
  Legal.bindingPrimaryAuthority
  "Solomon Islands"
  "Attorney-General's Chambers, Solomon Islands"
  "Leadership Code (Further Provisions) Act 1999"
  1999
  (Legal.statutoryCitation "Leadership Code (Further Provisions) Act 1999, s 20(1)-(2); authorised reprint current 5 February 2024")
  "section 20(1)-(2)"
  "a Leader commits misconduct if information acquired in official duty is disclosed or used for the personal gain or advantage of the Leader or another person; officially released information is excluded"
  false refl

------------------------------------------------------------------------
-- Exact consumer-use receipts.
------------------------------------------------------------------------

section11Use : Legal.LegalAuthorityUseReceipt leadershipCodeSection11PersonalBenefit
section11Use = Legal.legal-authority-use-receipt
  "Solomon treaty/funding facts / leader personal-benefit discriminator"
  "requires a benefit for the Leader or associate, or improper use of official position for a person's benefit; public or constituency funding alone does not pay that element"
  true refl true refl true refl false refl

section17Use : Legal.LegalAuthorityUseReceipt leadershipCodeSection17Bribery
section17Use = Legal.legal-authority-use-receipt
  "Solomon treaty/funding facts / leader bribery discriminator"
  "requires the property/benefit/favour plus the consideration, inducement or reward nexus to a Leader's doing or forbearing official action"
  true refl true refl true refl false refl

section20Use : Legal.LegalAuthorityUseReceipt leadershipCodeSection20OfficialInformation
section20Use = Legal.legal-authority-use-receipt
  "Sade relay topology / official-information-use discriminator"
  "requires information acquired in official duty plus personal gain or advantage for the Leader or another person; forwarding or political use alone does not establish personal gain"
  true refl true refl true refl false refl

------------------------------------------------------------------------
-- Fact-shape separation.
------------------------------------------------------------------------

data BenefitShape : Set where
  nationalPolicyFunding : BenefitShape
  constituencyPublicFunding : BenefitShape
  personalBenefitToLeader : BenefitShape
  benefitToLeaderAssociate : BenefitShape
  propertyBenefitOrFavourAsInducement : BenefitShape
  unresolvedBenefitShape : BenefitShape

record CurrentLeadershipCodeFit : Set where
  constructor current-leadership-code-fit
  field
    leaderStatusRelevant : Bool
    leaderStatusRelevantIsTrue : leaderStatusRelevant ≡ true
    australianFundingCommunicationReported : Bool
    australianFundingCommunicationReportedIsTrue : australianFundingCommunicationReported ≡ true
    sadeDownstreamPoliticalUseReported : Bool
    sadeDownstreamPoliticalUseReportedIsTrue : sadeDownstreamPoliticalUseReported ≡ true
    personalBenefitToSadeEstablished : Bool
    personalBenefitToSadeEstablishedIsFalse : personalBenefitToSadeEstablished ≡ false
    associateBenefitEstablished : Bool
    associateBenefitEstablishedIsFalse : associateBenefitEstablished ≡ false
    financialInterestConflictEstablished : Bool
    financialInterestConflictEstablishedIsFalse : financialInterestConflictEstablished ≡ false
    considerationInducementRewardNexusEstablished : Bool
    considerationInducementRewardNexusEstablishedIsFalse :
      considerationInducementRewardNexusEstablished ≡ false
    personalGainFromOfficialInformationEstablished : Bool
    personalGainFromOfficialInformationEstablishedIsFalse :
      personalGainFromOfficialInformationEstablished ≡ false
    nextElementDemand : String

open CurrentLeadershipCodeFit public

currentLeadershipCodeFit : CurrentLeadershipCodeFit
currentLeadershipCodeFit = current-leadership-code-fit
  true refl
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl
  false refl
  "Acquire facts showing whether any treaty/funding benefit was for Sade or an associate personally, or was offered/accepted as consideration, inducement or reward for official action; separately test whether any non-public official information was used for personal gain"

------------------------------------------------------------------------
-- Cross-statute discriminator.
------------------------------------------------------------------------

record BenefitInfluenceCrossStatuteCutset : Set where
  constructor benefit-influence-cross-statute-cutset
  field
    antiCorruptionSection92Mapped : Bool
    antiCorruptionSection92MappedIsTrue : antiCorruptionSection92Mapped ≡ true
    leadershipSection11Mapped : Bool
    leadershipSection11MappedIsTrue : leadershipSection11Mapped ≡ true
    leadershipSection17Mapped : Bool
    leadershipSection17MappedIsTrue : leadershipSection17Mapped ≡ true
    leadershipSection20Mapped : Bool
    leadershipSection20MappedIsTrue : leadershipSection20Mapped ≡ true
    factualBenefitRecipientPaid : Bool
    factualBenefitRecipientPaidIsFalse : factualBenefitRecipientPaid ≡ false
    factualInfluenceNexusPaid : Bool
    factualInfluenceNexusPaidIsFalse : factualInfluenceNexusPaid ≡ false

open BenefitInfluenceCrossStatuteCutset public

currentBenefitInfluenceCutset : BenefitInfluenceCrossStatuteCutset
currentBenefitInfluenceCutset = benefit-influence-cross-statute-cutset
  true refl
  true refl
  true refl
  true refl
  false refl
  false refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data ConstituencyFundingIsLeaderPersonalBenefit : Set where
data CoalitionPoliticalAdvantageIsPersonalGain : Set where
data TemporalAdjacencyIsInducement : Set where
data ForwardedOfficialInformationIsPersonalGainUse : Set where
data Section17AndSection92AreSameElementSet : Set where

constituencyFundingDoesNotAutoBecomePersonalBenefit :
  ConstituencyFundingIsLeaderPersonalBenefit → ⊥
constituencyFundingDoesNotAutoBecomePersonalBenefit ()

politicalAdvantageDoesNotAutoBecomePersonalGain :
  CoalitionPoliticalAdvantageIsPersonalGain → ⊥
politicalAdvantageDoesNotAutoBecomePersonalGain ()

timingDoesNotAutoBecomeInducement : TemporalAdjacencyIsInducement → ⊥
timingDoesNotAutoBecomeInducement ()

forwardingDoesNotAutoPayPersonalGain : ForwardedOfficialInformationIsPersonalGainUse → ⊥
forwardingDoesNotAutoPayPersonalGain ()

leadershipAndAntiCorruptionElementsDoNotCollapse :
  Section17AndSection92AreSameElementSet → ⊥
leadershipAndAntiCorruptionElementsDoNotCollapse ()
