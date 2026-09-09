module DASHI.Law.SolomonIslandsDomesticLegalCoverageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.LegalAuthorityCitationExact as Legal
import DASHI.Law.SolomonIslandsDomesticAuthorityExact as Domestic

------------------------------------------------------------------------
-- SOLOMON ISLANDS DOMESTIC-LEGAL COVERAGE / DEFEATER SWEEP
--
-- This module extends the already-source-backed constitutional/parliamentary
-- lane with the more specific integrity / bribery authorities most capable of
-- changing the legal characterisation of the reported treaty/funding facts.
--
-- Attribution discipline is inherited from LegalAuthorityCitationExact:
-- exact authority, locator, bounded proposition, authority role, jurisdictional
-- fit and consumer use remain separate from element payment or adjudication.
------------------------------------------------------------------------

antiCorruptionPublicOfficialDefinition : Legal.LegalCitation
antiCorruptionPublicOfficialDefinition = Legal.legal-citation
  Legal.legislation
  Legal.bindingPrimaryAuthority
  "Solomon Islands"
  "Attorney-General's Chambers, Solomon Islands"
  "Anti-Corruption Act 2018"
  2018
  (Legal.statutoryCitation "Anti-Corruption Act 2018, s 4A(1)(b)")
  "section 4A(1)(b)"
  "a member of Parliament, including a Minister or the Prime Minister, is a public official for the purposes of the Act"
  false refl

antiCorruptionBriberyPublicOfficial : Legal.LegalCitation
antiCorruptionBriberyPublicOfficial = Legal.legal-citation
  Legal.legislation
  Legal.bindingPrimaryAuthority
  "Solomon Islands"
  "Attorney-General's Chambers, Solomon Islands"
  "Anti-Corruption Act 2018"
  2018
  (Legal.statutoryCitation "Anti-Corruption Act 2018, s 92(1)-(2)")
  "section 92(1)-(2)"
  "a person commits an offence by directly or indirectly promising, offering or giving a benefit to a public official intending to influence the official's duties; a public official likewise commits an offence by soliciting, accepting or receiving a benefit intending that official duties be influenced"
  false refl

standingOrder78PersonalInterest : Legal.LegalCitation
standingOrder78PersonalInterest = Legal.legal-citation
  Legal.parliamentaryRecord
  Legal.bindingPrimaryAuthority
  "Solomon Islands"
  "National Parliament of Solomon Islands"
  "Standing Orders of the National Parliament of Solomon Islands"
  1982
  (Legal.parliamentaryCitation "Standing Order 78(1)-(5), as amended")
  "Standing Order 78(1)-(5)"
  "members must declare specified interests and must not move, speak or vote on a matter in which they have a direct personal pecuniary interest without disclosure; Parliament has a procedure for challenging such a vote"
  false refl

leadershipCodeFurtherProvisions : Legal.LegalCitation
leadershipCodeFurtherProvisions = Legal.legal-citation
  Legal.legislation
  Legal.bindingPrimaryAuthority
  "Solomon Islands"
  "Attorney-General's Chambers, Solomon Islands"
  "Leadership Code (Further Provisions) Act 1999"
  1999
  (Legal.statutoryCitation "Leadership Code (Further Provisions) Act 1999; current Attorney-General reprint")
  "Act-level implementation of Constitution Chapter VIII; sections 11-15 are relevant benefit/conflict provisions identified in official/legal-review materials"
  "the Act implements the constitutional Leadership Code and provides the statutory machinery for misconduct investigations and benefit/conflict rules concerning leaders; application to the present facts requires exact element-by-element review"
  false refl

leadershipCodeCommissionMandate : Legal.LegalCitation
leadershipCodeCommissionMandate = Legal.legal-citation
  Legal.officialGuidance
  Legal.officialInterpretiveMaterial
  "Solomon Islands"
  "Solomon Islands Government / Leadership Code Commission"
  "The Leadership Code Commission"
  2026
  (Legal.canonicalLegalURL "https://solomons.gov.sb/office-of-the-prime-minister-and-cabinet/the-leadership-code-commission/")
  "official mandate description"
  "the Leadership Code Commission is the integrity institution mandated to enforce the Leadership Code, including investigation, prosecution and adjudication of misconduct allegations by leaders"
  false refl

------------------------------------------------------------------------
-- Consumer-use receipts.
------------------------------------------------------------------------

antiCorruptionBriberyUse : Legal.LegalAuthorityUseReceipt antiCorruptionBriberyPublicOfficial
antiCorruptionBriberyUse = Legal.legal-authority-use-receipt
  "Solomon Islands foreign-interference / domestic bribery discriminator"
  "if a benefit was promised, offered, given, solicited, accepted or received with the statutorily required intent to influence official duties, s 92 supplies a more specific domestic offence theory than generic foreign-interference language"
  true refl true refl true refl false refl

standingOrder78Use : Legal.LegalAuthorityUseReceipt standingOrder78PersonalInterest
standingOrder78Use = Legal.legal-authority-use-receipt
  "Solomon Islands foreign-interference / parliamentary-interest discriminator"
  "Standing Order 78 is relevant only if a direct personal pecuniary interest of a member is shown; general constituency, policy or national funding is not automatically a personal pecuniary interest"
  true refl true refl true refl false refl

leadershipCodeUse : Legal.LegalAuthorityUseReceipt leadershipCodeFurtherProvisions
leadershipCodeUse = Legal.legal-authority-use-receipt
  "Solomon Islands foreign-interference / leader-integrity discriminator"
  "the statutory Leadership Code lane may be engaged by a leader-side benefit, conflict or misuse-of-office theory, but no such element is imported from the citation itself"
  true refl true refl true refl false refl

------------------------------------------------------------------------
-- Coverage cutset.
------------------------------------------------------------------------

data DomesticLegalCoordinate : Set where
  constitutionalNoConfidenceMechanism : DomesticLegalCoordinate
  constitutionalLeaderIntegrity : DomesticLegalCoordinate
  officialWithdrawalProcedure : DomesticLegalCoordinate
  statutoryPublicOfficialDefinition : DomesticLegalCoordinate
  statutoryBriberyBenefitIntent : DomesticLegalCoordinate
  parliamentaryPersonalPecuniaryInterest : DomesticLegalCoordinate
  leadershipCodeImplementation : DomesticLegalCoordinate
  domesticForeignInterferenceSpecificOffence : DomesticLegalCoordinate
  domesticCaseLawOnComparableForeignPoliticalFunding : DomesticLegalCoordinate

record DomesticLegalCoverage : Set where
  constructor domestic-legal-coverage
  field
    constitutionMapped : Bool
    constitutionMappedIsTrue : constitutionMapped ≡ true
    withdrawalProcedureMapped : Bool
    withdrawalProcedureMappedIsTrue : withdrawalProcedureMapped ≡ true
    antiCorruptionPublicOfficialMapped : Bool
    antiCorruptionPublicOfficialMappedIsTrue : antiCorruptionPublicOfficialMapped ≡ true
    antiCorruptionBriberyMapped : Bool
    antiCorruptionBriberyMappedIsTrue : antiCorruptionBriberyMapped ≡ true
    standingOrderPersonalInterestMapped : Bool
    standingOrderPersonalInterestMappedIsTrue : standingOrderPersonalInterestMapped ≡ true
    leadershipCodeImplementationMapped : Bool
    leadershipCodeImplementationMappedIsTrue : leadershipCodeImplementationMapped ≡ true
    specificDomesticForeignInterferenceOffenceFound : Bool
    specificDomesticForeignInterferenceOffenceFoundIsFalse :
      specificDomesticForeignInterferenceOffenceFound ≡ false
    comparableDomesticCaseLawFound : Bool
    comparableDomesticCaseLawFoundIsFalse : comparableDomesticCaseLawFound ≡ false
    nextLegalResidual : String

open DomesticLegalCoverage public

currentDomesticLegalCoverage : DomesticLegalCoverage
currentDomesticLegalCoverage = domestic-legal-coverage
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  false refl
  false refl
  "The high-value domestic authority families are mapped. Remaining legal work is not generic authority discovery: test the actual facts against Anti-Corruption Act s 92 and the Leadership Code, and continue a bounded defeater search for any directly comparable Solomon Islands case or specific foreign-political-influence offence."

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data GovernmentOrConstituencyFundingIsPersonalBenefit : Set where
data PolicyFundingAutomaticallyIsBribe : Set where
data PoliticalAdvantageEqualsOfficialDutyInfluence : Set where
data StandingOrder78AppliesWithoutPersonalPecuniaryInterest : Set where
data LeadershipCodeCitationProvesMisconduct : Set where

generalFundingDoesNotBecomePersonalBenefit : GovernmentOrConstituencyFundingIsPersonalBenefit → ⊥
generalFundingDoesNotBecomePersonalBenefit ()

policyFundingDoesNotAutoBecomeBribe : PolicyFundingAutomaticallyIsBribe → ⊥
policyFundingDoesNotAutoBecomeBribe ()

politicalAdvantageDoesNotAutoPayStatutoryIntent : PoliticalAdvantageEqualsOfficialDutyInfluence → ⊥
politicalAdvantageDoesNotAutoPayStatutoryIntent ()

standingOrderNeedsPersonalPecuniaryInterest : StandingOrder78AppliesWithoutPersonalPecuniaryInterest → ⊥
standingOrderNeedsPersonalPecuniaryInterest ()

leadershipCitationDoesNotAdjudicate : LeadershipCodeCitationProvesMisconduct → ⊥
leadershipCitationDoesNotAdjudicate ()
