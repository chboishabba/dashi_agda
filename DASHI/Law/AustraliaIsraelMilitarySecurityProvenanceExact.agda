module DASHI.Law.AustraliaIsraelMilitarySecurityProvenanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Australia-Israel military/security provenance.  This file records bounded
-- source propositions and preserves contradictory/qualifying state actions.
------------------------------------------------------------------------

data LinkSourceRole : Set where
  australianGovernmentStatement
  parliamentaryEvidence
  royalCommissionEvidence
  mediaReport
  civilSocietyAllegation
  pendingLitigationAllegation
  dashiInterpretiveBridge : LinkSourceRole

data LinkKind : Set where
  f35GlobalSupplyChain
  militaryExportPermit
  israeliDefenceIndustryContract
  privateCommunitySecurityCoordination
  armedPrivateSecurityAtFixedSites
  proposedArmingAtPublicEvents
  israelTrainingAllegation
  recognitionOfPalestine
  settlerSanctions
  directNSWPoliceIsraelOperationalTransfer : LinkKind

record AustraliaIsraelLinkReceipt : Set where
  constructor australiaIsraelLinkReceipt
  field
    kind : LinkKind
    role : LinkSourceRole
    sourceReference : String
    boundedDescription : String
    directCausalSupport : Bool

open AustraliaIsraelLinkReceipt public

f35SupplyChainReceipt : AustraliaIsraelLinkReceipt
f35SupplyChainReceipt = australiaIsraelLinkReceipt
  f35GlobalSupplyChain parliamentaryEvidence
  "ABC reporting of Senate Estimates evidence, 9 October 2025; Defence evidence on F-35 global supply chain"
  "Australia participates in the US-led F-35 global supply chain accessed by Israel; Defence described movement/allocation as centrally managed by Lockheed Martin/US mechanisms"
  false

activePermitReceipt : AustraliaIsraelLinkReceipt
activePermitReceipt = australiaIsraelLinkReceipt
  militaryExportPermit parliamentaryEvidence
  "ABC, 14 August and 9 October 2025, reporting Defence evidence"
  "Defence acknowledged active military export permits relating to Israel while the government maintained it was not directly supplying weapons or ammunition"
  false

elbitIndustryReceipt : AustraliaIsraelLinkReceipt
elbitIndustryReceipt = australiaIsraelLinkReceipt
  israeliDefenceIndustryContract australianGovernmentStatement
  "Defence Minister press conference 1 March 2024; Defence FOI 867/23/24"
  "Israeli firm Elbit Systems participates in Australian defence procurement as subcontractor/supplier in major Army programs"
  false

csgCoordinationReceipt : AustraliaIsraelLinkReceipt
csgCoordinationReceipt = australiaIsraelLinkReceipt
  privateCommunitySecurityCoordination royalCommissionEvidence
  "Royal Commission on Antisemitism and Social Cohesion hearing blocks 2 and 5, 2026"
  "CSG NSW coordinates with NSW Police and other security agencies regarding protection of Jewish institutions/events"
  false

armedFixedSiteSecurityReceipt : AustraliaIsraelLinkReceipt
armedFixedSiteSecurityReceipt = australiaIsraelLinkReceipt
  armedPrivateSecurityAtFixedSites royalCommissionEvidence
  "ABC reporting of Royal Commission evidence, 27 July 2026"
  "CSG/security personnel can carry weapons when providing licensed security at some schools and synagogues; this does not establish a general armed-patrol power in public space"
  false

publicArmingProposalReceipt : AustraliaIsraelLinkReceipt
publicArmingProposalReceipt = australiaIsraelLinkReceipt
  proposedArmingAtPublicEvents royalCommissionEvidence
  "Royal Commission/ABC evidence, June-July 2026"
  "Arming private Jewish security at open-air/public events was proposed and considered; NSW Police Deputy Commissioner David Hudson expressed reservations"
  false

israelTrainingAllegationReceipt : AustraliaIsraelLinkReceipt
israelTrainingAllegationReceipt = australiaIsraelLinkReceipt
  israelTrainingAllegation civilSocietyAllegation
  "NSW Legislative Council Notice Paper No 156, 23 June 2026, recording allegations attributed to a former CSG volunteer"
  "A parliamentary motion recorded an allegation that CSG training can involve tactical/self-defence/firearms training in Israel; this is not encoded as an adjudicated fact"
  false

palestineRecognitionReceipt : AustraliaIsraelLinkReceipt
palestineRecognitionReceipt = australiaIsraelLinkReceipt
  recognitionOfPalestine australianGovernmentStatement
  "Australian PM/Foreign Minister joint statement, 21 September 2025"
  "Australia formally recognised the independent and sovereign State of Palestine"
  false

settlerSanctionsReceipt : AustraliaIsraelLinkReceipt
settlerSanctionsReceipt = australiaIsraelLinkReceipt
  settlerSanctions australianGovernmentStatement
  "Australian Foreign Minister joint statement, 9 June 2026"
  "Australia joined sanctions/measures against extremist violent settlers and criticised settlement expansion"
  false

------------------------------------------------------------------------
-- Policy relation is multi-coordinate.  Military-industrial integration does
-- not permit the analyst to erase recognition/sanctions, and those latter acts
-- do not erase supply-chain or defence-industry links.
------------------------------------------------------------------------

record BilateralPolicyFibre : Set where
  constructor bilateralPolicyFibre
  field
    militaryIndustrialLinkObserved : Bool
    militaryIndustrialLinkObservedIsTrue : militaryIndustrialLinkObserved ≡ true
    palestineRecognitionObserved : Bool
    palestineRecognitionObservedIsTrue : palestineRecognitionObserved ≡ true
    settlerSanctionsObserved : Bool
    settlerSanctionsObservedIsTrue : settlerSanctionsObserved ≡ true
    directPoliceOperationalTransferProven : Bool
    directPoliceOperationalTransferProvenIsFalse : directPoliceOperationalTransferProven ≡ false
    policyReference : String

open BilateralPolicyFibre public

canonicalBilateralPolicyFibre : BilateralPolicyFibre
canonicalBilateralPolicyFibre = bilateralPolicyFibre
  true refl true refl true refl false refl
  "mixed policy surface: military/security links coexist with recognition of Palestine and sanctions on violent settlers"

------------------------------------------------------------------------
-- BIDI claims.
------------------------------------------------------------------------

data AustraliaIsraelClaim : Set where
  australiaMilitaryIndustriallyLinkedToIsrael
  australiaDirectlySuppliesEveryIsraeliMilitaryOperation
  israelSecurityPracticeTransferredToNSWPolice
  privateSecurityArmedAtSomeFixedSites
  privateSecurityGenerallyAuthorisedForArmedPublicPatrols
  australiaPolicyUniformlySupportsIsraeliGovernment : AustraliaIsraelClaim

data AustraliaIsraelProducer : Set where
  militarySupplyChainProducer
  operationSpecificTransferProducer
  policeTrainingOperationalTransferProducer
  licensedFixedSiteSecurityProducer
  publicArmingLegalAuthorityProducer
  completeBilateralPolicyProducer : AustraliaIsraelProducer

reverseAustraliaIsrael : AustraliaIsraelClaim → AustraliaIsraelProducer
reverseAustraliaIsrael australiaMilitaryIndustriallyLinkedToIsrael = militarySupplyChainProducer
reverseAustraliaIsrael australiaDirectlySuppliesEveryIsraeliMilitaryOperation = operationSpecificTransferProducer
reverseAustraliaIsrael israelSecurityPracticeTransferredToNSWPolice = policeTrainingOperationalTransferProducer
reverseAustraliaIsrael privateSecurityArmedAtSomeFixedSites = licensedFixedSiteSecurityProducer
reverseAustraliaIsrael privateSecurityGenerallyAuthorisedForArmedPublicPatrols = publicArmingLegalAuthorityProducer
reverseAustraliaIsrael australiaPolicyUniformlySupportsIsraeliGovernment = completeBilateralPolicyProducer

record AustraliaIsraelBoundary : Set where
  constructor australiaIsraelBoundary
  field
    f35SupplyChainEqualsDirectGovernmentWeaponsTransfer : Bool
    f35SupplyChainEqualsDirectGovernmentWeaponsTransferIsFalse : f35SupplyChainEqualsDirectGovernmentWeaponsTransfer ≡ false
    csgPoliceCoordinationProvesIsraeliOperationalTransfer : Bool
    csgPoliceCoordinationProvesIsraeliOperationalTransferIsFalse : csgPoliceCoordinationProvesIsraeliOperationalTransfer ≡ false
    fixedSiteArmedSecurityEqualsGeneralArmedPatrolAuthority : Bool
    fixedSiteArmedSecurityEqualsGeneralArmedPatrolAuthorityIsFalse : fixedSiteArmedSecurityEqualsGeneralArmedPatrolAuthority ≡ false
    militaryIndustrialLinkImpliesUniformForeignPolicySupport : Bool
    militaryIndustrialLinkImpliesUniformForeignPolicySupportIsFalse : militaryIndustrialLinkImpliesUniformForeignPolicySupport ≡ false

canonicalAustraliaIsraelBoundary : AustraliaIsraelBoundary
canonicalAustraliaIsraelBoundary =
  australiaIsraelBoundary false refl false refl false refl false refl
