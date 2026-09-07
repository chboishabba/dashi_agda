module DASHI.Law.ColonialJurisdictionalTotalisationAuthorityCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawLegalJurisdictionEvidenceExact as Jurisdiction
import DASHI.Cognition.PNF.SensibLawLegalSourceAuthorityEvidenceExact as Authority
import DASHI.Cognition.PNF.SensibLawApplicabilityPrerequisiteMeetExact as Meet
import DASHI.Law.AustralianColonialWrongTypeAuthorityReclassificationExact as ColonialWrong
import DASHI.Law.AustralianColonialPrimarySourceAttributionExact as Primary
import DASHI.Law.ColonialSemanticPrerequisiteWrongTypeCrossPollinationExact as Prereq
import DASHI.Law.MaboCountrySecurityClassificationCrossPollinationExact as MaboCross

------------------------------------------------------------------------
-- Jurisdictional totalisation / authority-frame audit.
--
-- SensibLaw jurisdiction and source-authority receipts are explicitly
-- intra-system receipts: they certify a legal system/status/jurisdiction/source
-- relation in one state.  They do not by themselves prove that another
-- normative order ceased, consented, ceded sovereignty, or became ontologically
-- subordinate.  Cross-system exhaustion therefore requires a separate bridge.
------------------------------------------------------------------------

data NormativeOrderPosition : Set where
  governingOrder
  coexistingOrder
  subordinatedOrder
  nonGoverningOrder
  erasedFromDominantObserver : NormativeOrderPosition

data JurisdictionalReach : Set where
  localReach
  limitedReach
  coexistingReach
  assertedTotalReach : JurisdictionalReach

data AuthorityFrame : Set where
  intraSystemLegalAuthority
  crossSystemNormativePriority
  historicalLegitimacy
  politicalConstitutionalClaim : AuthorityFrame

record FramedAuthorityClaim : Set where
  constructor framedAuthorityClaim
  field
    frame : AuthorityFrame
    propositionReference : String
    sourceReference : String
    sourceRole : Primary.PrimarySourceRole

open FramedAuthorityClaim public

cooperIntraSystemClaim : FramedAuthorityClaim
cooperIntraSystemClaim = framedAuthorityClaim
  intraSystemLegalAuthority
  "settled-colony classification supplies the reception-of-English-law premise inside the imperial/common-law frame"
  "Cooper v Stuart [1889] UKPC 16, paras 11-13"
  Primary.privyCouncilHolding

uluruCrossSystemClaim : FramedAuthorityClaim
uluruCrossSystemClaim = framedAuthorityClaim
  politicalConstitutionalClaim
  "First Nations sovereignty has never been ceded or extinguished and co-exists with Crown sovereignty"
  "Uluru Statement from the Heart, 2017"
  Primary.firstNationsPoliticalStatement

------------------------------------------------------------------------
-- Totalisation prerequisites.
------------------------------------------------------------------------

record JurisdictionalTotalisationReceipt : Set where
  constructor jurisdictionalTotalisationReceipt
  field
    reach : JurisdictionalReach
    antecedentOrderPosition : NormativeOrderPosition
    reclassification : ColonialWrong.AuthorityReclassification
    internalPower : Prereq.InternalPowerJustification
    sameProjectionAsPowerPrerequisite : Set
    assertedSystemReference : String
    competingOrderReference : String
    totalisationIsDASHISynthesis : Bool
    totalisationIsDASHISynthesisIsTrue : totalisationIsDASHISynthesis ≡ true

open JurisdictionalTotalisationReceipt public

cooperJurisdictionalTotalisation : JurisdictionalTotalisationReceipt
cooperJurisdictionalTotalisation = jurisdictionalTotalisationReceipt
  assertedTotalReach
  nonGoverningOrder
  ColonialWrong.cooperSettledColonyReclassification
  Prereq.cooperReceptionJustification
  ⊤
  "imperial/common-law legal order applied as governing law for the settled colony"
  "antecedent First Nations law/authority independently modelled outside the Cooper settled-colony observer"
  true refl

------------------------------------------------------------------------
-- Conditional theorem shape.
------------------------------------------------------------------------

record TotalReachRequiresAuthorityReclassification
    (t : JurisdictionalTotalisationReceipt) : Set where
  constructor totalReachRequiresAuthorityReclassification
  field
    reachIsTotal : reach t ≡ assertedTotalReach
    competingOrderMadeNonGoverningOrSubordinate :
      antecedentOrderPosition t ≡ nonGoverningOrder
      ⊎ antecedentOrderPosition t ≡ subordinatedOrder
    prerequisiteReceipt : Prereq.SemanticPrerequisiteReceipt (internalPower t)

open TotalReachRequiresAuthorityReclassification public

cooperTotalisationRequiresReclassification :
  TotalReachRequiresAuthorityReclassification cooperJurisdictionalTotalisation
cooperTotalisationRequiresReclassification =
  totalReachRequiresAuthorityReclassification
    refl
    (inj₁ refl)
    Prereq.cooperSemanticPrerequisite

------------------------------------------------------------------------
-- Donor pins: legal authority/jurisdiction remain necessary but non-exhaustive.
------------------------------------------------------------------------

jurisdictionAloneDoesNotEstablishApplicability :
  Jurisdiction.resolvedJurisdictionAloneEstablishesApplicability
    Jurisdiction.canonicalLegalJurisdictionBoundary ≡ false
jurisdictionAloneDoesNotEstablishApplicability = refl

authorityAloneDoesNotEstablishApplicability :
  Authority.legalSourceAuthorityAloneEstablishesApplicability
    Authority.canonicalLegalSourceAuthorityBoundary ≡ false
authorityAloneDoesNotEstablishApplicability = refl

applicabilityRequiresAuthority :
  Meet.legalSourceAuthorityRequired Meet.canonicalApplicabilityPrerequisiteMeetBoundary ≡ true
applicabilityRequiresAuthority = refl

applicabilityRequiresJurisdiction :
  Meet.resolvedJurisdictionRequired Meet.canonicalApplicabilityPrerequisiteMeetBoundary ≡ true
applicabilityRequiresJurisdiction = refl

applicabilityRequiresSameSystemWeld :
  Meet.authorityJurisdictionSameLegalSystemRequired
    Meet.canonicalApplicabilityPrerequisiteMeetBoundary ≡ true
applicabilityRequiresSameSystemWeld = refl

------------------------------------------------------------------------
-- Cross-system non-collapse.
------------------------------------------------------------------------

data JurisdictionalClaim : Set where
  crownSystemHasResolvedJurisdiction
  crownSourceHasIntraSystemAuthority
  crownJurisdictionExhaustsAllNormativeAuthority
  firstNationsSovereigntyWasCeded
  jurisdictionalTotalisationRequiredAuthorityReclassification
  modernPoliceJurisdictionRepeatsColonialTotalisation : JurisdictionalClaim

data JurisdictionalProducer : Set where
  intraSystemJurisdictionReceiptProducer
  intraSystemSourceAuthorityProducer
  crossSystemAuthorityExhaustionProducer
  cessionConsentProducer
  sameObjectPrerequisiteDoctrineProducer
  modernSameObjectPowerPrerequisiteProducer : JurisdictionalProducer

reverseJurisdictional : JurisdictionalClaim → JurisdictionalProducer
reverseJurisdictional crownSystemHasResolvedJurisdiction = intraSystemJurisdictionReceiptProducer
reverseJurisdictional crownSourceHasIntraSystemAuthority = intraSystemSourceAuthorityProducer
reverseJurisdictional crownJurisdictionExhaustsAllNormativeAuthority = crossSystemAuthorityExhaustionProducer
reverseJurisdictional firstNationsSovereigntyWasCeded = cessionConsentProducer
reverseJurisdictional jurisdictionalTotalisationRequiredAuthorityReclassification = sameObjectPrerequisiteDoctrineProducer
reverseJurisdictional modernPoliceJurisdictionRepeatsColonialTotalisation = modernSameObjectPowerPrerequisiteProducer

record JurisdictionalTotalisationBoundary : Set where
  constructor jurisdictionalTotalisationBoundary
  field
    crownJurisdictionReceiptProvesFirstNationsCession : Bool
    crownJurisdictionReceiptProvesFirstNationsCessionIsFalse : crownJurisdictionReceiptProvesFirstNationsCession ≡ false
    crownSourceAuthorityProvesCrossSystemLegitimacy : Bool
    crownSourceAuthorityProvesCrossSystemLegitimacyIsFalse : crownSourceAuthorityProvesCrossSystemLegitimacy ≡ false
    intraSystemSourcePriorityDeterminesCrossSystemPriority : Bool
    intraSystemSourcePriorityDeterminesCrossSystemPriorityIsFalse : intraSystemSourcePriorityDeterminesCrossSystemPriority ≡ false
    maboRecognitionExhaustsCountryAuthority : Bool
    maboRecognitionExhaustsCountryAuthorityIsFalse : maboRecognitionExhaustsCountryAuthority ≡ false
    dominantSystemCanProveItsOwnCrossSystemExhaustivenessByInternalReceipt : Bool
    dominantSystemCanProveItsOwnCrossSystemExhaustivenessByInternalReceiptIsFalse : dominantSystemCanProveItsOwnCrossSystemExhaustivenessByInternalReceipt ≡ false
    validModernPoliceJurisdictionProvesColonialMotive : Bool
    validModernPoliceJurisdictionProvesColonialMotiveIsFalse : validModernPoliceJurisdictionProvesColonialMotive ≡ false

canonicalJurisdictionalTotalisationBoundary : JurisdictionalTotalisationBoundary
canonicalJurisdictionalTotalisationBoundary =
  jurisdictionalTotalisationBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Mabo/Country residual remains outside the Crown administrative chart.
------------------------------------------------------------------------

maboCountryAuthorityResidual : MaboCross.SecurityCountryProducer
maboCountryAuthorityResidual = MaboCross.countryAuthorityResidualProducer

neverCededSourceRole : Primary.PrimarySourceRole
neverCededSourceRole = Primary.sourceRole Primary.uluruNeverCededPrimaryReceipt
