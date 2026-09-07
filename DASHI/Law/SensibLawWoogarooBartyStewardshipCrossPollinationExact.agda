module DASHI.Law.SensibLawWoogarooBartyStewardshipCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooBartyOutreachExact as Outreach
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Culture.PatternMindReciprocityLoveBridge as PatternMind
import DASHI.Environment.LESCountryExternalityRealisationExact as CountryExternality
import DASHI.Governance.WhyteKinshipTemporalityBoundaryExact as Whyte
import DASHI.Governance.RecognitionDistributionRepresentationAxesExact as Fraser

------------------------------------------------------------------------
-- WOOGAROO / BARTY / STEWARDSHIP CROSS-POLLINATION
--
-- This is a source-bounded DASHI composition, not a claim that any Indigenous
-- community, Robin Wall Kimmerer, Two-Eyed Seeing, PatternMind, Whyte, Fraser,
-- Ash Barty, or Save Woogaroo Forest endorses this exact formal carrier.
--
-- The purpose is to prevent the outreach brief from collapsing a living place
-- into one environmental metric, one celebrity relation, or one administrative
-- planning surface.
------------------------------------------------------------------------

data StewardshipCoordinate : Set where
  ecologicalContinuity : StewardshipCoordinate
  placeRelation : StewardshipCoordinate
  knowledgeProvenance : StewardshipCoordinate
  communityAuthority : StewardshipCoordinate
  reciprocalObligation : StewardshipCoordinate
  intergenerationalContinuity : StewardshipCoordinate
  distributionalBurden : StewardshipCoordinate
  recognition : StewardshipCoordinate
  representation : StewardshipCoordinate
  materialLivelihood : StewardshipCoordinate
  publicNarrative : StewardshipCoordinate
  commercialCompatibility : StewardshipCoordinate


data StewardshipObservation : Set where
  sharedPositivePublicStory : StewardshipObservation


data FineStewardshipState : Set where
  reciprocalAuthorityBearingState : FineStewardshipState
  extractiveAuthorityPoorState : FineStewardshipState

publicStoryObserver : FineStewardshipState → StewardshipObservation
publicStoryObserver _ = sharedPositivePublicStory

stewardshipSignature : FineStewardshipState → CountryExternality.CountryStewardshipState
stewardshipSignature reciprocalAuthorityBearingState =
  CountryExternality.authorityBearingEcologicalContinuity
stewardshipSignature extractiveAuthorityPoorState =
  CountryExternality.authorityPoorEcologicalDegradation

stewardshipDiffers :
  stewardshipSignature reciprocalAuthorityBearingState
  ≡ stewardshipSignature extractiveAuthorityPoorState → ⊥
stewardshipDiffers ()

publicStoryCannotRecoverStewardship :
  INF.FactorsThrough publicStoryObserver stewardshipSignature → ⊥
publicStoryCannotRecoverStewardship =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      reciprocalAuthorityBearingState
      extractiveAuthorityPoorState
      refl
      stewardshipDiffers)

------------------------------------------------------------------------
-- Two-Eyed / Braiding boundary.
--
-- Scientific/ecological evidence and situated Indigenous/community knowledge
-- may coordinate on the same place without sharing provenance, permission,
-- authority, obligation, or transmission history.
------------------------------------------------------------------------

sharedEcologicalObservationDoesNotFuseKnowledgeHistory :
  TwoEyed.sharedObservationMeansSameEpistemicHistory
    TwoEyed.canonicalKimmererTwoEyedSeeingBoundary ≡ false
sharedEcologicalObservationDoesNotFuseKnowledgeHistory = refl

coordinatedUseDoesNotRequireEpistemicFusion :
  TwoEyed.coordinatedUseRequiresEpistemicFusion
    TwoEyed.canonicalKimmererTwoEyedSeeingBoundary ≡ false
coordinatedUseDoesNotRequireEpistemicFusion = refl

scientificResultDoesNotRecoverPermission :
  INF.FactorsThrough IK.extractedProposition IK.permission → ⊥
scientificResultDoesNotRecoverPermission = IK.propositionCannotRecoverPermission

scientificResultDoesNotRecoverAuthority :
  INF.FactorsThrough IK.extractedProposition IK.authority → ⊥
scientificResultDoesNotRecoverAuthority = IK.propositionCannotRecoverAuthority

scientificResultDoesNotRecoverObligation :
  INF.FactorsThrough IK.extractedProposition IK.obligation → ⊥
scientificResultDoesNotRecoverObligation = IK.propositionCannotRecoverObligation

------------------------------------------------------------------------
-- PatternMind / reciprocity boundary.
--
-- The useful transfer is structural: relation-before-object, repeated
-- attention, reciprocity, consent and anti-domination constrain the outreach
-- process.  PatternMind is not promoted as a universal Indigenous ontology.
------------------------------------------------------------------------

patternMindBoundary : PatternMind.PatternMindReciprocityLoveBridge
patternMindBoundary = PatternMind.canonicalPatternMindReciprocityLoveBridge

reciprocityRequiresFreedom :
  PatternMind.reciprocityRequiresFreedom patternMindBoundary ≡ true
reciprocityRequiresFreedom = refl

coerciveReciprocityNotPromoted :
  PatternMind.coerciveReciprocityPromoted patternMindBoundary ≡ false
coerciveReciprocityNotPromoted = refl

------------------------------------------------------------------------
-- Economics / stewardship boundary.
--
-- Economic value can be represented, but it cannot exhaust Country,
-- community authority, reciprocity, ecological continuity or future burden.
------------------------------------------------------------------------

externalityBoundary : CountryExternality.ExternalityAccountingBoundary
externalityBoundary = CountryExternality.canonicalExternalityAccountingBoundary

marketRevenueDoesNotExhaustCountryValue :
  CountryExternality.marketRevenueExhaustsCountryValue externalityBoundary ≡ false
marketRevenueDoesNotExhaustCountryValue = refl

carbonMetricDoesNotExhaustCommunityAuthority :
  CountryExternality.carbonMetricExhaustsCommunityAuthority externalityBoundary ≡ false
carbonMetricDoesNotExhaustCommunityAuthority = refl

countryRelationNotAssetByDefault :
  CountryExternality.countryRelationIsAssetByDefault externalityBoundary ≡ false
countryRelationNotAssetByDefault = refl

communityAuthorityNotPropertyRightByDefault :
  CountryExternality.communityAuthorityIsPropertyRightByDefault externalityBoundary ≡ false
communityAuthorityNotPropertyRightByDefault = refl

------------------------------------------------------------------------
-- Intergenerational / relational-history boundary.
------------------------------------------------------------------------

whyteBoundary : Whyte.WhyteKinshipTemporalityBoundary
whyteBoundary = Whyte.canonicalWhyteKinshipTemporalityBoundary

samePresentBurdenDoesNotMeanSameRelationalHistory :
  Whyte.samePresentBurdenMeansSameRelationalHistory whyteBoundary ≡ false
samePresentBurdenDoesNotMeanSameRelationalHistory = refl

------------------------------------------------------------------------
-- Outreach refinement.
------------------------------------------------------------------------

data BraidedOutreachResidual : Set where
  indigenousAuthorityCarrierUnresolved : BraidedOutreachResidual
  communityDefinedOutcomeUnresolved : BraidedOutreachResidual
  ecologicalStewardshipOutcomeUnresolved : BraidedOutreachResidual
  intergenerationalContinuityUnresolved : BraidedOutreachResidual
  distributionRecognitionRepresentationUnresolved : BraidedOutreachResidual
  consentUnresolved : BraidedOutreachResidual

record BraidedStewardshipBrief : Set where
  constructor braidedStewardshipBrief
  field
    baseBrief : Outreach.FactualOutreachBrief
    preservesEcologicalEvidence : Bool
    preservesEcologicalEvidenceIsTrue : preservesEcologicalEvidence ≡ true
    preservesKnowledgeProvenance : Bool
    preservesKnowledgeProvenanceIsTrue : preservesKnowledgeProvenance ≡ true
    preservesAuthorityPermissionDistinction : Bool
    preservesAuthorityPermissionDistinctionIsTrue :
      preservesAuthorityPermissionDistinction ≡ true
    preservesReciprocityAsNonCoercive : Bool
    preservesReciprocityAsNonCoerciveIsTrue :
      preservesReciprocityAsNonCoercive ≡ true
    preservesIntergenerationalHistory : Bool
    preservesIntergenerationalHistoryIsTrue :
      preservesIntergenerationalHistory ≡ true
    preservesEconomicNonExhaustivity : Bool
    preservesEconomicNonExhaustivityIsTrue :
      preservesEconomicNonExhaustivity ≡ true
    doesNotClaimIndigenousAuthorityWithoutReceipt : Bool
    doesNotClaimIndigenousAuthorityWithoutReceiptIsTrue :
      doesNotClaimIndigenousAuthorityWithoutReceipt ≡ true

open BraidedStewardshipBrief public

currentBraidedStewardshipBrief : BraidedStewardshipBrief
currentBraidedStewardshipBrief =
  braidedStewardshipBrief
    Outreach.currentFactualBrief
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Consumer split: celebrity outreach and Country/community authority are
-- independent coordinates.  Barty consent cannot pay Indigenous authority;
-- Indigenous authority cannot be inferred from ecological evidence; a market
-- valuation cannot pay either one.
------------------------------------------------------------------------

data CelebrityConsentPaysIndigenousAuthority : Set where
data EcologicalEvidencePaysCommunityAuthority : Set where
data MarketValuePaysStewardshipContinuity : Set where
data IndigenousIdentityPaysCommunityMandate : Set where
data PublicRecognitionPaysRepresentation : Set where

data SchoolOrPlaygroundLegacyPaysCountryAuthority : Set where

celebrityConsentDoesNotPayIndigenousAuthority :
  CelebrityConsentPaysIndigenousAuthority → ⊥
celebrityConsentDoesNotPayIndigenousAuthority ()

ecologicalEvidenceDoesNotPayCommunityAuthority :
  EcologicalEvidencePaysCommunityAuthority → ⊥
ecologicalEvidenceDoesNotPayCommunityAuthority ()

marketValueDoesNotPayStewardshipContinuity :
  MarketValuePaysStewardshipContinuity → ⊥
marketValueDoesNotPayStewardshipContinuity ()

indigenousIdentityDoesNotPayCommunityMandate :
  IndigenousIdentityPaysCommunityMandate → ⊥
indigenousIdentityDoesNotPayCommunityMandate ()

publicRecognitionDoesNotPayRepresentation :
  PublicRecognitionPaysRepresentation → ⊥
publicRecognitionDoesNotPayRepresentation ()

playgroundLegacyDoesNotPayCountryAuthority :
  SchoolOrPlaygroundLegacyPaysCountryAuthority → ⊥
playgroundLegacyDoesNotPayCountryAuthority ()

------------------------------------------------------------------------
-- Current frontier.
--
-- The Barty-facing invitation itself is already evidence-permitted in the base
-- module.  This cross-pollinated surface adds a second independent frontier:
-- any claim to speak about Country, custodial authority, Indigenous knowledge,
-- or community-defined stewardship requires its own source/authority receipt.
------------------------------------------------------------------------

record WoogarooBraidedStewardshipBoundary : Set where
  constructor woogarooBraidedStewardshipBoundary
  field
    celebrityOutreachEqualsCountryGovernance : Bool
    celebrityOutreachEqualsCountryGovernanceIsFalse :
      celebrityOutreachEqualsCountryGovernance ≡ false

    ecologicalProtectionEqualsCompleteStewardship : Bool
    ecologicalProtectionEqualsCompleteStewardshipIsFalse :
      ecologicalProtectionEqualsCompleteStewardship ≡ false

    economicValueEqualsCountryValue : Bool
    economicValueEqualsCountryValueIsFalse : economicValueEqualsCountryValue ≡ false

    coordinationRequiresKnowledgeFusion : Bool
    coordinationRequiresKnowledgeFusionIsFalse :
      coordinationRequiresKnowledgeFusion ≡ false

    reciprocityRequiresConsentAndFreedom : Bool
    reciprocityRequiresConsentAndFreedomIsTrue :
      reciprocityRequiresConsentAndFreedom ≡ true

    indigenousAuthorityMustBeSourcePaid : Bool
    indigenousAuthorityMustBeSourcePaidIsTrue :
      indigenousAuthorityMustBeSourcePaid ≡ true

canonicalWoogarooBraidedStewardshipBoundary : WoogarooBraidedStewardshipBoundary
canonicalWoogarooBraidedStewardshipBoundary =
  woogarooBraidedStewardshipBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
