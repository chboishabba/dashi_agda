module DASHI.Wikimedia.IbrahimSnowballFoodSecurityLandTenurePrimarySourcesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballAgrarianLabourSecondOrderExact as Prior

------------------------------------------------------------------------
-- AGRARIAN / FOOD-SECURITY PRIMARY-SOURCE CONTINUATION
--
-- The existing food-security QID is retained; broad food-system and land-tenure
-- identities remain unresolved rather than promoting a Wikimedia category or a
-- nearby article. Primary FAO institutional records pay definition/source roles
-- only; they do not create land authority, local tenure truth or food access.
------------------------------------------------------------------------

foodSecurityQid : Identity.ExternalIdentityDemand
foodSecurityQid = Identity.mkOptionalIdentityDemand
  "Ibrahim agrarian primary-source continuation"
  "verified external concept identity"
  "food security" Identity.wikidataQid
  (Identity.verified "Q1229911" "Wikidata identity retained from first-order walk")

landTenureQid : Identity.ExternalIdentityDemand
landTenureQid = Identity.mkOptionalIdentityDemand
  "Ibrahim agrarian primary-source continuation"
  "external concept identity"
  "land tenure" Identity.wikidataQid
  (Identity.unresolved "current search located Category:Land tenure Q10172437, which is a Wikimedia category and is not promoted to the concept identity")

foodSystemQid : Identity.ExternalIdentityDemand
foodSystemQid = Identity.mkOptionalIdentityDemand
  "Ibrahim agrarian primary-source continuation"
  "external concept identity"
  "food system / agrifood system" Identity.wikidataQid
  (Identity.unresolved "broad concept identity not safely resolved in current tranche; article/work items are not promoted")

data InstitutionalSourceRole : Set where
  intergovernmentalDefinitionRecord summitAdoptedDefinitionRecord : InstitutionalSourceRole

record InstitutionalPrimarySource : Set where
  constructor institutional-primary-source
  field
    institution : String
    title : String
    year : Nat
    locator : String
    role : InstitutionalSourceRole
    boundedReading : String
    excludedPromotion : String
    sourceStrength : Attribution.SourceStrength
    claimOwner : Attribution.ClaimOwner
open InstitutionalPrimarySource public

worldFoodSummit1996 : InstitutionalPrimarySource
worldFoodSummit1996 = institutional-primary-source
  "Food and Agriculture Organization of the United Nations / World Food Summit"
  "Rome Declaration on World Food Security and World Food Summit Plan of Action"
  1996
  "WFS 96/REP; Report of the World Food Summit, 13-17 November 1996"
  summitAdoptedDefinitionRecord
  "Primary institutional record for the summit-adopted food-security definition, including physical/economic access as part of the definition."
  "Does not prove that a particular population is food-secure, does not equal food sovereignty, and does not establish causal adequacy of production alone."
  Attribution.primaryInstitutionalRecord
  Attribution.externalSourceOwner

faoLandTenure2002 : InstitutionalPrimarySource
faoLandTenure2002 = institutional-primary-source
  "Food and Agriculture Organization of the United Nations"
  "Land tenure and rural development, FAO Land Tenure Studies 3"
  2002
  "FAO Land Tenure Studies 3, section 3: What is land tenure"
  intergovernmentalDefinitionRecord
  "Primary institutional technical source defining land tenure as legally or customarily defined relationships among people with respect to land, including use/control/transfer conditions."
  "Does not identify the actual tenure regime, authority or rights of any particular Country/community/site and does not convert land use into land authority."
  Attribution.primaryInstitutionalRecord
  Attribution.externalSourceOwner

record AgrarianPrimaryAcquisitionState : Set where
  constructor agrarian-primary-acquisition-state
  field
    foodSecurityQidAcquired : Bool
    landTenureQidAcquired : Bool
    foodSystemQidAcquired : Bool
    summitPrimaryRecordAcquired : Bool
    faoLandTenurePrimaryRecordAcquired : Bool
    availabilityEvidenceAcquired : Bool
    accessEvidenceAcquired : Bool
    tenureRightsEvidenceAcquired : Bool
    communityAuthorityEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool
open AgrarianPrimaryAcquisitionState public

record AgrarianPrimaryPaymentState : Set where
  constructor agrarian-primary-payment-state
  field
    foodSecurityIdentityPaid : Bool
    landTenureIdentityPaid : Bool
    foodSystemIdentityPaid : Bool
    primarySourceRolePaid : Bool
    localAvailabilityPaid : Bool
    localAccessPaid : Bool
    localTenureRegimePaid : Bool
    localAuthorityPaid : Bool
    foodSecurityOutcomePaid : Bool
    foodSovereigntyRelationPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String
open AgrarianPrimaryPaymentState public

snowballAcquisitionDoesNotAdvanceAgrarianPrimaryPayment :
  AgrarianPrimaryAcquisitionState → AgrarianPrimaryPaymentState → AgrarianPrimaryPaymentState
snowballAcquisitionDoesNotAdvanceAgrarianPrimaryPayment _ payment = payment

data CategoryQidMeansConceptIdentity : Set where
data DefinitionMeansLocalOutcome : Set where
data LandUseMeansLandAuthority : Set where
data FoodAvailabilityMeansFoodSecurity : Set where
data FoodSecurityMeansFoodSovereignty : Set where
\data InstitutionalDefinitionMeansCommunityAuthority : Set where

categoryDoesNotPayConceptIdentity : CategoryQidMeansConceptIdentity → ⊥
categoryDoesNotPayConceptIdentity ()

definitionDoesNotPayLocalOutcome : DefinitionMeansLocalOutcome → ⊥
definitionDoesNotPayLocalOutcome ()

landUseDoesNotCreateLandAuthority : LandUseMeansLandAuthority → ⊥
landUseDoesNotCreateLandAuthority ()

availabilityDoesNotByItselfCreateFoodSecurity : FoodAvailabilityMeansFoodSecurity → ⊥
availabilityDoesNotByItselfCreateFoodSecurity ()

foodSecurityDoesNotEqualFoodSovereignty : FoodSecurityMeansFoodSovereignty → ⊥
foodSecurityDoesNotEqualFoodSovereignty ()

institutionalDefinitionDoesNotCreateCommunityAuthority : InstitutionalDefinitionMeansCommunityAuthority → ⊥
institutionalDefinitionDoesNotCreateCommunityAuthority ()

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

priorBoundary : Prior.AgrarianLabourSecondOrderBoundary
priorBoundary = Prior.canonicalAgrarianLabourSecondOrderBoundary
