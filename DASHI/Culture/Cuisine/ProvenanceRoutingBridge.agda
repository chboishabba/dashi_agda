module DASHI.Culture.Cuisine.ProvenanceRoutingBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Culture.Cuisine.SituatedMoleWorld as Situated

------------------------------------------------------------------------
-- Cuisine as a worked instance of channel-dependent provenance routing.
--
-- Dafna Hirsch,
-- "Hummus is best when it is fresh and made by Arabs": The gourmetization
-- of hummus in Israel and the return of the repressed Arab,
-- American Ethnologist 38 (2011), 617-630.
-- DOI: 10.1111/j.1548-1425.2011.01326.x
--
-- Ilan Zvi Baron and Galia Press-Barnathan,
-- "Foodways and Foodwashing: Israeli Cookbooks and the Politics of Culinary
-- Zionism", International Political Sociology 15(3) (2021), 338-358.
-- DOI: 10.1093/ips/olab007
--
-- Yael Raviv, "Falafel: A National Icon", Gastronomica 3(3) (2003), 20-25.
-- DOI: 10.1525/gfc.2003.3.3.20
--
-- These works motivate keeping nationalisation, Arab/Palestinian provenance,
-- authenticity, credit and value-flow as distinct channels.  They do not make
-- any one cuisine edge an ownership theorem.
------------------------------------------------------------------------

data CuisineOutputChannel : Set where
  publicBrand : CuisineOutputChannel
  authenticity : CuisineOutputChannel
  historicalCredit : CuisineOutputChannel
  economicBenefit : CuisineOutputChannel
  representationRights : CuisineOutputChannel
  ownershipClaim : CuisineOutputChannel
  communityMemory : CuisineOutputChannel

record RoutedCulinaryProvenance : Set where
  constructor routedCulinaryProvenance
  field
    contribution : Situated.HistoricalContribution
    channel : CuisineOutputChannel
    routedReading : String

open RoutedCulinaryProvenance public

------------------------------------------------------------------------
-- The same provenance contribution may be routed differently by channel.
-- National canonisation therefore does not imply origin, and visible
-- authenticity does not imply credit/rights/value return.
------------------------------------------------------------------------

record ChannelDependentCuisineRouting : Set where
  constructor channelDependentCuisineRouting
  field
    source : Situated.HistoricalContribution
    brandRoute : RoutedCulinaryProvenance
    creditRoute : RoutedCulinaryProvenance
    rightsRoute : RoutedCulinaryProvenance

    brandUsesSameSource : contribution brandRoute ≡ source
    creditUsesSameSource : contribution creditRoute ≡ source
    rightsUsesSameSource : contribution rightsRoute ≡ source

open ChannelDependentCuisineRouting public

data CuisineOwnershipPromotion : Set where
  historicalRelationObserved : CuisineOwnershipPromotion

data HistoricalRelationAutomaticallyProvesExclusiveOwnership :
  CuisineOwnershipPromotion → Set where

historicalRelationDoesNotProveExclusiveOwnership :
  HistoricalRelationAutomaticallyProvesExclusiveOwnership
    historicalRelationObserved → ⊥
historicalRelationDoesNotProveExclusiveOwnership ()

------------------------------------------------------------------------
-- Shared / adopted / canonised are separate propositions.
------------------------------------------------------------------------

record CuisinePropositionBoundary : Set where
  constructor cuisinePropositionBoundary
  field
    sharedEqualsOwnerless : Bool
    sharedEqualsOwnerlessIsFalse : sharedEqualsOwnerless ≡ false
    adoptedEqualsInvented : Bool
    adoptedEqualsInventedIsFalse : adoptedEqualsInvented ≡ false
    nationalCanonisationEqualsProvenance : Bool
    nationalCanonisationEqualsProvenanceIsFalse :
      nationalCanonisationEqualsProvenance ≡ false
    visibleAuthenticityImpliesRightsReturn : Bool
    visibleAuthenticityImpliesRightsReturnIsFalse :
      visibleAuthenticityImpliesRightsReturn ≡ false

canonicalCuisinePropositionBoundary : CuisinePropositionBoundary
canonicalCuisinePropositionBoundary =
  cuisinePropositionBoundary
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Adapter exposing the existing historical relation vocabulary rather than a
-- parallel food ontology.
------------------------------------------------------------------------

canonicalNationalisationRelation : Situated.HistoricalFoodRelation
canonicalNationalisationRelation = Situated.nationalCanonisationRelation

canonicalAppropriationRelation : Situated.HistoricalFoodRelation
canonicalAppropriationRelation = Situated.appropriatedTechniqueRelation

canonicalCommunityReclamationRelation : Situated.HistoricalFoodRelation
canonicalCommunityReclamationRelation = Situated.communityReclamationRelation
