module DASHI.Culture.RastafariItalInhabitedLandscapeBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Culture.RastafariItalLivityExact as Ital
import DASHI.Environment.LESSituatedObservationInteractionExact as LESObs
import DASHI.Planning.InhabitedLandscapeExact as Landscape

------------------------------------------------------------------------
-- CROSS-POLLINATION BOUNDARY
--
-- This module reuses repository structure without identifying the traditions:
--
--   Rastafari Ital livity
--        ↕ structural bridge only
--   inhabited-landscape multifunctionality
--        ↕ structural bridge only
--   LES situated observe/interact cycle
--
-- No theorem below says that Rastafari is permaculture, that permaculture is
-- Rastafari, or that either source tradition proves DASHI's planning / evidence
-- geometry.  The bridge says only that existing typed carriers can represent
-- some co-occurring dimensions without erasing provenance.
------------------------------------------------------------------------

record ItalSituatedLandscapePractice : Set where
  constructor italSituatedLandscapePractice
  field
    italProfile : Ital.ItalLivityProfile
    place : Landscape.Place
    time : Landscape.Time
    observationCycle : LESObs.ObserveInteractCycle

open ItalSituatedLandscapePractice public

canonicalMarketGardenItalPractice : ItalSituatedLandscapePractice
canonicalMarketGardenItalPractice =
  italSituatedLandscapePractice
    Ital.canonicalItalProfile
    Landscape.marketGarden
    Landscape.wetSeason
    LESObs.canonicalReversibleObservationCycle

------------------------------------------------------------------------
-- Existing planning structure already represents food + ecology + livelihood
-- on one place.  Ital can therefore be related to that carrier without adding
-- a second parallel place ontology.
------------------------------------------------------------------------

marketGardenSupportsFoodEcologyLivelihoodCarrier :
  Landscape.InhabitedLandscape.Role Landscape.landscape Landscape.marketGarden Landscape.foodProduction ×
  (Landscape.InhabitedLandscape.Role Landscape.landscape Landscape.marketGarden Landscape.ecologicalPatch ×
   Landscape.InhabitedLandscape.Role Landscape.landscape Landscape.marketGarden Landscape.workplace)
marketGardenSupportsFoodEcologyLivelihoodCarrier = tt , (tt , tt)

italProfileCanCoexistWithMultifunctionalLandscape :
  Ital.dimension (italProfile canonicalMarketGardenItalPractice) Ital.food ×
  (Ital.dimension (italProfile canonicalMarketGardenItalPractice) Ital.land ×
   Landscape.InhabitedLandscape.Role Landscape.landscape Landscape.marketGarden Landscape.foodProduction)
italProfileCanCoexistWithMultifunctionalLandscape = tt , (tt , tt)

------------------------------------------------------------------------
-- Observe/interact remains situated.  Attaching an Ital profile does not erase
-- season/site/provenance from the LES observation carrier.
------------------------------------------------------------------------

italAttachmentDoesNotFlattenObservationContext :
  (LESObs.INF.FactorsThrough
    LESObs.anonymousReading
    LESObs.situatedObservationSignature → ⊥)
italAttachmentDoesNotFlattenObservationContext =
  LESObs.anonymousReadingCannotRecoverSituatedSignature

------------------------------------------------------------------------
-- A lifestyle/practice orientation is not automatically a land-use permission
-- or an empirical environmental result.  Reuse the existing planning and LES
-- gates rather than inventing looser substitutes.
------------------------------------------------------------------------

italPracticeDoesNotAutoAuthorizeObservedUse :
  Landscape.InhabitedLandscape.ObservedUse Landscape.landscape Landscape.creek Landscape.drySeason Landscape.recreationUse ×
  (Landscape.InhabitedLandscape.PermittedUse Landscape.landscape Landscape.creek Landscape.recreationUse → ⊥)
italPracticeDoesNotAutoAuthorizeObservedUse = Landscape.observedUseNeedNotBePermittedUse

italBridgeDoesNotPromotePermacultureIdentity : Ital.ItalIsIdenticalToPermaculture → ⊥
italBridgeDoesNotPromotePermacultureIdentity = Ital.italIsNotAutoIdentifiedWithPermaculture

record ItalLandscapeBridgeBoundary : Set where
  constructor italLandscapeBridgeBoundary
  field
    structuralReuseMeansDoctrinalIdentity : Bool
    structuralReuseMeansDoctrinalIdentityIsFalse : structuralReuseMeansDoctrinalIdentity ≡ false

    lifestyleOrientationIsLandUsePermission : Bool
    lifestyleOrientationIsLandUsePermissionIsFalse : lifestyleOrientationIsLandUsePermission ≡ false

    sameVisibleReadingErasesSituatedContext : Bool
    sameVisibleReadingErasesSituatedContextIsFalse : sameVisibleReadingErasesSituatedContext ≡ false

    multifunctionalPlaceCarrierIsReusable : Bool
    multifunctionalPlaceCarrierIsReusableIsTrue : multifunctionalPlaceCarrierIsReusable ≡ true

canonicalItalLandscapeBridgeBoundary : ItalLandscapeBridgeBoundary
canonicalItalLandscapeBridgeBoundary =
  italLandscapeBridgeBoundary
    false refl
    false refl
    false refl
    true refl
