module DASHI.Culture.PowersPlantationParadiseComparativeVenueEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Governance.DomainPermeabilityAuthorityTransport as Domain

------------------------------------------------------------------------
-- COMPARATIVE FRENCH-COLONIAL VENUE EVIDENCE
--
-- Powers's book ranges across French slave colonies.  Martinique therefore
-- supplies useful comparative evidence for racialised theatre architecture and
-- pricing, but it does not transport a Saint-Pierre rule into Saint-Domingue.
------------------------------------------------------------------------

lamecaPetitesAntillesSource : Source.AttributedSource
lamecaPetitesAntillesSource =
  Source.mkNoDOISource
    "Médiathèque Caraïbe / Laméca"
    "La vie lyrique des Petites Antilles françaises"
    "La musique coloniale des Antilles françaises au 18ème siècle"
    "undated public digital dossier"
    "https://www.lameca.org/publications-numeriques/dossiers-et-articles/la-musique-coloniale-des-antilles-francaises-au-18eme-siecle/ii-la-vie-lyrique-des-petites-antilles-francaises/"
    Source.institutionalSource
    "institutional secondary dossier quoting contemporaneous Saint-Pierre theatre planning and Isert's travel account; bounded comparative evidence, not authority for Saint-Domingue rules"
    Source.publicAttribution

data ComparativeVenueEvidenceKind : Set where
  plannedArchitectureAndEconomy : ComparativeVenueEvidenceKind
  observedAccessAndPricing : ComparativeVenueEvidenceKind

record ComparativeVenueReceipt : Set where
  constructor comparative-venue-receipt
  field
    colonyReference : String
    venueReference : String
    dateReference : String
    evidenceKind : ComparativeVenueEvidenceKind
    seatingReference : String
    economicReference : String
    citedHistoricalCoordinate : String
    source : Source.AttributedSource
    historicalOriginalInspectedHere : Bool
    historicalOriginalInspectedHereIsFalse :
      historicalOriginalInspectedHere ≡ false

open ComparativeVenueReceipt public

saintPierre1786PlannedSeatingReceipt : ComparativeVenueReceipt
saintPierre1786PlannedSeatingReceipt =
  comparative-venue-receipt
    "Martinique"
    "planned Saint-Pierre theatre"
    "reported 21 January 1786"
    plannedArchitectureAndEconomy
    "three box tiers were planned: first and second for whites, third for people of colour"
    "reported construction cost 176000 livres; land 310000 livres with an instalment schedule"
    "Supplément aux Affiches Américaines, Port-au-Prince, 21 January 1786, quoted by Laméca"
    lamecaPetitesAntillesSource
    false refl

isertSaintPierreObservedPricingReceipt : ComparativeVenueReceipt
isertSaintPierreObservedPricingReceipt =
  comparative-venue-receipt
    "Martinique"
    "Saint-Pierre theatre observed by Paul Erdmann Isert"
    "Isert voyage account of his Caribbean stay, published 1793"
    observedAccessAndPricing
    "Isert describes unrestricted places within the box rows but a fourth tier called the 'paradise' for people of colour"
    "Isert reports whites paying one gourde and people of colour half a gourde"
    "P. E. Isert, Voyages en Guinée et dans les îles Caraïbes en Amérique, p.236, quoted by Laméca"
    lamecaPetitesAntillesSource
    false refl

data MartiniqueEvidenceTransportsSaintDomingueRule : Set where

martiniqueEvidenceDoesNotTransportSaintDomingueRule :
  MartiniqueEvidenceTransportsSaintDomingueRule → ⊥
martiniqueEvidenceDoesNotTransportSaintDomingueRule ()

domainTransportBoundary : Domain.DomainTransportReceipt
domainTransportBoundary = Domain.canonicalDomainTransportReceipt

record PowersComparativeVenueEvidenceBoundary : Set where
  constructor powers-comparative-venue-evidence-boundary
  field
    racialisedSeatingComparativeEvidencePaid : Bool
    racialisedSeatingComparativeEvidencePaidIsTrue :
      racialisedSeatingComparativeEvidencePaid ≡ true
    differentialPricingComparativeEvidencePaid : Bool
    differentialPricingComparativeEvidencePaidIsTrue :
      differentialPricingComparativeEvidencePaid ≡ true
    sameFrenchColonialTheatreDomainImpliesSameLocalRule : Bool
    sameFrenchColonialTheatreDomainImpliesSameLocalRuleIsFalse :
      sameFrenchColonialTheatreDomainImpliesSameLocalRule ≡ false
    secondaryQuotationEqualsPrimaryInspection : Bool
    secondaryQuotationEqualsPrimaryInspectionIsFalse :
      secondaryQuotationEqualsPrimaryInspection ≡ false

canonicalPowersComparativeVenueEvidenceBoundary :
  PowersComparativeVenueEvidenceBoundary
canonicalPowersComparativeVenueEvidenceBoundary =
  powers-comparative-venue-evidence-boundary
    true refl
    true refl
    false refl
    false refl
