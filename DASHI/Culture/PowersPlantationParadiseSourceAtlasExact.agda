module DASHI.Culture.PowersPlantationParadiseSourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- POWERS / PLANTATION TO PARADISE SOURCE ATLAS
--
-- Source propositions remain source-bound.  Publisher summaries, scholarly
-- reviews, later edited collections and DASHI finite countermodels occupy
-- different epistemic layers and are never silently identified.
------------------------------------------------------------------------

powersBookSource : Source.AttributedSource
powersBookSource =
  Source.mkNoDOISource
    "David M. Powers"
    "From Plantation to Paradise? Cultural Politics and Musical Theatre in French Slave Colonies, 1764-1789"
    "Michigan State University Press"
    "2014"
    "https://msupress.org/9781611861204/from-plantation-to-paradise/"
    Source.academicBookSource
    "primary scholarly monograph for social casting, nonwhite participation, theatre architecture, repertoire, seating/audience structure, and revolutionary disruption in Guadeloupe, Martinique and Saint-Domingue; exact chapter/page claims require page-level recovery"
    Source.publicAttribution

mondelliReviewSource : Source.AttributedSource
mondelliReviewSource =
  Source.mkDOISource
    "Peter Mondelli"
    "From Plantation to Paradise? Cultural Politics and Musical Theatre in French Slave Colonies, 1764-1789 by David M. Powers"
    "Early American Literature 51(1):184-188"
    "2016"
    "10.1353/eal.2016.0016"
    "https://doi.org/10.1353/eal.2016.0016"
    Source.academicArticleSource
    "secondary review source for the archive-silence problem and the joint empowerment/domination reading; the review is not substituted for Powers's primary argument"
    Source.publicAttribution

leichmanBenacGirouxSource : Source.AttributedSource
leichmanBenacGirouxSource =
  Source.mkNoDOISource
    "Jeffrey M. Leichman and Karine Benac-Giroux, editors"
    "Colonialism and Slavery in Performance: Theatre and the Eighteenth-Century French Caribbean"
    "Liverpool University Press; Oxford University Studies in the Enlightenment"
    "2021"
    "https://liverpooluniversitypress.co.uk/books/isbn/9781800348042/"
    Source.academicBookSource
    "later comparative research programme linking theatre history, performance studies, slavery, racialisation and trans-Atlantic colonial identity; used only for cross-pollination and not retroactively attributed to Powers"
    Source.publicAttribution

allPowersSources : List Source.AttributedSource
allPowersSources =
  powersBookSource ∷ mondelliReviewSource ∷ leichmanBenacGirouxSource ∷ []

powersSourceAtlas : Source.AttributedSourceAtlas
powersSourceAtlas =
  Source.mkSourceAtlas
    "Powers Plantation to Paradise source atlas"
    "DASHI.Culture.PowersPlantationParadiseSourceAtlasExact"
    allPowersSources
    "bounded attribution for Powers 2014, Mondelli 2016 review commentary, and Leichman/Benac-Giroux 2021 comparative theatre/slavery scholarship"

powersSourceAtlasReceipt : Receipt.GenericReceipt
powersSourceAtlasReceipt =
  Source.attributedSourceAtlasReceipt
    powersSourceAtlas
    "agda -i . DASHI/Culture/PowersPlantationParadiseSourceAtlasExact.agda"

powersSourceAtlasNonPromoting :
  Receipt.promotesClaim powersSourceAtlasReceipt ≡ false
powersSourceAtlasNonPromoting = refl

------------------------------------------------------------------------
-- Claim-layer boundary.
------------------------------------------------------------------------

data PowersClaimLayer : Set where
  sourceProposition : PowersClaimLayer
  reviewerInterpretation : PowersClaimLayer
  laterScholarship : PowersClaimLayer
  dashiFiniteTheorem : PowersClaimLayer
  empiricalPopulationClaim : PowersClaimLayer

sourceNotDASHITheorem : sourceProposition ≡ dashiFiniteTheorem → ⊥
sourceNotDASHITheorem ()

reviewNotPrimarySource : reviewerInterpretation ≡ sourceProposition → ⊥
reviewNotPrimarySource ()

laterScholarshipNotRetroactivePowersClaim : laterScholarship ≡ sourceProposition → ⊥
laterScholarshipNotRetroactivePowersClaim ()

record PowersSourceBoundary : Set where
  constructor powers-source-boundary
  field
    publisherSummaryCountsAsPageLevelReceipt : Bool
    publisherSummaryCountsAsPageLevelReceiptIsFalse :
      publisherSummaryCountsAsPageLevelReceipt ≡ false
    reviewBecomesPrimarySource : Bool
    reviewBecomesPrimarySourceIsFalse : reviewBecomesPrimarySource ≡ false
    sourceCitationImportsFormalProof : Bool
    sourceCitationImportsFormalProofIsFalse :
      sourceCitationImportsFormalProof ≡ false
    laterScholarshipMayCrossPollinate : Bool
    laterScholarshipMayCrossPollinateIsTrue :
      laterScholarshipMayCrossPollinate ≡ true

canonicalPowersSourceBoundary : PowersSourceBoundary
canonicalPowersSourceBoundary =
  powers-source-boundary false refl false refl false refl true refl
