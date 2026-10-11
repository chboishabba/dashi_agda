module DASHI.Culture.PowersPlantationParadiseSourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- POWERS / PLANTATION TO PARADISE SOURCE ATLAS
--
-- Source propositions remain source-bound. Publisher summaries, scholarly
-- reviews, later edited collections, chapter locators, inspected public
-- excerpts and DASHI finite countermodels occupy different epistemic layers.
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
    "primary scholarly monograph for social casting, nonwhite participation, theatre architecture, repertoire, seating/audience structure, and revolutionary disruption in Guadeloupe, Martinique and Saint-Domingue; chapter/page locators below are separated from passage inspection"
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
-- Chapter/page locators recovered from the published table of contents/JSTOR
-- chapter surfaces. A locator is not itself evidence for every proposition in
-- the located pages.
------------------------------------------------------------------------

record ChapterPageLocator : Set where
  constructor chapter-page-locator
  field
    chapterTitle : String
    pageRange : String
    publicLocator : String
    passageInspected : Bool

open ChapterPageLocator public

chapter1ColonialHierarchyPages : ChapterPageLocator
chapter1ColonialHierarchyPages =
  chapter-page-locator
    "Chapter 1. Establishment of Colonial Hierarchy"
    "25-46"
    "JSTOR book table of contents / published contents"
    false

chapter2PoliticsAndPowerPages : ChapterPageLocator
chapter2PoliticsAndPowerPages =
  chapter-page-locator
    "Chapter 2. Politics and Power"
    "47-64"
    "https://www.jstor.org/stable/10.14321/j.ctt7zt6t5.8"
    true

chapter3ColonialSocietyAtTheTheatrePages : ChapterPageLocator
chapter3ColonialSocietyAtTheTheatrePages =
  chapter-page-locator
    "Chapter 3. Colonial Society at the Theatre"
    "65-84"
    "https://www.jstor.org/stable/10.14321/j.ctt7zt6t5.9"
    false

chapter4IntroducingTheStarsPages : ChapterPageLocator
chapter4IntroducingTheStarsPages =
  chapter-page-locator
    "Chapter 4. Introducing the Stars"
    "85-92"
    "https://www.jstor.org/stable/10.14321/j.ctt7zt6t5.10"
    false

chapter5BreakingThroughBarrierPages : ChapterPageLocator
chapter5BreakingThroughBarrierPages =
  chapter-page-locator
    "Chapter 5. Breaking through the Barrier"
    "93-104"
    "https://www.jstor.org/stable/10.14321/j.ctt7zt6t5.11"
    false

chapter6EscapeFromRealityPages : ChapterPageLocator
chapter6EscapeFromRealityPages =
  chapter-page-locator
    "Chapter 6. The Escape from Reality Continues"
    "105-112"
    "https://www.jstor.org/stable/10.14321/j.ctt7zt6t5.12"
    true

chapter7FinalePages : ChapterPageLocator
chapter7FinalePages =
  chapter-page-locator
    "Chapter 7. Finale: The Beginning of the End"
    "113-122"
    "https://www.jstor.org/stable/10.14321/j.ctt7zt6t5.13"
    true

appendix4TheatreDescriptionsPages : ChapterPageLocator
appendix4TheatreDescriptionsPages =
  chapter-page-locator
    "Appendix 4. Descriptions of Colonial Theatres"
    "149-156"
    "published table of contents"
    false

------------------------------------------------------------------------
-- Claim-layer boundary.
------------------------------------------------------------------------

data PowersClaimLayer : Set where
  sourceProposition : PowersClaimLayer
  reviewerInterpretation : PowersClaimLayer
  laterScholarship : PowersClaimLayer
  chapterLocatorOnly : PowersClaimLayer
  inspectedPublicExcerpt : PowersClaimLayer
  dashiFiniteTheorem : PowersClaimLayer
  empiricalPopulationClaim : PowersClaimLayer

sourceNotDASHITheorem : sourceProposition ≡ dashiFiniteTheorem → ⊥
sourceNotDASHITheorem ()

reviewNotPrimarySource : reviewerInterpretation ≡ sourceProposition → ⊥
reviewNotPrimarySource ()

laterScholarshipNotRetroactivePowersClaim : laterScholarship ≡ sourceProposition → ⊥
laterScholarshipNotRetroactivePowersClaim ()

locatorNotInspectedExcerpt : chapterLocatorOnly ≡ inspectedPublicExcerpt → ⊥
locatorNotInspectedExcerpt ()

record PowersSourceBoundary : Set where
  constructor powers-source-boundary
  field
    publisherSummaryCountsAsPageLevelReceipt : Bool
    publisherSummaryCountsAsPageLevelReceiptIsFalse :
      publisherSummaryCountsAsPageLevelReceipt ≡ false
    chapterRangeCountsAsInspectedPassage : Bool
    chapterRangeCountsAsInspectedPassageIsFalse :
      chapterRangeCountsAsInspectedPassage ≡ false
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
  powers-source-boundary false refl false refl false refl false refl true refl
