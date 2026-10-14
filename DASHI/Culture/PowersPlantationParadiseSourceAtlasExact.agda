module DASHI.Culture.PowersPlantationParadiseSourceAtlasExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- POWERS / PLANTATION TO PARADISE SOURCE ATLAS
--
-- Source propositions remain source-bound. Publisher summaries, scholarly
-- reviews, later edited collections, archival catalogues, institutional
-- research databases, inspected public excerpts and DASHI finite countermodels
-- occupy different epistemic layers.
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

prestRacialScaleSource : Source.AttributedSource
prestRacialScaleSource =
  Source.mkNoDOISource
    "Julia Tamsin Prest"
    "Performing the racial scale: from colonial Saint-Domingue to contemporary Hollywood"
    "Insights 10, article 7; peer-reviewed accepted manuscript in University of St Andrews Research Repository"
    "2017"
    "https://research-repository.st-andrews.ac.uk/handle/10023/12607"
    Source.academicArticleSource
    "peer-reviewed same-object secondary evidence for Minette, segregated theatre seating, public-stage inclusion, press naming/status language and the limits of theatrical social mobility; citations to Moreau de Saint-Mery and Affiches Americaines remain source-local"
    Source.publicAttribution

prestIphigenieSource : Source.AttributedSource
prestIphigenieSource =
  Source.mkDOISource
    "Julia Tamsin Prest"
    "Iphigenie en Haiti: performing Gluck's Paris operas in the French colonial Caribbean"
    "Eighteenth-Century Music 14(1):13-29"
    "2017"
    "10.1017/S1478570616000282"
    "https://doi.org/10.1017/S1478570616000282"
    Source.academicArticleSource
    "peer-reviewed source for mixed but segregated Saint-Domingue audiences, local performance conditions, and documented performers of colour in the Gluck repertoire; later scholarship, not a Powers proposition"
    Source.publicAttribution

clayStagestruckSource : Source.AttributedSource
clayStagestruckSource =
  Source.mkDOISource
    "Lauren R. Clay"
    "The Production of Theater in the Colonies"
    "Stagestruck: The Business of Theater in Eighteenth-Century France and Its Colonies, chapter 7, pp. 195-224"
    "2013"
    "10.7591/cornell/9780801450389.003.0007"
    "https://doi.org/10.7591/cornell/9780801450389.003.0007"
    Source.academicChapterSource
    "scholarly business-history source for colonial theatre operations, capacity, staffing, commercial pressure, participation by free people of colour and the Port-au-Prince theatre economy; does not by itself identify distribution of surplus or burden"
    Source.publicAttribution

theatreSaintDomingueProjectSource : Source.AttributedSource
theatreSaintDomingueProjectSource =
  Source.mkNoDOISource
    "Julia Prest and Theatre in Saint-Domingue project"
    "Theatre in Saint-Domingue, 1764-1791"
    "University of St Andrews School of Modern Languages research project and performance database"
    "2020s"
    "https://www.st-andrews.ac.uk/modern-languages/research/projects/theatre-in-saint-domingue/"
    Source.institutionalSource
    "institutional research database built from local newspaper announcements between 1764 and 1791; source-acquisition surface for performance-level chronology, venues, repertoire and named participants where records survive"
    Source.publicAttribution

affichesAmericanesArchiveSource : Source.AttributedSource
affichesAmericanesArchiveSource =
  Source.mkNoDOISource
    "Imprimerie royale, Saint-Domingue"
    "Affiches americaines and Supplement aux Affiches americaines"
    "Colonial Saint-Domingue newspaper series, 1766-1790; BnF catalogue FRBNF32683014 and related digitised holdings"
    "1766-1790"
    "https://catalogue.bnf.fr/ark:/12148/cb32683014r"
    Source.archivalSource
    "primary newspaper corpus for performance announcements, public naming, advertisements and other contemporaneous notices; catalogue identity does not prove the content of any uninspected issue"
    Source.publicAttribution

lamecaSaintDomingueOperaSource : Source.AttributedSource
lamecaSaintDomingueOperaSource =
  Source.mkNoDOISource
    "Mediatheque Caraibe / Laméca"
    "Saint-Domingue et l'opera-comique"
    "La musique coloniale des Antilles francaises au 18eme siecle"
    "undated public digital dossier"
    "https://www.lameca.org/publications-numeriques/dossiers-et-articles/la-musique-coloniale-des-antilles-francaises-au-18eme-siecle/iii-saint-domingue-et-lopera-comique/"
    Source.institutionalSource
    "institutional secondary presentation preserving the 1782 Port-au-Prince theatre-plan archival locator ANOM FM F3 296 E 75 and contemporaneous-source quotations; useful for venue geometry, not a substitute for inspecting the archive original"
    Source.publicAttribution

allPowersSources : List Source.AttributedSource
allPowersSources =
  powersBookSource
  ∷ mondelliReviewSource
  ∷ leichmanBenacGirouxSource
  ∷ prestRacialScaleSource
  ∷ prestIphigenieSource
  ∷ clayStagestruckSource
  ∷ theatreSaintDomingueProjectSource
  ∷ affichesAmericanesArchiveSource
  ∷ lamecaSaintDomingueOperaSource
  ∷ []

powersSourceAtlas : Source.AttributedSourceAtlas
powersSourceAtlas =
  Source.mkSourceAtlas
    "Powers Plantation to Paradise source atlas"
    "DASHI.Culture.PowersPlantationParadiseSourceAtlasExact"
    allPowersSources
    "bounded attribution for Powers 2014, Mondelli 2016, later theatre/slavery scholarship, Prest's peer-reviewed same-object Saint-Domingue work, Clay's theatre-business history, the St Andrews performance database, Affiches Americaines archival corpus identity and the Laméca/ANOM theatre-plan locator"

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
    true

chapter5BreakingThroughBarrierPages : ChapterPageLocator
chapter5BreakingThroughBarrierPages =
  chapter-page-locator
    "Chapter 5. Breaking through the Barrier"
    "93-104"
    "https://www.jstor.org/stable/10.14321/j.ctt7zt6t5.11"
    true

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
