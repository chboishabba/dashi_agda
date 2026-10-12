module DASHI.Culture.PowersPlantationParadiseHistoricalClaimReceiptsExact where

open import DASHI.Core.Prelude

import DASHI.Culture.PowersPlantationParadiseSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- POWERS HISTORICAL CLAIM RECEIPTS
--
-- These receipts close the old undifferentiated "page recovery" residual by
-- separating three evidence levels:
--   * publisher/book-description observations;
--   * text actually exposed in a public JSTOR chapter excerpt;
--   * chapter/page locator only.
-- A locator is useful acquisition metadata but never becomes an inspected
-- passage by declaration.
------------------------------------------------------------------------

data HistoricalEvidenceKind : Set where
  publisherDescriptionEvidence : HistoricalEvidenceKind
  inspectedChapterExcerptEvidence : HistoricalEvidenceKind
  chapterLocatorOnlyEvidence : HistoricalEvidenceKind

record BoundedHistoricalClaimReceipt : Set where
  constructor bounded-historical-claim-receipt
  field
    locator : Atlas.ChapterPageLocator
    claim : String
    evidenceKind : HistoricalEvidenceKind
    sourceSurface : String
    promotesWholeChapter : Bool
    promotesWholeChapterIsFalse : promotesWholeChapter ≡ false
    promotesPopulationLaw : Bool
    promotesPopulationLawIsFalse : promotesPopulationLaw ≡ false

open BoundedHistoricalClaimReceipt public

------------------------------------------------------------------------
-- Book-level / publisher-grounded claims. These use the chapter locator for
-- acquisition routing but do not claim the chapter text itself was inspected.
------------------------------------------------------------------------

colonialHierarchyClaimReceipt : BoundedHistoricalClaimReceipt
colonialHierarchyClaimReceipt =
  bounded-historical-claim-receipt
    Atlas.chapter1ColonialHierarchyPages
    "Powers's published book description identifies an elaborate colonial system of social casting and treats the status of nonwhite artists as part of the historical object of study."
    publisherDescriptionEvidence
    "Michigan State University Press description / JSTOR book description"
    false refl
    false refl

colonialSocietyAtTheTheatreClaimReceipt : BoundedHistoricalClaimReceipt
colonialSocietyAtTheTheatreClaimReceipt =
  bounded-historical-claim-receipt
    Atlas.chapter3ColonialSocietyAtTheTheatrePages
    "The published book description states that Powers examines nonwhite participation together with theatre architecture, decor, repertoire, seating arrangements, and audience types."
    publisherDescriptionEvidence
    "Michigan State University Press description / JSTOR book description"
    false refl
    false refl

------------------------------------------------------------------------
-- Chapter 2 public excerpt: bounded to what the exposed chapter surface says.
------------------------------------------------------------------------

politicsAndPowerClaimReceipt : BoundedHistoricalClaimReceipt
politicsAndPowerClaimReceipt =
  bounded-historical-claim-receipt
    Atlas.chapter2PoliticsAndPowerPages
    "The public Chapter 2 excerpt distinguishes religious, military, and political colonial power and links their musical repertoires to maintaining peace, respect for social hierarchy, and promotion of French culture."
    inspectedChapterExcerptEvidence
    "JSTOR Chapter 2 public excerpt, pp. 47-64"
    false refl
    false refl

------------------------------------------------------------------------
-- Chapter 6 public excerpt: cultural spectacle as a governance instrument.
------------------------------------------------------------------------

escapeFromRealityClaimReceipt : BoundedHistoricalClaimReceipt
escapeFromRealityClaimReceipt =
  bounded-historical-claim-receipt
    Atlas.chapter6EscapeFromRealityPages
    "The public Chapter 6 excerpt states that colonial authorities encouraged and supported elaborate musical and dramatic activity as useful to their political goals, while colonial theatre architecture, decor, and costume could emulate metropolitan elaboration."
    inspectedChapterExcerptEvidence
    "JSTOR Chapter 6 public excerpt, pp. 105-112"
    false refl
    false refl

------------------------------------------------------------------------
-- Chapter 7 public excerpt: bounded revolutionary-period observation.
------------------------------------------------------------------------

finaleRevolutionClaimReceipt : BoundedHistoricalClaimReceipt
finaleRevolutionClaimReceipt =
  bounded-historical-claim-receipt
    Atlas.chapter7FinalePages
    "The public Chapter 7 excerpt reports a dramatic increase of interest in black Creole culture during the 1780s; the publisher description separately situates the conclusion amid slave uprisings, the French Revolution, and patriotic theatres."
    inspectedChapterExcerptEvidence
    "JSTOR Chapter 7 public excerpt, pp. 113-122 plus MSU Press book description"
    false refl
    false refl

------------------------------------------------------------------------
-- Locator-only receipts retain useful page acquisition without false passage
-- inspection. Chapters 4 and 5 remain routed, not silently paraphrased.
------------------------------------------------------------------------

introducingStarsLocatorReceipt : BoundedHistoricalClaimReceipt
introducingStarsLocatorReceipt =
  bounded-historical-claim-receipt
    Atlas.chapter4IntroducingTheStarsPages
    "Chapter 4 acquisition locator only; no uninspected passage-level proposition is promoted here."
    chapterLocatorOnlyEvidence
    "published table of contents / JSTOR chapter locator"
    false refl
    false refl

breakingBarrierLocatorReceipt : BoundedHistoricalClaimReceipt
breakingBarrierLocatorReceipt =
  bounded-historical-claim-receipt
    Atlas.chapter5BreakingThroughBarrierPages
    "Chapter 5 acquisition locator only; no uninspected passage-level proposition is promoted here."
    chapterLocatorOnlyEvidence
    "published table of contents / JSTOR chapter locator"
    false refl
    false refl

------------------------------------------------------------------------
-- Inspection/evidence coherence.
--
-- `passageInspected` is not allowed to drift independently of the evidence
-- kind.  Inspected evidence is inhabited exactly when the associated locator
-- carries `passageInspected = true`.
------------------------------------------------------------------------

InspectedEvidence : HistoricalEvidenceKind → Set
InspectedEvidence publisherDescriptionEvidence = ⊥
InspectedEvidence inspectedChapterExcerptEvidence = ⊤
InspectedEvidence chapterLocatorOnlyEvidence = ⊥

record InspectionEvidenceCoherent (receipt : BoundedHistoricalClaimReceipt) : Set where
  constructor inspection-evidence-coherent
  field
    evidenceImpliesInspected :
      InspectedEvidence (evidenceKind receipt) →
      Atlas.passageInspected (locator receipt) ≡ true
    inspectedImpliesEvidence :
      Atlas.passageInspected (locator receipt) ≡ true →
      InspectedEvidence (evidenceKind receipt)

open InspectionEvidenceCoherent public

colonialHierarchyInspectionCoherent :
  InspectionEvidenceCoherent colonialHierarchyClaimReceipt
colonialHierarchyInspectionCoherent =
  inspection-evidence-coherent (λ ()) (λ ())

colonialSocietyInspectionCoherent :
  InspectionEvidenceCoherent colonialSocietyAtTheTheatreClaimReceipt
colonialSocietyInspectionCoherent =
  inspection-evidence-coherent (λ ()) (λ ())

politicsAndPowerInspectionCoherent :
  InspectionEvidenceCoherent politicsAndPowerClaimReceipt
politicsAndPowerInspectionCoherent =
  inspection-evidence-coherent (λ _ → refl) (λ _ → tt)

escapeFromRealityInspectionCoherent :
  InspectionEvidenceCoherent escapeFromRealityClaimReceipt
escapeFromRealityInspectionCoherent =
  inspection-evidence-coherent (λ _ → refl) (λ _ → tt)

finaleRevolutionInspectionCoherent :
  InspectionEvidenceCoherent finaleRevolutionClaimReceipt
finaleRevolutionInspectionCoherent =
  inspection-evidence-coherent (λ _ → refl) (λ _ → tt)

introducingStarsInspectionCoherent :
  InspectionEvidenceCoherent introducingStarsLocatorReceipt
introducingStarsInspectionCoherent =
  inspection-evidence-coherent (λ ()) (λ ())

breakingBarrierInspectionCoherent :
  InspectionEvidenceCoherent breakingBarrierLocatorReceipt
breakingBarrierInspectionCoherent =
  inspection-evidence-coherent (λ ()) (λ ())

------------------------------------------------------------------------
-- Hard non-promotion boundary.
------------------------------------------------------------------------

data PageRangePromotesUninspectedPassage : Set where

pageRangeDoesNotPromoteUninspectedPassage :
  PageRangePromotesUninspectedPassage → ⊥
pageRangeDoesNotPromoteUninspectedPassage ()

record PowersHistoricalClaimBoundary : Set where
  constructor powers-historical-claim-boundary
  field
    locatorEqualsInspectedPassage : Bool
    locatorEqualsInspectedPassageIsFalse : locatorEqualsInspectedPassage ≡ false
    publicExcerptProvesWholeChapter : Bool
    publicExcerptProvesWholeChapterIsFalse : publicExcerptProvesWholeChapter ≡ false
    publisherDescriptionProvesNamedPersonBiography : Bool
    publisherDescriptionProvesNamedPersonBiographyIsFalse :
      publisherDescriptionProvesNamedPersonBiography ≡ false

canonicalPowersHistoricalClaimBoundary : PowersHistoricalClaimBoundary
canonicalPowersHistoricalClaimBoundary =
  powers-historical-claim-boundary false refl false refl false refl
