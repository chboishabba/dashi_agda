module DASHI.Biology.ParentalFearSourceAttributionExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Biology.EducationCorpusSourceRegistry as Sources
import DASHI.Biology.ParentalFearIndependentMobilityExact as Fear

------------------------------------------------------------------------
-- First-class attribution surface for the source formalised by
-- ParentalFearIndependentMobilityExact.
--
-- Preferred stable identifier:
--   DOI 10.1016/j.healthplace.2013.09.002
--   https://doi.org/10.1016/j.healthplace.2013.09.002
--
-- Full source:
--   Justen O'Connor; Alice Brown (2013).
--   "A qualitative study of 'fear' as a regulator of children's independent
--   physical activity in the suburbs."
--   Health & Place 24, 157-164.
--   DOI 10.1016/j.healthplace.2013.09.002.
--
-- This module exists so downstream imports do not have to inspect prose
-- comments to recover provenance.  Bibliographic identity is part of the
-- typed source surface.
------------------------------------------------------------------------

canonicalTitle : String
canonicalTitle =
  "A qualitative study of 'fear' as a regulator of children's independent physical activity in the suburbs"

canonicalAuthors : List String
canonicalAuthors = "Justen O'Connor" ∷ "Alice Brown" ∷ []

canonicalDOI : String
canonicalDOI = "10.1016/j.healthplace.2013.09.002"

canonicalDOIURL : String
canonicalDOIURL = "https://doi.org/10.1016/j.healthplace.2013.09.002"

canonicalJournal : String
canonicalJournal = "Health & Place"

canonicalYear : Nat
canonicalYear = 2013

canonicalVolumeIssue : String
canonicalVolumeIssue = "24"

canonicalPages : String
canonicalPages = "157-164"

registryTitleIsCanonical :
  Sources.paperTitle Sources.parentalFearIndependentMobilityPaper ≡ canonicalTitle
registryTitleIsCanonical = refl

registryAuthorsAreCanonical :
  Sources.paperAuthors Sources.parentalFearIndependentMobilityPaper ≡ canonicalAuthors
registryAuthorsAreCanonical = refl

registryDOIIsCanonical :
  Sources.paperDOI Sources.parentalFearIndependentMobilityPaper ≡ canonicalDOI
registryDOIIsCanonical = refl

registryJournalIsCanonical :
  Sources.paperJournal Sources.parentalFearIndependentMobilityPaper ≡ canonicalJournal
registryJournalIsCanonical = refl

registryYearIsCanonical :
  Sources.paperYear Sources.parentalFearIndependentMobilityPaper ≡ canonicalYear
registryYearIsCanonical = refl

registryVolumeIssueIsCanonical :
  Sources.paperVolumeIssue Sources.parentalFearIndependentMobilityPaper
  ≡ canonicalVolumeIssue
registryVolumeIssueIsCanonical = refl

registryPagesAreCanonical :
  Sources.paperPages Sources.parentalFearIndependentMobilityPaper ≡ canonicalPages
registryPagesAreCanonical = refl

formalisationUsesAttributedSource :
  Fear.sourcePaper Fear.canonicalParentalFearIndependentMobilitySource
  ≡ Sources.parentalFearIndependentMobilityPaper
formalisationUsesAttributedSource = refl

record ParentalFearSourceAttribution : Set where
  constructor mkParentalFearSourceAttribution
  field
    title : String
    authors : List String
    doi : String
    doiURL : String
    journal : String
    year : Nat
    volumeIssue : String
    pages : String
    registryPaper : Sources.PaperReference
    registryPaperIsCanonical :
      registryPaper ≡ Sources.parentalFearIndependentMobilityPaper
    formalisation : Fear.ParentalFearIndependentMobilitySource
    formalisationIsCanonical :
      formalisation ≡ Fear.canonicalParentalFearIndependentMobilitySource
    stableIdentifierPreferredWhenAvailable : Bool
    stableIdentifierPreferredWhenAvailableIsTrue :
      stableIdentifierPreferredWhenAvailable ≡ true
    attributionIsPartOfFormalSurface : Bool
    attributionIsPartOfFormalSurfaceIsTrue :
      attributionIsPartOfFormalSurface ≡ true
    reading : String

open ParentalFearSourceAttribution public

canonicalParentalFearSourceAttribution : ParentalFearSourceAttribution
canonicalParentalFearSourceAttribution =
  mkParentalFearSourceAttribution
    canonicalTitle
    canonicalAuthors
    canonicalDOI
    canonicalDOIURL
    canonicalJournal
    canonicalYear
    canonicalVolumeIssue
    canonicalPages
    Sources.parentalFearIndependentMobilityPaper refl
    Fear.canonicalParentalFearIndependentMobilitySource refl
    true refl
    true refl
    "Stable bibliographic provenance is a first-class part of the formal source surface: O'Connor and Brown, Health & Place 24 (2013), 157-164, DOI 10.1016/j.healthplace.2013.09.002. Downstream DASHI extensions retain this attribution rather than treating the formalised claims as source-free repository folklore."
