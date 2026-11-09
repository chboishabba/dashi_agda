module DASHI.Cognition.CCDCOEP3GCC1993PreResponseExpandedExact where

------------------------------------------------------------------------
-- ORIGINAL HISTORICAL OWNERSHIP / SOURCE-GRADE BOUNDARY
--
-- GCC 8 Mar 1993 position statement, 10 Mar release, Jan press letter;
-- original sources described and excerpts selected by Climate Files.
-- c.1993 GCC "What the Experts Say" brochure: no exact day is known.
-- The original GCC statement and individual named scientific quotations
-- remain attributable to their respective authors/speakers.
-- DASHI owns only the finite date/status comparison.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.CCDCOEP3GCC1993PreResponseBaselineExact as Earlier

data OriginalGCCSource : Set where
  januaryPressLetter : OriginalGCCSource
  marchEightPolicyStatement : OriginalGCCSource
  marchTenModelRelease : OriginalGCCSource
  undatedExpertSelectionBrochure : OriginalGCCSource
  junePressResponse : OriginalGCCSource

data DatePrecision : Set where
  exactArchiveCalendarDay : DatePrecision
  circaYearNoOrderedDay : DatePrecision

datePrecision : OriginalGCCSource → DatePrecision
datePrecision januaryPressLetter = exactArchiveCalendarDay
datePrecision marchEightPolicyStatement = exactArchiveCalendarDay
datePrecision marchTenModelRelease = exactArchiveCalendarDay
datePrecision undatedExpertSelectionBrochure = circaYearNoOrderedDay
datePrecision junePressResponse = exactArchiveCalendarDay

data ArchivedBefore : OriginalGCCSource → OriginalGCCSource → Set where
  janBeforeMarchEight : ArchivedBefore januaryPressLetter marchEightPolicyStatement
  marchEightBeforeMarchTen : ArchivedBefore marchEightPolicyStatement marchTenModelRelease
  marchTenBeforeJune : ArchivedBefore marchTenModelRelease junePressResponse

-- There is deliberately NO temporal edge orienting the c.1993 brochure.
undatedBrochureNotAnExactDay :
  datePrecision undatedExpertSelectionBrochure
  ≡ exactArchiveCalendarDay → ⊥
undatedBrochureNotAnExactDay ()

marchEightSourcePrecedesModelRelease :
  ArchivedBefore marchEightPolicyStatement marchTenModelRelease
marchEightSourcePrecedesModelRelease = marchEightBeforeMarchTen

reverseOrderingNotInSourceGraph :
  ArchivedBefore junePressResponse marchEightPolicyStatement → ⊥
reverseOrderingNotInSourceGraph ()

data SourceGrade : Set where
  archiveCatalogueDescription : SourceGrade
  archiveSelectedAttributedExcerpt : SourceGrade
  independentlyReviewedWholeOriginal : SourceGrade
  independentRecipientObservation : SourceGrade

selectedPolicyGrade : SourceGrade
selectedPolicyGrade = archiveSelectedAttributedExcerpt

marchPolicySelectedQuoteNotCompleteOriginal :
  selectedPolicyGrade ≡ independentlyReviewedWholeOriginal → ⊥
marchPolicySelectedQuoteNotCompleteOriginal ()

noRecipientEffectFromSelectedQuote :
  selectedPolicyGrade ≡ independentRecipientObservation → ⊥
noRecipientEffectFromSelectedQuote ()

-- Source-grade proof only: it does not adjudicate the validity of the
-- underlying GCC policy claims, authors' knowledge, or hostile purpose.
