module DASHI.Cognition.CCDCOEP3GCC1993DirectionDiscriminatorExact where

------------------------------------------------------------------------
-- ORIGINAL SOURCE ATTRIBUTION AND DIRECTION CONTROL
--
-- Climate Files / Climate Investigations Center catalogues:
--  * Boyce Rensberger, "'Greenhouse Effect' Seems Benign So Far",
--    The Washington Post, 1 June 1993 (original journalist/article).
--  * John Shlaes / GCC, 30 June 1993 response to that earlier article,
--    archived as "Patrick Michaels 'Benign Greenhouse' News Release".
--  * Original July press clipping featuring Christy/Spencer, later
--    referenced in GCC September Climate Watch bulletin.
--
-- Thus press -> GCC response is documented by catalogue descriptions.
-- GCC response -> the EARLIER 1 June article is not an admissible
-- historical direction. Mentioning a clipping later is not proof of
-- influencing its original authorship or publication.
--
-- These are transcribed catalogue relations, NOT authenticated PDF
-- bytes or independent causal audience effect estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.CCDCOEP3GCC1993SourceChainExact as Source

data OriginalSourceObject : Set where
  rensbergerWashingtonPostJune1 : OriginalSourceObject
  shlaesGCCResponseJune30 : OriginalSourceObject
  julyWashingtonPostClipping : OriginalSourceObject
  septemberGCCBulletin : OriginalSourceObject

data OriginalAuthor : Set where
  washingtonPostJournalist : OriginalAuthor
  gccCommunicationsOffice : OriginalAuthor

originalAuthor : OriginalSourceObject → OriginalAuthor
originalAuthor rensbergerWashingtonPostJune1 = washingtonPostJournalist
originalAuthor shlaesGCCResponseJune30 = gccCommunicationsOffice
originalAuthor julyWashingtonPostClipping = washingtonPostJournalist
originalAuthor septemberGCCBulletin = gccCommunicationsOffice

journalistNotGCCHistoricalAuthor :
  originalAuthor rensbergerWashingtonPostJune1
  ≡ originalAuthor shlaesGCCResponseJune30 → ⊥
journalistNotGCCHistoricalAuthor ()

data HistoricalSourceRelation : OriginalSourceObject →
                                OriginalSourceObject → Set where
  juneArticleReferencedByGCCResponse :
    HistoricalSourceRelation
      rensbergerWashingtonPostJune1
      shlaesGCCResponseJune30
  juneArticleAlsoReferencedInSeptemberBulletin :
    HistoricalSourceRelation
      rensbergerWashingtonPostJune1
      septemberGCCBulletin
  julyClippingReferencedInSeptemberBulletin :
    HistoricalSourceRelation
      julyWashingtonPostClipping
      septemberGCCBulletin

-- A reverse edge cannot be manufactured from the source relations.
responseCannotBeSourceOfEarlierArticle :
  HistoricalSourceRelation
    shlaesGCCResponseJune30
    rensbergerWashingtonPostJune1 → ⊥
responseCannotBeSourceOfEarlierArticle ()

septemberBulletinNotProvenSourceOfJulyPublication :
  HistoricalSourceRelation
    septemberGCCBulletin
    julyWashingtonPostClipping → ⊥
septemberBulletinNotProvenSourceOfJulyPublication ()

-- Distinguish kinds of temporal evidence from measured mechanisms.
-- Source date conflict: The Washington Post original article page displays
-- 31 May 1993, whereas the archive URL and Climate Files identify 1 June.
-- This metadata conflict is retained: either date is before June 30.
-- Both appearances remain as distinct source-specific observations;
-- neither is a proof of original publication bytes being authenticated.

data ArticleDateAssertion : Set where
  washingtonPostPageMay31 : ArticleDateAssertion
  washingtonPostArchiveJune1 : ArticleDateAssertion

sourceDateAssertionDistinct :
  washingtonPostPageMay31 ≡ washingtonPostArchiveJune1 → ⊥
sourceDateAssertionDistinct ()

-- The newspaper article itself reports competing scientific positions.
-- The reader must not fuse the journalist with either interview subject.
data ArticleVoice : Set where
  originalJournalist : ArticleVoice
  quotedPatrickMichaels : ArticleVoice
  quotedJamesHansen : ArticleVoice

hansenNotMichaels : quotedJamesHansen ≡ quotedPatrickMichaels → ⊥
hansenNotMichaels ()

data SourceLinkGrade : Set where
  sourceMentionsEarlierText : SourceLinkGrade
  independentEditorialUptake : SourceLinkGrade
  measuredExposureEffect : SourceLinkGrade

sourceDirectionEvidenceGrade : SourceLinkGrade
sourceDirectionEvidenceGrade = sourceMentionsEarlierText

sourceMentionNotEditorialUptake :
  sourceDirectionEvidenceGrade ≡ independentEditorialUptake → ⊥
sourceMentionNotEditorialUptake ()

sourceMentionNotAudienceEffect :
  sourceDirectionEvidenceGrade ≡ measuredExposureEffect → ⊥
sourceMentionNotAudienceEffect ()

-- No source-specific instance of audience effects or operational
-- targeting is constructed in this bounded historical stage owner.
