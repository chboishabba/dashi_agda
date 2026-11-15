module DASHI.Cognition.CCDCOEP3GCC1993PreResponseBaselineExact where

------------------------------------------------------------------------
-- ORIGINAL GCC 1993 PRE-RESPONSE BASELINE
--
-- Climate Files archival record: 10 March 1993 GCC Natural Warming,
-- Models, and National Action Plan News Release.
-- https://www.climatefiles.com/denial-groups/global-climate-coalition-collection/1993-natural-warming-models-national-action-plan/
-- A GCC communication predates Rensberger's May 31 / June 1 article,
-- Hansen's June 8 rebuttal, and Shlaes' June 30 press response.
-- This blocks classification of the JUNE RESPONSE as the unique
-- beginning of the GCC's public climate-model messaging. The archived
-- title does not authenticate the content of the unread March PDF.
-- Attribution: GCC original communicator; Climate Files catalogue.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data Stage : Set where
  marchGCCRelease : Stage
  rensbergerReport : Stage
  hansenCorrection : Stage
  juneGCCResponse : Stage
  septemberGCCBulletin : Stage

data AuthorRole : Set where
  originalCoalition : AuthorRole
  independentReporter : AuthorRole
  independentScientist : AuthorRole

author : Stage → AuthorRole
author marchGCCRelease = originalCoalition
author rensbergerReport = independentReporter
author hansenCorrection = independentScientist
author juneGCCResponse = originalCoalition
author septemberGCCBulletin = originalCoalition

data Before : Stage → Stage → Set where
  marchBeforeReport : Before marchGCCRelease rensbergerReport
  reportBeforeHansen : Before rensbergerReport hansenCorrection
  hansenBeforeJune : Before hansenCorrection juneGCCResponse
  juneBeforeSeptember : Before juneGCCResponse septemberGCCBulletin
  marchBeforeJune : Before marchGCCRelease juneGCCResponse

juneResponseCannotPrecedeMarchOriginal :
  Before juneGCCResponse marchGCCRelease → ⊥
juneResponseCannotPrecedeMarchOriginal ()

marchOriginalNotWrittenByReporter :
  author marchGCCRelease ≡ author rensbergerReport → ⊥
marchOriginalNotWrittenByReporter ()

-- Catalogue subject matter is not a coded quantitative baseline,
-- exposure receipt, newspaper causation, or hostility judgment.
data SourceGrade : Set where
  catalogueIndexedOriginal : SourceGrade
  independentlyCodedOriginalText : SourceGrade
  identifiedAudienceResponse : SourceGrade

marchGrade : SourceGrade
marchGrade = catalogueIndexedOriginal

catalogueNotCodedBaseline :
  marchGrade ≡ independentlyCodedOriginalText → ⊥
catalogueNotCodedBaseline ()

catalogueNotAudienceTreatment :
  marchGrade ≡ identifiedAudienceResponse → ⊥
catalogueNotAudienceTreatment ()
