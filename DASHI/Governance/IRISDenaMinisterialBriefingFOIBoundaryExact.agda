module DASHI.Governance.IRISDenaMinisterialBriefingFOIBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- IRIS DENA / MINISTERIAL BRIEFING FOI BOUNDARY
--
-- Current public carrier is journalism reporting on an FOI search/result.
-- The underlying FOI schedule/returned documents are not encoded here as a
-- primary source because they have not been independently acquired in this lane.
------------------------------------------------------------------------

mwmFOIReport : Source.AttributedSource
mwmFOIReport = Source.mkNoDOISource
  "Rex Patrick"
  "Disingenuous. Minister blindsided as Australia stumbled into Iran war"
  "Michael West Media"
  "2026-05-12"
  "https://michaelwest.com.au/disingenuous-minister-blindsided-as-australia-stumbled-into-iran-war/"
  Source.newsSource
  "secondary investigative report stating an FOI request for Defence briefs to Minister Richard Marles found no briefs until after the IRIS Dena sinking; underlying FOI return is not independently acquired in this owner"
  Source.publicAttribution

record MinisterialBriefingFOIReceipt : Set where
  constructor ministerial-briefing-foi-receipt
  field
    source : Source.AttributedSource
    reportedNoPreEventBriefs : Bool
    reportedNoPreEventBriefsIsTrue :
      reportedNoPreEventBriefs ≡ true
    underlyingFOIReturnAcquired : Bool
    underlyingFOIReturnAcquiredIsFalse :
      underlyingFOIReturnAcquired ≡ false
    provesMinisterHadNoKnowledge : Bool
    provesMinisterHadNoKnowledgeIsFalse :
      provesMinisterHadNoKnowledge ≡ false
    provesDefenceHadNoKnowledge : Bool
    provesDefenceHadNoKnowledgeIsFalse :
      provesDefenceHadNoKnowledge ≡ false
    provesNoOtherCommunicationChannel : Bool
    provesNoOtherCommunicationChannelIsFalse :
      provesNoOtherCommunicationChannel ≡ false
    provesNoAustralianAgency : Bool
    provesNoAustralianAgencyIsFalse :
      provesNoAustralianAgency ≡ false

open MinisterialBriefingFOIReceipt public

canonicalReceipt : MinisterialBriefingFOIReceipt
canonicalReceipt =
  ministerial-briefing-foi-receipt
    mwmFOIReport
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

record PrimaryFOIResidual : Set where
  constructor primary-foi-residual
  field
    residualRef : String
    requiredObject : String
    currentReading : String
    currentSourceRole : String

open PrimaryFOIResidual public

primaryFOIResidual : PrimaryFOIResidual
primaryFOIResidual =
  primary-foi-residual
    "residual:iris-dena:ministerial-briefing-foi-primary"
    "FOI decision/schedule and released Defence briefing documents relied on by the May 2026 report"
    "secondary report says no Defence briefs to Marles were found until after the sinking"
    "secondary FOI-based investigative reporting"

data NoBriefMeansNoKnowledge : Set where
data NoMinisterBriefMeansNoDefenceKnowledge : Set where
data NoBriefMeansNoAgency : Set where
data JournalistFOISummaryEqualsPrimaryFOIReturn : Set where

noBriefDoesNotMeanNoKnowledge : NoBriefMeansNoKnowledge → ⊥
noBriefDoesNotMeanNoKnowledge ()

noMinisterBriefDoesNotMeanNoDefenceKnowledge :
  NoMinisterBriefMeansNoDefenceKnowledge → ⊥
noMinisterBriefDoesNotMeanNoDefenceKnowledge ()

noBriefDoesNotEraseAgency : NoBriefMeansNoAgency → ⊥
noBriefDoesNotEraseAgency ()

summaryDoesNotEqualPrimaryFOIReturn :
  JournalistFOISummaryEqualsPrimaryFOIReturn → ⊥
summaryDoesNotEqualPrimaryFOIReturn ()

mwmSnowball : Snowball.SourceRoleSnowballReceipt mwmFOIReport
mwmSnowball = Snowball.canonicalSourceRoleSnowballReceipt mwmFOIReport
