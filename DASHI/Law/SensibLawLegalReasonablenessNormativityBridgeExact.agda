module DASHI.Law.SensibLawLegalReasonablenessNormativityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.InstitutionalNormSituatedReasonablenessBridgeExact as NormBridge
import DASHI.Core.InstitutionalNormProductionExact as NormProduction
import DASHI.Law.SensibLawLegalReasonablenessExact as LegalReason

------------------------------------------------------------------------
-- LEGAL REASONABLENESS × NORM PRODUCTION
--
-- The legal inquiry may require a court to apply a present statutory/doctrinal
-- standard while political/historical critique asks how the standard, factor
-- set or baseline was produced.  Those are distinct consumers.  Neither legal
-- application nor judicial restraint automatically proves political neutrality
-- or moral endorsement; political critique likewise does not automatically
-- establish legal invalidity.
------------------------------------------------------------------------

parentLegalReasonablenessBoundary : LegalReason.LegalReasonablenessBoundary
parentLegalReasonablenessBoundary = LegalReason.canonicalLegalReasonablenessBoundary

parentNormProductionReasonablenessBoundary :
  NormBridge.InstitutionalNormReasonablenessBoundary
parentNormProductionReasonablenessBoundary =
  NormBridge.canonicalInstitutionalNormReasonablenessBoundary

record LegalReasonablenessNormativityBoundary : Set where
  constructor legalReasonablenessNormativityBoundary
  field
    legalReasonablenessParentReused : Bool
    normProductionReasonablenessBridgeReused : Bool
    lawfulRangeAutomaticallyPoliticalNeutrality : Bool
    legallyRelevantFactorSetAutomaticallyValueFree : Bool
    judicialRestraintAutomaticallyNormativeEndorsement : Bool
    courtApplyingStatuteAutomaticallyApprovesStatutoryPolicy : Bool
    politicalCritiqueAutomaticallyLegalInvalidity : Bool
    historicalProductionCritiqueAutomaticallyMeritsReview : Bool
    doctrinalReasonablenessAutomaticallyOrdinaryLanguageReasonableness : Bool
    legalApplicationAndNormativeCritiqueCanRemainDistinct : Bool

open LegalReasonablenessNormativityBoundary public

canonicalLegalReasonablenessNormativityBoundary :
  LegalReasonablenessNormativityBoundary
canonicalLegalReasonablenessNormativityBoundary =
  legalReasonablenessNormativityBoundary
    true
    true
    false
    false
    false
    false
    false
    false
    false
    true


------------------------------------------------------------------------
-- META 2026 SETTLEMENT: SOURCE-BOUNDED NORM-TRANSMISSION CALIBRATION
--
-- Primary public calibration:
-- Meta, 26 August 2026, updated 27 August 2026:
-- https://about.fb.com/news/2026/08/agreement-with-state-attorneys-general-supporting-teens/
--
-- California Department of Justice, 26 August 2026:
-- https://www.oag.ca.gov/news/press-releases/attorney-general-bonta-secures-transformative-17-billion-settlement-meta
--
-- JMD / introsp3ctor poster provenance:
-- https://x.com/introsp3ctor/status/2092930669177446418
--
-- The poster is interpretive provenance. It is not legal authority.
------------------------------------------------------------------------

record Meta2026SettlementNormCalibration : Set where
  constructor meta2026-settlement-norm-calibration
  field
    transmissionBoundary : NormProduction.SettlementTransmissionBoundary
    metaOfficialSource : String
    californiaAGSource : String
    jmdPosterProvenance : String
    competitorAdoptionConditionsPartOfPaymentStructure : Bool
    competitorAdoptionConditionsPartOfPaymentStructureIsTrue :
      competitorAdoptionConditionsPartOfPaymentStructure ≡ true
    officialMetaSourceStatesIndustryWideAdoptionAim : Bool
    officialMetaSourceStatesIndustryWideAdoptionAimIsTrue :
      officialMetaSourceStatesIndustryWideAdoptionAim ≡ true
    settlementAloneLegallyBindsTikTokOrYouTube : Bool
    settlementAloneLegallyBindsTikTokOrYouTubeIsFalse :
      settlementAloneLegallyBindsTikTokOrYouTube ≡ false
    settlementCreatesFederalStatute : Bool
    settlementCreatesFederalStatuteIsFalse :
      settlementCreatesFederalStatute ≡ false
    settlementCreatesSupremeCourtHolding : Bool
    settlementCreatesSupremeCourtHoldingIsFalse :
      settlementCreatesSupremeCourtHolding ≡ false
    jmdPosterCreatesLegalAuthority : Bool
    jmdPosterCreatesLegalAuthorityIsFalse :
      jmdPosterCreatesLegalAuthority ≡ false

open Meta2026SettlementNormCalibration public

canonicalMeta2026SettlementNormCalibration :
  Meta2026SettlementNormCalibration
canonicalMeta2026SettlementNormCalibration =
  meta2026-settlement-norm-calibration
    NormProduction.canonicalSettlementTransmissionBoundary
    "Meta — Agreement With Bipartisan Attorneys General, 2026-08-26, updated 2026-08-27"
    "California DOJ — Attorney General Bonta Meta settlement release, 2026-08-26"
    "JMD / introsp3ctor — California uber alles poster, X post 2092930669177446418"
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
