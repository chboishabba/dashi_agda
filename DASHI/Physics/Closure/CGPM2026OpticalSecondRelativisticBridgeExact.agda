module DASHI.Physics.Closure.CGPM2026OpticalSecondRelativisticBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.QuantumClockProperTimeRedshiftBridge as Redshift
import DASHI.Promotion.SIMetreFromSecondAndCAdapter as Metre

------------------------------------------------------------------------
-- 28th CGPM (2026) x relativistic optical-clock metrology
--
-- Authority is deliberately split:
--   * CGPM Resolution 4 (2026) owns the institutional policy state on work
--     toward a future definition of the second.
--   * BIPM's redefinition roadmap/FAQ owns the surrounding timeline and
--     performance-context summary used here.
--   * Bothwell/Ye 2022 owns its experiment only.
--   * DASHI owns this crosswalk to the existing proper-time/SI machinery.
--
-- Nothing in this module attributes DASHI's redshift/geodesy synthesis to the
-- CGPM or makes Bothwell/Ye responsible for CGPM policy.
------------------------------------------------------------------------

resolutionDOI : String
resolutionDOI = "10.59161/CGPM2026RES4E"

resolutionTitle : String
resolutionTitle = "On the future definition of the second"

resolutionAdoptionDate : String
resolutionAdoptionDate = "2026-10-15"

proposalTargetMeeting : String
proposalTargetMeeting = "29th CGPM (2030)"

targetComparisonUncertaintyOrder : String
targetComparisonUncertaintyOrder = "approaching 1e-18"

currentSISecondReference : String
currentSISecondReference = "SI second remains based on the fixed caesium-133 hyperfine frequency at this stage"

record CGPM2026OpticalSecondRelativisticBridge : Set₁ where
  field
    redshiftLaw : Redshift.QuantumClockProperTimeRedshiftBridge
    redshiftLawIsCanonical :
      redshiftLaw ≡ Redshift.canonicalQuantumClockProperTimeRedshiftBridge

    metreAdapter : Metre.SIMetreFromSecondAndCAdapter
    metreAdapterIsCanonical :
      metreAdapter ≡ Metre.canonicalSIMetreFromSecondAndCAdapter

    cgpmResolutionDOI : String
    adoptionDate : String
    proposalTargetMeeting : String
    targetComparisonUncertaintyOrder : String

    cgpmPolicyAuthorityIngested : Bool
    cgpmPolicyAuthorityIngestedIsTrue : cgpmPolicyAuthorityIngested ≡ true

    opticalStandardsOutperformCurrentPrimaryRealization : Bool
    opticalStandardsOutperformCurrentPrimaryRealizationIsTrue :
      opticalStandardsOutperformCurrentPrimaryRealization ≡ true

    opticalClockComparisonsNeedRelativisticPotentialAccountingAtTargetScale : Bool
    opticalClockComparisonsNeedRelativisticPotentialAccountingAtTargetScaleIsTrue :
      opticalClockComparisonsNeedRelativisticPotentialAccountingAtTargetScale ≡ true

    futureSecondRedefinitionAlreadyImplemented : Bool
    futureSecondRedefinitionAlreadyImplementedIsFalse :
      futureSecondRedefinitionAlreadyImplemented ≡ false

    bothwellYeEstablishesCGPMPolicy : Bool
    bothwellYeEstablishesCGPMPolicyIsFalse :
      bothwellYeEstablishesCGPMPolicy ≡ false

    cgpmResolutionEstablishesBothwellYeExperiment : Bool
    cgpmResolutionEstablishesBothwellYeExperimentIsFalse :
      cgpmResolutionEstablishesBothwellYeExperiment ≡ false

    geodeticPotentialReceiptStillConsumerSpecific : Bool
    geodeticPotentialReceiptStillConsumerSpecificIsTrue :
      geodeticPotentialReceiptStillConsumerSpecific ≡ true

    reading : List String

open CGPM2026OpticalSecondRelativisticBridge public

canonicalCGPM2026OpticalSecondRelativisticBridge :
  CGPM2026OpticalSecondRelativisticBridge
canonicalCGPM2026OpticalSecondRelativisticBridge = record
  { redshiftLaw = Redshift.canonicalQuantumClockProperTimeRedshiftBridge
  ; redshiftLawIsCanonical = refl
  ; metreAdapter = Metre.canonicalSIMetreFromSecondAndCAdapter
  ; metreAdapterIsCanonical = refl
  ; cgpmResolutionDOI = resolutionDOI
  ; adoptionDate = resolutionAdoptionDate
  ; proposalTargetMeeting = "29th CGPM (2030)"
  ; targetComparisonUncertaintyOrder = "approaching 1e-18"
  ; cgpmPolicyAuthorityIngested = true
  ; cgpmPolicyAuthorityIngestedIsTrue = refl
  ; opticalStandardsOutperformCurrentPrimaryRealization = true
  ; opticalStandardsOutperformCurrentPrimaryRealizationIsTrue = refl
  ; opticalClockComparisonsNeedRelativisticPotentialAccountingAtTargetScale = true
  ; opticalClockComparisonsNeedRelativisticPotentialAccountingAtTargetScaleIsTrue = refl
  ; futureSecondRedefinitionAlreadyImplemented = false
  ; futureSecondRedefinitionAlreadyImplementedIsFalse = refl
  ; bothwellYeEstablishesCGPMPolicy = false
  ; bothwellYeEstablishesCGPMPolicyIsFalse = refl
  ; cgpmResolutionEstablishesBothwellYeExperiment = false
  ; cgpmResolutionEstablishesBothwellYeExperimentIsFalse = refl
  ; geodeticPotentialReceiptStillConsumerSpecific = true
  ; geodeticPotentialReceiptStillConsumerSpecificIsTrue = refl
  ; reading =
      "CGPM Resolution 4 (2026), adopted 15 October 2026, is the institutional authority for continued work toward a future definition of the second; it does not itself redefine the second immediately."
      ∷ "BIPM roadmap material places a proposal at the 29th CGPM in 2030 and describes international optical-standard comparison capability approaching 1e-18 as part of the maturation context."
      ∷ "At those scales relativistic potential accounting is operational metrology rather than an optional narrative annotation, but the required geopotential/transfer receipt remains consumer- and comparison-specific."
      ∷ "Bothwell/Ye supplies an experimental redshift reference; CGPM/BIPM supplies metrology-policy authority; DASHI supplies only the explicit crosswalk between these independently attributed objects."
      ∷ []
  }
