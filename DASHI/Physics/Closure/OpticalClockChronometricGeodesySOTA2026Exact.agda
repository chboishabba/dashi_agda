module DASHI.Physics.Closure.OpticalClockChronometricGeodesySOTA2026Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CLAIM-RELATIVE OPTICAL-CLOCK / CHRONOMETRIC-GEODESY SOTA ATLAS (2026)
--
-- Three orthogonal capability coordinates are kept separate:
--   1. long-baseline chronometric leveling against independent geodesy;
--   2. deployed/autonomous optical-clock robustness;
--   3. transportable 1e-18-class interspecies comparison reproducibility.
--
-- The sources do not mutually inherit one another's measurements. In
-- particular deployment robustness is not chronometric-height accuracy, and a
-- frequency-transfer standard is not by itself a geopotential model.
------------------------------------------------------------------------

record SOTAStudy : Set where
  field
    citationLabel : String
    persistentId : String
    evidenceRole : String
    peerReviewed : Bool
    sourceCeiling : String

open SOTAStudy public

longDistanceChronometricLeveling : SOTAStudy
longDistanceChronometricLeveling = record
  { citationLabel = "Grotti et al., Long-distance chronometric leveling with a portable optical clock, Physical Review Applied 21 L061001 (2024)"
  ; persistentId = "10.1103/PhysRevApplied.21.L061001"
  ; evidenceRole = "457-km optical-clock comparison via interferometric fibre link with independent geodetic comparison"
  ; peerReviewed = true
  ; sourceCeiling = "same-study chronometric geopotential comparison; does not generalise to arbitrary links, clocks or height datums"
  }

mobileClockSeaTrial : SOTAStudy
mobileClockSeaTrial = record
  { citationLabel = "Hilton et al., Demonstration of a mobile optical clock ensemble at sea, Nature Communications 16 6063 (2025)"
  ; persistentId = "10.1038/s41467-025-61140-2"
  ; evidenceRole = "three portable optical clocks operated autonomously during a naval sea trial"
  ; peerReviewed = true
  ; sourceCeiling = "deployment robustness and frequency-output performance; not a chronometric-geodesy accuracy measurement"
  }

transportableInterspeciesComparison : SOTAStudy
transportableInterspeciesComparison = record
  { citationLabel = "Vishwakarma et al., Interspecies clock comparison below 5e-18 uncertainty with a transportable clock (2026 preprint)"
  ; persistentId = "arXiv:2608.01916"
  ; evidenceRole = "transportable 87Sr versus stationary 171Yb+ optical-frequency-ratio comparison over repeated campaigns"
  ; peerReviewed = false
  ; sourceCeiling = "preprint-level transportable frequency-ratio reproducibility; not yet peer-reviewed and not a geopotential measurement"
  }

canonicalSOTAStudies : List SOTAStudy
canonicalSOTAStudies =
  longDistanceChronometricLeveling
  ∷ mobileClockSeaTrial
  ∷ transportableInterspeciesComparison
  ∷ []

longBaselineKilometres : Nat
longBaselineKilometres = 457

heightEquivalentUncertaintyCentimetres : Nat
heightEquivalentUncertaintyCentimetres = 27

unsupervisedSeaOperationDays : Nat
unsupervisedSeaOperationDays = 21

seaTrialDistanceKilometres : Nat
seaTrialDistanceKilometres = 150

-- 4.3e-18 represented as tenths of 1e-18.
transportableRatioFractionalUncertaintyE18Tenths : Nat
transportableRatioFractionalUncertaintyE18Tenths = 43

transportableResultIsPreprint : Bool
transportableResultIsPreprint = true

sourceDeploymentRobustnessNonCollapse : Bool
sourceDeploymentRobustnessNonCollapse = true

sourceFrequencyTransferNonCollapse : Bool
sourceFrequencyTransferNonCollapse = true

record OpticalClockChronometricGeodesySOTAAtlas : Set where
  field
    studies : List SOTAStudy

    longBaselineChronometricLevelingObserved : Bool
    longBaselineChronometricLevelingObservedIsTrue :
      longBaselineChronometricLevelingObserved ≡ true

    autonomousDeployedOpticalClockOperationObserved : Bool
    autonomousDeployedOpticalClockOperationObservedIsTrue :
      autonomousDeployedOpticalClockOperationObserved ≡ true

    transportableE18ClassComparisonReported : Bool
    transportableE18ClassComparisonReportedIsTrue :
      transportableE18ClassComparisonReported ≡ true

    deploymentRobustnessIsNotChronometricAccuracy : Bool
    deploymentRobustnessIsNotChronometricAccuracyIsTrue :
      deploymentRobustnessIsNotChronometricAccuracy ≡ true

    frequencyTransferIsNotGeopotentialKnowledge : Bool
    frequencyTransferIsNotGeopotentialKnowledgeIsTrue :
      frequencyTransferIsNotGeopotentialKnowledge ≡ true

    crossStudySameObjectIdentity : Bool
    crossStudySameObjectIdentityIsFalse : crossStudySameObjectIdentity ≡ false

    reading : List String

open OpticalClockChronometricGeodesySOTAAtlas public

canonicalOpticalClockChronometricGeodesySOTAAtlas :
  OpticalClockChronometricGeodesySOTAAtlas
canonicalOpticalClockChronometricGeodesySOTAAtlas = record
  { studies = canonicalSOTAStudies
  ; longBaselineChronometricLevelingObserved = true
  ; longBaselineChronometricLevelingObservedIsTrue = refl
  ; autonomousDeployedOpticalClockOperationObserved = true
  ; autonomousDeployedOpticalClockOperationObservedIsTrue = refl
  ; transportableE18ClassComparisonReported = true
  ; transportableE18ClassComparisonReportedIsTrue = refl
  ; deploymentRobustnessIsNotChronometricAccuracy = sourceDeploymentRobustnessNonCollapse
  ; deploymentRobustnessIsNotChronometricAccuracyIsTrue = refl
  ; frequencyTransferIsNotGeopotentialKnowledge = sourceFrequencyTransferNonCollapse
  ; frequencyTransferIsNotGeopotentialKnowledgeIsTrue = refl
  ; crossStudySameObjectIdentity = false
  ; crossStudySameObjectIdentityIsFalse = refl
  ; reading =
      "Grotti et al. 2024 provide the long-baseline chronometric-geodesy coordinate: a 457-km optical-clock comparison with chronometric geopotential uncertainty equivalent to 27 cm height and an independent conventional-geodesy comparator."
      ∷ "Hilton et al. 2025 provide a deployment coordinate: three portable optical clocks operated autonomously at sea for 21 days over roughly 150 km; this is robustness/PNT evidence, not a height-accuracy result."
      ∷ "Vishwakarma et al. 2026 report a transportable 87Sr/171Yb+ comparison at 4.3e-18 fractional uncertainty across repeated campaigns; the evidence ceiling remains preprint level."
      ∷ "The field frontier is therefore vector-valued: clock accuracy, transfer reproducibility, geopotential knowledge, survey transfer, deployment robustness and operational autonomy must not be collapsed into one scalar maturity claim."
      ∷ []
  }
