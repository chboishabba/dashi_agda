module DASHI.Physics.Closure.R2P2MountainOpticalClockComparisonExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.QuantumClockProperTimeRedshiftBridge as Redshift
import DASHI.Physics.Closure.QuantumClockEmpiricalRedshiftReceiptRequest as Request

------------------------------------------------------------------------
-- Relativistic Redshift Peak-to-Plains (R2P2): source-typed finite adapter.
--
-- Primary source: Triano et al., APS DAMOP oral abstract, 2026-06-03.
-- https://meetings-archive.aps.org/damop/2026/g07/7/
-- Original measurement, link engineering, and apparatus ownership remain
-- with the R2P2 team (Triano, Sinclair, Ludlow, Caldwell, et al.).
--
-- Optical frequency-comb identity: Hall / Haensch / Diddams et al.,
-- 1999-2000, and NIST metrology sources. This adapter adds no new optical
-- physics theorem. It keeps f_CEO and the signed beat branch explicit.
--
-- Supplied secondary transcript: Veritasium, clock comparison at Mt Blue
-- Sky and Boulder. Its numerical prediction is NOT raw clock data.
-- The source states heights approximately; 4300 - 1650 = 2650 metres,
-- while the APS abstract independently rounds the separation to ~2700 m.
--
-- Reuse the existing redshift law and evidence request. A demonstrated
-- optical link is not an accepted gravity ratio, full uncertainty budget,
-- or a quantum-gravity correction.
------------------------------------------------------------------------

record R2P2PrimarySource : Set where
  field
    sourceURI : String
    date : String
    sourceKind : String
    experimentAttribution : String
    freeSpaceLinkKm : Nat
    fibreLinkKm : Nat
    mountainElevationApproxM : Nat
    boulderElevationApproxM : Nat
    separationRoundedApproxM : Nat
    opticalSpecies : String
    shakedownDate : String
    reportedLinkInstability : String

open R2P2PrimarySource public

canonicalR2P2PrimarySource : R2P2PrimarySource
canonicalR2P2PrimarySource = record
  { sourceURI = "https://meetings-archive.aps.org/damop/2026/g07/7/"
  ; date = "2026-06-03"
  ; sourceKind = "APS DAMOP contributed oral abstract, not final calibrated clock-result data"
  ; experimentAttribution = "R2P2: Theodora Triano, Laura Sinclair, Andrew Ludlow, Emily Caldwell, and collaborators"
  ; freeSpaceLinkKm = 69
  ; fibreLinkKm = 81
  ; mountainElevationApproxM = 4300
  ; boulderElevationApproxM = 1650
  ; separationRoundedApproxM = 2700
  ; opticalSpecies = "two independent neutral ytterbium optical-lattice clocks"
  ; shakedownDate = "2025-08"
  ; reportedLinkInstability = "few parts in 1e-17 at approximately 100 s; network shakedown only"
  }

r2p2FreeSpaceFromSource :
  freeSpaceLinkKm canonicalR2P2PrimarySource ≡ 69
r2p2FreeSpaceFromSource = refl

r2p2FibreFromSource :
  fibreLinkKm canonicalR2P2PrimarySource ≡ 81
r2p2FibreFromSource = refl

------------------------------------------------------------------------
-- A comb tooth is n * f_rep + f_CEO, not just n * f_rep.
-- For a positive measured beat, the upper and lower branches are different.
-- These are exact finite arithmetic witnesses, not observed clock readings.
------------------------------------------------------------------------

record AboveCombTooth : Set where
  field
    modeIndex : Nat
    repetitionHz : Nat
    carrierEnvelopeOffsetHz : Nat
    combToothHz : Nat
    beatHz : Nat
    opticalHz : Nat
    toothIsIndexed : combToothHz ≡ modeIndex * repetitionHz + carrierEnvelopeOffsetHz
    targetAboveTooth : opticalHz ≡ combToothHz + beatHz

record BelowCombTooth : Set where
  field
    modeIndex : Nat
    repetitionHz : Nat
    carrierEnvelopeOffsetHz : Nat
    combToothHz : Nat
    beatHz : Nat
    opticalHz : Nat
    toothIsIndexed : combToothHz ≡ modeIndex * repetitionHz + carrierEnvelopeOffsetHz
    targetBelowTooth : combToothHz ≡ opticalHz + beatHz

exampleAboveCombTooth : AboveCombTooth
exampleAboveCombTooth = record
  { modeIndex = 3
  ; repetitionHz = 10
  ; carrierEnvelopeOffsetHz = 2
  ; combToothHz = 32
  ; beatHz = 4
  ; opticalHz = 36
  ; toothIsIndexed = refl
  ; targetAboveTooth = refl
  }

exampleBelowCombTooth : BelowCombTooth
exampleBelowCombTooth = record
  { modeIndex = 3
  ; repetitionHz = 10
  ; carrierEnvelopeOffsetHz = 2
  ; combToothHz = 32
  ; beatHz = 4
  ; opticalHz = 28
  ; toothIsIndexed = refl
  ; targetBelowTooth = refl
  }

------------------------------------------------------------------------
-- Transcript-only consistency check. 2.885e-13 = 2885 * 1e-16.
-- Multiply by 86400 s/day: 249264000 * 1e-16 seconds/day,
-- equivalent to 24.9264 nanoseconds/day. NOT a measured residual.
------------------------------------------------------------------------

transcriptRateInTenToMinus16 : Nat
transcriptRateInTenToMinus16 = 2885

secondsPerDay : Nat
secondsPerDay = 86400

transcriptDailyGainInTenToMinus16Seconds : Nat
transcriptDailyGainInTenToMinus16Seconds =
  transcriptRateInTenToMinus16 * secondsPerDay

transcriptDailyGainExact :
  transcriptDailyGainInTenToMinus16Seconds ≡ 249264000
transcriptDailyGainExact = refl

------------------------------------------------------------------------
-- Explicit attribution and promotion boundary. Import canonical owners.
------------------------------------------------------------------------

record R2P2ClockComparisonBoundary : Set where
  field
    source : R2P2PrimarySource
    sourceIsCanonical : source ≡ canonicalR2P2PrimarySource
    properTimeBridge : Redshift.QuantumClockProperTimeRedshiftBridge
    properTimeBridgeIsCanonical :
      properTimeBridge ≡ Redshift.canonicalQuantumClockProperTimeRedshiftBridge
    empiricalRequest : Request.EmpiricalRedshiftExperimentDescriptor
    empiricalRequestIsHeightComparison :
      empiricalRequest ≡ Request.opticalClockHeightComparisonRequested
    publishedPhaseContinuousNetworkShakedown : Bool
    networkShakedownReported :
      publishedPhaseContinuousNetworkShakedown ≡ true
    fullClockComparisonUncertaintyAcceptedHere : Bool
    fullClockComparisonUncertaintyAcceptedHereIsFalse :
      fullClockComparisonUncertaintyAcceptedHere ≡ false
    finalGRDeviationEstablishedHere : Bool
    finalGRDeviationEstablishedHereIsFalse :
      finalGRDeviationEstablishedHere ≡ false
    quantumGravityEstablishedHere : Bool
    quantumGravityEstablishedHereIsFalse :
      quantumGravityEstablishedHere ≡ false
    transcriptNumericsPromotedToRawData : Bool
    transcriptNumericsPromotedToRawDataIsFalse :
      transcriptNumericsPromotedToRawData ≡ false
    opticalLinkPerformanceEqualsGeopotentialCalibration : Bool
    opticalLinkPerformanceEqualsGeopotentialCalibrationIsFalse :
      opticalLinkPerformanceEqualsGeopotentialCalibration ≡ false
    pendingExternalEvidence : List String

open R2P2ClockComparisonBoundary public

canonicalR2P2ClockComparisonBoundary : R2P2ClockComparisonBoundary
canonicalR2P2ClockComparisonBoundary = record
  { source = canonicalR2P2PrimarySource
  ; sourceIsCanonical = refl
  ; properTimeBridge = Redshift.canonicalQuantumClockProperTimeRedshiftBridge
  ; properTimeBridgeIsCanonical = refl
  ; empiricalRequest = Request.opticalClockHeightComparisonRequested
  ; empiricalRequestIsHeightComparison = refl
  ; publishedPhaseContinuousNetworkShakedown = true
  ; networkShakedownReported = refl
  ; fullClockComparisonUncertaintyAcceptedHere = false
  ; fullClockComparisonUncertaintyAcceptedHereIsFalse = refl
  ; finalGRDeviationEstablishedHere = false
  ; finalGRDeviationEstablishedHereIsFalse = refl
  ; quantumGravityEstablishedHere = false
  ; quantumGravityEstablishedHereIsFalse = refl
  ; transcriptNumericsPromotedToRawData = false
  ; transcriptNumericsPromotedToRawDataIsFalse = refl
  ; opticalLinkPerformanceEqualsGeopotentialCalibration = false
  ; opticalLinkPerformanceEqualsGeopotentialCalibrationIsFalse = refl
  ; pendingExternalEvidence =
      "frozen experiment-specific raw phase/frequency-ratio stream, analysis code and timestamps"
      ∷ "clock systematic uncertainty budgets and correlations"
      ∷ "link nonreciprocity, turbulence, cycle slips and transfer uncertainty"
      ∷ "geopotential difference, surveyed datums, tides and uncertainty propagation"
      ∷ "source dataset checksum, independent replay and evidence ingestion"
      ∷ []
  }

r2p2HasNoClaimedQGDiscovery :
  quantumGravityEstablishedHere canonicalR2P2ClockComparisonBoundary ≡ false
r2p2HasNoClaimedQGDiscovery = refl

r2p2HasNoAcceptedClockRatio :
  fullClockComparisonUncertaintyAcceptedHere canonicalR2P2ClockComparisonBoundary ≡ false
r2p2HasNoAcceptedClockRatio = refl

r2p2NoReportedTranscriptRawDataPromotion :
  transcriptNumericsPromotedToRawData canonicalR2P2ClockComparisonBoundary ≡ false
r2p2NoReportedTranscriptRawDataPromotion = refl

r2p2CanonicalLawDoesNotPromote :
  Redshift.properTimeRedshiftPromoted ≡ false
r2p2CanonicalLawDoesNotPromote =
  Redshift.properTimeRedshiftPromotedIsFalse
