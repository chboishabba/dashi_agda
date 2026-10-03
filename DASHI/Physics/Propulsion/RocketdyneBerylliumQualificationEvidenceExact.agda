{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.RocketdyneBerylliumQualificationEvidenceExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Historical, source-indexed qualification evidence.
-- Source: Paster and French (October 1974), NASA-CR-140308, R-9557,
-- NTRS document 19740027091, contract NAS9-13476.
--
-- Integers below are counts/codes, not fabricated measured uncertainties.
-- Separate engine articles and test envelopes cannot be conflated.
------------------------------------------------------------------------

data TestArticle : Set where
  durabilityEngine offLimitsEngine vibrationSimulator : TestArticle

data TestKind : Set where
  environmentalExposure hotFire offLimitsHotFire randomVibration : TestKind

data Finding : Set where
  metPrescribedTest observedDamage observedAnomaly inconclusive : Finding

record Source : Set where
  constructor source
  field
    documentId : String
    reportId : String
    date : String
    evidenceLocator : String

nasa1974 : Source
nasa1974 = source "19740027091" "NASA-CR-140308 / R-9557"
                  "1974-10" "https://ntrs.nasa.gov/citations/19740027091"

record Observation : Set where
  constructor observation
  field
    provenance : Source
    article : TestArticle
    kind : TestKind
    cycleCount : Nat
    qualificationEnvelope : String
    measuredQuantityReference : String
    finding : Finding

-- These are explicitly reported campaign design/test counts, not inferred
-- probabilities or sample-size-based estimates of fleet reliability.
durabilityExposure : Observation
durabilityExposure =
  observation nasa1974 durabilityEngine environmentalExposure 6
  "six environmental cycles interspersed with firing, without intermediate servicing"
  "NASA-CR-140308 durability engine section" metPrescribedTest

brazeVibration : Observation
brazeVibration =
  observation nasa1974 vibrationSimulator randomVibration 100
  "equivalent of 100 missions of three-axis random vibration"
  "NASA-CR-140308 vibration simulator section" metPrescribedTest

offLimitsFiring : Observation
offLimitsFiring =
  observation nasa1974 offLimitsEngine offLimitsHotFire 0
  "off-nominal mixture ratio, chamber pressure and orifice plugging"
  "NASA-CR-140308 off-limits engine section" metPrescribedTest

-- The equality proof is about the typed article identity, never about
-- converting equivalent vibration missions to observed flown missions.
record SameArticleEvidence (x y : Observation) : Set where
  constructor same-article
  field
    identity : Observation.article x ≡ Observation.article y

selfArticle : (x : Observation) → SameArticleEvidence x x
selfArticle x = same-article refl

-- Admissible extrapolation is deliberately a NEW evidence obligation:
-- qualification by itself carries no universal lifetime or fleet claim.
record TransferEvidence (x : Observation) : Set where
  constructor transfer-evidence
  field
    targetSystem : String
    targetDutyCycle : String
    targetEnvironment : String
    targetMaterialAndJointRevision : String
    equivalenceOrBoundingArgument : String
    validationReference : String

record TransferClaim (x : Observation) : Set where
  constructor transferred
  field
    observation : Observation
    transfer : TransferEvidence x
    statedTarget : String

admitTransfer :
  (x : Observation) → TransferEvidence x → String → TransferClaim x
admitTransfer x proof target = transferred x proof target

-- Causal diagnosis is not entailed by a pass/fail campaign result.
record CausalAttribution (x : Observation) : Set where
  constructor causal-attribution
  field
    component : String
    mechanism : String
    inspectionOrFailureEvidence : String

-- Distinct histories / no conflation with the beryllium chamber tests.
data HistoricalProgramme : Set where
  berylliumINTEREGEN lithiumFluorineHydrogen dimethylmercuryProposal : HistoricalProgramme

programme : Observation → HistoricalProgramme
programme x = berylliumINTEREGEN

data EvidenceLevel : Set where
  archivalTestResult theoreticalPerformance historicalProposal contemporaryDemonstration : EvidenceLevel

record HistoricalClaim : Set where
  constructor historical-claim
  field
    subject : HistoricalProgramme
    level : EvidenceLevel
    sourceReference : String
    preciseClaim : String

lithiumTripropellant : HistoricalClaim
lithiumTripropellant =
  historical-claim lithiumFluorineHydrogen archivalTestResult
  "NASA CR-72325; NASA NTRS 19700018655"
  "Separate Rocketdyne Li/F2/H2 experimental propulsion programme"

mercuryProposal : HistoricalClaim
mercuryProposal =
  historical-claim dimethylmercuryProposal historicalProposal
  "John D. Clark, Ignition!, chapter High Density and Higher Foolishness"
  "Dimethylmercury was discussed as a proposed propellant; no engine firing established here"
