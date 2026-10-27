module DASHI.Empirical.KozyrevMirrorClaimTesting where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Empirical.GRQuantumPredictionProtocol as PredictionProtocol
import DASHI.Promotion.CrossDomainClaimPromotionBoundary as ClaimBoundary

------------------------------------------------------------------------
-- Source-typed Kozyrev mirror claim intake. No new physical law.
--
-- The apparatus attributed to Kaznacheev/Trofimov is not S. V. Kozyrev's
-- p-adic wavelet construction. N. A. Kozyrev's historical time hypothesis
-- is also not an experimental validation of the later apparatus.
------------------------------------------------------------------------

data KozyrevReferent : Set where
  nikolaiHistoricalTimeHypothesis : KozyrevReferent
  kaznacheevTrofimovSpiralApparatus : KozyrevReferent
  sergeiPadicWaveletTheory : KozyrevReferent

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

apparatusNotPadicWavelets :
  kaznacheevTrofimovSpiralApparatus
  ≢ sergeiPadicWaveletTheory
apparatusNotPadicWavelets ()

apparatusNotHistoricalHypothesis :
  kaznacheevTrofimovSpiralApparatus
  ≢ nikolaiHistoricalTimeHypothesis
apparatusNotHistoricalHypothesis ()

data ClaimFamily : Set where
  apparatusGeometry : ClaimFamily
  ordinaryOpticalOrAcousticScattering : ClaimFamily
  subjectiveExperience : ClaimFamily
  physiologicalOrClinicalEffect : ClaimFamily
  remoteInformationTransfer : ClaimFamily
  clockOrCausalityAnomaly : ClaimFamily
  undefinedTorsionOrTimeEnergy : ClaimFamily

data EvidencePosture : Set where
  sourceDescribesDesign : EvidencePosture
  sourceReportsEffect : EvidencePosture
  externalToyModelOnly : EvidencePosture
  unoperationalisedClaim : EvidencePosture

record SourceTypedClaim : Set where
  constructor sourceTypedClaim
  field
    claimIdentifier : String
    family : ClaimFamily
    sourceAuthors : String
    sourceYear : Nat
    primaryRoot : String
    evidencePosture : EvidencePosture
    limitation : String

canonicalClaimIntake : List SourceTypedClaim
canonicalClaimIntake =
  sourceTypedClaim
    "KM-GEOM"
    apparatusGeometry
    "V. P. Kaznacheev; A. V. Trofimov"
    1998
    "RU2122446C1, filed 1996-07-02, published 1998-11-27"
    sourceDescribesDesign
    "Patent describes a spiral metal enclosure. Patent status does not establish any claimed treatment efficacy. English abstract says 0.5 mm; translated specification/claim says 1.5 mm; source conflict is open."
  ∷ sourceTypedClaim
    "KM-SCATTER"
    ordinaryOpticalOrAcousticScattering
    "Broken Branch, HI-1 and HI-12"
    2026
    "https://www.brokenbranch.dev/labs/as-seen-on-tv/honest-spiral/"
    externalToyModelOnly
    "Two-dimensional scalar/sound simulations do not establish three-dimensional apparatus effects or novel time physics."
  ∷ sourceTypedClaim
    "KM-SUBJECTIVE"
    subjectiveExperience
    "V. P. Kaznacheev"
    2002
    "https://www.physics.socionic.info/index.php/physics/article/view/267"
    sourceReportsEffect
    "Subjective reports require masked sham comparison and independent replication."
  ∷ sourceTypedClaim
    "KM-CLINICAL"
    physiologicalOrClinicalEffect
    "V. P. Kaznacheev; A. V. Trofimov"
    1998
    "https://patents.google.com/patent/RU2122446C1/en"
    sourceReportsEffect
    "Patent anecdotes are not randomised controlled treatment evidence. No clinical authority follows."
  ∷ sourceTypedClaim
    "KM-REMOTE"
    remoteInformationTransfer
    "V. P. Kaznacheev; A. V. Trofimov"
    2006
    "https://physics.socionic.info/index.php/physics/article/view/376"
    sourceReportsEffect
    "Reported information transfer needs precommitted random targets, recipient blinding, leakage control and independent replication."
  ∷ sourceTypedClaim
    "KM-TIME"
    clockOrCausalityAnomaly
    "Kozyrev mirror claims, as later recounted"
    2026
    "https://www.brokenbranch.dev/labs/as-seen-on-tv/does-the-mirror-focus/"
    unoperationalisedClaim
    "No calibrated clock anomaly or falsifiable time-energy measurand has been established by the cited model."
  ∷ sourceTypedClaim
    "KM-TORSION"
    undefinedTorsionOrTimeEnergy
    "Kozyrev mirror claims, as later recounted"
    2026
    "https://www.brokenbranch.dev/labs/as-seen-on-tv/does-the-mirror-focus/"
    unoperationalisedClaim
    "Define a unit, detector response, calibration, null and predicted effect before a test is meaningful."
  ∷ []

------------------------------------------------------------------------
-- Frozen, falsifiable experimental design obligations.
-- These are planned comparisons, not observations or measured effects.
------------------------------------------------------------------------

record TestTarget : Set where
  constructor testTarget
  field
    claimFamily : ClaimFamily
    observable : String
    activeAndShamComparison : String
    decisiveNegativeControl : String
    rejectionCondition : String

canonicalTestTargets : List TestTarget
canonicalTestTargets =
  testTarget
    ordinaryOpticalOrAcousticScattering
    "Frequency-resolved flux, field map, torque and uncertainty"
    "Matched spiral and matched non-spiral material controls"
    "Empty chamber, thermal equilibrium, numerical timestep/grid refinement"
    "Fail the specified effect threshold or show it also occurs in the sham"
  ∷ testTarget
    subjectiveExperience
    "Predeclared rating or behavioural score"
    "Randomised, masked active versus sham enclosure"
    "Expectancy, audio, light, temperature, airflow and order controls"
    "Held-out treatment contrast misses the preregistered threshold"
  ∷ testTarget
    physiologicalOrClinicalEffect
    "Predeclared validated physiological endpoint"
    "Ethics-approved randomised, blinded sham-controlled study"
    "Medication, resting period, selection and adverse-event controls"
    "No clinically meaningful effect after multiplicity correction"
  ∷ testTarget
    remoteInformationTransfer
    "Exact predeclared blinded-target hit rate"
    "Random, precommitted targets versus chance baseline"
    "Leak-proof target allocation, decoy sessions and auditor blinding"
    "Hit rate not distinguishable from prespecified chance baseline"
  ∷ testTarget
    clockOrCausalityAnomaly
    "Traceable synchronised clock difference and uncertainty"
    "Chamber versus matched sham and colocated reference clocks"
    "EM, thermal, vibration, pressure, timing-network and drift controls"
    "Any deviation lies within calibrated uncertainty"
  ∷ testTarget
    undefinedTorsionOrTimeEnergy
    "No admissible observable until measurand and unit are specified"
    "Not yet test-ready"
    "Require a detector calibrated against known physical interactions"
    "Reject uninterpretable readings until a quantitative prediction exists"
  ∷ []

record ExperimentIntakeBoundary : Set where
  constructor experimentIntakeBoundary
  field
    claimsCatalogued : Bool
    claimsCataloguedIsTrue : claimsCatalogued ≡ true
    protocolIndependentlyPreregistered : Bool
    protocolIndependentlyPreregisteredIsFalse :
      protocolIndependentlyPreregistered ≡ false
    observationsSupplied : Bool
    observationsSuppliedIsFalse : observationsSupplied ≡ false
    independentlyReplicated : Bool
    independentlyReplicatedIsFalse : independentlyReplicated ≡ false
    empiricalPromotion : Bool
    empiricalPromotionIsFalse : empiricalPromotion ≡ false
    clinicalPromotion : Bool
    clinicalPromotionIsFalse : clinicalPromotion ≡ false

canonicalExperimentIntakeBoundary : ExperimentIntakeBoundary
canonicalExperimentIntakeBoundary =
  experimentIntakeBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

mirrorEmpiricalClaimBoundary :
  ClaimBoundary.CrossDomainPromotionExample
mirrorEmpiricalClaimBoundary =
  ClaimBoundary.mkBlockedExample
    "Mirror mechanism or source report is not verified physical efficacy"
    ClaimBoundary.structuralAnalogyClaim
    ClaimBoundary.empiricalFactClaim
    ClaimBoundary.measurementAuthorityBridgeReceipt
    ClaimBoundary.missingMeasurementAuthorityReason
    "Require frozen instrument calibration, controlled data, an independent replay and an explicit external authority review."

mirrorClinicalClaimBoundary :
  ClaimBoundary.CrossDomainPromotionExample
mirrorClinicalClaimBoundary =
  ClaimBoundary.mkBlockedExample
    "Patent and reported symptoms are not clinical efficacy"
    ClaimBoundary.evidenceGraphClaim
    ClaimBoundary.clinicalClaim
    ClaimBoundary.clinicalEvidenceAuthorityBridgeReceipt
    ClaimBoundary.missingClinicalEvidenceReason
    "Human intervention requires valid consent, safety review, a sham, prespecified endpoint, registered analysis and independent replication."

mirrorEmpiricalPromotionStillBlocked :
  ClaimBoundary.targetClaimPromoted mirrorEmpiricalClaimBoundary ≡ false
mirrorEmpiricalPromotionStillBlocked =
  ClaimBoundary.targetClaimPromotedIsFalse mirrorEmpiricalClaimBoundary

mirrorClinicalPromotionStillBlocked :
  ClaimBoundary.targetClaimPromoted mirrorClinicalClaimBoundary ≡ false
mirrorClinicalPromotionStillBlocked =
  ClaimBoundary.targetClaimPromotedIsFalse mirrorClinicalClaimBoundary

-- PredictionProtocol remains the canonical quantitative/holdout contract.
-- This module intentionally does not construct a prediction value or proof of
-- empirical confirmation and does not reclassify any p-adic Kozyrev theorem.
