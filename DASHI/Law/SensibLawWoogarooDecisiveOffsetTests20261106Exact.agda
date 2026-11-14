module DASHI.Law.SensibLawWoogarooDecisiveOffsetTests20261106Exact where

-- WOOGAROO EPBC 2019/8575 — original-source, adversarial decision tests.
-- Original source attribution remains:
-- QUT School of Law Taylor/Maguire/Lewis 12 March 2026; QCC Gough
-- 12 March 2026; RSPCA Queensland 2025 original wildlife articles
-- and 2025 Impact Report; BAAM/One Environment/Saunders Havill
-- January 2026 source tables; original Commonwealth EPBC approval
-- signed 16 October 2026; Australian Government 2012 offsets policy.
--
-- NEW 2026 National Environmental Standard F2026L01093 was registered
-- 21 August 2026, but departmental reform guidance says standards do
-- NOT apply to assessment/approval decisions until later commencement
-- of the new approval tests (on or before 1 December 2026). Thus do
-- not apply as if binding on the 16 October 2026 decision. Recheck
-- particular commencement/saved provisions before any legal reliance.
--
-- All results are SOURCE and MODEL gating, not empirical measurements,
-- legal merits, review time-limit determinations or Court findings.
-- No FOI, s474A enforcement, declaration, payment or filing inferred.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Law.SensibLawWoogarooIndependentObjectionBurden20261106Exact as Objection
import DASHI.Law.SensibLawWoogarooKoalaOAGStatusSensitivity20261106Exact as OAG
import DASHI.Law.SensibLawWoogarooProponentEvidenceAdversarialAudit20261106Exact as PD

data Test : Set where
  sameProtectedAttribute : Test
  directVsIndirectAndResidual : Test
  avoidanceBeforeOffsets : Test
  localConnectivityCounterfactual : Test
  sameHabitatMaturityAndThermalRefuge : Test
  sourceAreaAndBoundaryConsistency : Test
  temporalSurvivalAndTimeLag : Test
  impactOffsetAsymmetricScoring : Test
  speciesStatusAndTransitionLaw : Test
  sourceIndependenceAndDeduplication : Test
  priorOffsetsAndAdditionality : Test
  legallySecuredBeforeRelevantImpact : Test
  meaningfulMonitoringAndRemedy : Test
  completeCommentsAndDecisionConsideration : Test

data EvidentiaryStage : Set where
  independentProfessionallyAuthored : EvidentiaryStage
  directOrganisationPublicReport : EvidentiaryStage
  proponentCalculatorOnly : EvidentiaryStage
  officialPolicyOrStatute : EvidentiaryStage
  acquiredSignedInstrument : EvidentiaryStage
  missingIndependentSource : EvidentiaryStage

record Challenge : Set where
  constructor challenge
  field
    test : Test
    origin : EvidentiaryStage
    immediateFalsifier : String
    disputedBridge : String
    sameActionGrounded : Bool
    actualOutcomeVerified : Bool
open Challenge public

challengeFor : Test → Challenge
challengeFor sameProtectedAttribute = challenge sameProtectedAttribute
  independentProfessionallyAuthored
  "Original QUT/QCC habitat-function evidence and 2012 offsets policy principle 1"
  "Source projected forage hectares do not certify replaced breeding, corridor or mature-refuge attributes"
  true false
challengeFor directVsIndirectAndResidual = challenge directVsIndirectAndResidual
  officialPolicyOrStatute
  "2012 offsets policy principle 2: at least 90% direct normally; distinguish remaining compensatory measures"
  "Below 100% direct alone != automatic approval illegality; check actual 90% and final combination"
  true false
challengeFor avoidanceBeforeOffsets = challenge avoidanceBeforeOffsets
  independentProfessionallyAuthored
  "QUT original alternatives criticism and applicant's actual avoidance hierarchy / design versions"
  "An offset calculator does not demonstrate that residual loss was unavoidable"
  true false
challengeFor localConnectivityCounterfactual = challenge localConnectivityCounterfactual
  independentProfessionallyAuthored
  "QUT movement modelling and QCC Woogaroo Creek/Opossum Creek network"
  "Remote koala occurrence cannot restore lost paths for Woogaroo's local koalas"
  true false
challengeFor sameHabitatMaturityAndThermalRefuge = challenge sameHabitatMaturityAndThermalRefuge
  independentProfessionallyAuthored
  "QUT heat/moisture refuge evidence, mature/hollow trees, microclimate and seasonal foraging"
  "Twenty-year plantings and scalar habitat score do not demonstrate same functional thermal refuge"
  true false
challengeFor sourceAreaAndBoundaryConsistency = challenge sourceAreaAndBoundaryConsistency
  proponentCalculatorOnly
  "QUT 136 ha direct and 26 ha indirect; PD 128 ha; MWW A16 127.02 ha cross-table"
  "Different area scope and version must be source-joined, not subtracted as if identical polygons"
  true false
challengeFor temporalSurvivalAndTimeLag = challenge temporalSurvivalAndTimeLag
  proponentCalculatorOnly
  "Original A16 20-year maturity, projected tree survival and 75/85 quality-confidence"
  "Future habitat benefit is not observed present survival or flowering value"
  true false
challengeFor impactOffsetAsymmetricScoring = challenge impactOffsetAsymmetricScoring
  proponentCalculatorOnly
  "Original MWW 3/150 scat-positive tree slots, four 10/10 presence AU subscores; AU4 sum 30 != printed 40"
  "The direction of an inflated baseline and inflated future score in OAG are not identical"
  true false
challengeFor speciesStatusAndTransitionLaw = challenge speciesStatusAndTransitionLaw
  officialPolicyOrStatute
  "Koala 2019 Vulnerable OAG 0.2%; 2022 Endangered 1.2%; actual 2026 saved commencement law and delegate"
  "Numerical <90 scenario is CONDITIONAL, not a decided legal error"
  true false
challengeFor sourceIndependenceAndDeduplication = challenge sourceIndependenceAndDeduplication
  directOrganisationPublicReport
  "RSPCA 2025 public Maximus/William accounts and 2025 Impact Report; QCC; original clinical GPS"
  "Independent original organisation confirms Woogaroo returns; original release polygon not yet joined"
  true false
challengeFor priorOffsetsAndAdditionality = challenge priorOffsetsAndAdditionality
  officialPolicyOrStatute
  "2012 offsets policy principle 6 and original Avonvale prior-approved offset polygons"
  "Adjoining previous offsets is not duplication; added benefits and unchanged existing obligations need proof"
  true false
challengeFor legallySecuredBeforeRelevantImpact = challenge legallySecuredBeforeRelevantImpact
  acquiredSignedInstrument
  "16 Oct signed Annexure A conditions 24/25 and phase definitions, section 19F actual VDEC and titles"
  "Condition to secure offset is not proof that registration or commencement has occurred"
  true false
challengeFor meaningfulMonitoringAndRemedy = challenge meaningfulMonitoringAndRemedy
  acquiredSignedInstrument
  "Annexure A monitoring/publishing/incident conditions 48-69 and real site compliance receipts"
  "Formal management plans are not actual ecological success or condition breach"
  true false
challengeFor completeCommentsAndDecisionConsideration = challenge completeCommentsAndDecisionConsideration
  missingIndependentSource
  "Original 95B full 1786 comments and response summary, QUT/QCC transmission, s95C recommendation and reasons"
  "Publication notice does not prove actual delegate considered the objections"
  true false

-- One selected first-party source result: organisation reports two
-- named returns to the Woogaroo landscape (RSPCA Impact Report p11).
-- Note that both case-specific original clinical release GPS inputs are
-- STILL open. Koala releases are NOT independent proof of ecological
-- replacement and also not evidence of movement into remote offsets.
rspcaForestLevelConfirmedByOrganisation : Bool
rspcaForestLevelConfirmedByOrganisation = true

rspcaExact20198575FootprintCoordinatePaid : Bool
rspcaExact20198575FootprintCoordinatePaid = false

exactFootprintIsNotPaid :
  rspcaExact20198575FootprintCoordinatePaid ≡ false
exactFootprintIsNotPaid = refl

-- The 2026 National Environmental Standard is formally in force as an
-- instrument, but departmental guidance says its approval tests were
-- not yet operative at the 16 October decision. Treat binding applicability
-- as distinct from an instrument's registration/effective date.
data TemporalNorm : Set where
  EPBC2012OffsetsPolicy : TemporalNorm
  nationalEnvironmentalStandard2026 : TemporalNorm

record Applicability : Set where
  constructor applicability
  field
    norm : TemporalNorm
    instrumentInForceOnDecisionDate : Bool
    newApprovalTestsOperativeOnDecisionDate : Bool
    actualApplicabilityAdjudicated : Bool
open Applicability public

standard2026AtOctoberDecision : Applicability
standard2026AtOctoberDecision =
  applicability nationalEnvironmentalStandard2026 true false false

doNotPromoteRegistered2026StandardToOctoberBinding :
  newApprovalTestsOperativeOnDecisionDate standard2026AtOctoberDecision ≡ false
doNotPromoteRegistered2026StandardToOctoberBinding = refl

data Bridge : Set where
  proponentScore : Bridge
  measuredLocalEcologicalFunction : Bridge
  actualDecisionMakerAcceptance : Bridge
  approvedRegisteredOffsetDelivery : Bridge

data SourceOnlyProvesRealisedEcology : Set where
sourceScoreNotRealisedEcology : SourceOnlyProvesRealisedEcology → ⊥
sourceScoreNotRealisedEcology ()

-- Reuse of the original existing canonical modules; no duplicates.
originalQUT : Attribution.AttributedSource
originalQUT = Objection.priorQUTAttribution
originalQCC : Attribution.AttributedSource
originalQCC = Objection.priorQCCAttribution
originalOriginalKoalaCoeff :
  OAG.inputSum OAG.allRows ≡ 1010350
originalOriginalKoalaCoeff = OAG.sourceWeightSum

priorAU4Contradiction :
  PD.au4ComponentSumInTable ≡ 30
priorAU4Contradiction = PD.au4TableComponentsSumTo30

-- These tests enumerate the live decisional dimensions. There is no
-- fake blanket CompleteEvidence witness: every actualOutcomeVerified
-- remains false until a source-specific independent record is joined.
