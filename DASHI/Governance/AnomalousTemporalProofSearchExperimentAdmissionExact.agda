module DASHI.Governance.AnomalousTemporalProofSearchExperimentAdmissionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.ExperimentalCoordinateDesignExact as Design
import DASHI.Core.ActiveBidiDiscriminatorLoopExact as ActiveBidi
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal
import DASHI.Governance.AnomalousPhenomenonTemporalEvidenceTrajectoriesExact as Trajectory
import DASHI.Governance.AnomalousConsumerIndexedObligationFibreExact as Obligation

------------------------------------------------------------------------
-- TEMPORAL PROOF-SEARCH / EXPERIMENT ADMISSION
--
-- A candidate experiment is admitted only relative to a live time-indexed
-- fibre and a declared consumer obligation.  Naming a phenomenon or an
-- interesting protocol does not itself make the route live.
------------------------------------------------------------------------

data CandidateExperiment : Set where
  bemResidualMethodAudit
  presentimentPreregisteredReplication
  ganzfeldAdversarialReplication
  stargateProtocolAudit
  psilocybinExpectancyControlStudy
  ndeTimeLockedRealityTest
  : CandidateExperiment

data ExperimentalValue : Set where
  supportsDistinction doesNotSupportDistinction unresolvedOutcome : ExperimentalValue

data ExperimentalDimension : Set where
  informationalDimension : ExperimentalDimension

data ExperimentControl : Set where
  applyDeclaredProtocol : ExperimentControl

record ExperimentWorld : Set where
  constructor experimentWorld
  field
    candidate : CandidateExperiment
    moment : Trajectory.EvidenceMoment
    consumer : Obligation.EvidenceConsumer

open ExperimentWorld public

data ExperimentCoordinate : Set where
  targetedEvidenceCoordinate : Temporal.EvidenceCoordinate → ExperimentCoordinate

coordinateOf : CandidateExperiment → Temporal.EvidenceCoordinate
coordinateOf bemResidualMethodAudit = Temporal.mechanismDiscrimination
coordinateOf presentimentPreregisteredReplication = Temporal.independentReplication
coordinateOf ganzfeldAdversarialReplication = Temporal.independentReplication
coordinateOf stargateProtocolAudit = Temporal.controlStrength
coordinateOf psilocybinExpectancyControlStudy = Temporal.controlStrength
coordinateOf ndeTimeLockedRealityTest = Temporal.mechanismDiscrimination

readCoordinate : ExperimentCoordinate → ExperimentWorld → ExperimentalValue
readCoordinate _ _ = unresolvedOutcome

applyControl : ExperimentControl → ExperimentWorld → ExperimentWorld
applyControl applyDeclaredProtocol world = world

experimentDesign :
  Design.ExperimentalCoordinateDesign
    ExperimentWorld ExperimentControl ExperimentalValue ExperimentalDimension
experimentDesign = Design.experimentalCoordinateDesign
  ExperimentCoordinate
  (λ { (targetedEvidenceCoordinate _) → Design.derivedDiscriminator })
  (λ _ → informationalDimension)
  readCoordinate
  applyControl
  (λ _ → "consumer-indexed evidence coordinate")
  (λ _ → "informational/evidential coordinate, not a new physical dimension")
  (λ _ → "protocol calibration, randomisation, masking, scoring and analysis plan required")
  (λ _ → "declared experimental protocol only; authority is checked separately")

------------------------------------------------------------------------
-- Candidate routes carry the exact live obligation they intend to attack.
------------------------------------------------------------------------

record ExperimentRoute : Set₁ where
  constructor experimentRoute
  field
    experiment : CandidateExperiment
    moment : Trajectory.EvidenceMoment
    consumer : Obligation.EvidenceConsumer
    targetAxis : Temporal.EvidenceCoordinate
    targetMatchesExperiment : targetAxis ≡ coordinateOf experiment
    targetIsActive : Obligation.ActiveAxis moment consumer targetAxis
    calibrationReference : String
    expectedFibreEffectReference : String
    proofSearchAdmission : ProofSearch.RouteAdmission

open ExperimentRoute public

presentimentRoute : ExperimentRoute
presentimentRoute = experimentRoute
  presentimentPreregisteredReplication
  Trajectory.presentimentUpdate2018
  Obligation.replicationConsumer
  Temporal.independentReplication
  refl
  tt
  "preregistered multi-lab protocol with fixed stopping/scoring and leakage audit"
  "designed to separate persistent anticipatory anomaly from methodological explanation"
  ProofSearch.canonicalRouteAdmission

ganzfeldRoute : ExperimentRoute
ganzfeldRoute = experimentRoute
  ganzfeldAdversarialReplication
  Trajectory.ganzfeldContestedCurrent
  Obligation.replicationConsumer
  Temporal.independentReplication
  refl
  tt
  "proponent/skeptic joint protocol, automated randomisation and blinded scoring"
  "designed to refine the small-anomaly versus method-artifact fibre"
  ProofSearch.canonicalRouteAdmission

psilocybinRoute : ExperimentRoute
psilocybinRoute = experimentRoute
  psilocybinExpectancyControlStudy
  Trajectory.psilocybinMeta2025_2026
  Obligation.therapeuticConsumer
  Temporal.controlStrength
  refl
  tt
  "active-placebo / expectancy measurement / masking-integrity and analysis receipt"
  "designed to separate pharmacological therapeutic contribution from expectancy/blinding contribution"
  ProofSearch.canonicalRouteAdmission

ndeMechanismRoute : ExperimentRoute
ndeMechanismRoute = experimentRoute
  ndeTimeLockedRealityTest
  Trajectory.awareII2023
  Obligation.mechanismConsumer
  Temporal.mechanismDiscrimination
  refl
  tt
  "time-locked hidden-target/auditory/physiology protocol with prospective registration"
  "designed to discriminate mechanism-compatible interpretations without assuming extracerebral ontology"
  ProofSearch.canonicalRouteAdmission

------------------------------------------------------------------------
-- Rejected route shapes: wrong consumer/axis or silent ontological promotion.
------------------------------------------------------------------------

data RejectedExperimentRoute : Set where
  repeatBemOriginalAfterTransparentPsi
  ndePhenomenologySurveyForMechanismConsumer
  psychedelicMysticalReportAsPsiMechanismTest
  stargateHistoricalRecordAsOperationalUtilityTest
  : RejectedExperimentRoute

rejectionReason : RejectedExperimentRoute → ProofSearch.RouteError
rejectionReason repeatBemOriginalAfterTransparentPsi = ProofSearch.consumerMismatch
rejectionReason ndePhenomenologySurveyForMechanismConsumer = ProofSearch.consumerMismatch
rejectionReason psychedelicMysticalReportAsPsiMechanismTest = ProofSearch.strengthMismatch
rejectionReason stargateHistoricalRecordAsOperationalUtilityTest = ProofSearch.consumerMismatch

rejectedDisposition : RejectedExperimentRoute → ProofSearch.RouteDisposition
rejectedDisposition route = ProofSearch.rejected (rejectionReason route)

bemRepeatIsRedirectedFromCurrentFrontier :
  rejectedDisposition repeatBemOriginalAfterTransparentPsi
  ≡ ProofSearch.rejected ProofSearch.consumerMismatch
bemRepeatIsRedirectedFromCurrentFrontier = refl

ndeSurveyDoesNotAttackMechanismObligation :
  rejectedDisposition ndePhenomenologySurveyForMechanismConsumer
  ≡ ProofSearch.rejected ProofSearch.consumerMismatch
ndeSurveyDoesNotAttackMechanismObligation = refl

psychedelicExperienceDoesNotBecomePsiMechanismEvidence :
  rejectedDisposition psychedelicMysticalReportAsPsiMechanismTest
  ≡ ProofSearch.rejected ProofSearch.strengthMismatch
psychedelicExperienceDoesNotBecomePsiMechanismEvidence = refl

------------------------------------------------------------------------
-- Weld to the canonical active BIDI loop and experimental-design boundaries.
------------------------------------------------------------------------

bidiBoundary : ActiveBidi.ActiveBidiDiscriminatorLoopBoundary
bidiBoundary = ActiveBidi.canonicalActiveBidiDiscriminatorLoopBoundary

designBoundary : Design.ExperimentalCoordinateBoundary
designBoundary = Design.canonicalExperimentalCoordinateBoundary

proofSearchBoundary : ProofSearch.ProofSearchLeastPrivilegeBoundary
proofSearchBoundary = ProofSearch.canonicalProofSearchLeastPrivilegeBoundary

data CandidateExperimentPromotesTruth : Set where

data ExperimentRoutePromotesExpectedOutcome : Set where

data DerivedEvidenceCoordinatePromotesPhysicalDimension : Set where

data CalibrationPromotesInterventionAuthority : Set where

candidateDoesNotPromoteTruth : CandidateExperimentPromotesTruth → ⊥
candidateDoesNotPromoteTruth ()

routeDoesNotPromoteExpectedOutcome : ExperimentRoutePromotesExpectedOutcome → ⊥
routeDoesNotPromoteExpectedOutcome ()

derivedCoordinateDoesNotPromotePhysicalDimension :
  DerivedEvidenceCoordinatePromotesPhysicalDimension → ⊥
derivedCoordinateDoesNotPromotePhysicalDimension ()

calibrationDoesNotPromoteAuthority : CalibrationPromotesInterventionAuthority → ⊥
calibrationDoesNotPromoteAuthority ()

record AnomalousTemporalProofSearchAdmissionBoundary : Set where
  constructor anomalousTemporalProofSearchAdmissionBoundary
  field
    experimentTargetsActiveConsumerObligation : Bool
    experimentTargetsActiveConsumerObligationIsTrue :
      experimentTargetsActiveConsumerObligation ≡ true
    theoremOrExperimentNameIsAdmission : Bool
    theoremOrExperimentNameIsAdmissionIsFalse : theoremOrExperimentNameIsAdmission ≡ false
    expectedRefinementEqualsObservedRefinement : Bool
    expectedRefinementEqualsObservedRefinementIsFalse :
      expectedRefinementEqualsObservedRefinement ≡ false
    experimentCalibrationCreatesAuthority : Bool
    experimentCalibrationCreatesAuthorityIsFalse :
      experimentCalibrationCreatesAuthority ≡ false
    nextRouteMayChangeAsTemporalFibreChanges : Bool
    nextRouteMayChangeAsTemporalFibreChangesIsTrue :
      nextRouteMayChangeAsTemporalFibreChanges ≡ true

canonicalAnomalousTemporalProofSearchAdmissionBoundary :
  AnomalousTemporalProofSearchAdmissionBoundary
canonicalAnomalousTemporalProofSearchAdmissionBoundary =
  anomalousTemporalProofSearchAdmissionBoundary
    true refl false refl false refl false refl true refl
