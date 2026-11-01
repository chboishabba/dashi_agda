module DASHI.Culture.MissingDeceasedScienceDrivenAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificCapabilityCarrierBidiExact as C
import DASHI.Culture.MissingDeceasedScientificCapabilityCarrierMatrixExact as M

------------------------------------------------------------------------
-- SCIENCE-DRIVEN INVESTIGATIVE ACQUISITION
--
-- The science identifies capability-bearing carriers.  This compiler turns
-- those carriers into exact evidence-acquisition leaves.  It does not infer
-- person-specific possession, targeting, motive, disappearance causation, or
-- homicide merely from scientific importance.
------------------------------------------------------------------------

alloyProcessPossession : C.ScientificCriticalityReverseObligation
alloyProcessPossession = C.scientific-criticality-reverse-obligation
  M.alloyProcessWindowCarrier
  C.personCarrierPossession
  "recover event-time laboratory/process records, heat-treatment procedures, microstructure ownership, qualification reports, authorship/task assignments, and handover notes showing who actually held the alloy process-window knowledge"
  "a person/role-to-process-window possession proposition"
  "uniqueness, targeting, motive, disappearance causation or homicide"

alloyReplacement : C.ScientificCriticalityReverseObligation
alloyReplacement = C.scientific-criticality-reverse-obligation
  M.alloyProcessWindowCarrier
  C.carrierReplacementDifficulty
  "recover successor/handover evidence: exact heat-treatment schedules, gamma-prime/grain-state characterisation, process-control tolerances, failed batches and requalification effort after departure"
  "whether the reconstructive metallurgy carrier was difficult to replace"
  "a claim that any difficulty caused an event"

fissionQualificationPossession : C.ScientificCriticalityReverseObligation
fissionQualificationPossession = C.scientific-criticality-reverse-obligation
  M.fissionQualificationCarrier
  C.personCarrierPossession
  "recover component-specific qualification/test ownership for neutron fluence, gamma dose, temperature, lifetime, calibration drift, accelerated-life modelling, fault injection and autonomous recovery"
  "who or which role held the qualification-evidence carrier"
  "unique possession or targeting without independent evidence"

fissionReplacement : C.ScientificCriticalityReverseObligation
fissionReplacement = C.scientific-criticality-reverse-obligation
  M.fissionFailureMapCarrier
  C.carrierReplacementDifficulty
  "recover handover/succession records for failure envelopes, physics-of-failure models, calibration-drift knowledge, off-normal response logic and system-level probability-of-failure modelling"
  "whether failure-mode knowledge was distributed or concentrated and difficult to replace"
  "that a concentrated role was selected for harm"

plasmaArtifactStatus : C.ScientificCriticalityReverseObligation
plasmaArtifactStatus = C.scientific-criticality-reverse-obligation
  M.plasmaClosureCarrier
  C.carrierNonPublicness
  "recover source-code availability, exact Hermite closure/dissipation choices, resolution/convergence receipts, target-regime ordering notes and unpublished application-specific configuration"
  "whether any reconstructive plasma-simulation carrier remained non-public/partial"
  "criticality merely from deep public numerical science"

radiographyPossession : C.ScientificCriticalityReverseObligation
radiographyPossession = C.scientific-criticality-reverse-obligation
  M.radiographyInverseCarrier
  C.personCarrierPossession
  "recover event-time access/ownership for source-spectrum calibration, focal-spot maps, detector PSF/response, exact experiment geometry, attenuation/scatter/noise model, reconstruction priors/regularisation and uncertainty model"
  "a bounded possession proposition for the calibrated flash-radiography inverse chain"
  "weapons-design possession from public accelerator work alone"

radiographyObserver : C.ScientificCriticalityReverseObligation
radiographyObserver = C.scientific-criticality-reverse-obligation
  M.radiographyInverseCarrier
  C.carrierObserverVisibility
  "identify programme, security, data-access, calibration, review or configuration-management systems capable of recording who could access experiment-specific forward/inverse-model inputs"
  "whether a capability-aware observer surface existed"
  "selection, targeting, actor identity or event causation"

spectroscopyCalibrationPossession : C.ScientificCriticalityReverseObligation
spectroscopyCalibrationPossession = C.scientific-criticality-reverse-obligation
  M.spectroscopyCalibrationCarrier
  C.personCarrierPossession
  "recover apparatus calibration, tag-species/binding-energy response, conformer libraries, cross-tag comparisons, mixture-discrimination datasets and mission-realistic false-positive models together with task/ownership records"
  "who or which team held mission-relevant calibration/assignment knowledge"
  "unique holder, strategic relevance or event linkage without separate receipts"

spectroscopyReplacement : C.ScientificCriticalityReverseObligation
spectroscopyReplacement = C.scientific-criticality-reverse-obligation
  M.spectroscopyCalibrationCarrier
  C.carrierReplacementDifficulty
  "recover post-departure continuity: instrument calibration reproducibility, protocol transfer, conformer/DFT assignment libraries, mixture benchmarks, successor identity and requalification effort"
  "replacement difficulty for the spectroscopy carrier"
  "a causal explanation of death/disappearance"

------------------------------------------------------------------------
-- Priority ranking generated by mechanistic depth, not by narrative salience.
------------------------------------------------------------------------

data ScienceDrivenPriority : Set where
  highest : ScienceDrivenPriority
  high : ScienceDrivenPriority
  medium : ScienceDrivenPriority
  control : ScienceDrivenPriority


record PrioritisedAcquisition : Set where
  constructor prioritised-acquisition
  field
    priority : ScienceDrivenPriority
    obligation : C.ScientificCriticalityReverseObligation
    rationale : String

open PrioritisedAcquisition public

radiographyPriority : PrioritisedAcquisition
radiographyPriority = prioritised-acquisition highest radiographyPossession
  "The calibrated source/object/detector inverse chain is highly reconstructive and is explicitly separable from public accelerator architecture."

alloyPriority : PrioritisedAcquisition
alloyPriority = prioritised-acquisition high alloyProcessPossession
  "Nominal chemistry is public while process history and microstructure can materially determine properties; exact event-time possession remains open."

fissionPriority : PrioritisedAcquisition
fissionPriority = prioritised-acquisition high fissionQualificationPossession
  "Mission qualification integrates harsh-environment survivability, drift, reliability and autonomous fault response; the public programme explicitly identifies these as maturation gaps."

spectroscopyPriority : PrioritisedAcquisition
spectroscopyPriority = prioritised-acquisition medium spectroscopyCalibrationPossession
  "The protocol is substantially public, so the discriminating carrier is apparatus/tag/conformer/mixture calibration rather than the generic method."

plasmaPriority : PrioritisedAcquisition
plasmaPriority = prioritised-acquisition control plasmaArtifactStatus
  "Much of the mathematical/numerical architecture is public; first test whether any materially reconstructive residual is actually non-public before promoting criticality."

record ScienceDrivenInvestigationBoundary : Set where
  constructor science-driven-investigation-boundary
  field
    mechanisticDepthCanPrioritiseAcquisition : Bool
    mechanisticDepthCanPrioritiseAcquisitionIsTrue : mechanisticDepthCanPrioritiseAcquisition ≡ true
    priorityImpliesTargeting : Bool
    priorityImpliesTargetingIsFalse : priorityImpliesTargeting ≡ false
    possessionImpliesUniqueness : Bool
    possessionImpliesUniquenessIsFalse : possessionImpliesUniqueness ≡ false
    replacementDifficultyImpliesMotive : Bool
    replacementDifficultyImpliesMotiveIsFalse : replacementDifficultyImpliesMotive ≡ false
    eventLinkRequiresIndependentReceipt : Bool
    eventLinkRequiresIndependentReceiptIsTrue : eventLinkRequiresIndependentReceipt ≡ true

canonicalScienceDrivenInvestigationBoundary : ScienceDrivenInvestigationBoundary
canonicalScienceDrivenInvestigationBoundary = science-driven-investigation-boundary true refl false refl false refl false refl true refl
