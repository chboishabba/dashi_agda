module DASHI.Culture.MissingDeceasedScientificCapabilityCarrierMatrixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificCapabilityCarrierBidiExact as C

------------------------------------------------------------------------
-- SCIENTIFIC CAPABILITY CARRIER MATRIX
--
-- These are capability-level technical objects revealed by formalising the
-- science.  They are not person-specific possession claims unless separately
-- sourced, and they do not imply targeting or causal linkage to any event.
------------------------------------------------------------------------

-- Nickel-base burn-resistant superalloy lane.
alloyCompositionCarrier : C.ScientificCapabilityCarrier
alloyCompositionCarrier = C.scientific-capability-carrier
  "nickel-base burn-resistant superalloys"
  "nominal composition window"
  C.constitutiveParameters
  C.carrierPublic
  "DASHI.Physics.Materials.NickelBaseSuperalloyMechanismExact"
  "published patent composition ranges"
  "Public composition materially narrows design space but does not determine heat treatment, microstructure or full processing history."

alloyProcessWindowCarrier : C.ScientificCapabilityCarrier
alloyProcessWindowCarrier = C.scientific-capability-carrier
  "nickel-base burn-resistant superalloys"
  "heat-treatment / gamma-prime / grain-state process window"
  C.processWindow
  C.carrierUnknown
  "DASHI.Physics.Materials.NickelBaseSuperalloyMechanismExact"
  "current public record incomplete"
  "This is a likely reconstructive carrier, but its exact public/private state for the relevant alloy family is not yet established."

-- Fission instrumentation and control.
fissionQualificationCarrier : C.ScientificCapabilityCarrier
fissionQualificationCarrier = C.scientific-capability-carrier
  "space fission instrumentation and control"
  "radiation-temperature-lifetime qualification evidence"
  C.qualificationEvidence
  C.carrierUnknown
  "DASHI.Physics.Nuclear.FissionInstrumentationControlReliabilityExact"
  "NASA public maturation material identifies qualification as necessary"
  "Qualification evidence is capability-bearing because it determines whether components survive and remain trustworthy in mission conditions; access status remains unresolved."

fissionFailureMapCarrier : C.ScientificCapabilityCarrier
fissionFailureMapCarrier = C.scientific-capability-carrier
  "space fission instrumentation and control"
  "sensor/electronics drift and failure-mode map"
  C.failureModeMap
  C.carrierUnknown
  "DASHI.Physics.Nuclear.FissionInstrumentationControlReliabilityExact"
  "NASA public material motivates radiation/temperature/lifetime/fault concerns"
  "Detailed empirical failure envelopes are not established as public in the current record."

-- Reduced fluid-kinetic plasma computation.
plasmaAlgorithmCarrier : C.ScientificCapabilityCarrier
plasmaAlgorithmCarrier = C.scientific-capability-carrier
  "reduced fluid-kinetic plasma simulation"
  "operator splitting + spatial + Hermite velocity-space numerical architecture"
  C.sourceCodeOrAlgorithm
  C.carrierPublic
  "DASHI.Physics.Plasma.ReducedFluidKineticHermiteNumericsExact"
  "Viriato publication exposes numerical architecture"
  "Algorithmic architecture is public; exact source-code release remains a separate artifact-status question."

plasmaClosureCarrier : C.ScientificCapabilityCarrier
plasmaClosureCarrier = C.scientific-capability-carrier
  "reduced fluid-kinetic plasma simulation"
  "Hermite truncation / closure / dissipation choices"
  C.constitutiveParameters
  C.carrierPartial
  "DASHI.Physics.Plasma.ReducedFluidKineticHermiteNumericsExact"
  "published method plus unresolved application-specific closure choices"
  "The general numerical treatment is public, while target-specific closure/resolution adequacy remains case dependent."

-- Flash radiography / pulsed accelerator imaging.
radiographyArchitectureCarrier : C.ScientificCapabilityCarrier
radiographyArchitectureCarrier = C.scientific-capability-carrier
  "flash radiography"
  "accelerator-to-bremsstrahlung-to-radiograph architecture"
  C.designGeometry
  C.carrierPublic
  "DASHI.Physics.Accelerators.FlashRadiographyPhysicsExact"
  "LANL/NNSA public accelerator descriptions"
  "The public architecture explains the imaging chain but is not equivalent to experiment-specific geometry or inference data."

radiographyInverseCarrier : C.ScientificCapabilityCarrier
radiographyInverseCarrier = C.scientific-capability-carrier
  "flash radiography"
  "experiment-specific calibrated forward/inverse model"
  C.inverseModel
  C.carrierBounded
  "DASHI.Physics.Accelerators.FlashRadiographyPhysicsExact"
  "public accelerator architecture is separated from classified experiment-specific weapons information"
  "The capability-bearing object is the calibrated mapping from source/detector/geometry/radiograph to physical-state inference, not merely the accelerator principle."

-- Cryogenic messenger-tag action spectroscopy.
spectroscopyProtocolCarrier : C.ScientificCapabilityCarrier
spectroscopyProtocolCarrier = C.scientific-capability-carrier
  "cryogenic messenger-tag action spectroscopy"
  "ion-generation / cryogenic-tagging / IR-photodissociation protocol"
  C.fabricationRecipe
  C.carrierPublic
  "DASHI.Chemistry.Spectroscopy.CryogenicMessengerTagActionSpectroscopyExact"
  "JPL public spectroscopy poster and general action-spectroscopy literature"
  "The public protocol is reconstructive at laboratory-method level, subject to apparatus-specific calibration."

spectroscopyCalibrationCarrier : C.ScientificCapabilityCarrier
spectroscopyCalibrationCarrier = C.scientific-capability-carrier
  "cryogenic messenger-tag action spectroscopy"
  "apparatus calibration + mixture-specific discrimination model"
  C.calibrationData
  C.carrierUnknown
  "DASHI.Chemistry.Spectroscopy.CryogenicMessengerTagActionSpectroscopyExact"
  "current public record does not close mission-realistic mixture calibration"
  "Calibration and false-positive behaviour are required to promote laboratory structural discrimination to mission-level identification."

------------------------------------------------------------------------
-- Reconstructive roles.
------------------------------------------------------------------------

alloyProcessWindowReconstructive : C.ReconstructiveCarrierReceipt alloyProcessWindowCarrier
alloyProcessWindowReconstructive = C.reconstructive-carrier-receipt
  C.reproducesProcess
  "processing -> microstructure -> property chain"
  "A closed process window would materially reduce work needed to reproduce the alloy performance, but current access/status remains unresolved."

fissionQualificationReconstructive : C.ReconstructiveCarrierReceipt fissionQualificationCarrier
fissionQualificationReconstructive = C.reconstructive-carrier-receipt
  C.enablesQualification
  "qualification evidence controls mission-readiness promotion"
  "Component lists do not substitute for qualification evidence."

radiographyInverseReconstructive : C.ReconstructiveCarrierReceipt radiographyInverseCarrier
radiographyInverseReconstructive = C.reconstructive-carrier-receipt
  C.enablesExtension
  "calibrated inverse model converts radiographs into physical-state constraints"
  "This carrier can be strategically important without implying that any named individual uniquely possessed it."

spectroscopyProtocolReconstructive : C.ReconstructiveCarrierReceipt spectroscopyProtocolCarrier
spectroscopyProtocolReconstructive = C.reconstructive-carrier-receipt
  C.reproducesExperiment
  "public method chain supports independent laboratory reproduction"
  "Laboratory reproducibility does not imply mission-level biosignature specificity."

------------------------------------------------------------------------
-- Highest-alpha reverse leaves revealed by the science.
------------------------------------------------------------------------

alloyCriticalityTarget : C.ScientificCriticalityReverseObligation
alloyCriticalityTarget = C.scientific-criticality-reverse-obligation
  alloyProcessWindowCarrier
  C.personCarrierPossession
  "identify who actually held process-window, heat-treatment, microstructure and qualification know-how at the relevant event time"
  "a bounded person-to-capability possession proposition"
  "uniqueness, targeting, motive, disappearance causation or homicide"

fissionCriticalityTarget : C.ScientificCriticalityReverseObligation
fissionCriticalityTarget = C.scientific-criticality-reverse-obligation
  fissionQualificationCarrier
  C.carrierReplacementDifficulty
  "recover successor/handover records and whether qualification/failure knowledge was distributed across teams or concentrated in a small role"
  "replacement-difficulty evidence for the technical carrier"
  "person-specific targeting or event causation"

radiographyVisibilityTarget : C.ScientificCriticalityReverseObligation
radiographyVisibilityTarget = C.scientific-criticality-reverse-obligation
  radiographyInverseCarrier
  C.carrierObserverVisibility
  "identify which programme/security/review surfaces could know who had access to experiment-specific inverse/calibration knowledge"
  "whether a capability-aware observer existed"
  "that such an observer selected, targeted or harmed anyone"

record CurrentScientificCapabilityCarrierAssessment : Set where
  constructor current-scientific-capability-carrier-assessment
  field
    domainScienceNowRefinesInvestigation : Bool
    domainScienceNowRefinesInvestigationIsTrue :
      domainScienceNowRefinesInvestigation ≡ true
    personSpecificPossessionGenerallyClosed : Bool
    personSpecificPossessionGenerallyClosedIsFalse :
      personSpecificPossessionGenerallyClosed ≡ false
    replacementDifficultyGenerallyClosed : Bool
    replacementDifficultyGenerallyClosedIsFalse :
      replacementDifficultyGenerallyClosed ≡ false
    commonCapabilityAwareObserverClosed : Bool
    commonCapabilityAwareObserverClosedIsFalse :
      commonCapabilityAwareObserverClosed ≡ false
    commonCausalEventLinkClosed : Bool
    commonCausalEventLinkClosedIsFalse :
      commonCausalEventLinkClosed ≡ false

canonicalCurrentScientificCapabilityCarrierAssessment :
  CurrentScientificCapabilityCarrierAssessment
canonicalCurrentScientificCapabilityCarrierAssessment =
  current-scientific-capability-carrier-assessment
    true refl
    false refl
    false refl
    false refl
    false refl
