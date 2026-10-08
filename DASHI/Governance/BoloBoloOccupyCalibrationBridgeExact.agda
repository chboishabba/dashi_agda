module DASHI.Governance.BoloBoloOccupyCalibrationBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison
import DASHI.Governance.OccupyMeetingLevelProcessPanelExact as Panel
import DASHI.Governance.OccupyPseudonymousNetworkFeaturesExact as Network
import DASHI.Governance.OccupyOWSDevelopmentInterfaceProcessPanelExact as InterfacePanel
import DASHI.Governance.OccupyPanelMissingnessAuditExact as Missingness
import DASHI.Governance.OccupyDevelopmentDiagnosticsExact as Diagnostics
import DASHI.Governance.OccupyHoldoutPromotionGateExact as HoldoutGate

------------------------------------------------------------------------
-- OCCUPY -> BOLO'BOLO COST-MODEL CALIBRATION SOCKET.
--
-- Occupy is used here as an empirical calibration / falsification source for
-- DASHI's counterfactual model. It is not treated as proof that bolo'bolo
-- works, nor are OWS process observables silently reinterpreted as the cost
-- components required by the federation win theorem.
------------------------------------------------------------------------

data CalibrationTarget : Set where
  removedGlobalCouplingTerm : CalibrationTarget
  boundaryOverheadTerm : CalibrationTarget
  delegationOverheadTerm : CalibrationTarget
  unresolvedDependencyTerm : CalibrationTarget
  documentaryCompletenessTerm : CalibrationTarget

record CalibrationSocket : Set where
  constructor calibrationSocket
  field
    target : CalibrationTarget
    evidenceLabel : String
    observableSurfacePresent : Bool
    coefficientOrBoundIdentified : Bool
    causalInterpretationPaid : Bool

open CalibrationSocket public

removedCouplingSocket : CalibrationSocket
removedCouplingSocket =
  calibrationSocket
    removedGlobalCouplingTerm
    "meeting-level process plus pseudonymous incidence/network features"
    true
    false
    false

boundaryOverheadSocket : CalibrationSocket
boundaryOverheadSocket =
  calibrationSocket
    boundaryOverheadTerm
    "development-only inter-group / liaison / spokes / working-group lexical process surface"
    true
    false
    false

delegationOverheadSocket : CalibrationSocket
delegationOverheadSocket =
  calibrationSocket
    delegationOverheadTerm
    "development-only report-back / delegate / spokes lexical process surface"
    true
    false
    false

unresolvedDependencySocket : CalibrationSocket
unresolvedDependencySocket =
  calibrationSocket
    unresolvedDependencyTerm
    "development-only tabled / mediation plus existing block/process-strain observables"
    true
    false
    false

documentaryCompletenessSocket : CalibrationSocket
documentaryCompletenessSocket =
  calibrationSocket
    documentaryCompletenessTerm
    "source-regime missingness/documentary-completeness audit"
    true
    false
    false

canonicalCalibrationSockets : List CalibrationSocket
canonicalCalibrationSockets =
  removedCouplingSocket
  ∷ boundaryOverheadSocket
  ∷ delegationOverheadSocket
  ∷ unresolvedDependencySocket
  ∷ documentaryCompletenessSocket
  ∷ []

------------------------------------------------------------------------
-- Calibration packet keeps the already-built evidence surfaces attached.
------------------------------------------------------------------------

record BoloOccupyCalibrationPacket : Set where
  constructor boloOccupyCalibrationPacket
  field
    meetingPanel : Panel.MeetingLevelProcessPanel
    networkRows : List Network.NetworkFeatureRow
    interfaceProcessRows : List InterfacePanel.InterfaceProcessRow
    developmentDiagnostics : List Diagnostics.DurationModelDiagnostic
    calibrationSockets : List CalibrationSocket

open BoloOccupyCalibrationPacket public

canonicalBoloOccupyCalibrationPacket : BoloOccupyCalibrationPacket
canonicalBoloOccupyCalibrationPacket =
  boloOccupyCalibrationPacket
    Panel.canonicalMeetingLevelProcessPanel
    Network.canonicalNetworkFeatureRows
    InterfacePanel.canonicalInterfaceProcessRows
    Diagnostics.canonicalDurationDiagnostics
    canonicalCalibrationSockets

------------------------------------------------------------------------
-- Empirical promotion boundary.
------------------------------------------------------------------------

record BoloOccupyCalibrationBoundary : Set where
  constructor boloOccupyCalibrationBoundary
  field
    meetingLevelProcessEvidenceAvailable : Bool
    pseudonymousNetworkEvidenceAvailable : Bool
    boundaryOverheadObservableSurfaceAvailable : Bool
    delegationOverheadObservableSurfaceAvailable : Bool
    unresolvedDependencyObservableSurfaceAvailable : Bool
    documentaryMissingnessAudited : Bool
    currentDurationPredictorPassesDevelopmentGate : Bool
    protectedHoldoutMayBeConsumedNow : Bool

    removedGlobalCouplingCostIdentified : Bool
    boundaryOverheadCostIdentified : Bool
    delegationOverheadCostIdentified : Bool
    unresolvedDependencyOverheadIdentified : Bool
    documentaryCompletenessProved : Bool

    interfaceLexicalCountsIdentifyCostBounds : Bool
    occupyObservablesEqualCoordinationCostTerms : Bool
    occupyAutomaticallyValidatesBoloArchitecture : Bool
    sourceRegimesSilentlyPooled : Bool
    removalPaysOverheadEmpiricallyInstantiated : Bool
    empiricalBoloSuperiorityEstablished : Bool

open BoloOccupyCalibrationBoundary public

canonicalBoloOccupyCalibrationBoundary : BoloOccupyCalibrationBoundary
canonicalBoloOccupyCalibrationBoundary =
  boloOccupyCalibrationBoundary
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- What evidence would actually discharge the counterfactual theorem?
------------------------------------------------------------------------

record BoloComparisonCalibrationObligations : Set where
  constructor boloComparisonCalibrationObligations
  field
    estimateOrBoundRemovedGlobalCouplingCost : Bool
    estimateOrBoundBoundaryOverhead : Bool
    estimateOrBoundDelegationOverhead : Bool
    estimateOrBoundUnresolvedDependencyOverhead : Bool
    auditDocumentaryCompleteness : Bool
    carrySourceRegimeAndContextControls : Bool
    identifyEstimand : Bool
    passDevelopmentGate : Bool
    passSensitivityChecks : Bool
    passProspectiveHoldout : Bool

open BoloComparisonCalibrationObligations public

canonicalCalibrationObligations : BoloComparisonCalibrationObligations
canonicalCalibrationObligations =
  boloComparisonCalibrationObligations
    true true true true true true true true true true

canonicalBoloOccupyCalibrationReceipt : GenericReceipt.GenericReceipt
canonicalBoloOccupyCalibrationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Occupy calibration socket for bolo'bolo counterfactual comparison"
    "DASHI.Governance.BoloBoloOccupyCalibrationBridgeExact"
    "canonicalBoloOccupyCalibrationBoundary / canonicalCalibrationObligations"
    "recasts the Occupy corpus, meeting-level process panel, pseudonymous network features and a development-only interface-process lexical panel as calibration/falsification inputs for the DASHI bolo-federation model; observable text/process surfaces are now present for removed coupling, boundary/interface activity, delegation/reportback activity, unresolved/process-strain activity and documentary completeness"
    "observable surface presence is not parameter identification: report-back/delegate/spokes/liaison/inter-group/working-group/mediation/tabled lexical measurements are not semantic overhead events or cost bounds; no required cost component is identified, protected holdout access remains blocked, and the federation win condition is not empirically instantiated"
    "agda -i . DASHI/Governance/BoloBoloOccupyCalibrationBridgeRegression.agda"
