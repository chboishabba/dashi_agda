module DASHI.Law.SensibLawWoogaroo9281ExecutionStateResidualExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogaroo9281NegotiatedApprovedGeometryExact as Geometry
import DASHI.Law.SensibLawWoogarooS102StatutorySpatialRelationExact as S102

------------------------------------------------------------------------
-- 9281/2024/OW EXECUTION-STATE RESIDUAL
--
-- The approval and negotiated plan geometry are already acquired. The live
-- uncertainty is whether the approval has moved into a present execution
-- state, and whether prerequisite records have been supplied. Absence from a
-- public web surface is not evidence that a record does not exist.
------------------------------------------------------------------------

data ExecutionEvidenceKind : Set where
  condition6aReceipt : ExecutionEvidenceKind
  prestartMeetingReceipt : ExecutionEvidenceKind
  preclearanceFaunaPlan : ExecutionEvidenceKind
  spotterCatcherReceipt : ExecutionEvidenceKind
  arboristAssessmentReceipt : ExecutionEvidenceKind
  erosionSedimentControlReceipt : ExecutionEvidenceKind
  accessWorksLicenceReceipt : ExecutionEvidenceKind
  issueForConstructionSet : ExecutionEvidenceKind
  commencementNotice : ExecutionEvidenceKind
  fieldExecutionEvidence : ExecutionEvidenceKind

data EvidenceState : Set where
  acquired : EvidenceState
  notInCurrentCorpus : EvidenceState
  publicSurfaceNotLocated : EvidenceState
  conditionalFutureRecord : EvidenceState

record ExecutionEvidenceResidual : Set where
  constructor execution-evidence-residual
  field
    kind : ExecutionEvidenceKind
    state : EvidenceState
    whyItMatters : String
    exactRequest : String
    nonInferenceBoundary : String

open ExecutionEvidenceResidual public

condition6aResidual : ExecutionEvidenceResidual
condition6aResidual = execution-evidence-residual
  condition6aReceipt
  notInCurrentCorpus
  "The negotiated decision requires Commonwealth-related evidence before the prestart meeting. The condition is acquired; satisfaction is not."
  "Provide the record supplied to Council for Condition 6(a), including the DCCEEW determination/letter or Commonwealth approval relied on, its date, and the date Council accepted it as satisfying the condition."
  "The existence of Condition 6(a) does not prove compliance or non-compliance."

prestartResidual : ExecutionEvidenceResidual
prestartResidual = execution-evidence-residual
  prestartMeetingReceipt
  notInCurrentCorpus
  "A prestart record would materially narrow whether the approval has moved from paper approval toward physical execution and would help sequence other prerequisite records."
  "Provide any prestart request, booking, agenda, minutes, attendance record, inspection record, Council acceptance or other record identifying whether and when the prestart meeting occurred."
  "No prestart record in the current corpus does not prove that no prestart meeting occurred."

faunaPlanResidual : ExecutionEvidenceResidual
faunaPlanResidual = execution-evidence-residual
  preclearanceFaunaPlan
  notInCurrentCorpus
  "The negotiated approval requires fauna-management steps before/during habitat disturbance. These records can identify current fauna knowledge, intended clearing sequence and execution readiness."
  "Provide the current pre-clearance fauna management plan and any Council acceptance/review record, including dates and the works/stages to which it applies."
  "A required fauna plan does not prove that clearing has begun or that every fauna risk is resolved."

spotterResidual : ExecutionEvidenceResidual
spotterResidual = execution-evidence-residual
  spotterCatcherReceipt
  notInCurrentCorpus
  "A licensed spotter-catcher engagement or pre-clearance assessment can be a strong execution-readiness signal and may produce current wildlife observations."
  "Provide the appointed spotter-catcher details, licence/authority, pre-clearance assessment, dates, stage/area coverage and any fauna relocation or observation records."
  "Appointment of a spotter-catcher does not itself prove commencement or legal compliance with every condition."

arboristResidual : ExecutionEvidenceResidual
arboristResidual = execution-evidence-residual
  arboristAssessmentReceipt
  notInCurrentCorpus
  "The negotiated approval requires arboricultural assessment before specified clearing near Open Space. That assessment can refine the tree-retention/removal interface and timing."
  "Provide the current arboricultural assessment required for retained trees/clearing near Open Space, together with any Council acceptance and revised protection/retention drawings."
  "An arborist assessment is not a complete site-wide tree inventory and does not itself determine ecological or legal significance."

commencementResidual : ExecutionEvidenceResidual
commencementResidual = execution-evidence-residual
  commencementNotice
  publicSurfaceNotLocated
  "Current or imminent commencement changes urgency and may alter which preservation, evidence-preservation or enforcement route is practically available."
  "Provide any notice of intention to commence, commencement notice, contractor mobilisation record, site possession/handover record, clearing schedule, prestart completion notice or other dated record identifying when physical works may begin or began."
  "Development.i showing an approved application does not prove commencement. A web search that does not surface commencement material does not prove no such record exists."

fieldEvidenceResidual : ExecutionEvidenceResidual
fieldEvidenceResidual = execution-evidence-residual
  fieldExecutionEvidence
  conditionalFutureRecord
  "Dated field evidence can independently establish whether approved clearing/earthworks are merely authorised, imminent, underway or completed."
  "Preserve dated photographs/video, machinery/clearing observations, site signage, contractor notices and location context only if lawfully obtained; retain original metadata where possible."
  "A photograph of machinery or disturbed ground does not automatically identify the approval, stage, responsible actor, legality or exact conduct."

------------------------------------------------------------------------
-- Current execution state is deliberately fail-closed.
------------------------------------------------------------------------

record Current9281ExecutionState : Set where
  constructor current-9281-execution-state
  field
    negotiatedDecisionAcquired : Bool
    negotiatedApprovedPlansAcquired : Bool
    planScaleThreateningProcessGeometryAcquired : Bool
    condition6aTextAcquired : Bool
    condition6aSatisfactionAcquired : Bool
    prestartAcquired : Bool
    commencementAcquired : Bool
    worksCommencedEstablished : Bool
    likelySignificantDetrimentalEffectEstablished : Bool
    exactCurrentQuestion : String

current9281ExecutionState : Current9281ExecutionState
current9281ExecutionState = current-9281-execution-state
  true true true true
  false false false false false
  "What is the present execution state of 9281/2024/OW, and does the current ecological evidence support the s 102 opinion that qualifying wildlife/habitat is subject to a threatening process likely to have a significant detrimental effect?"

------------------------------------------------------------------------
-- Acquisition order: execution evidence before optional GIS refinement.
------------------------------------------------------------------------

record ExecutionAcquisitionOrder : Set where
  constructor execution-acquisition-order
  field
    first : String
    second : String
    third : String
    fourth : String
    fifth : String
    lidarBlocksThisOrder : Bool

currentExecutionAcquisitionOrder : ExecutionAcquisitionOrder
currentExecutionAcquisitionOrder = execution-acquisition-order
  "Condition 6(a) satisfaction record"
  "prestart meeting/request/acceptance record"
  "current pre-clearance fauna / spotter-catcher / arborist records"
  "commencement or contractor-mobilisation chronology"
  "current ecological likely-effect evidence for the s 102 consumer"
  false

------------------------------------------------------------------------
-- WrongType / no-promotion firewalls.
------------------------------------------------------------------------

data ApprovalEqualsCommencement : Set where
data MissingPublicRecordEqualsNoRecord : Set where
data ConditionTextEqualsConditionSatisfied : Set where
data PrestartEqualsClearingStarted : Set where
data SpotterAppointmentEqualsNoSignificantEffect : Set where
data FaunaPlanEqualsS102Defeated : Set where
data GeometryEqualsCurrentExecution : Set where

approvalDoesNotProveCommencement : ApprovalEqualsCommencement → ⊥
approvalDoesNotProveCommencement ()

missingPublicRecordDoesNotProveAbsence : MissingPublicRecordEqualsNoRecord → ⊥
missingPublicRecordDoesNotProveAbsence ()

conditionTextDoesNotProveSatisfaction : ConditionTextEqualsConditionSatisfied → ⊥
conditionTextDoesNotProveSatisfaction ()

prestartDoesNotProveClearingStarted : PrestartEqualsClearingStarted → ⊥
prestartDoesNotProveClearingStarted ()

spotterDoesNotDefeatEffect : SpotterAppointmentEqualsNoSignificantEffect → ⊥
spotterDoesNotDefeatEffect ()

faunaPlanDoesNotDefeatS102 : FaunaPlanEqualsS102Defeated → ⊥
faunaPlanDoesNotDefeatS102 ()

geometryDoesNotProveCurrentExecution : GeometryEqualsCurrentExecution → ⊥
geometryDoesNotProveCurrentExecution ()
