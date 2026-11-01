module DASHI.Law.SensibLawWoogaroo9281NegotiatedApprovedGeometryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- 9281/2024/OW APPROVED-GEOMETRY SNOWBALL
--
-- Thin source-specific carrier for the two supplied Council-stamped plan sets.
-- It does not create a second legal/provenance calculus.  The point is to keep
-- original-decision geometry, negotiated-decision geometry, GIS precision,
-- construction status and federal permission as distinct coordinates.
------------------------------------------------------------------------

data ApprovalPlanState : Set where
  originalDecisionPlans : ApprovalPlanState
  negotiatedDecisionPlans : ApprovalPlanState

record ApprovedPlanCarrierReceipt : Set where
  constructor approved-plan-carrier-receipt
  field
    attachmentId : String
    applicationId : String
    state : ApprovalPlanState
    councilStampDate : String
    pageCount : String
    planIdentity : String
    geometryReading : String
    clearingReading : String
    environmentalInterfaceReading : String
    sourceBoundary : String

open ApprovedPlanCarrierReceipt public

original9281ApprovedPlans : ApprovedPlanCarrierReceipt
original9281ApprovedPlans = approved-plan-carrier-receipt
  "A11954489"
  "9281/2024/OW"
  originalDecisionPlans
  "19 September 2025"
  "26 pages"
  "Kalina Village 2 Stages 1 to 16 and External Sewer - Bulk Earthworks; Arcadis project 30192738. Rendered Council approval stamp ties this supplied plan set to 9281/2024/OW and the original decision date."
  "Plan-scale geometry includes stage boundaries, extent-of-work boundaries, earthworks, retaining structures, drainage, O'Dwyer's Gully, Opossum Creek, Village 3 fill area and Springfield Structure Plan Open Space designation."
  "The plans distinguish bulk-earthworks extents from bushfire-management vegetation-clearing extents and carry the Tree Retention and Removal Plan symbology at environmental-corridor interfaces."
  "This is the earlier Council-approved plan state. It is retained separately from the negotiated 20 March 2026 state and is not silently promoted to the current negotiated geometry."
  "Council approval stamp pays planning-plan carrier identity; it does not by itself prove issue-for-construction status, works commencement, federal approval, compliance or machine-precise GIS geometry."

negotiated9281ApprovedPlans : ApprovedPlanCarrierReceipt
negotiated9281ApprovedPlans = approved-plan-carrier-receipt
  "A12705838"
  "9281/2024/OW"
  negotiatedDecisionPlans
  "20 March 2026"
  "29 pages"
  "Kalina Village 2 Stages 1 to 16 and External Sewer - Bulk Earthworks; Arcadis project 30192738. Rendered Council approval stamps tie this supplied plan set to 9281/2024/OW and the negotiated decision date."
  "The negotiated plan set provides the approved plan-scale works surface: stage and existing-stage boundaries, extent-of-work boundary, design/existing contours, walls, drainage, O'Dwyer's Gully, Opossum Creek, Village 3 fill area, DAF mapped waterway and Springfield Structure Plan Open Space designation."
  "The legend expressly carries bushfire-management vegetation-clearing extents, bushland-management zone and Tree Retention and Removal Plan categories for trees retained, retained subject to arborist assessment, removed and of particular ecological value. Revised earthworks sheets are Issue 02 / RFI response dated 15 July 2025."
  "The general arrangement notes require clearing to be strictly in accordance with the Council-approved Vegetation Management Plan and EPBC approval; require an authorised spotter-catcher before/during clearing; and state that tree plots cover only selected works interfaces with environmental corridors. Bushfire clearing outside bulk-earthworks extents is stated to require removal of trees, woody regrowth and tall grass to the prescribed minimum extent."
  "This pays the negotiated approved plan carrier and plan-scale geometry. It does not prove that Condition 6(a) has been satisfied, that clearing has commenced, that every plan note is a statutory condition, or that the drawings are a GIS polygon or an issued-for-construction set."

------------------------------------------------------------------------
-- Consumer-indexed payment state after acquisition.
------------------------------------------------------------------------

record GeometryPaymentState : Set where
  constructor geometry-payment-state
  field
    originalApprovedPlanCarrierPaid : Bool
    negotiatedApprovedPlanCarrierPaid : Bool
    planScaleExtentOfWorksPaid : Bool
    bushfireClearingLayerPaid : Bool
    openSpaceDesignationPaid : Bool
    environmentalCorridorInterfacePaid : Bool
    treeRetentionRemovalInterfacePaid : Bool
    odwyersOpossumContextPaid : Bool
    revisedDrawingLineagePaid : Bool
    exactGISPolygonPaid : Bool
    currentHabitatSpeciesIntersectionPaid : Bool
    frogIDCoordinateIntersectionPaid : Bool
    condition6aCompliancePaid : Bool
    prestartOrCommencementPaid : Bool
    worksActuallyCommencedPaid : Bool
    issuedForConstructionStatusPaid : Bool

currentGeometryPaymentState : GeometryPaymentState
currentGeometryPaymentState = geometry-payment-state
  true true true true true true true true true
  false false false false false false false

record ApprovedGeometryResidual : Set where
  constructor approved-geometry-residual
  field
    firstResidual : String
    legalConsumer : String
    acquisitionAction : String

open ApprovedGeometryResidual public

currentApprovedGeometryResidual : ApprovedGeometryResidual
currentApprovedGeometryResidual = approved-geometry-residual
  "Digitise/georeference the negotiated A12705838 approved plan surface and intersect it with exact current habitat/species/corridor evidence; plan-scale geometry is now paid, machine-precise same-object GIS intersection is not."
  "NCA ss 102-107 threatening-process/significant-detrimental-effect analysis and any exact compliance/enforcement analysis."
  "Acquire the Condition 6(a) satisfaction receipt, prestart/commencement record, current arborist assessment, spotter-catcher/pre-clearance fauna plan and any issued-for-construction/current field set; then perform the GIS join."

------------------------------------------------------------------------
-- The consultant title block and the Council approval stamp are distinct.
------------------------------------------------------------------------

record PlanStatusBoundary : Set where
  constructor plan-status-boundary
  field
    consultantTitleBlock : String
    councilApprovalSurface : String
    coexistWithoutCollapse : Bool

negotiatedPlanStatusBoundary : PlanStatusBoundary
negotiatedPlanStatusBoundary = plan-status-boundary
  "Arcadis drawings retain FOR APPROVAL / NOT TO BE USED FOR CONSTRUCTION title-block language."
  "The supplied A12705838 pages visibly carry a Council approval stamp for 9281/2024/OW dated 20 March 2026."
  true

------------------------------------------------------------------------
-- WrongType / no-promotion firewalls.
------------------------------------------------------------------------

data ApprovedPlanEqualsGISPolygon : Set where
data ApprovedPlanEqualsWorksCommenced : Set where
data ApprovedPlanEqualsCondition6aCompliance : Set where
data CouncilApprovalStampEqualsFederalApproval : Set where
data CouncilApprovalStampEqualsIssuedForConstruction : Set where
data ConsultantNotForConstructionEqualsNoPlanningApproval : Set where
data OriginalPlansEqualNegotiatedPlans : Set where
data PlanTreeSymbolEqualsCurrentSpeciesOccurrence : Set where
data PlanEnvironmentalCorridorEqualsNCA13CriticalHabitat : Set where

approvedPlanDoesNotBecomeGISPolygon : ApprovedPlanEqualsGISPolygon → ⊥
approvedPlanDoesNotBecomeGISPolygon ()

approvedPlanDoesNotProveCommencement : ApprovedPlanEqualsWorksCommenced → ⊥
approvedPlanDoesNotProveCommencement ()

approvedPlanDoesNotProveCondition6a : ApprovedPlanEqualsCondition6aCompliance → ⊥
approvedPlanDoesNotProveCondition6a ()

councilStampDoesNotCreateFederalApproval : CouncilApprovalStampEqualsFederalApproval → ⊥
councilStampDoesNotCreateFederalApproval ()

councilStampDoesNotCreateConstructionIssue : CouncilApprovalStampEqualsIssuedForConstruction → ⊥
councilStampDoesNotCreateConstructionIssue ()

consultantStatusDoesNotErasePlanningApproval : ConsultantNotForConstructionEqualsNoPlanningApproval → ⊥
consultantStatusDoesNotErasePlanningApproval ()

originalAndNegotiatedStatesRemainDistinct : OriginalPlansEqualNegotiatedPlans → ⊥
originalAndNegotiatedStatesRemainDistinct ()

planTreeSymbolDoesNotCreateCurrentOccurrence : PlanTreeSymbolEqualsCurrentSpeciesOccurrence → ⊥
planTreeSymbolDoesNotCreateCurrentOccurrence ()

planCorridorDoesNotCreateNCA13Classification : PlanEnvironmentalCorridorEqualsNCA13CriticalHabitat → ⊥
planCorridorDoesNotCreateNCA13Classification ()
