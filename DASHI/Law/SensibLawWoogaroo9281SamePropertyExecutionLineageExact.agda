module DASHI.Law.SensibLawWoogaroo9281SamePropertyExecutionLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- 9281/2024/OW SAME-PROPERTY / EXECUTION LINEAGE
--
-- This owner pays only the administrative/property lineage exposed by Ipswich
-- Council.  It deliberately does not promote shared parcels/application history
-- into same-polygon identity, actual commencement, or federal contravention.
------------------------------------------------------------------------

data EvidenceStatus : Set where
  councilPrimaryPaid : EvidenceStatus
  geometryResidualOpen : EvidenceStatus
  imminenceResidualOpen : EvidenceStatus

data ExecutionCoordinate : Set where
  negotiatedOperationalWorksApproval : ExecutionCoordinate
  associatedProperties : ExecutionCoordinate
  priorSpringviewPlanningChain : ExecutionCoordinate
  laterLandscapingAndManagementPlanChain : ExecutionCoordinate
  approvedPlanGeometry : ExecutionCoordinate
  commencementImminence : ExecutionCoordinate

application9281 : Source.AttributedSource
application9281 = Source.mkNoDOISource
  "Ipswich City Council"
  "9281/2024/OW — Kalina Village 2 Stages 1 to 16"
  "Development.i"
  "2026"
  "https://developmenti.ipswich.qld.gov.au/Home/ApplicationDetailsView?appNo=9281%2F2024%2FOW&type=plan_development_apps"
  Source.governmentSource
  "Primary Council application surface: negotiated approval for operational works described as earthworks, clearing vegetation and stormwater. The application surface does not itself prove exact clearing geometry or commencement."
  Source.publicAttribution

telopeaProperty : Source.AttributedSource
telopeaProperty = Source.mkNoDOISource
  "Ipswich City Council"
  "1 Telopea Way SPRINGFIELD 4300 — Property Details"
  "Development.i"
  "2026"
  "https://developmenti.ipswich.qld.gov.au/Home/PropertyDetailsView?landNumber=180377"
  Source.governmentSource
  "Primary property-history surface for historic parcel 9995SP307769 / 7.12 ha, listing 9281/2024/OW alongside 6243/2023/LAP, 7477/2022/ADP and later management/landscaping applications. Administrative lineage does not pay same-polygon identity."
  Source.publicAttribution

application9281Documents : Source.AttributedSource
application9281Documents = Source.mkNoDOISource
  "Ipswich City Council"
  "9281/2024/OW application document register"
  "eDoc Ipswich"
  "2026"
  "https://edoc.ipswich.qld.gov.au/objective/?env=iccecm&id=1697504&plat=pwy"
  Source.governmentSource
  "Primary document manifest locating the 20 March 2026 negotiated decision notice and approved plans, plus tree-retention/removal and desktop-assessment material. The manifest identifies the files but does not substitute for their geometry/conditions."
  Source.publicAttribution

record ExecutionLineageEvidence : Set where
  constructor execution-lineage-evidence
  field
    coordinate : ExecutionCoordinate
    source : Source.AttributedSource
    exactLocator : String
    boundedStatement : String
    status : EvidenceStatus
    importsSameActionGeometry : Bool
    importsSameActionGeometryIsFalse : importsSameActionGeometry ≡ false

open ExecutionLineageEvidence public

application9281DecisionState : ExecutionLineageEvidence
application9281DecisionState = execution-lineage-evidence
  negotiatedOperationalWorksApproval
  application9281
  "Approved - Negotiated Decision Approved; decision date 20 March 2026"
  "Council records 9281/2024/OW as decided and approved by negotiated decision for Kalina Village 2 Stages 1 to 16, with operational works including earthworks, stormwater drainage and vegetation clearing."
  councilPrimaryPaid
  false refl

telopeaSamePropertyLineage : ExecutionLineageEvidence
telopeaSamePropertyLineage = execution-lineage-evidence
  associatedProperties
  telopeaProperty
  "1 Telopea Way / historic lot 9995SP307769"
  "The same Council property surface lists 9281/2024/OW, 9293/2024/OW, 6243/2023/LAP, 7477/2022/ADP, 5547/2020/ADP, 4272/2020/ADP, 7477/2022/SSP/A and 2082/2025/MAMC/A over the same historic parcel lineage."
  councilPrimaryPaid
  false refl

springviewToKalinaAdministrativeLineage : ExecutionLineageEvidence
springviewToKalinaAdministrativeLineage = execution-lineage-evidence
  priorSpringviewPlanningChain
  telopeaProperty
  "6243/2023/LAP → 9281/2024/OW / 9293/2024/OW → 2082/2025/MAMC/A"
  "Council's application history materially strengthens the administrative lineage from the Springview Village 2/3 precinct-plan stage into Kalina Village 2 operational works and later landscaping/management-plan stages. This pays administrative continuity only."
  councilPrimaryPaid
  false refl

record ExecutionResidual : Set where
  constructor execution-residual
  field
    coordinate : ExecutionCoordinate
    exactMissingObject : String
    whyNeeded : String
    laterPrimaryMaterialMayDischarge : Bool
    conclusionMaySkip : Bool

open ExecutionResidual public

approvedPlansRemainFirstGeometryLeaf : ExecutionResidual
approvedPlansRemainFirstGeometryLeaf = execution-residual
  approvedPlanGeometry
  "20 March 2026 9281/2024/OW DA Approved Plans - Negotiated Decision, including earthworks/vegetation-clearing polygons, plus the negotiated decision conditions."
  "Shared property and administrative lineage materially strengthen identity, but only the approved drawings overlaid against the EPBC 2019/8575 referral/128-ha impact geometry can pay the exact spatial same-action link."
  true false

prestartAndFaunaRecordsRemainFirstImminenceLeaf : ExecutionResidual
prestartAndFaunaRecordsRemainFirstImminenceLeaf = execution-residual
  commencementImminence
  "Pre-start meeting notices/minutes, fauna spotter-catcher engagement or pre-clearance records, condition-satisfaction material, contractor mobilisation, temporary fencing/site establishment or other primary evidence of proposed/imminent execution."
  "Approval and a maintenance-stage status do not themselves prove that clearing is imminent or has commenced; proposed-conduct evidence is the next payment needed for an emergency-relief theory."
  true false

data LandParcelLineagePaysGeometry : Set where
data ApplicationAssociationPaysCommencement : Set where

data NegotiatedApprovalPaysFederalAuthorisation : Set where

landParcelLineageDoesNotPayGeometry : LandParcelLineagePaysGeometry → ⊥
landParcelLineageDoesNotPayGeometry ()

applicationAssociationDoesNotPayCommencement : ApplicationAssociationPaysCommencement → ⊥
applicationAssociationDoesNotPayCommencement ()

negotiatedApprovalDoesNotPayFederalAuthorisation : NegotiatedApprovalPaysFederalAuthorisation → ⊥
negotiatedApprovalDoesNotPayFederalAuthorisation ()

record ExecutionPareto : Set where
  constructor execution-pareto
  field
    approvedPlansBeforeOverlapConclusion : Bool
    geometryBeforeSameControlledActionConclusion : Bool
    prestartBeforeImminenceConclusion : Bool
    administrativeLineageUsefulButNonDispositive : Bool
    secondaryMayLocatePrimary : Bool
    secondaryMayPayPrimary : Bool

canonical9281ExecutionPareto : ExecutionPareto
canonical9281ExecutionPareto = execution-pareto true true true true true false
