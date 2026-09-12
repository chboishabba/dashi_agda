module DASHI.Law.SensibLawWoogarooEPBC8575BlockingCutsetExecutionStateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- EPBC 2019/8575 BLOCKING CUTSET / EXECUTION-STATE OWNER
--
-- The preservation objective is kept lawful and source-bounded:
-- identify the smallest currently live legal/factual cutset capable of stopping
-- clearing or other implementation of the controlled action.  Local planning
-- approval, federal assessment status, same-object geometry, commencement and
-- injunction standing are separate coordinates.  No source identity imports a
-- conclusion that works are unlawful or that any particular person has standing.
------------------------------------------------------------------------

data EvidenceStatus : Set where
  primaryPaid : EvidenceStatus
  portalStatusPaid : EvidenceStatus
  executionResidualOpen : EvidenceStatus
  legalApplicationResidualOpen : EvidenceStatus

data CutsetCoordinate : Set where
  federalAssessmentState : CutsetCoordinate
  localOperationalWorksState : CutsetCoordinate
  federalControlledActionGate : CutsetCoordinate
  federalInjunctionRoute : CutsetCoordinate
  sameObjectSpatialOverlap : CutsetCoordinate
  commencementOrProposedConduct : CutsetCoordinate
  interestedPersonStanding : CutsetCoordinate

federalRegisterEPBC2026 : Source.AttributedSource
federalRegisterEPBC2026 = Source.mkNoDOISource
  "Commonwealth of Australia"
  "Environment Protection and Biodiversity Conservation Act 1999 — compilation 1 July 2026"
  "Federal Register of Legislation"
  "2026"
  "https://www.legislation.gov.au/C2004A00485/2026-07-01"
  Source.governmentSource
  "Primary current statutory source for sections 67A and 475. Statutory text does not itself establish project-specific conduct, same-object overlap or standing of a particular applicant."
  Source.publicAttribution

federalPortal8575 : Source.AttributedSource
federalPortal8575 = Source.mkNoDOISource
  "Australian Government"
  "Springfield Residential Development — EPBC 2019/8575"
  "EPBC Act Public Portal"
  "2026"
  "https://epbcpublicportal.environment.gov.au/all-notices/project-decision/?id=d951b5fa-9efb-ee11-9f89-00224892a860"
  Source.governmentSource
  "Primary project-status surface currently showing Project Status 'Final Preliminary Documentation Published' and Decision Status 'Published'. The portal status label is not promoted into a Part 9 approval receipt without the actual approval instrument."
  Source.publicAttribution

ipswich9281 : Source.AttributedSource
ipswich9281 = Source.mkNoDOISource
  "Ipswich City Council"
  "9281/2024/OW — Kalina Village 2 Stages 1 to 16"
  "Development.i"
  "2026"
  "https://developmenti.ipswich.qld.gov.au/Home/ApplicationDetailsView?appNo=9281%2F2024%2FOW&type=plan_development_apps"
  Source.governmentSource
  "Primary local planning register showing negotiated approval for operational works including earthworks, vegetation clearing and stormwater over properties also associated with the Springview Village 2/3 planning chain. Local approval does not establish federal EPBC authorisation or actual commencement."
  Source.publicAttribution

ipswich9293 : Source.AttributedSource
ipswich9293 = Source.mkNoDOISource
  "Ipswich City Council"
  "9293/2024/OW — Kalina Village 2 Stages 1 to 4A"
  "Development.i"
  "2026"
  "https://developmenti.ipswich.qld.gov.au/Home/ApplicationDetailsView?appNo=9293%2F2024%2FOW&type=plan_development_apps"
  Source.governmentSource
  "Primary local planning register showing approval for road work, drainage, stormwater, earthworks and signage. This is execution-readiness context only until same-object project geometry and commencement are paid."
  Source.publicAttribution

ipswich9281DocumentRegister : Source.AttributedSource
ipswich9281DocumentRegister = Source.mkNoDOISource
  "Ipswich City Council"
  "9281/2024/OW application document register"
  "eDoc Ipswich"
  "2026"
  "https://edoc.ipswich.qld.gov.au/objective/?env=iccecm&id=1697504&plat=pwy"
  Source.governmentSource
  "Primary document manifest recording a negotiated decision notice and approved plans dated 20 March 2026 plus the earlier decision, tree-retention/removal plan and desktop assessment. The manifest locates exact primary objects but does not substitute for reading their conditions and geometry."
  Source.publicAttribution

record CutsetEvidence : Set where
  constructor cutset-evidence
  field
    coordinate : CutsetCoordinate
    source : Source.AttributedSource
    exactLocator : String
    boundedStatement : String
    status : EvidenceStatus
    importsProjectSpecificIllegality : Bool
    importsProjectSpecificIllegalityIsFalse : importsProjectSpecificIllegality ≡ false

open CutsetEvidence public

federalPortalFinalPDPublished : CutsetEvidence
federalPortalFinalPDPublished = cutset-evidence
  federalAssessmentState
  federalPortal8575
  "EPBC 2019/8575 project status surface"
  "The federal portal currently shows the controlled-action assessment at Final Preliminary Documentation Published. No same-object Part 9 approval instrument has been located in the inspected portal surface."
  portalStatusPaid
  false refl

local9281OperationalWorksApproved : CutsetEvidence
local9281OperationalWorksApproved = cutset-evidence
  localOperationalWorksState
  ipswich9281
  "9281/2024/OW — Approved - Negotiated Decision Approved"
  "Council has approved local operational works described as earthworks, clearing vegetation and stormwater for Kalina Village 2 Stages 1 to 16."
  primaryPaid
  false refl

local9293OperationalWorksApproved : CutsetEvidence
local9293OperationalWorksApproved = cutset-evidence
  localOperationalWorksState
  ipswich9293
  "9293/2024/OW — Approved"
  "Council has approved local operational works for roads, drainage, stormwater, earthworks and signage for Kalina Village 2 Stages 1 to 4A."
  primaryPaid
  false refl

section67AControlledActionGate : CutsetEvidence
section67AControlledActionGate = cutset-evidence
  federalControlledActionGate
  federalRegisterEPBC2026
  "EPBC Act s 67A"
  "Section 67A provides that a person must not take a controlled action unless a relevant Part 9 approval is in operation or another specified statutory exception applies. This is the federal execution gate; project-specific application still requires same-object conduct and exception analysis."
  primaryPaid
  false refl

section475InjunctionRoute : CutsetEvidence
section475InjunctionRoute = cutset-evidence
  federalInjunctionRoute
  federalRegisterEPBC2026
  "EPBC Act s 475"
  "Section 475 permits the Minister or an interested person to apply to the Federal Court for prohibitory, mandatory or interim injunctions concerning conduct that constitutes or would constitute an offence or other contravention. This does not itself establish standing, merits or entitlement to relief in EPBC 2019/8575."
  primaryPaid
  false refl

------------------------------------------------------------------------
-- The actual blocking cutset is conditional, not rhetorical.
------------------------------------------------------------------------

record ExecutionResidual : Set where
  constructor execution-residual
  field
    coordinate : CutsetCoordinate
    paid : Bool
    exactMissingObject : String
    whyItChangesBlockingPosition : String
    acquisitionMayOccurOutOfOrder : Bool
    conclusionMaySkipThisDependency : Bool

open ExecutionResidual public

sameObjectOverlapResidual : ExecutionResidual
sameObjectOverlapResidual = execution-residual
  sameObjectSpatialOverlap
  false
  "9281/2024/OW negotiated decision notice and approved-plan geometry, overlaid against the EPBC 2019/8575 controlled-action/referral and 2026 impact footprints."
  "Local operational-works approval is highly relevant only if the proposed clearing/work to be restrained is paid as the same action or a legally relevant component of the controlled action. Property-level adjacency or shared project naming is not enough."
  true false

commencementEvidenceResidual : ExecutionResidual
commencementEvidenceResidual = execution-residual
  commencementOrProposedConduct
  false
  "Pre-start notices, condition-satisfaction records, fauna/clearing pre-clearance records, contractor mobilisation, site notices, commencement correspondence or other primary evidence of actual/proposed execution under 9281/2024/OW."
  "Section 475 can concern proposed conduct, so proof of imminent/proposed clearing can be as important as proof of completed commencement. The local approval alone does not establish that conduct is occurring or imminent."
  true false

federalApprovalInstrumentResidual : ExecutionResidual
federalApprovalInstrumentResidual = execution-residual
  federalAssessmentState
  false
  "Any actual Part 9 approval/refusal instrument for EPBC 2019/8575, including conditions, decision date, approval holder and any current statutory exception/determination relevant to s 67A."
  "The portal label 'Published' cannot be substituted for the operative approval instrument. Locating an approval would materially change the injunction theory from 'no approval' to compliance/validity/condition analysis."
  true false

standingResidual : ExecutionResidual
standingResidual = execution-residual
  interestedPersonStanding
  false
  "Counsel-grade facts and evidence for the standing limb relied upon under EPBC Act s 475(6)/(7), if an injunction applicant is contemplated."
  "The statute defines interested person broadly in specified circumstances, but DASHI does not infer that any named individual or organisation satisfies those facts without a separate evidentiary carrier."
  true false

------------------------------------------------------------------------
-- WrongType / no-skip firewalls.
------------------------------------------------------------------------

data LocalApprovalEqualsFederalApproval : Set where
data PortalPublishedEqualsPart9Approval : Set where
data SharedPropertyEqualsSameControlledActionGeometry : Set where
data ApprovedOperationalWorksEqualsCommencement : Set where
data Section475ExistenceEqualsInjunctionSuccess : Set where

localApprovalDoesNotEqualFederalApproval : LocalApprovalEqualsFederalApproval → ⊥
localApprovalDoesNotEqualFederalApproval ()

portalPublishedDoesNotEqualPart9Approval : PortalPublishedEqualsPart9Approval → ⊥
portalPublishedDoesNotEqualPart9Approval ()

sharedPropertyDoesNotEqualSameControlledActionGeometry : SharedPropertyEqualsSameControlledActionGeometry → ⊥
sharedPropertyDoesNotEqualSameControlledActionGeometry ()

approvedOperationalWorksDoesNotEqualCommencement : ApprovedOperationalWorksEqualsCommencement → ⊥
approvedOperationalWorksDoesNotEqualCommencement ()

section475DoesNotEqualInjunctionSuccess : Section475ExistenceEqualsInjunctionSuccess → ⊥
section475DoesNotEqualInjunctionSuccess ()

------------------------------------------------------------------------
-- Highest-alpha lawful preservation Pareto.
------------------------------------------------------------------------

data BlockingParetoLeaf : Set where
  exactFederalApprovalInstrument : BlockingParetoLeaf
  localNegotiatedDecisionAndPlans : BlockingParetoLeaf
  sameObjectGISOverlap : BlockingParetoLeaf
  commencementOrImminenceEvidence : BlockingParetoLeaf
  finalPDCumulativeSufficiency : BlockingParetoLeaf
  standingAndCounselReview : BlockingParetoLeaf

record BlockingCutsetPareto : Set where
  constructor blocking-cutset-pareto
  field
    federalApprovalStatusFirst : Bool
    localExecutionGeometrySecond : Bool
    sameObjectOverlapBeforeIllegalityClaim : Bool
    imminenceBeforeEmergencyReliefClaim : Bool
    cumulativeSufficiencyPreservedAsMeritsLane : Bool
    lobbyingCorruptionLaneMayPreemptFederalCutset : Bool
    secondarySourcesMayLocatePrimary : Bool
    secondarySourcesMayPayPrimary : Bool

canonicalBlockingCutsetPareto : BlockingCutsetPareto
canonicalBlockingCutsetPareto = blocking-cutset-pareto
  true true true true true false true false
