module DASHI.Law.SensibLawWoogarooEPBC8575BlockingCutsetExecutionStateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- EPBC 2019/8575 BLOCKING CUTSET / EXECUTION-STATE OWNER
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
  "Australian Government / National Environmental Protection Agency"
  "Springfield Residential Development — EPBC 2019/8575"
  "EPBC Act Public Portal"
  "2026"
  "https://epbcpublicportal.environment.gov.au/all-notices/project-decision/?id=3c8edc14-9ffb-ee11-9f89-00224892a860"
  Source.governmentSource
  "Primary project-status surface showing Project Status 'Final Preliminary Documentation Published'. The separate Decision Status field has been observed with differing manifestations while the portal warns status fields are being updated. No portal status string is promoted into Part 9 legal effect without the literal decision instrument."
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
  "Primary document manifest recording the negotiated decision notice and approved plans plus earlier application material. It locates primary objects but does not establish post-decision condition satisfaction or commencement."
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
  "EPBC 2019/8575 Project Status manifestation"
  "The federal portal displays Project Status 'Final Preliminary Documentation Published'. The mutable Decision Status field is not used here to infer operative legal state. No same-object Part 9 approval/refusal instrument has been located in the inspected portal surface."
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
  "Section 67A provides that a person must not take a controlled action unless a relevant Part 9 approval is in operation or another specified statutory exception applies. Project-specific application still requires same-object conduct and exception analysis."
  primaryPaid
  false refl

section475InjunctionRoute : CutsetEvidence
section475InjunctionRoute = cutset-evidence
  federalInjunctionRoute
  federalRegisterEPBC2026
  "EPBC Act s 475"
  "Section 475 provides a Federal Court injunction route concerning conduct that constitutes or would constitute an offence or other contravention. It does not itself establish standing, merits or entitlement to relief for EPBC 2019/8575."
  primaryPaid
  false refl

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
  "Authoritative 9281/2024/OW clearing/work geometry overlaid against authoritative relevant Commonwealth action/approval geometry, separating older 2014/7306 coverage from 2019/8575."
  "Local operational-works approval is blocking-relevant only if the conduct at issue is paid as the same action or legally relevant component. Property-level adjacency or shared naming is not enough."
  true false

commencementEvidenceResidual : ExecutionResidual
commencementEvidenceResidual = execution-residual
  commencementOrProposedConduct
  false
  "Post-decision Condition 6(a) satisfaction/acceptance, same-phase pre-start and environmental-preclearance records, fauna/arborist/access records, mobilisation or other primary evidence of actual/proposed execution under 9281/2024/OW."
  "Both State and federal restraint routes can turn on proposed conduct; local approval alone does not establish actual or imminent execution."
  true false

federalApprovalInstrumentResidual : ExecutionResidual
federalApprovalInstrumentResidual = execution-residual
  federalAssessmentState
  false
  "Any literal Part 9 approval/refusal instrument for EPBC 2019/8575, including conditions, decision date, approval holder and any current statutory exception/determination relevant to s 67A."
  "Portal status manifestations cannot substitute for the operative decision instrument. A Part 9 decision would materially change the federal execution analysis."
  true false

standingResidual : ExecutionResidual
standingResidual = execution-residual
  interestedPersonStanding
  false
  "Counsel-grade facts and evidence for the standing limb relied upon under EPBC Act s 475, if a Federal Court applicant is contemplated."
  "DASHI does not infer that a particular individual or organisation satisfies standing facts without a separate evidentiary carrier."
  true false

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
