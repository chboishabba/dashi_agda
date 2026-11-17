module DASHI.Governance.BoloBoloEmpiricalAcquisitionParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Governance.BoloBoloOWSSpokesPrimaryLocatorAtlasExact as Spokes
import DASHI.Governance.OccupyDeclaredRealizedControlExact as Declared
import DASHI.Governance.BoloBoloOWSSpokesProposalLineageExact as Proposal

------------------------------------------------------------------------
-- EMPIRICAL ACQUISITION PARETO FRONTIER
--
-- DASHI routing only. This owner does not grade truth, politics, source
-- credibility, or causal effect. It asks which currently admissible
-- acquisitions are non-dominated for the declared historical/comparator
-- calibration consumer.
--
-- The Nat cost/gain values below are DASHI scheduling values only. They are
-- not money, person-hours, probabilities, evidence strength, effect sizes, or
-- source-author claims.
--
-- Current OWS source ladder after the latest acquisition pass:
--
--   PRIMARY CONSTITUTIONAL DECLARATION      paid
--     Principles of Solidarity + Statement of Autonomy
--
--   INTENDED SPOKES DESIGN                  paid as source-bounded lineage
--     original locator + contemporaneous linked presentation + preserved
--     mirror + archival finding aid + later scholarship; rotation/recall/
--     observer/operational design coordinates retained
--
--   REALISED SPOKES OPERATION               unpaid at primary-minute level
--     exact 7/9/14 Nov archival locators known, 11 Nov exact page unresolved,
--     primary minute bodies not materialised in this environment
--
-- Therefore more normative/design-source acquisition is not the live max-cut.
-- Primary operational minutes and comparator realised-control/capacity data
-- remain the non-dominated source-acquisition routes.
------------------------------------------------------------------------

data AcquisitionRequirement : Set where
  recoverPrimarySpokesMinutes : AcquisitionRequirement
  enrichComparatorInterfaceWorkload : AcquisitionRequirement
  expandSecondarySpokesRetrospectives : AcquisitionRequirement
  consumeProtectedGAHoldout : AcquisitionRequirement
  acquireTargetPilotOutcomes : AcquisitionRequirement
  broadGenericGovernanceSweep : AcquisitionRequirement

primarySpokesMinutesCell : Pareto.RequirementCandidate AcquisitionRequirement
primarySpokesMinutesCell =
  Pareto.requirement-candidate
    recoverPrimarySpokesMinutes
    true true true true
    1 8
    "recover primary NYCGA Spokes minute content at the known archival locators and code any source-paid issue-surfacing, framing, facilitation, role-rotation, delegation, block/advance, reportback, repeated-influence, correction-handling and reopening/appeal coordinates; constitutional declarations and intended-design documents are already paid and do not substitute for operation"

comparatorWorkloadCell : Pareto.RequirementCandidate AcquisitionRequirement
comparatorWorkloadCell =
  Pareto.requirement-candidate
    enrichComparatorInterfaceWorkload
    true true true true
    3 6
    "acquire remaining comparator attendance/duration, boundary-demand, interface-capacity/backlog, matched reportback workload and observable realised-control coordinates with institutional-version provenance"

secondaryExpansionCell : Pareto.RequirementCandidate AcquisitionRequirement
secondaryExpansionCell =
  Pareto.requirement-candidate
    expandSecondarySpokesRetrospectives
    true true true true
    2 2
    "expand secondary retrospective discussion of Spokes; useful context but lower current discriminatory gain than recovering the cited primary operational minutes"

protectedHoldoutCell : Pareto.RequirementCandidate AcquisitionRequirement
protectedHoldoutCell =
  Pareto.requirement-candidate
    consumeProtectedGAHoldout
    false true true true
    1 9
    "prospective GA holdout: retained but excluded from current acquisition frontier until the development/promotion gate earns access"

targetPilotDataCell : Pareto.RequirementCandidate AcquisitionRequirement
targetPilotDataCell =
  Pareto.requirement-candidate
    acquireTargetPilotOutcomes
    false true true true
    9 10
    "future target paired-pilot outcomes; not a current historical-source acquisition and not runnable merely because this routing cell exists"

genericSweepCell : Pareto.RequirementCandidate AcquisitionRequirement
genericSweepCell =
  Pareto.requirement-candidate
    broadGenericGovernanceSweep
    true true true true
    4 3
    "broad generic governance literature sweep without a specific live calibration coordinate"

currentPortfolio : List (Pareto.RequirementCandidate AcquisitionRequirement)
currentPortfolio =
  primarySpokesMinutesCell ∷
  comparatorWorkloadCell ∷
  secondaryExpansionCell ∷
  protectedHoldoutCell ∷
  targetPilotDataCell ∷
  genericSweepCell ∷ []

primarySpokesOnFrontier :
  Pareto.onParetoFrontier? currentPortfolio primarySpokesMinutesCell ≡ true
primarySpokesOnFrontier = refl

comparatorWorkloadOnFrontier :
  Pareto.onParetoFrontier? currentPortfolio comparatorWorkloadCell ≡ true
comparatorWorkloadOnFrontier = refl

secondaryExpansionOffFrontier :
  Pareto.onParetoFrontier? currentPortfolio secondaryExpansionCell ≡ false
secondaryExpansionOffFrontier = refl

holdoutExcludedNow : Pareto.eligible? protectedHoldoutCell ≡ false
holdoutExcludedNow = refl

pilotExcludedFromSourceAcquisitionConsumer :
  Pareto.eligible? targetPilotDataCell ≡ false
pilotExcludedFromSourceAcquisitionConsumer = refl

currentParetoFrontierExact :
  Pareto.paretoFrontier currentPortfolio ≡
    primarySpokesMinutesCell ∷ comparatorWorkloadCell ∷ []
currentParetoFrontierExact = refl

locatorBoundary : Spokes.SpokesPrimaryLocatorBoundary
locatorBoundary = Spokes.canonicalSpokesPrimaryLocatorBoundary

declaredBoundary : Declared.OccupyDeclaredRealizedBoundary
declaredBoundary = Declared.canonicalOccupyDeclaredRealizedBoundary

proposalBoundary : Proposal.SpokesProposalLineageBoundary
proposalBoundary = Proposal.canonicalSpokesProposalLineageBoundary

record EmpiricalAcquisitionBoundary : Set where
  constructor empirical-acquisition-boundary
  field
    paretoValuesAreDashIRoutingCalibration : Bool
    paretoPriorityPaysEvidence : Bool
    paretoPriorityUpgradesSourceAuthority : Bool
    locatorIdentityPaysPrimaryMinuteContent : Bool
    secondaryRetrospectiveEqualsPrimaryMinute : Bool
    protectedHoldoutMayBeSpentForModelSelectionNow : Bool
    targetPilotMayRunWithoutAdmissibilityReceipts : Bool
    offFrontierRequirementIsDeleted : Bool
    recomputeFrontierAfterNewAcquisition : Bool

    primaryDeclaredPurposeBaselinePaid : Bool
    intendedSpokesDesignSurfacePaid : Bool
    declarationOrDesignPaysRealizedSpokesControl : Bool
    primaryOperationalSpokesMinutesStillRequired : Bool

open EmpiricalAcquisitionBoundary public

canonicalEmpiricalAcquisitionBoundary : EmpiricalAcquisitionBoundary
canonicalEmpiricalAcquisitionBoundary =
  empirical-acquisition-boundary
    true
    false false false false false false false
    true
    true true false true
