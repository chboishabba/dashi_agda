module DASHI.Governance.BoloBoloEmpiricalAcquisitionParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Governance.BoloBoloOWSSpokesPrimaryLocatorAtlasExact as Spokes

------------------------------------------------------------------------
-- EMPIRICAL ACQUISITION PARETO FRONTIER
--
-- DASHI routing only. This owner does not grade truth, politics, source
-- credibility, or causal effect. It asks a narrower operational question:
-- among currently admissible acquisitions for the declared historical /
-- comparator calibration consumer, which cells are non-dominated in a small
-- cost-versus-certified-information-gain routing calibration?
--
-- The Nat cost/gain values below are DASHI scheduling values only. They are
-- not money, person-hours, probabilities, evidence strength, effect sizes, or
-- source-author claims.
--
-- This calibration was recomputed after acquiring:
--   * official current Porto Alegre process observations;
--   * MONDRAGON corporation/governance-capacity observations;
--   * the anarchist/horizontal leadership-tension SOTA atlas;
--   * the Cybersyn/VSM + POSIWID source boundary;
--   * the realised-control acquisition surface.
--
-- The primary OWS/Spokes consumer is therefore no longer generic "minutes".
-- It seeks source-paid realised-control coordinates: issue surfacing, framing,
-- facilitation, role rotation, delegation, block/advance events, reportback,
-- repeated influence, correction handling and reopening/appeal.  These are
-- descriptive/control-topology observables only; they do not themselves pay
-- domination, legitimacy or causal-effect claims.
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
    "recover primary NYCGA Spokes minute content at the known archival locators and code any source-paid issue-surfacing, framing, facilitation, role-rotation, delegation, block/advance, reportback, repeated-influence, correction-handling and reopening/appeal coordinates; locator identity alone pays none of that content"

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
    "expand secondary retrospective discussion of Spokes; useful context but lower current discriminatory gain than recovering the cited primary minutes"

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

open EmpiricalAcquisitionBoundary public

canonicalEmpiricalAcquisitionBoundary : EmpiricalAcquisitionBoundary
canonicalEmpiricalAcquisitionBoundary =
  empirical-acquisition-boundary
    true
    false false false false false false false
    true
