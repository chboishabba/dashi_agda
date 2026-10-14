module DASHI.Governance.BoloBoloEmpiricalAcquisitionParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Governance.BoloBoloOWSSpokesPrimaryLocatorAtlasExact as Spokes

------------------------------------------------------------------------
-- EMPIRICAL ACQUISITION PARETO FRONTIER
--
-- DASHI routing only.  This owner does not grade truth, politics, source
-- credibility, or causal effect.  It asks a narrower operational question:
-- among currently admissible acquisitions for the declared historical /
-- comparator calibration consumer, which cells are non-dominated in a small
-- cost-versus-certified-information-gain routing calibration?
--
-- The Nat cost/gain values below are DASHI scheduling values only.  They are
-- not money, person-hours, probabilities, evidence strength, effect sizes, or
-- source-author claims.
--
-- This calibration was recomputed after acquiring the official current Porto
-- Alegre three-hour COP meeting observation.  That acquisition narrows the
-- comparator-duration gap but leaves attendance, interface capacity, delegate /
-- representative reportback burden and richer Mondragon workload unresolved.
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
    1 5
    "recover the primary NYCGA Spokes minutes at the known archival locators; locator identity is already paid but minute content is not"

comparatorWorkloadCell : Pareto.RequirementCandidate AcquisitionRequirement
comparatorWorkloadCell =
  Pareto.requirement-candidate
    enrichComparatorInterfaceWorkload
    true true true true
    3 7
    "after paying one current Porto three-hour meeting observation, acquire remaining Porto/Mondragon attendance, boundary, reportback, capacity and workload observations with institutional-version provenance"

secondaryExpansionCell : Pareto.RequirementCandidate AcquisitionRequirement
secondaryExpansionCell =
  Pareto.requirement-candidate
    expandSecondarySpokesRetrospectives
    true true true true
    2 2
    "expand secondary retrospective discussion of Spokes; useful context but lower current discriminatory gain than recovering the cited primary minutes"

-- The holdout remains important for prospective validation but is not required
-- for the CURRENT acquisition consumer because the development gate has not
-- earned its use.  Exclusion here is protocol preservation, not a claim that
-- the held-out source lacks authority.
protectedHoldoutCell : Pareto.RequirementCandidate AcquisitionRequirement
protectedHoldoutCell =
  Pareto.requirement-candidate
    consumeProtectedGAHoldout
    false true true true
    1 9
    "prospective GA holdout: retained but excluded from current acquisition frontier until the development/promotion gate earns access"

-- Target-pilot outcomes belong to a later direct-study route rather than the
-- present historical/comparator SOURCE-acquisition consumer.  Their acquisition
-- also requires independently paid participant/admissibility receipts.
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

------------------------------------------------------------------------
-- Attribution / routing boundary.
------------------------------------------------------------------------

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
