module DASHI.WorldModel.VERIDNSExistingEvidenceConvergenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Programmes.CFDExact as CFD
import DASHI.Programmes.ResearchProgrammeExact as Programme
import DASHI.Core.ResidualConditionedExperimentPortfolioExact as Portfolio
import DASHI.Core.CostedResidualInformationChoiceExact as Costed
import DASHI.Reasoning.BlockedImplicationExperimentBackpropExact as Backprop
import DASHI.Physics.Closure.DashiCFDThetaRuntimeDiagnosticReceipt as Theta
import DASHI.WorldModel.VERIDNSFiniteTwinContactExact as NS

------------------------------------------------------------------------
-- Reuse of *previously executed* NS diagnostics and existing adaptive
-- residual scheduler. Simulation parity, fitted bounds, and physical or
-- theorem claims remain separate. This module does not rerun CFD.
------------------------------------------------------------------------

existingCFDProgramme : Programme.ResearchProgramme
existingCFDProgramme = CFD.dashiCFDProgramme

initialExperiment :
  Portfolio.ResidualConditionedSelection
    Portfolio.toyPortfolio
    Portfolio.chemistryUnresolved
    Portfolio.mechanismConsumer
    Portfolio.measurementAuthority
initialExperiment = Portfolio.initialSelection

postEvidenceExperiment :
  Portfolio.ResidualConditionedSelection
    Portfolio.toyPortfolio
    Portfolio.chemistryResolvedDownstreamLive
    Portfolio.mechanismConsumer
    Portfolio.measurementAuthority
postEvidenceExperiment = Portfolio.laterSelection

residualUpdateChangesSelection :
  Portfolio.selected initialExperiment ≡
  Portfolio.selected postEvidenceExperiment → ⊥
residualUpdateChangesSelection =
  Portfolio.selectionChangesAfterResidualUpdate

existingThetaStressTestRoles : List Theta.RuntimeStressTestRole
existingThetaStressTestRoles = Theta.canonicalRuntimeStressTestRoles

existingFiniteRHSModeClosure : Bool
existingFiniteRHSModeClosure = NS.finiteRHSCoordinateRetentionBoundary

record EvidenceConvergenceBoundary : Set where
  constructor evidenceConvergenceBoundary
  field
    matchedCutoffEvidenceExistsInRepository : Bool
    diagnosticHasHeldOutFalsification : Bool
    acquisitionEqualsAnalyticUniformEstimate : Bool
    numericalParityAutomaticallyProvesContinuum : Bool
    experimentSelectionAutomaticallyExecutes : Bool

canonicalEvidenceConvergenceBoundary : EvidenceConvergenceBoundary
canonicalEvidenceConvergenceBoundary =
  evidenceConvergenceBoundary true true false false false

existingExperimentPortfolioBoundary :
  Portfolio.ResidualConditionedPortfolioBoundary
existingExperimentPortfolioBoundary =
  Portfolio.canonicalResidualConditionedPortfolioBoundary

existingBackpropBoundary : Backprop.BlockedImplicationBackpropBoundary
existingBackpropBoundary =
  Backprop.canonicalBlockedImplicationBackpropBoundary
