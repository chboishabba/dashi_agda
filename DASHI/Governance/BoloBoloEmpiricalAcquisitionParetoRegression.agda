module DASHI.Governance.BoloBoloEmpiricalAcquisitionParetoRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Governance.BoloBoloEmpiricalAcquisitionParetoExact as Frontier

spokesOnFrontier :
  Frontier.Pareto.onParetoFrontier? Frontier.currentPortfolio Frontier.primarySpokesMinutesCell ≡ true
spokesOnFrontier = refl

comparatorWorkloadOnFrontier :
  Frontier.Pareto.onParetoFrontier? Frontier.currentPortfolio Frontier.comparatorWorkloadCell ≡ true
comparatorWorkloadOnFrontier = refl

secondaryExpansionDominated :
  Frontier.Pareto.onParetoFrontier? Frontier.currentPortfolio Frontier.secondaryExpansionCell ≡ false
secondaryExpansionDominated = refl

protectedHoldoutNotEligible :
  Frontier.Pareto.eligible? Frontier.protectedHoldoutCell ≡ false
protectedHoldoutNotEligible = refl

pilotNotYetEligible :
  Frontier.Pareto.eligible? Frontier.targetPilotDataCell ≡ false
pilotNotYetEligible = refl

currentFrontierExact :
  Frontier.Pareto.paretoFrontier Frontier.currentPortfolio ≡
    Frontier.primarySpokesMinutesCell ∷
    Frontier.comparatorWorkloadCell ∷ []
currentFrontierExact = refl

priorityDoesNotPayEvidence :
  Frontier.paretoPriorityPaysEvidence Frontier.canonicalEmpiricalAcquisitionBoundary ≡ false
priorityDoesNotPayEvidence = refl

primaryDeclaredPurposeBaselinePaid :
  Frontier.primaryDeclaredPurposeBaselinePaid Frontier.canonicalEmpiricalAcquisitionBoundary ≡ true
primaryDeclaredPurposeBaselinePaid = refl

intendedSpokesDesignSurfacePaid :
  Frontier.intendedSpokesDesignSurfacePaid Frontier.canonicalEmpiricalAcquisitionBoundary ≡ true
intendedSpokesDesignSurfacePaid = refl

declarationAndDesignDoNotPayOperations :
  Frontier.declarationOrDesignPaysRealizedSpokesControl Frontier.canonicalEmpiricalAcquisitionBoundary ≡ false
declarationAndDesignDoNotPayOperations = refl
