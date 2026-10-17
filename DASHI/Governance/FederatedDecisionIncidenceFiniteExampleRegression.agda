module DASHI.Governance.FederatedDecisionIncidenceFiniteExampleRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.FederatedDecisionIncidenceFiniteExampleExact as Example
import DASHI.Governance.FederatedDecisionIncidenceExact as Incidence

localIssueNotGloballyCoupled :
  ¬ Incidence.GloballyCoupledIssue
      Example.exampleGovernance
      Example.localAIssue
localIssueNotGloballyCoupled =
  Example.exampleLocalIssueNotGloballyCoupled

localVsGlobalIsStrictContraction :
  Incidence.StrictParticipationContraction
    Example.exampleGovernance
    Example.localAIssue
    Example.federationIssue
localVsGlobalIsStrictContraction =
  Example.exampleStrictParticipationContraction

finiteAccountingIsFiveEdges :
  Incidence.totalEdges Example.exampleIncidenceAccounting ≡ 5
finiteAccountingIsFiveEdges = refl

finiteModelIsNotEmpiricalPopulationLaw :
  Example.finiteExampleIsEmpiricalPopulationLaw
    Example.canonicalFiniteExampleBoundary
  ≡ false
finiteModelIsNotEmpiricalPopulationLaw = refl
