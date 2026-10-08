module DASHI.Governance.BoloBoloPairedGovernanceExperimentRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloPairedGovernanceExperimentExact as Experiment

sameContextPreferred :
  Experiment.sameTargetContextPreferredOverUnqualifiedHistoricalTransfer Experiment.canonicalPairedExperimentBoundary ≡ true
sameContextPreferred = refl

costMappingPredeclared :
  Experiment.costMappingMustBeFrozenBeforeOutcomes Experiment.canonicalPairedExperimentBoundary ≡ true
costMappingPredeclared = refl

flatNestedContrastDirect :
  Experiment.flatVersusNestedContrastIsPrimaryStructuralComparison Experiment.canonicalPairedExperimentBoundary ≡ true
flatNestedContrastDirect = refl

interfaceCapacityMeasured :
  Experiment.experimentMustMeasureInterfaceDemandCapacityAndBacklog Experiment.canonicalPairedExperimentBoundary ≡ true
interfaceCapacityMeasured = refl

realisedTopologyAudited :
  Experiment.experimentMustAuditRealisedNotOnlyDeclaredTopology Experiment.canonicalPairedExperimentBoundary ≡ true
realisedTopologyAudited = refl

longitudinalFollowupRequiredForLongRunClaim :
  Experiment.longitudinalFollowupNeededForLongRunClaim Experiment.canonicalPairedExperimentBoundary ≡ true
longitudinalFollowupRequiredForLongRunClaim = refl

capacityMapped :
  Experiment.interfaceCapacityOperationalized Experiment.canonicalCounterfactualTermMappingPlan ≡ true
  × Experiment.concurrentBoundaryDemandOperationalized Experiment.canonicalCounterfactualTermMappingPlan ≡ true
  × Experiment.backlogOperationalized Experiment.canonicalCounterfactualTermMappingPlan ≡ true
capacityMapped = refl , refl , refl

pilotNotLegitimacy :
  Experiment.experimentalCoordinationWinCreatesPoliticalLegitimacy Experiment.canonicalPairedExperimentBoundary ≡ false
pilotNotLegitimacy = refl

pilotNotEcologicalProof :
  Experiment.experimentalCoordinationWinProvesEcologicalViability Experiment.canonicalPairedExperimentBoundary ≡ false
pilotNotEcologicalProof = refl
