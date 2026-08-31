module DASHI.SexedHistoricalStatisticalExperimentValidation where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.SexedHistoricalStatisticalExperimentHyperfabricExact as Stats

recordedSexConstructionRegression :
  INF.FactorsThrough Stats.recordedSexSurface Stats.relationalCell → ⊥
recordedSexConstructionRegression =
  Stats.recordedSexCannotRecoverConstructionDirection

constructionPowerRegression :
  INF.FactorsThrough Stats.constructionDirectionSurface Stats.powerContext → ⊥
constructionPowerRegression = Stats.constructionDirectionCannotRecoverPower

associationCausationRegression :
  INF.FactorsThrough Stats.associationSurface Stats.causalStatus → ⊥
associationCausationRegression = Stats.associationCannotRecoverCausalStatus

significanceOutcomeRegression :
  INF.FactorsThrough Stats.significanceSurface Stats.institutionalOutcomeSurface → ⊥
significanceOutcomeRegression = Stats.significanceCannotRecoverInstitutionalOutcome

logisticRoleRegression :
  Stats.dynamicalLogisticMap ≡ Stats.statisticalLogitLink → ⊥
logisticRoleRegression = Stats.dynamicalLogisticRoleIsNotStatisticalLogitRole

canonicalDesignRegression : Stats.SexConstructionStudyDesign
canonicalDesignRegression = Stats.canonicalSexConstructionStudyDesign
