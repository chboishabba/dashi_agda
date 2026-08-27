module DASHI.Trading.DashiTradeDreamRegression where

import DASHI.Trading.PermissionKernel as Legacy
import DASHI.Trading.DashiTradeDreamOptionConeExact as Dream

legacyOwnerRetained : Legacy.Permission
legacyOwnerRetained = Legacy.HOLD

holdRemainsAvailable :
  Dream.Available Dream.cleanLongState Dream.holdAction
holdRemainsAvailable = Dream.holdAlwaysAvailable Dream.cleanLongState

sameProposalWitness :
  Dream.candidateObserver Dream.cleanLongState
  ≡ Dream.candidateObserver Dream.crowdedLongState
sameProposalWitness = Dream.sameLongProposal

buyNonFactorabilityWitness :
  Dream.INF.NonFactorabilityWitness
    Dream.candidateObserver
    (λ state → Dream.actionAvailable state Dream.buyAction)
buyNonFactorabilityWitness = Dream.buyViabilityDoesNotFactorThroughDirection

sameWeightWitness :
  Dream.predictedWeight Dream.sameWeightAccessible
  ≡ Dream.predictedWeight Dream.sameWeightInaccessible
sameWeightWitness = Dream.samePredictedWeightDifferentAccessibility

jointClosureWitness :
  Dream.jointCrowdedBuyAvailable ≡ false
jointClosureWitness = Dream.jointCanStillClose
