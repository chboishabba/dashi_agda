module DASHI.Trading.DashiTradeDreamRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Core.IntersectionalNonFactorability as INF
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
  INF.NonFactorabilityWitness
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
