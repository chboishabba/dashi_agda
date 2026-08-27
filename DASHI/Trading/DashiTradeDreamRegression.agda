module DASHI.Trading.DashiTradeDreamRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Core.DeclaredRealizedIntegrityResidualExact as Integrity
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Trading.PermissionKernel as Legacy
import DASHI.Trading.DashiTradeDreamOptionConeExact as Dream
import DASHI.Trading.TradingDeclaredRealizedViabilityBridgeExact as DeclaredRealized

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

declaredRealizedObserverReused :
  Integrity.SituatedIntegrityObserver
    DeclaredRealized.TradingAgent
    Dream.TradingFabricState
    Dream.Direction
    Agda.Builtin.Bool.Bool
    DeclaredRealized.ViabilityResidual
declaredRealizedObserverReused =
  DeclaredRealized.tradingProposalViabilityObserver

sameProposalDifferentResidualWitness :
  Integrity.integrityResidual
    DeclaredRealized.tradingProposalViabilityObserver
    DeclaredRealized.canonicalTradingAgent
    Dream.cleanLongState
  ≡ Integrity.integrityResidual
      DeclaredRealized.tradingProposalViabilityObserver
      DeclaredRealized.canonicalTradingAgent
      Dream.crowdedLongState →
  Data.Empty.⊥
sameProposalDifferentResidualWitness =
  DeclaredRealized.sameProposalDifferentResidual
