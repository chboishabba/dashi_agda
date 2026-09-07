module DASHI.Economics.AIInfrastructureConsumerIndexedFibreAdequacyExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.ConsumerIndexedTrajectoryFibreAdequacyExact as Fibre
import DASHI.Core.SituatedActionabilityFibreExact as ActionFibre
import DASHI.Core.TrajectoryRecoveryFibreExact as RecoveryFibre
import DASHI.Core.MultiaxialIncidenceFibreExact as IncidenceFibre
import DASHI.Economics.DashiTradeAIInfrastructureMarketCrossPollinationExact as Market
import DASHI.Economics.AIInfrastructureGenericFibreAdaptersExact as Generic

------------------------------------------------------------------------
-- AI INFRASTRUCTURE AS A CONSUMER-INDEXED FIBRE APPLICATION
------------------------------------------------------------------------

data AIInfraState : Set where
  cleanExpansion : AIInfraState
  crowdedExpansion : AIInfraState
  impairedRecovery : AIInfraState
  publicLossRecovery : AIInfraState


data AIInfraObservation : Set where
  strongDemandSurface : AIInfraObservation
  recoveredCapacitySurface : AIInfraObservation

data AIInfraConsumer : Set where
  headlineDemandConsumer : AIInfraConsumer
  refinancingConsumer : AIInfraConsumer
  capitalRecoveryConsumer : AIInfraConsumer
  futureConeConsumer : AIInfraConsumer
  incidenceConsumer : AIInfraConsumer


data AIInfraAnswer : Set where
  demandStrongAnswer : AIInfraAnswer
  refinanceAvailableAnswer refinanceUnavailableAnswer : AIInfraAnswer
  capitalRecoveredAnswer capitalImpairedAnswer : AIInfraAnswer
  broadFutureAnswer constrainedFutureAnswer : AIInfraAnswer
  privateIncidenceAnswer publicIncidenceAnswer : AIInfraAnswer


observeAIInfra : AIInfraState → AIInfraObservation
observeAIInfra cleanExpansion = strongDemandSurface
observeAIInfra crowdedExpansion = strongDemandSurface
observeAIInfra impairedRecovery = recoveredCapacitySurface
observeAIInfra publicLossRecovery = recoveredCapacitySurface

answerAIInfra : AIInfraConsumer → AIInfraState → AIInfraAnswer
answerAIInfra headlineDemandConsumer _ = demandStrongAnswer
answerAIInfra refinancingConsumer cleanExpansion = refinanceAvailableAnswer
answerAIInfra refinancingConsumer crowdedExpansion = refinanceUnavailableAnswer
answerAIInfra refinancingConsumer impairedRecovery = refinanceUnavailableAnswer
answerAIInfra refinancingConsumer publicLossRecovery = refinanceUnavailableAnswer
answerAIInfra capitalRecoveryConsumer cleanExpansion = capitalRecoveredAnswer
answerAIInfra capitalRecoveryConsumer crowdedExpansion = capitalImpairedAnswer
answerAIInfra capitalRecoveryConsumer impairedRecovery = capitalImpairedAnswer
answerAIInfra capitalRecoveryConsumer publicLossRecovery = capitalRecoveredAnswer
answerAIInfra futureConeConsumer cleanExpansion = broadFutureAnswer
answerAIInfra futureConeConsumer crowdedExpansion = constrainedFutureAnswer
answerAIInfra futureConeConsumer impairedRecovery = constrainedFutureAnswer
answerAIInfra futureConeConsumer publicLossRecovery = broadFutureAnswer
answerAIInfra incidenceConsumer cleanExpansion = privateIncidenceAnswer
answerAIInfra incidenceConsumer crowdedExpansion = privateIncidenceAnswer
answerAIInfra incidenceConsumer impairedRecovery = privateIncidenceAnswer
answerAIInfra incidenceConsumer publicLossRecovery = publicIncidenceAnswer

aiInfrastructureFibreSystem : Fibre.ConsumerIndexedFibreSystem
aiInfrastructureFibreSystem =
  Fibre.consumerIndexedFibreSystem
    AIInfraState AIInfraObservation AIInfraConsumer AIInfraAnswer
    observeAIInfra answerAIInfra
    "AI infrastructure consumers ask distinct questions over the same situated state fibre: headline demand, refinancing, capital recovery, future cone and incidence do not collapse."

headlineDemandAdequate :
  Fibre.AdequateForConsumer aiInfrastructureFibreSystem headlineDemandConsumer
headlineDemandAdequate =
  NF.factorsThrough (λ _ → demandStrongAnswer) (λ _ → refl)

refinancingDefect :
  Fibre.ConsumerAdequacyDefect aiInfrastructureFibreSystem refinancingConsumer
refinancingDefect =
  NF.nonFactorabilityWitness cleanExpansion crowdedExpansion refl (λ ())

recoveryDefect :
  Fibre.ConsumerAdequacyDefect aiInfrastructureFibreSystem capitalRecoveryConsumer
recoveryDefect =
  NF.nonFactorabilityWitness impairedRecovery publicLossRecovery refl (λ ())

futureConeDefect :
  Fibre.ConsumerAdequacyDefect aiInfrastructureFibreSystem futureConeConsumer
futureConeDefect =
  NF.nonFactorabilityWitness cleanExpansion crowdedExpansion refl (λ ())

incidenceDefect :
  Fibre.ConsumerAdequacyDefect aiInfrastructureFibreSystem incidenceConsumer
incidenceDefect =
  NF.nonFactorabilityWitness impairedRecovery publicLossRecovery refl (λ ())

headlineDemandAdequacyDoesNotPayRefinancing :
  Fibre.AdequateForConsumer aiInfrastructureFibreSystem refinancingConsumer → ⊥
headlineDemandAdequacyDoesNotPayRefinancing =
  Fibre.consumerAdequacyDefectBlocksAdequacy refinancingDefect

sameRecoveredCapacityDoesNotPayRecovery :
  Fibre.AdequateForConsumer aiInfrastructureFibreSystem capitalRecoveryConsumer → ⊥
sameRecoveredCapacityDoesNotPayRecovery =
  Fibre.consumerAdequacyDefectBlocksAdequacy recoveryDefect

sameRecoveredCapacityDoesNotPayIncidence :
  Fibre.AdequateForConsumer aiInfrastructureFibreSystem incidenceConsumer → ⊥
sameRecoveredCapacityDoesNotPayIncidence =
  Fibre.consumerAdequacyDefectBlocksAdequacy incidenceDefect

------------------------------------------------------------------------
-- Existing application donors remain visible but are no longer theorem owners.
------------------------------------------------------------------------

marketActionabilityFibre : ActionFibre.SituatedActionabilityFibre
marketActionabilityFibre = Market.infrastructureActionabilityFibre

genericRecoveryFibre : RecoveryFibre.TrajectoryRecoveryFibre
genericRecoveryFibre = Generic.aiInfrastructureRecoveryFibre

genericIncidenceFibre : IncidenceFibre.MultiaxialIncidenceFibre
genericIncidenceFibre = Generic.aiInfrastructureIncidenceFibre

------------------------------------------------------------------------
-- Consumer-specific missing-coordinate schedule.
------------------------------------------------------------------------

data AIFibreMissingCoordinate : Set where
  refinancingContextCoordinate : AIFibreMissingCoordinate
  financingHistoryCoordinate : AIFibreMissingCoordinate
  residualAssetValueCoordinate : AIFibreMissingCoordinate
  futureOptionalityCoordinate : AIFibreMissingCoordinate
  lossIncidenceCoordinate : AIFibreMissingCoordinate


missingCoordinateFor : AIInfraConsumer → AIFibreMissingCoordinate
missingCoordinateFor headlineDemandConsumer = refinancingContextCoordinate
missingCoordinateFor refinancingConsumer = refinancingContextCoordinate
missingCoordinateFor capitalRecoveryConsumer = financingHistoryCoordinate
missingCoordinateFor futureConeConsumer = futureOptionalityCoordinate
missingCoordinateFor incidenceConsumer = lossIncidenceCoordinate

data HeadlineDemandAdequacyImpliesEconomicAdequacyPermission : Set where

data RefinancingAdequacyImpliesRecoveryAdequacyPermission : Set where

data RecoveryAdequacyImpliesIncidenceAdequacyPermission : Set where

headlineDemandAdequacyDoesNotAutoPromoteToEconomicAdequacy :
  HeadlineDemandAdequacyImpliesEconomicAdequacyPermission → ⊥
headlineDemandAdequacyDoesNotAutoPromoteToEconomicAdequacy ()

refinancingAdequacyDoesNotAutoPromoteToRecoveryAdequacy :
  RefinancingAdequacyImpliesRecoveryAdequacyPermission → ⊥
refinancingAdequacyDoesNotAutoPromoteToRecoveryAdequacy ()

recoveryAdequacyDoesNotAutoPromoteToIncidenceAdequacy :
  RecoveryAdequacyImpliesIncidenceAdequacyPermission → ⊥
recoveryAdequacyDoesNotAutoPromoteToIncidenceAdequacy ()
