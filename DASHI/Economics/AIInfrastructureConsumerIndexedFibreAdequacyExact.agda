module DASHI.Economics.AIInfrastructureConsumerIndexedFibreAdequacyExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.ConsumerIndexedTrajectoryFibreAdequacyExact as Fibre
import DASHI.Economics.DashiTradeAIInfrastructureMarketCrossPollinationExact as Market
import DASHI.Economics.AIInfrastructureGenericFibreAdaptersExact as Generic

------------------------------------------------------------------------
-- AI INFRASTRUCTURE AS A CONSUMER-INDEXED FIBRE APPLICATION
------------------------------------------------------------------------

data AIInfraState : Set where
  cleanExpansion
  crowdedExpansion
  impairedRecovery
  publicLossRecovery
  : AIInfraState

data AIInfraObservation : Set where
  strongDemandSurface recoveredCapacitySurface : AIInfraObservation

data AIInfraConsumer : Set where
  headlineDemandConsumer
  refinancingConsumer
  capitalRecoveryConsumer
  futureConeConsumer
  incidenceConsumer
  : AIInfraConsumer

data AIInfraAnswer : Set where
  demandStrongAnswer
  refinanceAvailableAnswer refinanceUnavailableAnswer
  capitalRecoveredAnswer capitalImpairedAnswer
  broadFutureAnswer constrainedFutureAnswer
  privateIncidenceAnswer publicIncidenceAnswer
  : AIInfraAnswer

observeAIInfra : AIInfraState → AIInfraObservation
observeAIInfra cleanExpansion = strongDemandSurface
observeAIInfra crowdedExpansion = strongDemandSurface
observeAIInfra impairedRecovery = recoveredCapacitySurface
observeAIInfra publicLossRecovery = recoveredCapacitySurface

answerAIInfra : AIInfraConsumer → AIInfraState → AIInfraAnswer
answerAIInfra headlineDemandConsumer cleanExpansion = demandStrongAnswer
answerAIInfra headlineDemandConsumer crowdedExpansion = demandStrongAnswer
answerAIInfra headlineDemandConsumer impairedRecovery = demandStrongAnswer
answerAIInfra headlineDemandConsumer publicLossRecovery = demandStrongAnswer
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

------------------------------------------------------------------------
-- Same observation is adequate for headline demand but inadequate for richer
-- consumers.
------------------------------------------------------------------------

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

marketActionabilityFibre : DASHI.Core.SituatedActionabilityFibreExact.SituatedActionabilityFibre
marketActionabilityFibre = Market.infrastructureActionabilityFibre

genericRecoveryFibre : DASHI.Core.TrajectoryRecoveryFibreExact.TrajectoryRecoveryFibre
genericRecoveryFibre = Generic.aiInfrastructureRecoveryFibre

genericIncidenceFibre : DASHI.Core.MultiaxialIncidenceFibreExact.MultiaxialIncidenceFibre
genericIncidenceFibre = Generic.aiInfrastructureIncidenceFibre

------------------------------------------------------------------------
-- Consumer-specific missing-coordinate schedule.
------------------------------------------------------------------------

data AIFibreMissingCoordinate : Set where
  refinancingContextCoordinate
  financingHistoryCoordinate
  residualAssetValueCoordinate
  futureOptionalityCoordinate
  lossIncidenceCoordinate
  : AIFibreMissingCoordinate

missingCoordinateFor : AIInfraConsumer → AIFibreMissingCoordinate
missingCoordinateFor headlineDemandConsumer = refinancingContextCoordinate
missingCoordinateFor refinancingConsumer = refinancingContextCoordinate
missingCoordinateFor capitalRecoveryConsumer = financingHistoryCoordinate
missingCoordinateFor futureConeConsumer = futureOptionalityCoordinate
missingCoordinateFor incidenceConsumer = lossIncidenceCoordinate

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

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
