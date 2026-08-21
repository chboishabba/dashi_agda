module DASHI.Biology.TwoBoundaryRepairModesExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- THREE DISTINCT WAYS TO WIDEN A TWO-BOUNDARY CORRIDOR
--
-- resource repair        : widen forward/world accessibility
-- future-model repair    : widen represented backward compatibility
-- coupling repair        : improve their intersection without identifying
--                          either boundary with the other
------------------------------------------------------------------------

data ResourceAccess : Set where restrictedResources expandedResources : ResourceAccess
data FutureModel : Set where threatPrediction flexiblePrediction : FutureModel
data CouplingState : Set where rigidCoupling flexibleCoupling : CouplingState

data HistoryCarrier : Set where retainedPast : HistoryCarrier

record CorridorState : Set where
  constructor corridorState
  field
    resources : ResourceAccess
    futureModel : FutureModel
    coupling : CouplingState
    history : HistoryCarrier

open CorridorState public

contractedCorridor : CorridorState
contractedCorridor = corridorState restrictedResources threatPrediction rigidCoupling retainedPast

resourceRepaired : CorridorState
resourceRepaired = corridorState expandedResources threatPrediction rigidCoupling retainedPast

futureModelRepaired : CorridorState
futureModelRepaired = corridorState restrictedResources flexiblePrediction rigidCoupling retainedPast

couplingRepaired : CorridorState
couplingRepaired = corridorState restrictedResources threatPrediction flexibleCoupling retainedPast

corridorWidth : CorridorState → Nat
corridorWidth (corridorState restrictedResources threatPrediction rigidCoupling retainedPast) = 1
corridorWidth (corridorState expandedResources threatPrediction rigidCoupling retainedPast) = 2
corridorWidth (corridorState restrictedResources flexiblePrediction rigidCoupling retainedPast) = 2
corridorWidth (corridorState restrictedResources threatPrediction flexibleCoupling retainedPast) = 2
corridorWidth (corridorState expandedResources flexiblePrediction rigidCoupling retainedPast) = 3
corridorWidth (corridorState expandedResources threatPrediction flexibleCoupling retainedPast) = 3
corridorWidth (corridorState restrictedResources flexiblePrediction flexibleCoupling retainedPast) = 3
corridorWidth (corridorState expandedResources flexiblePrediction flexibleCoupling retainedPast) = 3

resourceRepairWidensCorridor :
  corridorWidth contractedCorridor ≡ corridorWidth resourceRepaired → ⊥
resourceRepairWidensCorridor ()

futureModelRepairWidensCorridor :
  corridorWidth contractedCorridor ≡ corridorWidth futureModelRepaired → ⊥
futureModelRepairWidensCorridor ()

couplingRepairWidensCorridor :
  corridorWidth contractedCorridor ≡ corridorWidth couplingRepaired → ⊥
couplingRepairWidensCorridor ()

resourceRepairIsNotFutureModelRepair : resourceRepaired ≡ futureModelRepaired → ⊥
resourceRepairIsNotFutureModelRepair ()

futureModelRepairIsNotCouplingRepair : futureModelRepaired ≡ couplingRepaired → ⊥
futureModelRepairIsNotCouplingRepair ()

couplingRepairIsNotResourceRepair : couplingRepaired ≡ resourceRepaired → ⊥
couplingRepairIsNotResourceRepair ()

allRepairsPreserveHistory :
  history resourceRepaired ≡ history contractedCorridor
  × history futureModelRepaired ≡ history contractedCorridor
  × history couplingRepaired ≡ history contractedCorridor
allRepairsPreserveHistory = refl , (refl , refl)

record TwoBoundaryRepairBoundary : Set where
  constructor twoBoundaryRepairBoundary
  field
    wideningRequiresHistoryErasure : Bool
    resourceAndPredictionRepairAreIdentical : Bool
    predictionAndCouplingRepairAreIdentical : Bool
    severalRepairCoordinatesCanWidenCorridor : Bool

canonicalTwoBoundaryRepairBoundary : TwoBoundaryRepairBoundary
canonicalTwoBoundaryRepairBoundary =
  twoBoundaryRepairBoundary false false false true
