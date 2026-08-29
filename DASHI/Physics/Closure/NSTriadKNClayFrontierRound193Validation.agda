module DASHI.Physics.Closure.NSTriadKNClayFrontierRound193Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNCriticalRawCurlPhysicalSwapRound189Exact as R189
import DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorTangentRound190Exact as R190
import DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorEnergyRound191Exact as R191
import DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorOwnerSplitRound192Exact as R192
import DASHI.Physics.Closure.NSTriadKNCriticalExternalDoubleCommutatorCellsRound193Exact as R193
import DASHI.Physics.Closure.NSTriadKNClayFrontierRound193Exact as Frontier

fullSwapInvariant : R189.round189PhysicalRawCurlProductionSwapInvariant ≡ true
fullSwapInvariant = refl

fullSwapDoesNotCancel : R189.round189FullSwapOrbitProvidesCancellation ≡ false
fullSwapDoesNotCancel = refl

completeDynamics : R190.round190CompleteDoubleCommutatorDynamicsClosed ≡ true
completeDynamics = refl

completeEnergyLedger : R191.round191CompleteProductionEnergyLedgerClosed ≡ true
completeEnergyLedger = refl

completeOwnerSplit : R192.round192CompleteForcingWorkOwnerSplitClosed ≡ true
completeOwnerSplit = refl

externalCellExpansion : R193.round193CompleteExternalDoubleCommutatorCellExpansionClosed ≡ true
externalCellExpansion = refl

packageAStillOpen : Frontier.round193PackageAClosed ≡ false
packageAStillOpen = refl

noClayPromotion : Frontier.round193ClayPromotion ≡ false
noClayPromotion = refl
