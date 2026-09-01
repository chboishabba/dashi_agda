module DASHI.Computation.BFSLayerFibreExact where

-- BFS fibre: vertices in the same discovered distance layer may have residual
-- processing order when the consumer observes only layer membership/distance.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

record BFSLayerState : Set where
  constructor bfsLayerState
  field
    settledDepth : Nat
    currentLayerCode : Nat
    withinLayerSchedule : Bool

open BFSLayerState public

data LayerSwap : Set where identityLayerSwap swapLayerSchedule : LayerSwap

composeSwap : LayerSwap → LayerSwap → LayerSwap
composeSwap identityLayerSwap h = h
composeSwap swapLayerSchedule identityLayerSwap = swapLayerSchedule
composeSwap swapLayerSchedule swapLayerSchedule = identityLayerSwap

actSwap : LayerSwap → BFSLayerState → BFSLayerState
actSwap identityLayerSwap s = s
actSwap swapLayerSchedule (bfsLayerState d layer false) = bfsLayerState d layer true
actSwap swapLayerSchedule (bfsLayerState d layer true) = bfsLayerState d layer false

record BFSObservation : Set where
  constructor bfsObservation
  field observedDepth observedLayer : Nat

observeBFS : BFSLayerState → BFSObservation
observeBFS s = bfsObservation (settledDepth s) (currentLayerCode s)

swapPreservesBFSObservation :
  (g : LayerSwap) (s : BFSLayerState) →
  observeBFS (actSwap g s) ≡ observeBFS s
swapPreservesBFSObservation identityLayerSwap s = refl
swapPreservesBFSObservation swapLayerSchedule (bfsLayerState d layer false) = refl
swapPreservesBFSObservation swapLayerSchedule (bfsLayerState d layer true) = refl

record BFSFibreBoundary : Set where
  constructor bfsFibreBoundary
  field
    intraLayerOrderMayBeResidual : Bool
    intraLayerOrderMayBeResidualIsTrue : intraLayerOrderMayBeResidual ≡ true
    crossLayerOrderMayBeIgnored : Bool
    crossLayerOrderMayBeIgnoredIsFalse : crossLayerOrderMayBeIgnored ≡ false

canonicalBFSFibreBoundary : BFSFibreBoundary
canonicalBFSFibreBoundary = bfsFibreBoundary true refl false refl
