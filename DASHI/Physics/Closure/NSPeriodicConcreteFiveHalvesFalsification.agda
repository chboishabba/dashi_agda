module DASHI.Physics.Closure.NSPeriodicConcreteFiveHalvesFalsification where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Exact mirror of the sparse shell-energy counterexample in the runner.
--
-- The finite state satisfies the displayed static compact-Gamma thresholds while
-- its squared weighted adjacent ratio is enormous.  This rules out promoting a
-- bare static adjacent-contraction statement from those hypotheses alone.
------------------------------------------------------------------------

counterexampleTargetShell : Nat
counterexampleTargetShell = 4

counterexampleEnergyDenominator : Nat
counterexampleEnergyDenominator = 16777216

counterexampleGammaNumerator counterexampleGammaDenominator : Nat
counterexampleGammaNumerator = 6
counterexampleGammaDenominator = 7

counterexampleOffPacketNumerator counterexampleOffPacketDenominator : Nat
counterexampleOffPacketNumerator = 1
counterexampleOffPacketDenominator = 8

counterexamplePacketFractionNumerator counterexamplePacketFractionDenominator : Nat
counterexamplePacketFractionNumerator = 7
counterexamplePacketFractionDenominator = 8

counterexampleAdjacentWeightedRatioSquared : Nat
counterexampleAdjacentWeightedRatioSquared = 33554432

staticThresholdsSatisfied : Bool
staticThresholdsSatisfied = true

staticAdjacentContractionRefuted : Bool
staticAdjacentContractionRefuted = true

adjacentRatioRegression :
  counterexampleAdjacentWeightedRatioSquared ≡ 33554432
adjacentRatioRegression = refl

pointwiseFiveHalvesTheoremFromStaticThresholds : Bool
pointwiseFiveHalvesTheoremFromStaticThresholds = false

dynamicRemainderOrIntegratedRouteRequired : Bool
dynamicRemainderOrIntegratedRouteRequired = true
