module DASHI.Physics.Materials.RezaBurnResistantAlloyCompositionTradeoffExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- SOURCE-EXACT FINITE ARITHMETIC FOR THE TWO PATENT EXAMPLES
--
-- Weight fractions are encoded in tenths of a weight-percent so the reported
-- decimal compositions become exact natural-number coordinates.  This pays
-- finite composition closure and the observed cross-example tradeoff only; it
-- does not manufacture a constitutive law for the whole alloy family.
------------------------------------------------------------------------

record FiveElementCompositionTenths : Set where
  constructor composition-tenths
  field
    nickel cobalt chromium aluminum titanium : Nat

open FiveElementCompositionTenths public

compositionSum : FiveElementCompositionTenths → Nat
compositionSum c =
  nickel c + cobalt c + chromium c + aluminum c + titanium c

example1Composition : FiveElementCompositionTenths
example1Composition = composition-tenths 715 165 80 15 25

example2Composition : FiveElementCompositionTenths
example2Composition = composition-tenths 699 166 81 15 39

example1CompositionSumTenths : Nat
example1CompositionSumTenths = compositionSum example1Composition

example2CompositionSumTenths : Nat
example2CompositionSumTenths = compositionSum example2Composition

example1CompositionCloses : example1CompositionSumTenths ≡ 1000
example1CompositionCloses = refl

example2CompositionCloses : example2CompositionSumTenths ≡ 1000
example2CompositionCloses = refl

record FiniteStrengthBurnPoint : Set where
  constructor strength-burn-point
  field
    composition : FiveElementCompositionTenths
    tensileStrengthKsiApprox : Nat
    extinguishingThresholdPsiApprox : Nat

open FiniteStrengthBurnPoint public

example1Point : FiniteStrengthBurnPoint
example1Point = strength-burn-point example1Composition 170 10000

example2Point : FiniteStrengthBurnPoint
example2Point = strength-burn-point example2Composition 187 7000

example2HigherTensileStrength : Bool
example2HigherTensileStrength = true

example1HigherExtinguishingThreshold : Bool
example1HigherExtinguishingThreshold = true

record ObservedTwoPointTradeoff : Set where
  constructor observed-two-point-tradeoff
  field
    lowerStrengthPoint : FiniteStrengthBurnPoint
    higherStrengthPoint : FiniteStrengthBurnPoint
    strengthOrderingObserved : Bool
    burnThresholdOrderingReverses : Bool

observedPatentTradeoff : ObservedTwoPointTradeoff
observedPatentTradeoff = observed-two-point-tradeoff
  example1Point example2Point true true

observedTradeoffDoesNotCreateUniversalMonotonicLaw : Bool
observedTradeoffDoesNotCreateUniversalMonotonicLaw = false

compositionClosureDoesNotPayProcessingState : Bool
compositionClosureDoesNotPayProcessingState = false

compositionClosureDoesNotPayMicrostructure : Bool
compositionClosureDoesNotPayMicrostructure = false
