module DASHI.Physics.Materials.RezaTestedAlloyTradeoffMatrixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record AlloyExample : Set where
  constructor alloy-example
  field
    label : String
    nickelPct cobaltPct chromiumPct aluminumPct titaniumPct : String
    tensileKsi : Nat
    burnThresholdPsi : Nat
    thresholdIsLowerBound : Bool
    sourceReference : String

open AlloyExample public

example1 : AlloyExample
example1 = alloy-example "Example 1" "71.0" "14.7" "8.2" "2.4" "3.7" 170 10000 false "Jacinto/Hardwick patent tested example matrix"

example2 : AlloyExample
example2 = alloy-example "Example 2" "69.9" "16.6" "8.1" "1.5" "3.9" 187 7000 false "Jacinto/Hardwick patent tested example matrix"

example3 : AlloyExample
example3 = alloy-example "Example 3" "73.6" "12.0" "8.1" "2.4" "3.9" 145 10000 false "Jacinto/Hardwick patent tested example matrix"

example4 : AlloyExample
example4 = alloy-example "Example 4" "70.2" "14.8" "8.2" "3.0" "3.8" 195 6000 true "Jacinto/Hardwick patent tested example matrix; burn threshold reported at least 6000 psi"

example5 : AlloyExample
example5 = alloy-example "Example 5" "68.8" "14.8" "11.0" "1.6" "3.8" 183 10000 false "Jacinto/Hardwick patent tested example matrix"

record PairwiseTradeoffReceipt : Set where
  constructor pairwise-tradeoff-receipt
  field
    left right : AlloyExample
    leftHasHigherBurnThreshold : Bool
    rightHasHigherTensileStrength : Bool
    thereforeNeitherDominatesOnBothObjectives : Bool
    thereforeNeitherDominatesOnBothObjectivesIsTrue :
      thereforeNeitherDominatesOnBothObjectives ≡ true

open PairwiseTradeoffReceipt public

example1Vs2 : PairwiseTradeoffReceipt
example1Vs2 = pairwise-tradeoff-receipt example1 example2 true true true refl

record RezaTradeoffBoundary : Set where
  constructor reza-tradeoff-boundary
  field
    strongestExampleIsAutomaticallyMostBurnResistant : Bool
    strongestExampleIsAutomaticallyMostBurnResistantIsFalse : strongestExampleIsAutomaticallyMostBurnResistant ≡ false
    onePairwiseTradeoffDefinesWholeParetoFront : Bool
    onePairwiseTradeoffDefinesWholeParetoFrontIsFalse : onePairwiseTradeoffDefinesWholeParetoFront ≡ false
    lowerBoundThresholdCanBeTreatedAsExactThreshold : Bool
    lowerBoundThresholdCanBeTreatedAsExactThresholdIsFalse : lowerBoundThresholdCanBeTreatedAsExactThreshold ≡ false
    testedExamplesValidateEveryCompositionInClaimRange : Bool
    testedExamplesValidateEveryCompositionInClaimRangeIsFalse : testedExamplesValidateEveryCompositionInClaimRange ≡ false

canonicalRezaTradeoffBoundary : RezaTradeoffBoundary
canonicalRezaTradeoffBoundary = reza-tradeoff-boundary false refl false refl false refl false refl
