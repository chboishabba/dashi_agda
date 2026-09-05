module DASHI.Physics.Materials.RezaGammaPrimeBurnStrengthTradeoffDepthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Monica A. Jacinto / Dallis Ann Hardwick patent US20040208777A1.
-- This file owns the tested example matrix and the source-stated gamma-prime
-- strength versus burn-resistance tradeoff.

record AlloyExample : Set where
  constructor alloy-example
  field
    label : String
    nickel cobalt chromium titanium aluminum : String
    other : String
    combustionThresholdPsi : String
    tensileStrengthKsi : String
    sourceReference : String

open AlloyExample public

example1 : AlloyExample
example1 = alloy-example "Example 1" "71.5" "16.5" "8.0" "2.5" "1.5" ""
  "10000" "170" "US20040208777A1 Table 1 / Example 1"

example2 : AlloyExample
example2 = alloy-example "Example 2" "69.9" "16.6" "8.1" "3.9" "1.5" ""
  "7000" "187" "US20040208777A1 Table 1 / Example 2"

example3 : AlloyExample
example3 = alloy-example "Example 3" "83.6" "" "8.0" "3.1" "1.3" "4.0 Mo"
  "10000" "145" "US20040208777A1 Table 1 / Example 3"

example4 : AlloyExample
example4 = alloy-example "Example 4" "70.10" "16.4" "7.7" "3.4" "1.4" ".05 C"
  ">=6000" "195" "US20040208777A1 Table 1 / Example 4"

example5 : AlloyExample
example5 = alloy-example "Example 5" "77.2" "" "7.8" "3.4" "1.4" ".04 C"
  "10000" "183" "US20040208777A1 Table 1 / Example 5"

record GammaPrimeTradeoff : Set where
  constructor gamma-prime-tradeoff
  field
    formers : String
    strengthEffect : String
    burnResistanceEffect : String
    designProblem : String
    sourceReference : String

open GammaPrimeTradeoff public

canonicalGammaPrimeTradeoff : GammaPrimeTradeoff
canonicalGammaPrimeTradeoff = gamma-prime-tradeoff
  "Al and Ti are identified as gamma-prime formers"
  "gamma-prime formation can increase selected alloy strength"
  "the patent warns that gamma-prime formation may reduce burn resistance"
  "choose gamma-prime-former content to reach required strength without substantially sacrificing burn resistance, conditional on the rest of the composition"
  "US20040208777A1 paras. [0019], [0029], [0031]"

record ProcessingChain : Set where
  constructor processing-chain
  field
    firstMelt : String
    secondMelt : String
    mechanicalWork : String
    finalForms : String

open ProcessingChain public

canonicalProcessingChain : ProcessingChain
canonicalProcessingChain = processing-chain
  "vacuum induction melting"
  "vacuum arc remelting"
  "mechanical working of the resulting ingot"
  "billet, bar, sheet or plate"

record RezaTradeoffBoundary : Set where
  constructor reza-tradeoff-boundary
  field
    higherTitaniumAlwaysImprovesBothObjectives : Bool
    higherTitaniumAlwaysImprovesBothObjectivesIsFalse : higherTitaniumAlwaysImprovesBothObjectives ≡ false
    example2DominatesExample1OnBothObjectives : Bool
    example2DominatesExample1OnBothObjectivesIsFalse : example2DominatesExample1OnBothObjectives ≡ false
    tableExamplesProveEveryCompositionInsidePatentRange : Bool
    tableExamplesProveEveryCompositionInsidePatentRangeIsFalse : tableExamplesProveEveryCompositionInsidePatentRange ≡ false
    processingHistoryMayAffectPropertyRealisation : Bool
    processingHistoryMayAffectPropertyRealisationIsTrue : processingHistoryMayAffectPropertyRealisation ≡ true

canonicalRezaTradeoffBoundary : RezaTradeoffBoundary
canonicalRezaTradeoffBoundary = reza-tradeoff-boundary false refl false refl false refl true refl

data RezaReverseTarget : Set where
  acquireGammaPrimeFraction
  acquireHeatTreatment
  acquireMicrostructure
  acquireTensileProtocol
  acquireOxygenBurnProtocol
  acquireProcessingHistory
  acquireComparativeAlloyBaseline
  : RezaReverseTarget
