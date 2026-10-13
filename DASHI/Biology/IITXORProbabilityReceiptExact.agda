module DASHI.Biology.IITXORProbabilityReceiptExact where

open import DASHI.Core.Prelude

import DASHI.Biology.IITXORGridAdversarialExact as XOR
import DASHI.Biology.IIT4FiniteProbabilityRepertoireExact as Prob

------------------------------------------------------------------------
-- EXACT FINITE PROBABILITY RECEIPTS FOR THE TWO-BIT XOR SYSTEM
--
-- The same four-state deterministic system introduced by the XOR adversarial
-- owner is evaluated through the generic finite probability machinery.  Its
-- transition map is a permutation of the four states, so every row has total
-- weight 1 and every target has one incoming preimage.  Thus the unconstrained
-- effect marginal is exactly 1/4 at every target.
------------------------------------------------------------------------

row00IsOne :
  Prob.rowWeightTotal XOR.xorTwoBitFiniteCausalSystem (false , false) ≡ 1
row00IsOne = refl

row01IsOne :
  Prob.rowWeightTotal XOR.xorTwoBitFiniteCausalSystem (false , true) ≡ 1
row01IsOne = refl

row10IsOne :
  Prob.rowWeightTotal XOR.xorTwoBitFiniteCausalSystem (true , false) ≡ 1
row10IsOne = refl

row11IsOne :
  Prob.rowWeightTotal XOR.xorTwoBitFiniteCausalSystem (true , true) ≡ 1
row11IsOne = refl

totalTransitionWeightIsFour :
  Prob.totalTransitionWeight XOR.xorTwoBitFiniteCausalSystem ≡ 4
totalTransitionWeightIsFour = refl

conditional10to11IsCertain :
  Prob.effectConditionalFraction
    XOR.xorTwoBitFiniteCausalSystem
    (true , false)
    (true , true)
  ≡ Prob.probabilityFraction 1 1
conditional10to11IsCertain = refl

conditional10to00IsZero :
  Prob.effectConditionalFraction
    XOR.xorTwoBitFiniteCausalSystem
    (true , false)
    (false , false)
  ≡ Prob.probabilityFraction 0 1
conditional10to00IsZero = refl

incoming00IsOne :
  Prob.incomingWeightTotal XOR.xorTwoBitFiniteCausalSystem (false , false) ≡ 1
incoming00IsOne = refl

incoming01IsOne :
  Prob.incomingWeightTotal XOR.xorTwoBitFiniteCausalSystem (false , true) ≡ 1
incoming01IsOne = refl

incoming10IsOne :
  Prob.incomingWeightTotal XOR.xorTwoBitFiniteCausalSystem (true , false) ≡ 1
incoming10IsOne = refl

incoming11IsOne :
  Prob.incomingWeightTotal XOR.xorTwoBitFiniteCausalSystem (true , true) ≡ 1
incoming11IsOne = refl

unconstrained11IsOneQuarter :
  Prob.unconstrainedEffectFraction
    XOR.xorTwoBitFiniteCausalSystem
    (true , true)
  ≡ Prob.probabilityFraction 1 4
unconstrained11IsOneQuarter = refl

unconstrained00IsOneQuarter :
  Prob.unconstrainedEffectFraction
    XOR.xorTwoBitFiniteCausalSystem
    (false , false)
  ≡ Prob.probabilityFraction 1 4
unconstrained00IsOneQuarter = refl

record XORProbabilityReceiptBoundary : Set where
  constructor xorProbabilityReceiptBoundary
  field
    deterministicRowsHaveUnitTotal : Bool
    totalWeightIsFour : Bool
    eachTargetHasOneIncomingPreimage : Bool
    unconstrainedEffectIsUniformQuarter : Bool
    theseReceiptsAlreadyComputePartitionedIITPhi : Bool
    partitionCutProbabilitiesStillRequired : Bool

open XORProbabilityReceiptBoundary public

canonicalXORProbabilityReceiptBoundary : XORProbabilityReceiptBoundary
canonicalXORProbabilityReceiptBoundary =
  xorProbabilityReceiptBoundary
    true true true true false true

unpartitionedProbabilitiesDoNotManufacturePhi :
  theseReceiptsAlreadyComputePartitionedIITPhi
    canonicalXORProbabilityReceiptBoundary ≡ false
unpartitionedProbabilitiesDoNotManufacturePhi = refl
