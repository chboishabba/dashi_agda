module DASHI.Biology.IITXOREffectCutReceiptExact where

open import DASHI.Core.Prelude

import DASHI.Biology.StateDependentMultiplexTransducer as Gate
import DASHI.Biology.IIT4FiniteCausalStructureExact as IIT4
import DASHI.Biology.IIT4FiniteProbabilityRepertoireExact as Prob
import DASHI.Biology.IIT4SystemPhiInputExact as Phi
import DASHI.Biology.IIT4SymbolicScalarBackendExact as Symbolic
import DASHI.Biology.IITXORGridAdversarialExact as XOR

------------------------------------------------------------------------
-- ONE SOURCE-FAITHFUL DIRECTIONAL CUT ON THE TWO-BIT XOR SYSTEM
--
-- Unit false is the parity-output unit and unit true is the copied-left unit.
-- The directed partition below cuts the input from the copied-left/right side
-- into the parity unit while leaving the reverse direction intact.  For source
-- state (true,false), noising the right input uniformly over {false,true}
-- changes the probability of target (true,true) from 1 to 1/2.
--
-- This is the finite Eq. (18) causal-marginalisation step for this fixture.
------------------------------------------------------------------------

leftUnitMask : IIT4.UnitMask XOR.xorTwoBitFiniteCausalSystem
leftUnitMask false = true
leftUnitMask true = false

rightUnitMask : IIT4.UnitMask XOR.xorTwoBitFiniteCausalSystem
rightUnitMask false = false
rightUnitMask true = true

leftPart : IIT4.DirectedPart XOR.xorTwoBitFiniteCausalSystem
leftPart =
  IIT4.directedPart
    leftUnitMask
    IIT4.cutInputs
    "parity unit: cut input arriving from the other part"

rightPart : IIT4.DirectedPart XOR.xorTwoBitFiniteCausalSystem
rightPart =
  IIT4.directedPart
    rightUnitMask
    IIT4.cutOutputs
    "copied-left unit: its output toward the parity part is cut"

oneWayXorPartition : IIT4.SystemPartition XOR.xorTwoBitFiniteCausalSystem
oneWayXorPartition =
  IIT4.systemPartition
    (leftPart ∷ rightPart ∷ [])
    "two-part right-to-left XOR input cut"
    1
    "two nonempty singleton parts"
    "Bool unit carrier split by false/true singleton masks"

oneWayCutAffectsOnePairwiseConnection :
  IIT4.affectedConnectionCount oneWayXorPartition ≡ 1
oneWayCutAffectsOnePairwiseConnection = refl

trueIndicator : Bool → Nat
trueIndicator false = 0
trueIndicator true = 1

-- Hold the left/source bit true and causally marginalize the cut right input.
rightNoiseFalseSupportsTargetParityTrue : Nat
rightNoiseFalseSupportsTargetParityTrue =
  trueIndicator (Gate.xor true false)

rightNoiseTrueSupportsTargetParityTrue : Nat
rightNoiseTrueSupportsTargetParityTrue =
  trueIndicator (Gate.xor true true)

causalMarginalizedSupportCount : Nat
causalMarginalizedSupportCount =
  rightNoiseFalseSupportsTargetParityTrue
  + rightNoiseTrueSupportsTargetParityTrue

causalMarginalizedSupportCountIsOne :
  causalMarginalizedSupportCount ≡ 1
causalMarginalizedSupportCountIsOne = refl

partitionedEffect10to11 : Prob.ProbabilityFraction
partitionedEffect10to11 =
  Prob.probabilityFraction causalMarginalizedSupportCount 2

partitionedEffect10to11IsHalf :
  partitionedEffect10to11 ≡ Prob.probabilityFraction 1 2
partitionedEffect10to11IsHalf = refl

unpartitionedEffect10to11 : Prob.ProbabilityFraction
unpartitionedEffect10to11 =
  Prob.effectConditionalFraction
    XOR.xorTwoBitFiniteCausalSystem
    (true , false)
    (true , true)

unpartitionedEffect10to11IsOne :
  unpartitionedEffect10to11 ≡ Prob.probabilityFraction 1 1
unpartitionedEffect10to11IsOne = refl

effectLoss10to11 : Phi.ProbabilityLossInput
effectLoss10to11 =
  Phi.probabilityLossInput
    (Prob.probabilityFraction 1 1)
    unpartitionedEffect10to11
    partitionedEffect10to11
    "IIT4 effect-side loss for source 10, target 11, one-way XOR cut"

symbolicIntegratedEffect10to11 : Symbolic.SymbolicScore
symbolicIntegratedEffect10to11 =
  Phi.integratedSideScore Symbolic.symbolicBackend effectLoss10to11

symbolicIntegratedEffect10to11IsExactEquationTree :
  symbolicIntegratedEffect10to11 ≡
  Symbolic.probabilityWeightedTerm
    (Prob.probabilityFraction 1 1)
    (Symbolic.positiveLogRatioTerm
      (Prob.probabilityFraction 1 1)
      (Prob.probabilityFraction 1 2))
symbolicIntegratedEffect10to11IsExactEquationTree = refl

record XOREffectCutBoundary : Set where
  constructor xorEffectCutBoundary
  field
    usesCanonicalDirectionalPartition : Bool
    cutConnectionReplacedByUniformNoise : Bool
    finiteMarginalizationComputedExactly : Bool
    unpartitionedTargetProbabilityIsOne : Bool
    partitionedTargetProbabilityIsHalf : Bool
    positiveLogRatioInputIsTwoToOne : Bool
    symbolicExpressionIsNumericalBitValue : Bool
    causeSideAndMIPStillSeparateObligations : Bool

open XOREffectCutBoundary public

canonicalXOREffectCutBoundary : XOREffectCutBoundary
canonicalXOREffectCutBoundary =
  xorEffectCutBoundary
    true true true true true true false true

symbolicEffectDoesNotPretendToBeEvaluatedBits :
  symbolicExpressionIsNumericalBitValue canonicalXOREffectCutBoundary ≡ false
symbolicEffectDoesNotPretendToBeEvaluatedBits = refl
