module DASHI.Biology.FRACTRANWreathControlledSymmetryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Henry Cohn, Robert Kleinberg, Balazs Szegedy, Christopher Umans,
-- "Group-theoretic algorithms for matrix multiplication", FOCS 2005.
-- DOI: 10.1109/SFCS.2005.39.
--
-- John D. Dixon and Brian Mortimer, "Permutation Groups", Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- DASHI CONTRIBUTION
--
-- Cross the repository's existing first-enabled FRACTRAN/SSP controller with
-- its existing finite wreath-style local-transform/index-permutation action.
-- Arithmetic state decides whether a symmetry step fires; the fibre assignment
-- carries the local/global symmetry action.  This is an executable finite
-- arithmetic-controlled symmetry machine, not a claim that the Cohn--Umans
-- matrix-multiplication construction or a Monster action has been recovered.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.FRACTRANSSPTransitionExact as F
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Physics.Common.FiniteWreathRefinementExact as W

record ControlledState : Set where
  constructor controlledState
  field
    arithmeticState : F.PrimeValuationState
    fibreAssignment : W.Assignment

open ControlledState public

anyEnabled : F.PrimeValuationState → Bool
anyEnabled state with F.ruleEnabled F.transfer47To59 state
... | true = true
... | false with F.ruleEnabled F.transfer59To71 state
...   | true = true
...   | false with F.ruleEnabled F.transfer71To47 state
...     | true = true
...     | false = F.ruleEnabled F.residual53To47 state

controlledAssignmentStep :
  F.PrimeValuationState → W.Assignment → W.Assignment
controlledAssignmentStep state assignment with anyEnabled state
... | true = W.localPermutationStep assignment
... | false = assignment

controlledStep : ControlledState → ControlledState
controlledStep state =
  controlledState
    (F.firstEnabledStep (arithmeticState state))
    (controlledAssignmentStep
      (arithmeticState state)
      (fibreAssignment state))

canonicalControlledState : ControlledState
canonicalControlledState =
  controlledState F.canonicalPrimeState W.canonicalAssignment

canonicalControlIsEnabled : anyEnabled F.canonicalPrimeState ≡ true
canonicalControlIsEnabled = refl

canonicalControlledArithmeticStep :
  arithmeticState (controlledStep canonicalControlledState)
  ≡ F.firstCanonicalTransfer
canonicalControlledArithmeticStep = F.canonicalPriorityUses47To59

canonicalControlledLeft :
  fibreAssignment (controlledStep canonicalControlledState) W.leftSite
  ≡ W.neutralState
canonicalControlledLeft = W.canonicalStepLeft

canonicalControlledRight :
  fibreAssignment (controlledStep canonicalControlledState) W.rightSite
  ≡ W.positiveState
canonicalControlledRight = W.canonicalStepRight

-- When two successive arithmetic states both enable a symmetry move, the
-- wreath assignment returns pointwise because the existing local permutation
-- step is involutive.  The arithmetic controller itself need not return.
twoFiredWreathStepsReturn :
  (assignment : W.Assignment) (site : W.TwoSite) →
  W.localPermutationStep (W.localPermutationStep assignment) site
  ≡ assignment site
twoFiredWreathStepsReturn = W.localPermutationStepTwiceAt

------------------------------------------------------------------------
-- Binary execution predicate versus triadic oriented residual.
--
-- Two bits can encode all three local states, proving expressive sufficiency
-- for this finite carrier.  Nothing here proves equal local rule count, MDL,
-- transition cost, normal-form size or equivariance cost.
------------------------------------------------------------------------

data Bit : Set where
  bit0 bit1 : Bit

encodeTriState : W.TriState → Bit × Bit
encodeTriState W.negativeState = bit0 , bit0
encodeTriState W.neutralState = bit0 , bit1
encodeTriState W.positiveState = bit1 , bit0

decodeTriState : Bit × Bit → W.TriState
decodeTriState (bit0 , bit0) = W.negativeState
decodeTriState (bit0 , bit1) = W.neutralState
decodeTriState (bit1 , bit0) = W.positiveState
decodeTriState (bit1 , bit1) = W.neutralState

decodeEncodeTriState :
  (state : W.TriState) → decodeTriState (encodeTriState state) ≡ state
decodeEncodeTriState W.negativeState = refl
decodeEncodeTriState W.neutralState = refl
decodeEncodeTriState W.positiveState = refl

executionPredicateIsBoolean : ControlledState → Bool
executionPredicateIsBoolean state = anyEnabled (arithmeticState state)

-- Reuse the full signed SSP weave's genuinely three-way orientation rather
-- than encoding it into the Boolean control predicate.
orientationCarrier : Set
orientationCarrier = Signed.FibreOrientation

record ControlledWreathClaimScope : Set where
  constructor controlledWreathClaimScope
  field
    arithmeticControlledFiniteSymmetryConstructed : Bool
    arithmeticControlledFiniteSymmetryConstructedIsTrue :
      arithmeticControlledFiniteSymmetryConstructed ≡ true

    binaryEncodingOfThreeLocalStatesConstructed : Bool
    binaryEncodingOfThreeLocalStatesConstructedIsTrue :
      binaryEncodingOfThreeLocalStatesConstructed ≡ true

    expressiveEncodingProvesEqualRepresentationCost : Bool
    expressiveEncodingProvesEqualRepresentationCostIsFalse :
      expressiveEncodingProvesEqualRepresentationCost ≡ false

    cohnUmansAlgorithmRecovered : Bool
    cohnUmansAlgorithmRecoveredIsFalse :
      cohnUmansAlgorithmRecovered ≡ false

    monsterActionConstructed : Bool
    monsterActionConstructedIsFalse :
      monsterActionConstructed ≡ false

canonicalControlledWreathClaimScope : ControlledWreathClaimScope
canonicalControlledWreathClaimScope =
  controlledWreathClaimScope
    true refl
    true refl
    false refl
    false refl
    false refl
