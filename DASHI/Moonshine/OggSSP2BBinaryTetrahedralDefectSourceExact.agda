module DASHI.Moonshine.OggSSP2BBinaryTetrahedralDefectSourceExact where

------------------------------------------------------------------------
-- SOURCE MEANING OF THE FIVE DEFECT NUMBERS
--
-- The binary tetrahedral group 2T ~= SL(2,3) has order 24.  Its conjugacy
-- classes have element orders
--
--   1, 2, 3, 3, 4, 6, 6
--
-- and class sizes
--
--   1, 1, 4, 4, 6, 4, 4.
--
-- Grouping by element order gives five strata 1,2,4,3,6.  Representative
-- centralizer orders are therefore
--
--   24,24,4,6,6,
--
-- whose exact powers of two are
--
--   8,8,4,2,2 = 2^3,2^3,2^2,2^1,2^1.
--
-- Hence the independently defined 2-adic centralizer-exponent profile is
-- exactly
--
--   3,3,2,1,1.
--
-- This pays the meaning of the defect vector.  It does not identify the
-- repository Completion10 modes with these binary-tetrahedral order strata.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- 1. Five order strata.
------------------------------------------------------------------------

data OrderStratum : Set where
  identity centralMinusOne orderFour orderThree orderSix : OrderStratum

representativeOrder : OrderStratum → Nat
representativeOrder identity = 1
representativeOrder centralMinusOne = 2
representativeOrder orderFour = 4
representativeOrder orderThree = 3
representativeOrder orderSix = 6

classSize : OrderStratum → Nat
classSize identity = 1
classSize centralMinusOne = 1
classSize orderFour = 6
classSize orderThree = 4
classSize orderSix = 4

centralizerOrder : OrderStratum → Nat
centralizerOrder identity = 24
centralizerOrder centralMinusOne = 24
centralizerOrder orderFour = 4
centralizerOrder orderThree = 6
centralizerOrder orderSix = 6

twoAdicCentralizerExponent : OrderStratum → Nat
twoAdicCentralizerExponent identity = 3
twoAdicCentralizerExponent centralMinusOne = 3
twoAdicCentralizerExponent orderFour = 2
twoAdicCentralizerExponent orderThree = 1
twoAdicCentralizerExponent orderSix = 1

/-- Literal largest power of two dividing the representative centralizer order.
Kept explicit to avoid depending on a particular exponentiation API. -/
twoPrimaryPart : OrderStratum → Nat
twoPrimaryPart identity = 8
twoPrimaryPart centralMinusOne = 8
twoPrimaryPart orderFour = 4
twoPrimaryPart orderThree = 2
twoPrimaryPart orderSix = 2

centralizerOddPart : OrderStratum → Nat
centralizerOddPart identity = 3
centralizerOddPart centralMinusOne = 3
centralizerOddPart orderFour = 1
centralizerOddPart orderThree = 3
centralizerOddPart orderSix = 3

centralizerTwoAdicFactorization :
  (s : OrderStratum) →
  twoPrimaryPart s * centralizerOddPart s ≡ centralizerOrder s
centralizerTwoAdicFactorization identity = refl
centralizerTwoAdicFactorization centralMinusOne = refl
centralizerTwoAdicFactorization orderFour = refl
centralizerTwoAdicFactorization orderThree = refl
centralizerTwoAdicFactorization orderSix = refl

------------------------------------------------------------------------
-- 2. Exact profile.
------------------------------------------------------------------------

defectIdentityIsThree : twoAdicCentralizerExponent identity ≡ 3
defectIdentityIsThree = refl

defectMinusOneIsThree : twoAdicCentralizerExponent centralMinusOne ≡ 3
defectMinusOneIsThree = refl

defectOrderFourIsTwo : twoAdicCentralizerExponent orderFour ≡ 2
defectOrderFourIsTwo = refl

defectOrderThreeIsOne : twoAdicCentralizerExponent orderThree ≡ 1
defectOrderThreeIsOne = refl

defectOrderSixIsOne : twoAdicCentralizerExponent orderSix ≡ 1
defectOrderSixIsOne = refl

------------------------------------------------------------------------
-- 3. Recognition frontier.
------------------------------------------------------------------------

record FiveModeToOrderStratumRecognition (Mode5 : Set) : Set₁ where
  field
    modeToOrderStratum : Mode5 → OrderStratum
    sourceProvenance : String
    independentlySourced : Bool

open FiveModeToOrderStratumRecognition public

data MatchingFiveNumbersConstructsModeRecognition : Set where

matchingNumbersDoNotConstructModeRecognition :
  MatchingFiveNumbersConstructsModeRecognition → ⊥
matchingNumbersDoNotConstructModeRecognition ()

record DefectSourceStatus : Set where
  constructor defect-source-status
  field
    binaryTetrahedralGroupSourced : Bool
    centralizerOrderInvariantDefined : Bool
    twoAdicExponentProfilePaid : Bool
    profileIsThreeThreeTwoOneOne : Bool
    completionModeToOrderStratumRecognitionPaid : Bool
    actualQ10ModeRecognitionPaid : Bool

canonicalDefectSourceStatus : DefectSourceStatus
canonicalDefectSourceStatus =
  defect-source-status
    true true true true false false
