module DASHI.Analysis.NonArchimedeanOrbitCancellationToMinusTwoExact where

------------------------------------------------------------------------
-- MINIMAL SIGNED ORBIT PRODUCER
--
-- The source already owns W1 * W2 = 2 for a supplied odd partition.
-- The stronger explicit phase values W1 = +/- i sqrt(2) are unnecessary for
-- the doubled-return power theorem.  The minimal additional producer is
--
--   W1 + W2 = 0.
--
-- In any ring-like scalar carrier with the elementary negation laws below,
-- cancellation plus product two implies
--
--   W1^2 = W2^2 = -2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

record SignedProductLaws (Scalar : Set) : Set₁ where
  field
    zero two : Scalar
    add multiply : Scalar → Scalar → Scalar
    negate : Scalar → Scalar

    sumZeroGivesRightNeg :
      (a b : Scalar) → add a b ≡ zero → b ≡ negate a

    multiplyRightNeg :
      (a b : Scalar) →
      multiply a (negate b) ≡ negate (multiply a b)

    negateInvolutive :
      (a : Scalar) → negate (negate a) ≡ a

    negateSquare :
      (a : Scalar) →
      multiply (negate a) (negate a) ≡ multiply a a

open SignedProductLaws public

record OrbitCancellationProduct
    {Scalar : Set}
    (laws : SignedProductLaws Scalar) : Set where
  field
    W1 W2 : Scalar
    cancellation : add laws W1 W2 ≡ zero laws
    pairedProduct : multiply laws W1 W2 ≡ two laws

open OrbitCancellationProduct public

W2IsNegW1 :
  ∀ {Scalar}
    (laws : SignedProductLaws Scalar)
    (data : OrbitCancellationProduct laws) →
  W2 data ≡ negate laws (W1 data)
W2IsNegW1 laws data =
  sumZeroGivesRightNeg laws
    (W1 data) (W2 data) (cancellation data)

W1SquareIsMinusTwo :
  ∀ {Scalar}
    (laws : SignedProductLaws Scalar)
    (data : OrbitCancellationProduct laws) →
  multiply laws (W1 data) (W1 data) ≡ negate laws (two laws)
W1SquareIsMinusTwo laws data =
  let
    hneg = W2IsNegW1 laws data
    hnegSquare :
      negate laws (multiply laws (W1 data) (W1 data))
      ≡ two laws
    hnegSquare =
      trans
        (sym (multiplyRightNeg laws (W1 data) (W1 data)))
        (trans
          (sym (cong (multiply laws (W1 data)) hneg))
          (pairedProduct data))
  in
  trans
    (sym (negateInvolutive laws
      (multiply laws (W1 data) (W1 data))))
    (cong (negate laws) hnegSquare)

W2SquareIsMinusTwo :
  ∀ {Scalar}
    (laws : SignedProductLaws Scalar)
    (data : OrbitCancellationProduct laws) →
  multiply laws (W2 data) (W2 data) ≡ negate laws (two laws)
W2SquareIsMinusTwo laws data =
  let hneg = W2IsNegW1 laws data in
  trans
    (cong₂ (multiply laws) hneg hneg)
    (trans
      (negateSquare laws (W1 data))
      (W1SquareIsMinusTwo laws data))

record MinimalPhaseBoundary : Set where
  constructor minimalPhaseBoundary
  field
    pairedProductTwoAlreadyOwned : Bool
    cancellationSumZeroStillRequired : Bool
    explicitPlusMinusISqrtTwoRequired : Bool
    doubledReturnMinusTwoCompilesFromCancellationAndProduct : Bool

canonicalMinimalPhaseBoundary : MinimalPhaseBoundary
canonicalMinimalPhaseBoundary =
  minimalPhaseBoundary true true false true


data PhaseLeaf : Set where
  proveOrbitCancellationSumZero : PhaseLeaf
  recoverExplicitComplexPhaseValues : PhaseLeaf
  compileBothOrbitSquaresMinusTwo : PhaseLeaf


data PhaseLeafDisposition : Set where
  live : PhaseLeafDisposition
  optional : PhaseLeafDisposition
  downstream : PhaseLeafDisposition

phaseLeafDisposition : PhaseLeaf → PhaseLeafDisposition
phaseLeafDisposition proveOrbitCancellationSumZero = live
phaseLeafDisposition recoverExplicitComplexPhaseValues = optional
phaseLeafDisposition compileBothOrbitSquaresMinusTwo = downstream

highestAlphaPhasePath : List PhaseLeaf
highestAlphaPhasePath =
  proveOrbitCancellationSumZero ∷
  compileBothOrbitSquaresMinusTwo ∷
  []

explicitPhaseValuesPrunedFromCriticalPath :
  MinimalPhaseBoundary.explicitPlusMinusISqrtTwoRequired
    canonicalMinimalPhaseBoundary
  ≡ false
explicitPhaseValuesPrunedFromCriticalPath = refl
