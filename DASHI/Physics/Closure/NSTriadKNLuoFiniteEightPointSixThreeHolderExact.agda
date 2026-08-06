module DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointSixThreeHolderExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Classical Hölder inequality, specialized to the finite eight-point
-- periodic carrier.  Repository-original radical-free Agda proof; no DOI is
-- assigned.
--
-- Related references:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Supply an actual finite (L6,L3)->L2 estimate rather than an exponent table.
-- For eight nonnegative samples a_i,b_i, define
--
--   S2 = sum (a_i b_i)^2,
--   A6 = sum a_i^6,
--   B3 = sum b_i^3.
--
-- The checked radical-free theorem is
--
--   S2^3 <= 64 A6 B3^2.
--
-- The factor 64 is the elementary eight-point power-mean constant.  It is not
-- sharp, but is uniform and sufficient for the shell-gap argument.  No roots
-- or unformalized real powers are used.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Product.Base using (_×_; _,_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

three four sixteen sixtyFour : ℚ
three = Int.+ 3 / 1
four = Int.+ 4 / 1
sixteen = Int.+ 16 / 1
sixtyFour = Int.+ 64 / 1

cube : ℚ → ℚ
cube value = value * value * value

sixth : ℚ → ℚ
sixth value = cube value * cube value

threeNonnegative : 0ℚ ≤ three
threeNonnegative = ℚₚ.≤-refl

fourNonnegative : 0ℚ ≤ four
fourNonnegative = ℚₚ.≤-refl

sixteenNonnegative : 0ℚ ≤ sixteen
sixteenNonnegative = ℚₚ.≤-refl

sixtyFourNonnegative : 0ℚ ≤ sixtyFour
sixtyFourNonnegative = ℚₚ.≤-refl

cubeNonnegative :
  (value : ℚ) →
  0ℚ ≤ value →
  0ℚ ≤ cube value
cubeNonnegative value valueNonnegative =
  let
    instance
      valueNN = nonNegative valueNonnegative
      squareNN = ℚₚ.nonNeg*nonNeg⇒nonNeg value value
      cubeNN = ℚₚ.nonNeg*nonNeg⇒nonNeg (value * value) value
  in
  ℚₚ.nonNegative⁻¹ (cube value)

cubePairBound :
  (left right : ℚ) →
  0ℚ ≤ left →
  0ℚ ≤ right →
  cube (left + right) ≤ four * (cube left + cube right)
cubePairBound left right leftNN rightNN =
  let
    sumNN : 0ℚ ≤ left + right
    sumNN = L2.addNonnegative leftNN rightNN

    squareDifferenceNN : 0ℚ ≤ L2.square (left - right)
    squareDifferenceNN = L2.squareNonnegative (left - right)

    defectNN :
      0ℚ ≤ three * (left + right) * L2.square (left - right)
    defectNN =
      let
        instance
          threeNNI = nonNegative threeNonnegative
          sumNNI = nonNegative sumNN
          firstProductNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg three (left + right)
          squareNNI = nonNegative squareDifferenceNN
          totalNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (three * (left + right))
              (L2.square (left - right))
      in
      ℚₚ.nonNegative⁻¹
        (three * (left + right) * L2.square (left - right))

    addDefect :
      cube (left + right)
      ≤ cube (left + right)
        + three * (left + right) * L2.square (left - right)
    addDefect =
      subst
        (λ lower →
          lower
          ≤ cube (left + right)
            + three * (left + right) * L2.square (left - right))
        (ℚₚ.+-identityʳ (cube (left + right)))
        (ℚₚ.+-monoʳ-≤ (cube (left + right)) defectNN)

    identity :
      cube (left + right)
        + three * (left + right) * L2.square (left - right)
      ≡ four * (cube left + cube right)
    identity = solve (left ∷ right ∷ [])
  in
  subst
    (λ upper → cube (left + right) ≤ upper)
    identity
    addDefect

scaleBound :
  (scale left right : ℚ) →
  0ℚ ≤ scale →
  left ≤ right →
  scale * left ≤ scale * right
scaleBound scale left right scaleNN left≤right =
  let
    instance scaleNNI = nonNegative scaleNN
  in
  ℚₚ.*-monoˡ-≤-nonNeg scale left≤right

fourValueCubeBound :
  (a b c d : ℚ) →
  0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ c → 0ℚ ≤ d →
  cube (a + b + c + d)
  ≤ sixteen * (cube a + cube b + cube c + cube d)
fourValueCubeBound a b c d aNN bNN cNN dNN =
  let
    abNN = L2.addNonnegative aNN bNN
    cdNN = L2.addNonnegative cNN dNN

    outer :
      cube ((a + b) + (c + d))
      ≤ four * (cube (a + b) + cube (c + d))
    outer = cubePairBound (a + b) (c + d) abNN cdNN

    innerSum :
      cube (a + b) + cube (c + d)
      ≤ four * (cube a + cube b)
        + four * (cube c + cube d)
    innerSum =
      ℚₚ.+-mono-≤
        (cubePairBound a b aNN bNN)
        (cubePairBound c d cNN dNN)

    scaledInner :
      four * (cube (a + b) + cube (c + d))
      ≤ four
        * (four * (cube a + cube b)
          + four * (cube c + cube d))
    scaledInner = scaleBound four _ _ fourNonnegative innerSum

    endpoint :
      four
        * (four * (cube a + cube b)
          + four * (cube c + cube d))
      ≡ sixteen * (cube a + cube b + cube c + cube d)
    endpoint = solve (cube a ∷ cube b ∷ cube c ∷ cube d ∷ [])

    reassociate :
      cube (a + b + c + d)
      ≡ cube ((a + b) + (c + d))
    reassociate = solve (a ∷ b ∷ c ∷ d ∷ [])
  in
  subst
    (λ lower →
      lower ≤ sixteen * (cube a + cube b + cube c + cube d))
    (sym reassociate)
    (ℚₚ.≤-trans
      outer
      (subst
        (λ upper →
          four * (cube (a + b) + cube (c + d)) ≤ upper)
        endpoint
        scaledInner))

eightValueCubeBound :
  (a b c d e f g h : ℚ) →
  0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ c → 0ℚ ≤ d →
  0ℚ ≤ e → 0ℚ ≤ f → 0ℚ ≤ g → 0ℚ ≤ h →
  cube (a + b + c + d + e + f + g + h)
  ≤ sixtyFour
    * (cube a + cube b + cube c + cube d
      + cube e + cube f + cube g + cube h)
eightValueCubeBound a b c d e f g h
  aNN bNN cNN dNN eNN fNN gNN hNN =
  let
    left4 = a + b + c + d
    right4 = e + f + g + h

    left4NN =
      L2.addNonnegative
        (L2.addNonnegative (L2.addNonnegative aNN bNN) cNN)
        dNN
    right4NN =
      L2.addNonnegative
        (L2.addNonnegative (L2.addNonnegative eNN fNN) gNN)
        hNN

    outer :
      cube (left4 + right4)
      ≤ four * (cube left4 + cube right4)
    outer = cubePairBound left4 right4 left4NN right4NN

    inner :
      cube left4 + cube right4
      ≤ sixteen * (cube a + cube b + cube c + cube d)
        + sixteen * (cube e + cube f + cube g + cube h)
    inner =
      ℚₚ.+-mono-≤
        (fourValueCubeBound a b c d aNN bNN cNN dNN)
        (fourValueCubeBound e f g h eNN fNN gNN hNN)

    scaled = scaleBound four _ _ fourNonnegative inner

    endpoint :
      four
        * (sixteen * (cube a + cube b + cube c + cube d)
          + sixteen * (cube e + cube f + cube g + cube h))
      ≡ sixtyFour
        * (cube a + cube b + cube c + cube d
          + cube e + cube f + cube g + cube h)
    endpoint =
      solve
        ( cube a ∷ cube b ∷ cube c ∷ cube d
        ∷ cube e ∷ cube f ∷ cube g ∷ cube h ∷ [])

    reassociate :
      cube (a + b + c + d + e + f + g + h)
      ≡ cube (left4 + right4)
    reassociate = solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ [])
  in
  subst
    (λ lower →
      lower
      ≤ sixtyFour
        * (cube a + cube b + cube c + cube d
          + cube e + cube f + cube g + cube h))
    (sym reassociate)
    (ℚₚ.≤-trans
      outer
      (subst
        (λ upper → four * (cube left4 + cube right4) ≤ upper)
        endpoint
        scaled))

Pair : Set
Pair = ℚ × ℚ

sumLeft : List Pair → ℚ
sumLeft [] = 0ℚ
sumLeft ((left , right) ∷ rest) = left + sumLeft rest

sumRight : List Pair → ℚ
sumRight [] = 0ℚ
sumRight ((left , right) ∷ rest) = right + sumRight rest

diagonal : List Pair → ℚ
diagonal [] = 0ℚ
diagonal ((left , right) ∷ rest) = left * right + diagonal rest

data NonnegativePairs : List Pair → Set where
  nn[] : NonnegativePairs []
  nn∷ :
    ∀ {left right rest} →
    0ℚ ≤ left →
    0ℚ ≤ right →
    NonnegativePairs rest →
    NonnegativePairs ((left , right) ∷ rest)

sumLeftNonnegative :
  ∀ {pairs} →
  NonnegativePairs pairs →
  0ℚ ≤ sumLeft pairs
sumLeftNonnegative nn[] = ℚₚ.≤-refl
sumLeftNonnegative (nn∷ leftNN rightNN restNN) =
  L2.addNonnegative leftNN (sumLeftNonnegative restNN)

sumRightNonnegative :
  ∀ {pairs} →
  NonnegativePairs pairs →
  0ℚ ≤ sumRight pairs
sumRightNonnegative nn[] = ℚₚ.≤-refl
sumRightNonnegative (nn∷ leftNN rightNN restNN) =
  L2.addNonnegative rightNN (sumRightNonnegative restNN)

diagonalBelowProductOfSums :
  ∀ {pairs} →
  NonnegativePairs pairs →
  diagonal pairs ≤ sumLeft pairs * sumRight pairs
diagonalBelowProductOfSums nn[] = ℚₚ.≤-refl
diagonalBelowProductOfSums
  (nn∷ {left} {right} {rest} leftNN rightNN restNN) =
  let
    ih = diagonalBelowProductOfSums restNN
    first :
      left * right + diagonal rest
      ≤ left * right + sumLeft rest * sumRight rest
    first = ℚₚ.+-monoʳ-≤ (left * right) ih

    crossNN :
      0ℚ
      ≤ left * sumRight rest + sumLeft rest * right
    crossNN =
      let
        instance
          leftNNI = nonNegative leftNN
          rightNNI = nonNegative rightNN
          sumLeftNNI = nonNegative (sumLeftNonnegative restNN)
          sumRightNNI = nonNegative (sumRightNonnegative restNN)
          firstCrossNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg left (sumRight rest)
          secondCrossNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg (sumLeft rest) right
      in
      L2.addNonnegative
        (ℚₚ.nonNegative⁻¹ (left * sumRight rest))
        (ℚₚ.nonNegative⁻¹ (sumLeft rest * right))

    addCross :
      left * right + sumLeft rest * sumRight rest
      ≤ left * right + sumLeft rest * sumRight rest
        + (left * sumRight rest + sumLeft rest * right)
    addCross =
      subst
        (λ lower →
          lower
          ≤ left * right + sumLeft rest * sumRight rest
            + (left * sumRight rest + sumLeft rest * right))
        (ℚₚ.+-identityʳ
          (left * right + sumLeft rest * sumRight rest))
        (ℚₚ.+-monoʳ-≤
          (left * right + sumLeft rest * sumRight rest)
          crossNN)

    endpoint :
      left * right + sumLeft rest * sumRight rest
        + (left * sumRight rest + sumLeft rest * right)
      ≡ (left + sumLeft rest) * (right + sumRight rest)
    endpoint =
      solve
        (left ∷ right ∷ sumLeft rest ∷ sumRight rest ∷ [])
  in
  ℚₚ.≤-trans
    first
    (subst
      (λ upper →
        left * right + sumLeft rest * sumRight rest ≤ upper)
      endpoint
      addCross)

record EightSixThreeData : Set where
  constructor eight-six-three-data
  field
    a0 a1 a2 a3 a4 a5 a6 a7 : ℚ
    b0 b1 b2 b3 b4 b5 b6 b7 : ℚ
    a0NN : 0ℚ ≤ a0
    a1NN : 0ℚ ≤ a1
    a2NN : 0ℚ ≤ a2
    a3NN : 0ℚ ≤ a3
    a4NN : 0ℚ ≤ a4
    a5NN : 0ℚ ≤ a5
    a6NN : 0ℚ ≤ a6
    a7NN : 0ℚ ≤ a7
    b0NN : 0ℚ ≤ b0
    b1NN : 0ℚ ≤ b1
    b2NN : 0ℚ ≤ b2
    b3NN : 0ℚ ≤ b3
    b4NN : 0ℚ ≤ b4
    b5NN : 0ℚ ≤ b5
    b6NN : 0ℚ ≤ b6
    b7NN : 0ℚ ≤ b7

open EightSixThreeData public

productSquare : ℚ → ℚ → ℚ
productSquare a b = L2.square (a * b)

productL2Squared : EightSixThreeData → ℚ
productL2Squared dataSet =
    productSquare (a0 dataSet) (b0 dataSet)
  + productSquare (a1 dataSet) (b1 dataSet)
  + productSquare (a2 dataSet) (b2 dataSet)
  + productSquare (a3 dataSet) (b3 dataSet)
  + productSquare (a4 dataSet) (b4 dataSet)
  + productSquare (a5 dataSet) (b5 dataSet)
  + productSquare (a6 dataSet) (b6 dataSet)
  + productSquare (a7 dataSet) (b7 dataSet)

lowSixthMass : EightSixThreeData → ℚ
lowSixthMass dataSet =
    sixth (a0 dataSet) + sixth (a1 dataSet)
  + sixth (a2 dataSet) + sixth (a3 dataSet)
  + sixth (a4 dataSet) + sixth (a5 dataSet)
  + sixth (a6 dataSet) + sixth (a7 dataSet)

highCubeMass : EightSixThreeData → ℚ
highCubeMass dataSet =
    cube (b0 dataSet) + cube (b1 dataSet)
  + cube (b2 dataSet) + cube (b3 dataSet)
  + cube (b4 dataSet) + cube (b5 dataSet)
  + cube (b6 dataSet) + cube (b7 dataSet)

productSquaresNonnegative :
  (dataSet : EightSixThreeData) →
  0ℚ ≤ productSquare (a0 dataSet) (b0 dataSet)
productSquaresNonnegative dataSet =
  L2.squareNonnegative (a0 dataSet * b0 dataSet)

-- The diagonal-product theorem gives the sharp comparison of the sum of
-- cubed product-squares with A6 B3^2; the only loss is the elementary
-- eight-point power-mean constant above.
eightPointSixThreeHolderRadicalFree :
  (dataSet : EightSixThreeData) →
  cube (productL2Squared dataSet)
  ≤ sixtyFour
    * lowSixthMass dataSet
    * (highCubeMass dataSet * highCubeMass dataSet)
eightPointSixThreeHolderRadicalFree dataSet =
  let
    c0 = productSquare (a0 dataSet) (b0 dataSet)
    c1 = productSquare (a1 dataSet) (b1 dataSet)
    c2 = productSquare (a2 dataSet) (b2 dataSet)
    c3 = productSquare (a3 dataSet) (b3 dataSet)
    c4 = productSquare (a4 dataSet) (b4 dataSet)
    c5 = productSquare (a5 dataSet) (b5 dataSet)
    c6 = productSquare (a6 dataSet) (b6 dataSet)
    c7 = productSquare (a7 dataSet) (b7 dataSet)

    c0NN = L2.squareNonnegative (a0 dataSet * b0 dataSet)
    c1NN = L2.squareNonnegative (a1 dataSet * b1 dataSet)
    c2NN = L2.squareNonnegative (a2 dataSet * b2 dataSet)
    c3NN = L2.squareNonnegative (a3 dataSet * b3 dataSet)
    c4NN = L2.squareNonnegative (a4 dataSet * b4 dataSet)
    c5NN = L2.squareNonnegative (a5 dataSet * b5 dataSet)
    c6NN = L2.squareNonnegative (a6 dataSet * b6 dataSet)
    c7NN = L2.squareNonnegative (a7 dataSet * b7 dataSet)

    powerMean :
      cube (productL2Squared dataSet)
      ≤ sixtyFour
        * (cube c0 + cube c1 + cube c2 + cube c3
          + cube c4 + cube c5 + cube c6 + cube c7)
    powerMean =
      eightValueCubeBound
        c0 c1 c2 c3 c4 c5 c6 c7
        c0NN c1NN c2NN c3NN c4NN c5NN c6NN c7NN

    a6b6Pairs : List Pair
    a6b6Pairs =
        (sixth (a0 dataSet) , sixth (b0 dataSet))
      ∷ (sixth (a1 dataSet) , sixth (b1 dataSet))
      ∷ (sixth (a2 dataSet) , sixth (b2 dataSet))
      ∷ (sixth (a3 dataSet) , sixth (b3 dataSet))
      ∷ (sixth (a4 dataSet) , sixth (b4 dataSet))
      ∷ (sixth (a5 dataSet) , sixth (b5 dataSet))
      ∷ (sixth (a6 dataSet) , sixth (b6 dataSet))
      ∷ (sixth (a7 dataSet) , sixth (b7 dataSet))
      ∷ []

    b3Pairs : List Pair
    b3Pairs =
        (cube (b0 dataSet) , cube (b0 dataSet))
      ∷ (cube (b1 dataSet) , cube (b1 dataSet))
      ∷ (cube (b2 dataSet) , cube (b2 dataSet))
      ∷ (cube (b3 dataSet) , cube (b3 dataSet))
      ∷ (cube (b4 dataSet) , cube (b4 dataSet))
      ∷ (cube (b5 dataSet) , cube (b5 dataSet))
      ∷ (cube (b6 dataSet) , cube (b6 dataSet))
      ∷ (cube (b7 dataSet) , cube (b7 dataSet))
      ∷ []

    a6b6NN : NonnegativePairs a6b6Pairs
    a6b6NN =
      nn∷ (cubeNonnegative (cube (a0 dataSet)) (cubeNonnegative (a0 dataSet) (a0NN dataSet)))
        (cubeNonnegative (cube (b0 dataSet)) (cubeNonnegative (b0 dataSet) (b0NN dataSet)))
      (nn∷ (cubeNonnegative (cube (a1 dataSet)) (cubeNonnegative (a1 dataSet) (a1NN dataSet)))
        (cubeNonnegative (cube (b1 dataSet)) (cubeNonnegative (b1 dataSet) (b1NN dataSet)))
      (nn∷ (cubeNonnegative (cube (a2 dataSet)) (cubeNonnegative (a2 dataSet) (a2NN dataSet)))
        (cubeNonnegative (cube (b2 dataSet)) (cubeNonnegative (b2 dataSet) (b2NN dataSet)))
      (nn∷ (cubeNonnegative (cube (a3 dataSet)) (cubeNonnegative (a3 dataSet) (a3NN dataSet)))
        (cubeNonnegative (cube (b3 dataSet)) (cubeNonnegative (b3 dataSet) (b3NN dataSet)))
      (nn∷ (cubeNonnegative (cube (a4 dataSet)) (cubeNonnegative (a4 dataSet) (a4NN dataSet)))
        (cubeNonnegative (cube (b4 dataSet)) (cubeNonnegative (b4 dataSet) (b4NN dataSet)))
      (nn∷ (cubeNonnegative (cube (a5 dataSet)) (cubeNonnegative (a5 dataSet) (a5NN dataSet)))
        (cubeNonnegative (cube (b5 dataSet)) (cubeNonnegative (b5 dataSet) (b5NN dataSet)))
      (nn∷ (cubeNonnegative (cube (a6 dataSet)) (cubeNonnegative (a6 dataSet) (a6NN dataSet)))
        (cubeNonnegative (cube (b6 dataSet)) (cubeNonnegative (b6 dataSet) (b6NN dataSet)))
      (nn∷ (cubeNonnegative (cube (a7 dataSet)) (cubeNonnegative (a7 dataSet) (a7NN dataSet)))
        (cubeNonnegative (cube (b7 dataSet)) (cubeNonnegative (b7 dataSet) (b7NN dataSet)))
        nn[]))))))))

    b3NN : NonnegativePairs b3Pairs
    b3NN =
      nn∷ (cubeNonnegative (b0 dataSet) (b0NN dataSet)) (cubeNonnegative (b0 dataSet) (b0NN dataSet))
      (nn∷ (cubeNonnegative (b1 dataSet) (b1NN dataSet)) (cubeNonnegative (b1 dataSet) (b1NN dataSet))
      (nn∷ (cubeNonnegative (b2 dataSet) (b2NN dataSet)) (cubeNonnegative (b2 dataSet) (b2NN dataSet))
      (nn∷ (cubeNonnegative (b3 dataSet) (b3NN dataSet)) (cubeNonnegative (b3 dataSet) (b3NN dataSet))
      (nn∷ (cubeNonnegative (b4 dataSet) (b4NN dataSet)) (cubeNonnegative (b4 dataSet) (b4NN dataSet))
      (nn∷ (cubeNonnegative (b5 dataSet) (b5NN dataSet)) (cubeNonnegative (b5 dataSet) (b5NN dataSet))
      (nn∷ (cubeNonnegative (b6 dataSet) (b6NN dataSet)) (cubeNonnegative (b6 dataSet) (b6NN dataSet))
      (nn∷ (cubeNonnegative (b7 dataSet) (b7NN dataSet)) (cubeNonnegative (b7 dataSet) (b7NN dataSet))
        nn[]))))))))

    diagonalMeaning :
      cube c0 + cube c1 + cube c2 + cube c3
        + cube c4 + cube c5 + cube c6 + cube c7
      ≡ diagonal a6b6Pairs
    diagonalMeaning =
      solve
        ( a0 dataSet ∷ a1 dataSet ∷ a2 dataSet ∷ a3 dataSet
        ∷ a4 dataSet ∷ a5 dataSet ∷ a6 dataSet ∷ a7 dataSet
        ∷ b0 dataSet ∷ b1 dataSet ∷ b2 dataSet ∷ b3 dataSet
        ∷ b4 dataSet ∷ b5 dataSet ∷ b6 dataSet ∷ b7 dataSet ∷ [])

    firstDiagonal :
      diagonal a6b6Pairs
      ≤ sumLeft a6b6Pairs * sumRight a6b6Pairs
    firstDiagonal = diagonalBelowProductOfSums a6b6NN

    bSixToCubeSquare :
      diagonal b3Pairs ≤ sumLeft b3Pairs * sumRight b3Pairs
    bSixToCubeSquare = diagonalBelowProductOfSums b3NN

    massMeanings :
      sumLeft a6b6Pairs ≡ lowSixthMass dataSet
      × sumRight a6b6Pairs ≡ diagonal b3Pairs
    massMeanings = solve [] , solve []

    highMeaning :
      sumLeft b3Pairs ≡ highCubeMass dataSet
      × sumRight b3Pairs ≡ highCubeMass dataSet
    highMeaning = solve [] , solve []

    firstAdjusted :
      cube c0 + cube c1 + cube c2 + cube c3
        + cube c4 + cube c5 + cube c6 + cube c7
      ≤ lowSixthMass dataSet * diagonal b3Pairs
    firstAdjusted =
      subst
        (λ lower → lower ≤ lowSixthMass dataSet * diagonal b3Pairs)
        (sym diagonalMeaning)
        (subst
          (λ leftMass →
            diagonal a6b6Pairs
            ≤ leftMass * diagonal b3Pairs)
          (proj₁ massMeanings)
          (subst
            (λ rightMass →
              diagonal a6b6Pairs
              ≤ sumLeft a6b6Pairs * rightMass)
            (proj₂ massMeanings)
            firstDiagonal))

    highAdjusted :
      diagonal b3Pairs
      ≤ highCubeMass dataSet * highCubeMass dataSet
    highAdjusted =
      subst
        (λ leftMass →
          diagonal b3Pairs ≤ leftMass * highCubeMass dataSet)
        (proj₁ highMeaning)
        (subst
          (λ rightMass →
            diagonal b3Pairs ≤ sumLeft b3Pairs * rightMass)
          (proj₂ highMeaning)
          bSixToCubeSquare)

    lowMassNN : 0ℚ ≤ lowSixthMass dataSet
    lowMassNN = sumLeftNonnegative a6b6NN

    scaledHigh :
      lowSixthMass dataSet * diagonal b3Pairs
      ≤ lowSixthMass dataSet
        * (highCubeMass dataSet * highCubeMass dataSet)
    scaledHigh = scaleBound
      (lowSixthMass dataSet)
      (diagonal b3Pairs)
      (highCubeMass dataSet * highCubeMass dataSet)
      lowMassNN
      highAdjusted

    inside :
      cube c0 + cube c1 + cube c2 + cube c3
        + cube c4 + cube c5 + cube c6 + cube c7
      ≤ lowSixthMass dataSet
        * (highCubeMass dataSet * highCubeMass dataSet)
    inside = ℚₚ.≤-trans firstAdjusted scaledHigh

    scaledInside = scaleBound sixtyFour _ _ sixtyFourNonnegative inside

    endpoint :
      sixtyFour
        * (lowSixthMass dataSet
          * (highCubeMass dataSet * highCubeMass dataSet))
      ≡ sixtyFour * lowSixthMass dataSet
        * (highCubeMass dataSet * highCubeMass dataSet)
    endpoint = solve
      (lowSixthMass dataSet ∷ highCubeMass dataSet ∷ [])
  in
  ℚₚ.≤-trans
    powerMean
    (subst
      (λ upper →
        sixtyFour
          * (cube c0 + cube c1 + cube c2 + cube c3
            + cube c4 + cube c5 + cube c6 + cube c7)
        ≤ upper)
      endpoint
      scaledInside)
