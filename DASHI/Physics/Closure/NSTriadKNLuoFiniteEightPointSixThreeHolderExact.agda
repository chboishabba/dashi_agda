module DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointSixThreeHolderExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Classical Hölder inequality, specialized to the finite eight-point
-- periodic carrier. Repository-original radical-free Agda proof; no DOI is
-- assigned.
--
-- Related reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Prove, for eight nonnegative samples,
--
--   (sum_i (a_i b_i)^2)^3
--     <= 64 (sum_i a_i^6) (sum_i b_i^3)^2.
--
-- This is a radical-free finite (L6,L3)->L2 estimate. The factor 64 comes
-- from the elementary eight-value cubic power-mean bound. The remaining
-- steps are diagonal <= product of sums and sum of squares <= square of sum.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

three four sixteen sixtyFour : ℚ
three = Int.+ 3 / 1
four = Int.+ 4 / 1
sixteen = Int.+ 16 / 1
sixtyFour = Int.+ 64 / 1

threeNonnegative : 0ℚ ≤ three
threeNonnegative = toWitness {a? = 0ℚ ≤? three} _

fourNonnegative : 0ℚ ≤ four
fourNonnegative = toWitness {a? = 0ℚ ≤? four} _

sixtyFourNonnegative : 0ℚ ≤ sixtyFour
sixtyFourNonnegative = toWitness {a? = 0ℚ ≤? sixtyFour} _

cube : ℚ → ℚ
cube value = value * value * value

sixth : ℚ → ℚ
sixth value = cube value * cube value

cubeNonnegative :
  (value : ℚ) → 0ℚ ≤ value → 0ℚ ≤ cube value
cubeNonnegative value valueNN =
  let
    instance
      valueNNI = nonNegative valueNN
      squareNN = ℚₚ.nonNeg*nonNeg⇒nonNeg value value
      resultNN = ℚₚ.nonNeg*nonNeg⇒nonNeg (value * value) value
  in
  ℚₚ.nonNegative⁻¹ (cube value)

sixthNonnegative :
  (value : ℚ) → 0ℚ ≤ value → 0ℚ ≤ sixth value
sixthNonnegative value valueNN =
  let
    cubeNN = cubeNonnegative value valueNN
    instance
      leftNN = nonNegative cubeNN
      rightNN = nonNegative cubeNN
      resultNN = ℚₚ.nonNeg*nonNeg⇒nonNeg (cube value) (cube value)
  in
  ℚₚ.nonNegative⁻¹ (sixth value)

scaleBound :
  (scale left right : ℚ) →
  0ℚ ≤ scale → left ≤ right → scale * left ≤ scale * right
scaleBound scale left right scaleNN left≤right =
  let instance scaleNNI = nonNegative scaleNN
  in ℚₚ.*-monoˡ-≤-nonNeg scale left≤right

cubePairBound :
  (left right : ℚ) →
  0ℚ ≤ left → 0ℚ ≤ right →
  cube (left + right) ≤ four * (cube left + cube right)
cubePairBound left right leftNN rightNN =
  let
    sumNN = L2.addNonnegative leftNN rightNN
    squareDifferenceNN = L2.squareNonnegative (left - right)

    defectNN :
      0ℚ ≤ three * (left + right) * L2.square (left - right)
    defectNN =
      let
        instance
          threeNNI = nonNegative threeNonnegative
          sumNNI = nonNegative sumNN
          firstNN = ℚₚ.nonNeg*nonNeg⇒nonNeg three (left + right)
          squareNNI = nonNegative squareDifferenceNN
          resultNN =
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
  subst (λ upper → cube (left + right) ≤ upper) identity addDefect

fourValueCubeBound :
  (a b c d : ℚ) →
  0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ c → 0ℚ ≤ d →
  cube (a + b + c + d)
  ≤ sixteen * (cube a + cube b + cube c + cube d)
fourValueCubeBound a b c d aNN bNN cNN dNN =
  let
    outer =
      cubePairBound
        (a + b) (c + d)
        (L2.addNonnegative aNN bNN)
        (L2.addNonnegative cNN dNN)

    inner =
      ℚₚ.+-mono-≤
        (cubePairBound a b aNN bNN)
        (cubePairBound c d cNN dNN)

    scaled = scaleBound four _ _ fourNonnegative inner

    endpoint :
      four
        * (four * (cube a + cube b)
          + four * (cube c + cube d))
      ≡ sixteen * (cube a + cube b + cube c + cube d)
    endpoint = solve (cube a ∷ cube b ∷ cube c ∷ cube d ∷ [])

    reassociate :
      cube (a + b + c + d) ≡ cube ((a + b) + (c + d))
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
        scaled))

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
        (L2.addNonnegative (L2.addNonnegative aNN bNN) cNN) dNN
    right4NN =
      L2.addNonnegative
        (L2.addNonnegative (L2.addNonnegative eNN fNN) gNN) hNN

    outer = cubePairBound left4 right4 left4NN right4NN

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

sum : List ℚ → ℚ
sum [] = 0ℚ
sum (value ∷ values) = value + sum values

squares : List ℚ → ℚ
squares [] = 0ℚ
squares (value ∷ values) = L2.square value + squares values

data NonnegativeList : List ℚ → Set where
  nn[] : NonnegativeList []
  nn∷ :
    ∀ {value values} →
    0ℚ ≤ value → NonnegativeList values →
    NonnegativeList (value ∷ values)

sumNonnegative :
  ∀ {values} → NonnegativeList values → 0ℚ ≤ sum values
sumNonnegative nn[] = ℚₚ.≤-refl
sumNonnegative (nn∷ valueNN valuesNN) =
  L2.addNonnegative valueNN (sumNonnegative valuesNN)

squaresBelowSquareSum :
  ∀ {values} →
  NonnegativeList values →
  squares values ≤ L2.square (sum values)
squaresBelowSquareSum nn[] = ℚₚ.≤-refl
squaresBelowSquareSum
  (nn∷ {value} {values} valueNN valuesNN) =
  let
    ih = squaresBelowSquareSum valuesNN
    first = ℚₚ.+-monoʳ-≤ (L2.square value) ih
    sumNN = sumNonnegative valuesNN

    crossProductNN : 0ℚ ≤ value * sum values
    crossProductNN =
      let
        instance
          valueNNI = nonNegative valueNN
          sumNNI = nonNegative sumNN
          productNN = ℚₚ.nonNeg*nonNeg⇒nonNeg value (sum values)
      in
      ℚₚ.nonNegative⁻¹ (value * sum values)

    crossNN = L2.addNonnegative crossProductNN crossProductNN

    addCross :
      L2.square value + L2.square (sum values)
      ≤ L2.square value + L2.square (sum values)
        + (value * sum values + value * sum values)
    addCross =
      subst
        (λ lower →
          lower
          ≤ L2.square value + L2.square (sum values)
            + (value * sum values + value * sum values))
        (ℚₚ.+-identityʳ
          (L2.square value + L2.square (sum values)))
        (ℚₚ.+-monoʳ-≤
          (L2.square value + L2.square (sum values)) crossNN)

    endpoint :
      L2.square value + L2.square (sum values)
        + (value * sum values + value * sum values)
      ≡ L2.square (value + sum values)
    endpoint = solve (value ∷ sum values ∷ [])
  in
  ℚₚ.≤-trans
    first
    (subst
      (λ upper →
        L2.square value + L2.square (sum values) ≤ upper)
      endpoint
      addCross)

Pair : Set
Pair = ℚ × ℚ

pairSumLeft : List Pair → ℚ
pairSumLeft [] = 0ℚ
pairSumLeft ((left , right) ∷ rest) = left + pairSumLeft rest

pairSumRight : List Pair → ℚ
pairSumRight [] = 0ℚ
pairSumRight ((left , right) ∷ rest) = right + pairSumRight rest

pairDiagonal : List Pair → ℚ
pairDiagonal [] = 0ℚ
pairDiagonal ((left , right) ∷ rest) =
  left * right + pairDiagonal rest

data NonnegativePairs : List Pair → Set where
  nnp[] : NonnegativePairs []
  nnp∷ :
    ∀ {left right rest} →
    0ℚ ≤ left → 0ℚ ≤ right → NonnegativePairs rest →
    NonnegativePairs ((left , right) ∷ rest)

pairLeftNonnegative :
  ∀ {pairs} → NonnegativePairs pairs → 0ℚ ≤ pairSumLeft pairs
pairLeftNonnegative nnp[] = ℚₚ.≤-refl
pairLeftNonnegative (nnp∷ leftNN rightNN restNN) =
  L2.addNonnegative leftNN (pairLeftNonnegative restNN)

pairRightNonnegative :
  ∀ {pairs} → NonnegativePairs pairs → 0ℚ ≤ pairSumRight pairs
pairRightNonnegative nnp[] = ℚₚ.≤-refl
pairRightNonnegative (nnp∷ leftNN rightNN restNN) =
  L2.addNonnegative rightNN (pairRightNonnegative restNN)

pairDiagonalBelowProduct :
  ∀ {pairs} →
  NonnegativePairs pairs →
  pairDiagonal pairs ≤ pairSumLeft pairs * pairSumRight pairs
pairDiagonalBelowProduct nnp[] = ℚₚ.≤-refl
pairDiagonalBelowProduct
  (nnp∷ {left} {right} {rest} leftNN rightNN restNN) =
  let
    first =
      ℚₚ.+-monoʳ-≤
        (left * right)
        (pairDiagonalBelowProduct restNN)

    crossOneNN : 0ℚ ≤ left * pairSumRight rest
    crossOneNN =
      let
        instance
          leftNNI = nonNegative leftNN
          restNNI = nonNegative (pairRightNonnegative restNN)
          productNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg left (pairSumRight rest)
      in ℚₚ.nonNegative⁻¹ (left * pairSumRight rest)

    crossTwoNN : 0ℚ ≤ pairSumLeft rest * right
    crossTwoNN =
      let
        instance
          restNNI = nonNegative (pairLeftNonnegative restNN)
          rightNNI = nonNegative rightNN
          productNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg (pairSumLeft rest) right
      in ℚₚ.nonNegative⁻¹ (pairSumLeft rest * right)

    crossNN = L2.addNonnegative crossOneNN crossTwoNN

    addCross :
      left * right + pairSumLeft rest * pairSumRight rest
      ≤ left * right + pairSumLeft rest * pairSumRight rest
        + (left * pairSumRight rest + pairSumLeft rest * right)
    addCross =
      subst
        (λ lower →
          lower
          ≤ left * right + pairSumLeft rest * pairSumRight rest
            + (left * pairSumRight rest + pairSumLeft rest * right))
        (ℚₚ.+-identityʳ
          (left * right + pairSumLeft rest * pairSumRight rest))
        (ℚₚ.+-monoʳ-≤
          (left * right + pairSumLeft rest * pairSumRight rest)
          crossNN)

    endpoint :
      left * right + pairSumLeft rest * pairSumRight rest
        + (left * pairSumRight rest + pairSumLeft rest * right)
      ≡ (left + pairSumLeft rest) * (right + pairSumRight rest)
    endpoint = solve
      (left ∷ right ∷ pairSumLeft rest ∷ pairSumRight rest ∷ [])
  in
  ℚₚ.≤-trans
    first
    (subst
      (λ upper →
        left * right + pairSumLeft rest * pairSumRight rest ≤ upper)
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

highCubeList : EightSixThreeData → List ℚ
highCubeList dataSet =
    cube (b0 dataSet) ∷ cube (b1 dataSet)
  ∷ cube (b2 dataSet) ∷ cube (b3 dataSet)
  ∷ cube (b4 dataSet) ∷ cube (b5 dataSet)
  ∷ cube (b6 dataSet) ∷ cube (b7 dataSet) ∷ []

highCubeListNonnegative :
  (dataSet : EightSixThreeData) →
  NonnegativeList (highCubeList dataSet)
highCubeListNonnegative dataSet =
  nn∷ (cubeNonnegative (b0 dataSet) (b0NN dataSet))
  (nn∷ (cubeNonnegative (b1 dataSet) (b1NN dataSet))
  (nn∷ (cubeNonnegative (b2 dataSet) (b2NN dataSet))
  (nn∷ (cubeNonnegative (b3 dataSet) (b3NN dataSet))
  (nn∷ (cubeNonnegative (b4 dataSet) (b4NN dataSet))
  (nn∷ (cubeNonnegative (b5 dataSet) (b5NN dataSet))
  (nn∷ (cubeNonnegative (b6 dataSet) (b6NN dataSet))
  (nn∷ (cubeNonnegative (b7 dataSet) (b7NN dataSet)) nn[])))))))

sixthPairs : EightSixThreeData → List Pair
sixthPairs dataSet =
    (sixth (a0 dataSet) , sixth (b0 dataSet))
  ∷ (sixth (a1 dataSet) , sixth (b1 dataSet))
  ∷ (sixth (a2 dataSet) , sixth (b2 dataSet))
  ∷ (sixth (a3 dataSet) , sixth (b3 dataSet))
  ∷ (sixth (a4 dataSet) , sixth (b4 dataSet))
  ∷ (sixth (a5 dataSet) , sixth (b5 dataSet))
  ∷ (sixth (a6 dataSet) , sixth (b6 dataSet))
  ∷ (sixth (a7 dataSet) , sixth (b7 dataSet)) ∷ []

sixthPairsNonnegative :
  (dataSet : EightSixThreeData) →
  NonnegativePairs (sixthPairs dataSet)
sixthPairsNonnegative dataSet =
  nnp∷
    (sixthNonnegative (a0 dataSet) (a0NN dataSet))
    (sixthNonnegative (b0 dataSet) (b0NN dataSet))
  (nnp∷
    (sixthNonnegative (a1 dataSet) (a1NN dataSet))
    (sixthNonnegative (b1 dataSet) (b1NN dataSet))
  (nnp∷
    (sixthNonnegative (a2 dataSet) (a2NN dataSet))
    (sixthNonnegative (b2 dataSet) (b2NN dataSet))
  (nnp∷
    (sixthNonnegative (a3 dataSet) (a3NN dataSet))
    (sixthNonnegative (b3 dataSet) (b3NN dataSet))
  (nnp∷
    (sixthNonnegative (a4 dataSet) (a4NN dataSet))
    (sixthNonnegative (b4 dataSet) (b4NN dataSet))
  (nnp∷
    (sixthNonnegative (a5 dataSet) (a5NN dataSet))
    (sixthNonnegative (b5 dataSet) (b5NN dataSet))
  (nnp∷
    (sixthNonnegative (a6 dataSet) (a6NN dataSet))
    (sixthNonnegative (b6 dataSet) (b6NN dataSet))
  (nnp∷
    (sixthNonnegative (a7 dataSet) (a7NN dataSet))
    (sixthNonnegative (b7 dataSet) (b7NN dataSet))
    nnp[]))))))))

cubeProductSumMeaning :
  (dataSet : EightSixThreeData) →
  cube (productSquare (a0 dataSet) (b0 dataSet))
    + cube (productSquare (a1 dataSet) (b1 dataSet))
    + cube (productSquare (a2 dataSet) (b2 dataSet))
    + cube (productSquare (a3 dataSet) (b3 dataSet))
    + cube (productSquare (a4 dataSet) (b4 dataSet))
    + cube (productSquare (a5 dataSet) (b5 dataSet))
    + cube (productSquare (a6 dataSet) (b6 dataSet))
    + cube (productSquare (a7 dataSet) (b7 dataSet))
  ≡ pairDiagonal (sixthPairs dataSet)
cubeProductSumMeaning dataSet =
  solve
    ( a0 dataSet ∷ a1 dataSet ∷ a2 dataSet ∷ a3 dataSet
    ∷ a4 dataSet ∷ a5 dataSet ∷ a6 dataSet ∷ a7 dataSet
    ∷ b0 dataSet ∷ b1 dataSet ∷ b2 dataSet ∷ b3 dataSet
    ∷ b4 dataSet ∷ b5 dataSet ∷ b6 dataSet ∷ b7 dataSet ∷ [])

pairLeftMeaning :
  (dataSet : EightSixThreeData) →
  pairSumLeft (sixthPairs dataSet) ≡ lowSixthMass dataSet
pairLeftMeaning dataSet =
  solve
    ( a0 dataSet ∷ a1 dataSet ∷ a2 dataSet ∷ a3 dataSet
    ∷ a4 dataSet ∷ a5 dataSet ∷ a6 dataSet ∷ a7 dataSet ∷ [])

pairRightMeaning :
  (dataSet : EightSixThreeData) →
  pairSumRight (sixthPairs dataSet)
  ≡ squares (highCubeList dataSet)
pairRightMeaning dataSet =
  solve
    ( b0 dataSet ∷ b1 dataSet ∷ b2 dataSet ∷ b3 dataSet
    ∷ b4 dataSet ∷ b5 dataSet ∷ b6 dataSet ∷ b7 dataSet ∷ [])

highCubeListSumMeaning :
  (dataSet : EightSixThreeData) →
  sum (highCubeList dataSet) ≡ highCubeMass dataSet
highCubeListSumMeaning dataSet =
  solve
    ( b0 dataSet ∷ b1 dataSet ∷ b2 dataSet ∷ b3 dataSet
    ∷ b4 dataSet ∷ b5 dataSet ∷ b6 dataSet ∷ b7 dataSet ∷ [])

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

    powerMean =
      eightValueCubeBound
        c0 c1 c2 c3 c4 c5 c6 c7
        (L2.squareNonnegative (a0 dataSet * b0 dataSet))
        (L2.squareNonnegative (a1 dataSet * b1 dataSet))
        (L2.squareNonnegative (a2 dataSet * b2 dataSet))
        (L2.squareNonnegative (a3 dataSet * b3 dataSet))
        (L2.squareNonnegative (a4 dataSet * b4 dataSet))
        (L2.squareNonnegative (a5 dataSet * b5 dataSet))
        (L2.squareNonnegative (a6 dataSet * b6 dataSet))
        (L2.squareNonnegative (a7 dataSet * b7 dataSet))

    diagonal = pairDiagonalBelowProduct (sixthPairsNonnegative dataSet)

    diagonalMassAdjusted :
      pairDiagonal (sixthPairs dataSet)
      ≤ lowSixthMass dataSet * squares (highCubeList dataSet)
    diagonalMassAdjusted =
      subst
        (λ leftMass →
          pairDiagonal (sixthPairs dataSet)
          ≤ leftMass * squares (highCubeList dataSet))
        (pairLeftMeaning dataSet)
        (subst
          (λ rightMass →
            pairDiagonal (sixthPairs dataSet)
            ≤ pairSumLeft (sixthPairs dataSet) * rightMass)
          (pairRightMeaning dataSet)
          diagonal)

    highSquare :
      squares (highCubeList dataSet)
      ≤ highCubeMass dataSet * highCubeMass dataSet
    highSquare =
      subst
        (λ upper →
          squares (highCubeList dataSet) ≤ upper * upper)
        (highCubeListSumMeaning dataSet)
        (squaresBelowSquareSum (highCubeListNonnegative dataSet))

    lowNN : 0ℚ ≤ lowSixthMass dataSet
    lowNN =
      subst
        (λ value → 0ℚ ≤ value)
        (pairLeftMeaning dataSet)
        (pairLeftNonnegative (sixthPairsNonnegative dataSet))

    scaledHigh =
      scaleBound
        (lowSixthMass dataSet)
        (squares (highCubeList dataSet))
        (highCubeMass dataSet * highCubeMass dataSet)
        lowNN
        highSquare

    diagonalFinal = ℚₚ.≤-trans diagonalMassAdjusted scaledHigh

    cubeSumFinal :
      cube c0 + cube c1 + cube c2 + cube c3
        + cube c4 + cube c5 + cube c6 + cube c7
      ≤ lowSixthMass dataSet
        * (highCubeMass dataSet * highCubeMass dataSet)
    cubeSumFinal =
      subst
        (λ lower →
          lower
          ≤ lowSixthMass dataSet
            * (highCubeMass dataSet * highCubeMass dataSet))
        (sym (cubeProductSumMeaning dataSet))
        diagonalFinal

    scaled = scaleBound sixtyFour _ _ sixtyFourNonnegative cubeSumFinal

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
      scaled)
