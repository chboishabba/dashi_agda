module DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointSixThreeHolderBoundary where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Classical Hölder inequality, finite counting-measure specialization.
-- Related reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- COMPILER BOUNDARY
--
-- Agda 2.9 profiling isolated the legacy eight-point Holder implementation as
-- an elaboration hotspot even after the finite L2 carrier was removed.  The
-- expensive part is elementary ordered-rational/ring normalization.  This file
-- owns that algebra once, behind its compiled .agdai boundary.  The legacy
-- eight-point theorem module should contain only the concrete eight-point data
-- transport and final theorem assembly.
--
-- Round 61 profiling sharpened the hotspot further: the old eight-variable
-- RingSolver call used only to reassociate the cube of an eight-term sum took
-- about 76 seconds and drove the warm-cache check to roughly 17.7 GiB RSS.
-- Reassociation below is therefore proved from binary associativity, and the
-- four/eight endpoint arithmetic is factored through two-variable solver
-- lemmas.  The public theorem statements are unchanged.
--
-- No postulates or new analytic assumptions are introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalOrderCore as Core

module L2 = Core

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

cubeMeaning :
  (value : ℚ) → cube value ≡ value * value * value
cubeMeaning value = refl

threeMeaning : three ≡ Int.+ 3 / 1
threeMeaning = refl

fourMeaning : four ≡ Int.+ 4 / 1
fourMeaning = refl

sixteenMeaning : sixteen ≡ Int.+ 16 / 1
sixteenMeaning = refl

sixtyFourMeaning : sixtyFour ≡ Int.+ 64 / 1
sixtyFourMeaning = refl

sumFourReassociate :
  (a b c d : ℚ) →
  a + b + c + d ≡ (a + b) + (c + d)
sumFourReassociate a b c d =
  ℚₚ.+-assoc (a + b) c d

sumRightFourAssociate :
  (a b c d : ℚ) →
  a + b + c + d ≡ a + (b + (c + d))
sumRightFourAssociate a b c d =
  trans
    (ℚₚ.+-assoc (a + b) c d)
    (ℚₚ.+-assoc a b (c + d))

sumEightReassociate :
  (a b c d e f g h : ℚ) →
  a + b + c + d + e + f + g + h
    ≡ (a + b + c + d) + (e + f + g + h)
sumEightReassociate a b c d e f g h =
  let
    left4 : ℚ
    left4 = a + b + c + d

    tailRightAssociated :
      e + f + g + h ≡ e + (f + (g + h))
    tailRightAssociated = sumRightFourAssociate e f g h
  in
  trans
    (ℚₚ.+-assoc ((left4 + e) + f) g h)
    (trans
      (ℚₚ.+-assoc (left4 + e) f (g + h))
      (trans
        (ℚₚ.+-assoc left4 e (f + (g + h)))
        (cong (λ tail → left4 + tail) (sym tailRightAssociated))))

fourPairEndpointGrouped :
  (left right : ℚ) →
  four * (four * left + four * right)
    ≡ sixteen * (left + right)
fourPairEndpointGrouped left right
  rewrite fourMeaning | sixteenMeaning
  = solve (left ∷ right ∷ [])

fourPairEndpoint :
  (x y z w : ℚ) →
  four * (four * (x + y) + four * (z + w))
    ≡ sixteen * (x + y + z + w)
fourPairEndpoint x y z w =
  trans
    (fourPairEndpointGrouped (x + y) (z + w))
    (cong
      (λ total → sixteen * total)
      (sym (sumFourReassociate x y z w)))

cubeFourSumReassociate :
  (a b c d : ℚ) →
  cube (a + b + c + d) ≡ cube ((a + b) + (c + d))
cubeFourSumReassociate a b c d =
  cong cube (sumFourReassociate a b c d)

eightEndpointGrouped :
  (left right : ℚ) →
  four * (sixteen * left + sixteen * right)
    ≡ sixtyFour * (left + right)
eightEndpointGrouped left right
  rewrite fourMeaning | sixteenMeaning | sixtyFourMeaning
  = solve (left ∷ right ∷ [])

eightEndpoint :
  (a b c d e f g h : ℚ) →
  four * (sixteen * (a + b + c + d) + sixteen * (e + f + g + h))
    ≡ sixtyFour * (a + b + c + d + e + f + g + h)
eightEndpoint a b c d e f g h =
  trans
    (eightEndpointGrouped
      (a + b + c + d)
      (e + f + g + h))
    (cong
      (λ total → sixtyFour * total)
      (sym (sumEightReassociate a b c d e f g h)))

cubeEightSumReassociate :
  (a b c d e f g h : ℚ) →
  cube (a + b + c + d + e + f + g + h)
    ≡ cube ((a + b + c + d) + (e + f + g + h))
cubeEightSumReassociate a b c d e f g h =
  cong cube (sumEightReassociate a b c d e f g h)

l2SquareMeaning :
  (value : ℚ) → Core.square value ≡ value * value
l2SquareMeaning value = refl

squareAddIdentity :
  (value sumValue : ℚ) →
  Core.square value + Core.square sumValue
    + (value * sumValue + value * sumValue)
    ≡ Core.square (value + sumValue)
squareAddIdentity value sumValue
  rewrite l2SquareMeaning value
        | l2SquareMeaning sumValue
        | l2SquareMeaning (value + sumValue)
  = solve (value ∷ sumValue ∷ [])

pairProductDistribute :
  (left right leftRest rightRest : ℚ) →
  left * right + leftRest * rightRest
    + (left * rightRest + leftRest * right)
  ≡ (left + leftRest) * (right + rightRest)
pairProductDistribute left right leftRest rightRest =
  solve (left ∷ right ∷ leftRest ∷ rightRest ∷ [])

cubePairIdentityExpanded :
  (left right : ℚ) →
  cube (left + right)
    + three * (left + right) * ((left - right) * (left - right))
  ≡ four * (cube left + cube right)
cubePairIdentityExpanded left right
  rewrite cubeMeaning (left + right)
        | cubeMeaning left
        | cubeMeaning right
        | threeMeaning
        | fourMeaning
  = solve (left ∷ right ∷ [])

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

    squareMeaning :
      L2.square (left - right) ≡ (left - right) * (left - right)
    squareMeaning = refl

    identity :
      cube (left + right)
        + three * (left + right) * L2.square (left - right)
      ≡ four * (cube left + cube right)
    identity =
      subst
        (λ squareValue →
          cube (left + right)
            + three * (left + right) * squareValue
          ≡ four * (cube left + cube right))
        (sym squareMeaning)
        (cubePairIdentityExpanded left right)
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
    endpoint = fourPairEndpoint (cube a) (cube b) (cube c) (cube d)

    reassociate :
      cube (a + b + c + d) ≡ cube ((a + b) + (c + d))
    reassociate = cubeFourSumReassociate a b c d
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
      eightEndpoint
        (cube a) (cube b) (cube c) (cube d)
        (cube e) (cube f) (cube g) (cube h)

    reassociate :
      cube (a + b + c + d + e + f + g + h)
      ≡ cube (left4 + right4)
    reassociate = cubeEightSumReassociate a b c d e f g h
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
    endpoint = squareAddIdentity value (sum values)
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
    endpoint =
      pairProductDistribute
        left right (pairSumLeft rest) (pairSumRight rest)
  in
  ℚₚ.≤-trans
    first
    (subst
      (λ upper →
        left * right + pairSumLeft rest * pairSumRight rest ≤ upper)
      endpoint
      addCross)
