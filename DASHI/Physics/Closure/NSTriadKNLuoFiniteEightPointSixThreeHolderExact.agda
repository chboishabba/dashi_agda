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
-- COMPILER SPLIT
--
-- The elementary ordered-rational/ring algebra is compiled separately in
-- NSTriadKNLuoFiniteEightPointSixThreeHolderBoundary.  This legacy module now
-- owns only the literal eight-point carrier, transport identities, and final
-- Holder assembly.  Its public theorem surface is unchanged.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import
  DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointSixThreeHolderBoundary
  public

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

productSquareMeaning :
  (a b : ℚ) → productSquare a b ≡ L2.square (a * b)
productSquareMeaning a b = refl

sixthMeaning :
  (value : ℚ) → sixth value ≡ cube value * cube value
sixthMeaning value = refl

cubeProductPairMeaning :
  (a b : ℚ) → cube (productSquare a b) ≡ sixth a * sixth b
cubeProductPairMeaning a b
  rewrite productSquareMeaning a b
        | cubeMeaning (L2.square (a * b))
        | l2SquareMeaning (a * b)
        | cubeMeaning a
        | cubeMeaning b
        | sixthMeaning a
        | sixthMeaning b
  = solve (a ∷ b ∷ [])

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
    nnp[])))))))

-- Keep each product opaque to the ring solver.  The former proof passed all
-- sixteen xᵢ,yᵢ variables to `solve`, forcing Agda 2.9 to normalize the full
-- product polynomial.  Reassociating the eight already-formed products gives
-- the identical theorem while cutting the solver arity in half.
eightPairDiagonalMeaning :
  (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 x7 y7 : ℚ) →
  x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3
    + x4 * y4 + x5 * y5 + x6 * y6 + x7 * y7
  ≡ pairDiagonal
      ( (x0 , y0) ∷ (x1 , y1) ∷ (x2 , y2) ∷ (x3 , y3)
      ∷ (x4 , y4) ∷ (x5 , y5) ∷ (x6 , y6) ∷ (x7 , y7) ∷ [])
eightPairDiagonalMeaning x0 y0 x1 y1 x2 y2 x3 y3
    x4 y4 x5 y5 x6 y6 x7 y7 =
  let
    p0 = x0 * y0
    p1 = x1 * y1
    p2 = x2 * y2
    p3 = x3 * y3
    p4 = x4 * y4
    p5 = x5 * y5
    p6 = x6 * y6
    p7 = x7 * y7

    expanded :
      p0 + p1 + p2 + p3 + p4 + p5 + p6 + p7
      ≡ p0 + (p1 + (p2 + (p3 + (p4 + (p5 + (p6 + (p7 + 0ℚ)))))))
    expanded = solve (p0 ∷ p1 ∷ p2 ∷ p3 ∷ p4 ∷ p5 ∷ p6 ∷ p7 ∷ [])
  in
  trans expanded refl

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
cubeProductSumMeaning dataSet
  rewrite cubeProductPairMeaning (a0 dataSet) (b0 dataSet)
        | cubeProductPairMeaning (a1 dataSet) (b1 dataSet)
        | cubeProductPairMeaning (a2 dataSet) (b2 dataSet)
        | cubeProductPairMeaning (a3 dataSet) (b3 dataSet)
        | cubeProductPairMeaning (a4 dataSet) (b4 dataSet)
        | cubeProductPairMeaning (a5 dataSet) (b5 dataSet)
        | cubeProductPairMeaning (a6 dataSet) (b6 dataSet)
        | cubeProductPairMeaning (a7 dataSet) (b7 dataSet)
  = eightPairDiagonalMeaning
      (sixth (a0 dataSet)) (sixth (b0 dataSet))
      (sixth (a1 dataSet)) (sixth (b1 dataSet))
      (sixth (a2 dataSet)) (sixth (b2 dataSet))
      (sixth (a3 dataSet)) (sixth (b3 dataSet))
      (sixth (a4 dataSet)) (sixth (b4 dataSet))
      (sixth (a5 dataSet)) (sixth (b5 dataSet))
      (sixth (a6 dataSet)) (sixth (b6 dataSet))
      (sixth (a7 dataSet)) (sixth (b7 dataSet))

pairLeftMeaning :
  (dataSet : EightSixThreeData) →
  pairSumLeft (sixthPairs dataSet) ≡ lowSixthMass dataSet
pairLeftMeaning dataSet =
  let
    reassociate :
      (x0 x1 x2 x3 x4 x5 x6 x7 : ℚ) →
      x0 + (x1 + (x2 + (x3 + (x4 + (x5 + (x6 + x7))))))
      ≡ x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7
    reassociate x0 x1 x2 x3 x4 x5 x6 x7 =
      solve (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ [])
  in
  reassociate
    (sixth (a0 dataSet)) (sixth (a1 dataSet))
    (sixth (a2 dataSet)) (sixth (a3 dataSet))
    (sixth (a4 dataSet)) (sixth (a5 dataSet))
    (sixth (a6 dataSet)) (sixth (a7 dataSet))

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
