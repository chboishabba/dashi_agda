module DASHI.Physics.Closure.NSTriadKNLuoFiniteEightPointSixThreeHolderTransportBoundary where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Classical Hölder inequality, specialized to the finite eight-point
-- periodic carrier.
-- Related reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- COMPILER PURPOSE
--
-- Agda 2.9 profiling showed that the remaining cost of the historical
-- eight-point module was not the small ring identities but the final assembly:
-- repeated dependent `subst` over concrete eight-entry list proofs forced
-- large normalization of imported boundary evidence.
--
-- This module changes only the representation of the internal transport.
-- The public EightSixThreeData carrier and final factor-64 theorem are the
-- same.  The low/high masses are definitionally the recursive masses consumed
-- by the finite ordered-rational lemmas, so the final proof no longer needs
-- the expensive pairLeft/pairRight/high-list dependent substitutions.
-- No postulate or new analytic assumption is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym; trans)

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
  (a b : ℚ) →
  cube (productSquare a b)
  ≡ sixth a * L2.square (cube b)
cubeProductPairMeaning a b
  rewrite productSquareMeaning a b
        | cubeMeaning (L2.square (a * b))
        | l2SquareMeaning (a * b)
        | cubeMeaning a
        | cubeMeaning b
        | sixthMeaning a
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

highCubeList : EightSixThreeData → List ℚ
highCubeList dataSet =
    cube (b0 dataSet) ∷ cube (b1 dataSet)
  ∷ cube (b2 dataSet) ∷ cube (b3 dataSet)
  ∷ cube (b4 dataSet) ∷ cube (b5 dataSet)
  ∷ cube (b6 dataSet) ∷ cube (b7 dataSet) ∷ []

sixthPairs : EightSixThreeData → List Pair
sixthPairs dataSet =
    (sixth (a0 dataSet) , L2.square (cube (b0 dataSet)))
  ∷ (sixth (a1 dataSet) , L2.square (cube (b1 dataSet)))
  ∷ (sixth (a2 dataSet) , L2.square (cube (b2 dataSet)))
  ∷ (sixth (a3 dataSet) , L2.square (cube (b3 dataSet)))
  ∷ (sixth (a4 dataSet) , L2.square (cube (b4 dataSet)))
  ∷ (sixth (a5 dataSet) , L2.square (cube (b5 dataSet)))
  ∷ (sixth (a6 dataSet) , L2.square (cube (b6 dataSet)))
  ∷ (sixth (a7 dataSet) , L2.square (cube (b7 dataSet))) ∷ []

-- These definitions are deliberately aligned with the recursive finite-list
-- quantities consumed below.  They are propositionally the same explicit
-- eight-term sums as the historical definitions, but make the transport
-- equalities definitional rather than dependent `subst` obligations.
lowSixthMass : EightSixThreeData → ℚ
lowSixthMass dataSet = pairSumLeft (sixthPairs dataSet)

highCubeMass : EightSixThreeData → ℚ
highCubeMass dataSet = sum (highCubeList dataSet)

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

sixthPairsNonnegative :
  (dataSet : EightSixThreeData) →
  NonnegativePairs (sixthPairs dataSet)
sixthPairsNonnegative dataSet =
  nnp∷ (sixthNonnegative (a0 dataSet) (a0NN dataSet))
        (L2.squareNonnegative (cube (b0 dataSet)))
  (nnp∷ (sixthNonnegative (a1 dataSet) (a1NN dataSet))
        (L2.squareNonnegative (cube (b1 dataSet)))
  (nnp∷ (sixthNonnegative (a2 dataSet) (a2NN dataSet))
        (L2.squareNonnegative (cube (b2 dataSet)))
  (nnp∷ (sixthNonnegative (a3 dataSet) (a3NN dataSet))
        (L2.squareNonnegative (cube (b3 dataSet)))
  (nnp∷ (sixthNonnegative (a4 dataSet) (a4NN dataSet))
        (L2.squareNonnegative (cube (b4 dataSet)))
  (nnp∷ (sixthNonnegative (a5 dataSet) (a5NN dataSet))
        (L2.squareNonnegative (cube (b5 dataSet)))
  (nnp∷ (sixthNonnegative (a6 dataSet) (a6NN dataSet))
        (L2.squareNonnegative (cube (b6 dataSet)))
  (nnp∷ (sixthNonnegative (a7 dataSet) (a7NN dataSet))
        (L2.squareNonnegative (cube (b7 dataSet)))
        nnp[])))))))

-- Legacy transport names are retained, but all three are now definitional.
pairLeftMeaning :
  (dataSet : EightSixThreeData) →
  pairSumLeft (sixthPairs dataSet) ≡ lowSixthMass dataSet
pairLeftMeaning dataSet = refl

pairRightMeaning :
  (dataSet : EightSixThreeData) →
  pairSumRight (sixthPairs dataSet) ≡ squares (highCubeList dataSet)
pairRightMeaning dataSet = refl

highCubeListSumMeaning :
  (dataSet : EightSixThreeData) →
  sum (highCubeList dataSet) ≡ highCubeMass dataSet
highCubeListSumMeaning dataSet = refl

-- Reassociate eight already-formed terms only.  Unlike the historical proof,
-- the ring solver never sees the sixteen x_i,y_i product variables.
eightNestedSum :
  (x0 x1 x2 x3 x4 x5 x6 x7 : ℚ) →
  x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7
  ≡ x0 + (x1 + (x2 + (x3 + (x4 + (x5 + (x6 + (x7 + 0ℚ)))))))
eightNestedSum x0 x1 x2 x3 x4 x5 x6 x7 =
  solve (x0 ∷ x1 ∷ x2 ∷ x3 ∷ x4 ∷ x5 ∷ x6 ∷ x7 ∷ [])

sumCongruence8 :
  (x0 x1 x2 x3 x4 x5 x6 x7
   y0 y1 y2 y3 y4 y5 y6 y7 : ℚ) →
  x0 ≡ y0 → x1 ≡ y1 → x2 ≡ y2 → x3 ≡ y3 →
  x4 ≡ y4 → x5 ≡ y5 → x6 ≡ y6 → x7 ≡ y7 →
  x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7
  ≡ y0 + y1 + y2 + y3 + y4 + y5 + y6 + y7
sumCongruence8 x0 x1 x2 x3 x4 x5 x6 x7
                y0 y1 y2 y3 y4 y5 y6 y7
                p0 p1 p2 p3 p4 p5 p6 p7 =
  cong₂ _+_
    (cong₂ _+_
      (cong₂ _+_
        (cong₂ _+_ (cong₂ _+_ (cong₂ _+_ (cong₂ _+_ p0 p1) p2) p3) p4) p5)
        p6)
      p7

sixtyFourEndpoint :
  (low high : ℚ) →
  sixtyFour * (low * (high * high))
  ≡ sixtyFour * low * (high * high)
sixtyFourEndpoint low high = solve (low ∷ high ∷ [])

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
  = trans
      (sumCongruence8
        (cube (productSquare (a0 dataSet) (b0 dataSet)))
        (cube (productSquare (a1 dataSet) (b1 dataSet)))
        (cube (productSquare (a2 dataSet) (b2 dataSet)))
        (cube (productSquare (a3 dataSet) (b3 dataSet)))
        (cube (productSquare (a4 dataSet) (b4 dataSet)))
        (cube (productSquare (a5 dataSet) (b5 dataSet)))
        (cube (productSquare (a6 dataSet) (b6 dataSet)))
        (cube (productSquare (a7 dataSet) (b7 dataSet)))
        (sixth (a0 dataSet) * L2.square (cube (b0 dataSet)))
        (sixth (a1 dataSet) * L2.square (cube (b1 dataSet)))
        (sixth (a2 dataSet) * L2.square (cube (b2 dataSet)))
        (sixth (a3 dataSet) * L2.square (cube (b3 dataSet)))
        (sixth (a4 dataSet) * L2.square (cube (b4 dataSet)))
        (sixth (a5 dataSet) * L2.square (cube (b5 dataSet)))
        (sixth (a6 dataSet) * L2.square (cube (b6 dataSet)))
        (sixth (a7 dataSet) * L2.square (cube (b7 dataSet)))
        (cubeProductPairMeaning (a0 dataSet) (b0 dataSet))
        (cubeProductPairMeaning (a1 dataSet) (b1 dataSet))
        (cubeProductPairMeaning (a2 dataSet) (b2 dataSet))
        (cubeProductPairMeaning (a3 dataSet) (b3 dataSet))
        (cubeProductPairMeaning (a4 dataSet) (b4 dataSet))
        (cubeProductPairMeaning (a5 dataSet) (b5 dataSet))
        (cubeProductPairMeaning (a6 dataSet) (b6 dataSet))
        (cubeProductPairMeaning (a7 dataSet) (b7 dataSet)))
      (eightNestedSum
      (sixth (a0 dataSet) * L2.square (cube (b0 dataSet)))
      (sixth (a1 dataSet) * L2.square (cube (b1 dataSet)))
      (sixth (a2 dataSet) * L2.square (cube (b2 dataSet)))
      (sixth (a3 dataSet) * L2.square (cube (b3 dataSet)))
      (sixth (a4 dataSet) * L2.square (cube (b4 dataSet)))
      (sixth (a5 dataSet) * L2.square (cube (b5 dataSet)))
      (sixth (a6 dataSet) * L2.square (cube (b6 dataSet)))
      (sixth (a7 dataSet) * L2.square (cube (b7 dataSet)))
      )

abstract
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

      -- The three identities which formerly required dependent substitutions
      -- are now definitional consequences of lowSixthMass/highCubeMass and
      -- the right component chosen in sixthPairs.
      diagonalMassAdjusted :
        pairDiagonal (sixthPairs dataSet)
        ≤ lowSixthMass dataSet * squares (highCubeList dataSet)
      diagonalMassAdjusted =
        pairDiagonalBelowProduct (sixthPairsNonnegative dataSet)

      highSquare :
        squares (highCubeList dataSet)
        ≤ highCubeMass dataSet * highCubeMass dataSet
      highSquare =
        squaresBelowSquareSum (highCubeListNonnegative dataSet)

      lowNN : 0ℚ ≤ lowSixthMass dataSet
      lowNN = pairLeftNonnegative (sixthPairsNonnegative dataSet)

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
      endpoint = sixtyFourEndpoint
        (lowSixthMass dataSet)
        (highCubeMass dataSet)
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
