module DASHI.Physics.YangMills.BalabanNoncommutativeMarkedOperatorProductExact where

------------------------------------------------------------------------
-- ROUND72: NONCOMMUTATIVE MARKED PRODUCT TELESCOPE FOR CMP109 TREE FACTORS
--
-- PRIMARY SOURCE CALIBRATION
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99(3) (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- OPERATOR-NORM CALIBRATION
--
-- Tosio Kato, "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- Roger A. Horn and Charles R. Johnson, "Matrix Analysis", second edition,
-- Cambridge University Press. DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- CMP109's differentiated tree factors are operator/multilinear compositions,
-- so the source-faithful telescope is NONCOMMUTATIVE.  For finite products
--
--   A_1 ... A_n  and  B_1 ... B_n,
--
-- the recursive identity
--
--   A P - B Q = (A-B) P + B (P-Q)
--
-- gives the ordered replacement expansion
--
--   A_1...A_n - B_1...B_n
--     = (A_1-B_1)A_2...A_n
--       + B_1(A_2-B_2)A_3...A_n
--       + ...
--       + B_1...B_{n-1}(A_n-B_n).
--
-- With ||A_i||,||B_i|| <= b_i and ||A_i-B_i|| <= m_i, triangle inequality
-- and norm submultiplicativity yield the same ordered scalar majorant.  Thus
-- the physical Lemma 7 producer supplies only factorwise ordinary/marked
-- operator bounds; no whole tree-product replacement estimate remains.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record MarkedOperatorNormAlgebra (Operator Bound : Set) : Set₁ where
  field
    identityOperator : Operator
    compose : Operator → Operator → Operator
    difference : Operator → Operator → Operator
    addOperator : Operator → Operator → Operator

    operatorNorm : Operator → Bound

    zeroBound oneBound : Bound
    addBound multiplyBound : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {a b c d} →
      LessEqual a b → LessEqual c d →
      LessEqual (addBound a c) (addBound b d)
    multiplyMonotone : ∀ {a b c d} →
      LessEqual a b → LessEqual c d →
      LessEqual (multiplyBound a c) (multiplyBound b d)

    identityNormBound : LessEqual (operatorNorm identityOperator) oneBound
    zeroDifferenceNormBound :
      LessEqual (operatorNorm (difference identityOperator identityOperator))
        zeroBound

    normTriangle : ∀ left right →
      LessEqual
        (operatorNorm (addOperator left right))
        (addBound (operatorNorm left) (operatorNorm right))

    normSubmultiplicative : ∀ outer inner →
      LessEqual
        (operatorNorm (compose outer inner))
        (multiplyBound (operatorNorm outer) (operatorNorm inner))

    -- Standard noncommutative product-difference identity.
    productDifferenceSplit : ∀ a b p q →
      difference (compose a p) (compose b q)
      ≡ addOperator
          (compose (difference a b) p)
          (compose b (difference p q))

open MarkedOperatorNormAlgebra public

operatorProduct :
  ∀ {Operator Bound} →
  MarkedOperatorNormAlgebra Operator Bound →
  {A : Set} → (A → Operator) → List A → Operator
operatorProduct algebra f [] = identityOperator algebra
operatorProduct algebra f (x ∷ xs) =
  compose algebra (f x) (operatorProduct algebra f xs)

ordinaryProductMajorant :
  ∀ {Operator Bound} →
  MarkedOperatorNormAlgebra Operator Bound →
  {A : Set} → (A → Bound) → List A → Bound
ordinaryProductMajorant algebra ordinary [] = oneBound algebra
ordinaryProductMajorant algebra ordinary (x ∷ xs) =
  multiplyBound algebra
    (ordinary x)
    (ordinaryProductMajorant algebra ordinary xs)

markedProductMajorant :
  ∀ {Operator Bound} →
  MarkedOperatorNormAlgebra Operator Bound →
  {A : Set} → (A → Bound) → (A → Bound) → List A → Bound
markedProductMajorant algebra ordinary marked [] = zeroBound algebra
markedProductMajorant algebra ordinary marked (x ∷ xs) =
  addBound algebra
    (multiplyBound algebra
      (marked x)
      (ordinaryProductMajorant algebra ordinary xs))
    (multiplyBound algebra
      (ordinary x)
      (markedProductMajorant algebra ordinary marked xs))

operatorProductNormBelowOrdinaryMajorant :
  ∀ {Operator Bound}
    (algebra : MarkedOperatorNormAlgebra Operator Bound)
    {A : Set}
    (f : A → Operator)
    (ordinary : A → Bound)
    (xs : List A) →
  (∀ x → LessEqual algebra (operatorNorm algebra (f x)) (ordinary x)) →
  LessEqual algebra
    (operatorNorm algebra (operatorProduct algebra f xs))
    (ordinaryProductMajorant algebra ordinary xs)
operatorProductNormBelowOrdinaryMajorant algebra f ordinary [] factorBound =
  identityNormBound algebra
operatorProductNormBelowOrdinaryMajorant
  algebra f ordinary (x ∷ xs) factorBound =
  transitive algebra
    (normSubmultiplicative algebra
      (f x) (operatorProduct algebra f xs))
    (multiplyMonotone algebra
      (factorBound x)
      (operatorProductNormBelowOrdinaryMajorant
        algebra f ordinary xs factorBound))

operatorProductDifferenceFromFactorwiseBounds :
  ∀ {Operator Bound}
    (algebra : MarkedOperatorNormAlgebra Operator Bound)
    {A : Set}
    (left right : A → Operator)
    (ordinary marked : A → Bound)
    (xs : List A) →
  (∀ x → LessEqual algebra
    (operatorNorm algebra (left x)) (ordinary x)) →
  (∀ x → LessEqual algebra
    (operatorNorm algebra (right x)) (ordinary x)) →
  (∀ x → LessEqual algebra
    (operatorNorm algebra (difference algebra (left x) (right x)))
    (marked x)) →
  LessEqual algebra
    (operatorNorm algebra
      (difference algebra
        (operatorProduct algebra left xs)
        (operatorProduct algebra right xs)))
    (markedProductMajorant algebra ordinary marked xs)
operatorProductDifferenceFromFactorwiseBounds
  algebra left right ordinary marked [] leftBound rightBound markedBound =
  zeroDifferenceNormBound algebra
operatorProductDifferenceFromFactorwiseBounds
  algebra left right ordinary marked (x ∷ xs)
  leftBound rightBound markedBound =
  let
    leftTail = operatorProduct algebra left xs
    rightTail = operatorProduct algebra right xs

    leftTailBound = operatorProductNormBelowOrdinaryMajorant
      algebra left ordinary xs leftBound

    tailDifferenceBound = operatorProductDifferenceFromFactorwiseBounds
      algebra left right ordinary marked xs leftBound rightBound markedBound

    markedHeadBound = transitive algebra
      (normSubmultiplicative algebra
        (difference algebra (left x) (right x)) leftTail)
      (multiplyMonotone algebra
        (markedBound x)
        leftTailBound)

    unchangedHeadBound = transitive algebra
      (normSubmultiplicative algebra
        (right x)
        (difference algebra leftTail rightTail))
      (multiplyMonotone algebra
        (rightBound x)
        tailDifferenceBound)

    splitBound = transitive algebra
      (normTriangle algebra
        (compose algebra (difference algebra (left x) (right x)) leftTail)
        (compose algebra (right x) (difference algebra leftTail rightTail)))
      (addMonotone algebra markedHeadBound unchangedHeadBound)
  in
  subst
    (λ expanded →
      LessEqual algebra
        (operatorNorm algebra
          (difference algebra
            (operatorProduct algebra left (x ∷ xs))
            (operatorProduct algebra right (x ∷ xs))))
        expanded)
    refl
    (subst
      (λ actual →
        LessEqual algebra
          (operatorNorm algebra actual)
          (markedProductMajorant algebra ordinary marked (x ∷ xs)))
      (productDifferenceSplit algebra
        (left x) (right x) leftTail rightTail)
      splitBound)

noncommutativeMarkedOperatorProductLevel : ProofLevel
noncommutativeMarkedOperatorProductLevel = machineChecked

-- Physical Lemma 7 seam after this theorem:
-- instantiate the algebra with the literal CMP109 operator/multilinear factors;
-- ordinary factor norms come from the published differentiated tree bounds and
-- the marked difference norm of the changed factor comes from CMP99(3).
physicalCMP109MarkedOperatorFactorBoundsLevel : ProofLevel
physicalCMP109MarkedOperatorFactorBoundsLevel = conditional
