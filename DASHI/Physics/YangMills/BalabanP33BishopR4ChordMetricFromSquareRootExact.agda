module DASHI.Physics.YangMills.BalabanP33BishopR4ChordMetricFromSquareRootExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Errett Bishop and Douglas Bridges,
-- "Constructive Analysis", Grundlehren der mathematischen Wissenschaften 279,
-- Springer, 1985. DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Complete the finite-dimensional part of the constructive square-root chord
-- metric.  A single scalar square-root backend supplies the standard scalar
-- laws together with nonnegativity of squares.  From those laws this module
-- proves, rather than assumes:
--
--   * the four-dimensional Lagrange identity;
--   * squared Cauchy--Schwarz;
--   * the Minkowski/triangle inequality for the Euclidean square-root norm;
--   * symmetry and reflexivity of the resulting chord distance;
--   * d_ch(exp X,1) <= ||X|| for the literal Bishop quaternion exponential.
--
-- The Lagrange remainder is the explicit six-square sum
--
--   sum_{i<j} (a_i b_j-a_j b_i)^2.
--
-- Thus the remaining foundational seam is exactly construction of one Bishop
-- square-root operation satisfying the scalar specification below.  The
-- current pinned Bishop dependency does not yet implement such an operation;
-- no metric or Cauchy--Schwarz authority is otherwise imported.
------------------------------------------------------------------------

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanClayT2BishopQuaternionNormalizationExact as Quaternion
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpPositiveDenominatorExact as Positive
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Cross
import DASHI.Physics.YangMills.BalabanP33BishopLiteralQuaternionExponentialChordExact as Literal
open import DASHI.Physics.YangMills.CompactLieProofLevel

square : BishopReal.ℝ → BishopReal.ℝ
square value = BishopReal._*_ value value

record BishopSquareRootCalculus : Set₁ where
  field
    root : BishopReal.ℝ → BishopReal.ℝ
    squareNonnegative : ∀ value → BishopReal.NonNegative (square value)
    rootCongruent : ∀ {left right} →
      BishopReal._≃_ left right → BishopReal._≃_ (root left) (root right)
    rootNonnegative : ∀ value →
      BishopReal.NonNegative value → BishopReal.NonNegative (root value)
    rootSquare : ∀ value →
      BishopReal.NonNegative value →
      BishopReal._≃_ (square (root value)) value
    rootMonotone : ∀ {left right} →
      BishopReal.NonNegative left →
      BishopReal._≤_ left right → BishopReal._≤_ (root left) (root right)
    rootOfSquare : ∀ value →
      BishopReal._≃_ (root (square value)) (BishopReal.∣ value ∣)
    rootProduct : ∀ left right →
      BishopReal.NonNegative left → BishopReal.NonNegative right →
      BishopReal._≃_
        (root (BishopReal._*_ left right))
        (BishopReal._*_ (root left) (root right))

open BishopSquareRootCalculus public

record Vec4B : Set where
  constructor vec4B
  field x0 x1 x2 x3 : BishopReal.ℝ
open Vec4B public

add4 sub4 : Vec4B → Vec4B → Vec4B
add4 (vec4B a0 a1 a2 a3) (vec4B b0 b1 b2 b3) =
  vec4B (BishopReal._+_ a0 b0) (BishopReal._+_ a1 b1)
    (BishopReal._+_ a2 b2) (BishopReal._+_ a3 b3)
sub4 (vec4B a0 a1 a2 a3) (vec4B b0 b1 b2 b3) =
  vec4B (BishopReal._-_ a0 b0) (BishopReal._-_ a1 b1)
    (BishopReal._-_ a2 b2) (BishopReal._-_ a3 b3)

dot4 : Vec4B → Vec4B → BishopReal.ℝ
dot4 (vec4B a0 a1 a2 a3) (vec4B b0 b1 b2 b3) =
  BishopReal._+_ (BishopReal._*_ a0 b0)
    (BishopReal._+_ (BishopReal._*_ a1 b1)
      (BishopReal._+_ (BishopReal._*_ a2 b2) (BishopReal._*_ a3 b3)))

normSq4 : Vec4B → BishopReal.ℝ
normSq4 value = dot4 value value

normSq4Nonnegative :
  (roots : BishopSquareRootCalculus) →
  ∀ value → BishopReal.NonNegative (normSq4 value)
normSq4Nonnegative roots (vec4B a0 a1 a2 a3) =
  BishopProperties.nonNegx,y⇒nonNegx+y (squareNonnegative roots a0)
    (BishopProperties.nonNegx,y⇒nonNegx+y (squareNonnegative roots a1)
      (BishopProperties.nonNegx,y⇒nonNegx+y
        (squareNonnegative roots a2) (squareNonnegative roots a3)))

pairMinor : BishopReal.ℝ → BishopReal.ℝ → BishopReal.ℝ → BishopReal.ℝ → BishopReal.ℝ
pairMinor ai aj bi bj =
  BishopReal._-_ (BishopReal._*_ ai bj) (BishopReal._*_ aj bi)

lagrangeSixSquares : Vec4B → Vec4B → BishopReal.ℝ
lagrangeSixSquares (vec4B a0 a1 a2 a3) (vec4B b0 b1 b2 b3) =
  BishopReal._+_ (square (pairMinor a0 a1 b0 b1))
    (BishopReal._+_ (square (pairMinor a0 a2 b0 b2))
      (BishopReal._+_ (square (pairMinor a0 a3 b0 b3))
        (BishopReal._+_ (square (pairMinor a1 a2 b1 b2))
          (BishopReal._+_ (square (pairMinor a1 a3 b1 b3))
            (square (pairMinor a2 a3 b2 b3))))))

lagrangeSixSquaresNonnegative :
  (roots : BishopSquareRootCalculus) →
  ∀ left right → BishopReal.NonNegative (lagrangeSixSquares left right)
lagrangeSixSquaresNonnegative roots
    (vec4B a0 a1 a2 a3) (vec4B b0 b1 b2 b3) =
  BishopProperties.nonNegx,y⇒nonNegx+y
    (squareNonnegative roots (pairMinor a0 a1 b0 b1))
    (BishopProperties.nonNegx,y⇒nonNegx+y
      (squareNonnegative roots (pairMinor a0 a2 b0 b2))
      (BishopProperties.nonNegx,y⇒nonNegx+y
        (squareNonnegative roots (pairMinor a0 a3 b0 b3))
        (BishopProperties.nonNegx,y⇒nonNegx+y
          (squareNonnegative roots (pairMinor a1 a2 b1 b2))
          (BishopProperties.nonNegx,y⇒nonNegx+y
            (squareNonnegative roots (pairMinor a1 a3 b1 b3))
            (squareNonnegative roots (pairMinor a2 a3 b2 b3))))))

lagrangeIdentity4 : ∀ left right →
  BishopReal._≃_
    (BishopReal._-_ (BishopReal._*_ (normSq4 left) (normSq4 right))
      (square (dot4 left right)))
    (lagrangeSixSquares left right)
lagrangeIdentity4 (vec4B a0 a1 a2 a3) (vec4B b0 b1 b2 b3) =
  let open BishopProperties.ℝ-Solver
  in solve 8
    (λ a0 a1 a2 a3 b0 b1 b2 b3 →
      ((((a0 ⊗ a0) ⊕ ((a1 ⊗ a1) ⊕ ((a2 ⊗ a2) ⊕ (a3 ⊗ a3))))
        ⊗ ((b0 ⊗ b0) ⊕ ((b1 ⊗ b1) ⊕ ((b2 ⊗ b2) ⊕ (b3 ⊗ b3)))))
       ⊖ ((a0 ⊗ b0 ⊕ (a1 ⊗ b1 ⊕ (a2 ⊗ b2 ⊕ a3 ⊗ b3)))
        ⊗ (a0 ⊗ b0 ⊕ (a1 ⊗ b1 ⊕ (a2 ⊗ b2 ⊕ a3 ⊗ b3)))))
      ⊜ (((a0 ⊗ b1 ⊖ a1 ⊗ b0) ⊗ (a0 ⊗ b1 ⊖ a1 ⊗ b0))
        ⊕ (((a0 ⊗ b2 ⊖ a2 ⊗ b0) ⊗ (a0 ⊗ b2 ⊖ a2 ⊗ b0))
          ⊕ (((a0 ⊗ b3 ⊖ a3 ⊗ b0) ⊗ (a0 ⊗ b3 ⊖ a3 ⊗ b0))
            ⊕ (((a1 ⊗ b2 ⊖ a2 ⊗ b1) ⊗ (a1 ⊗ b2 ⊖ a2 ⊗ b1))
              ⊕ (((a1 ⊗ b3 ⊖ a3 ⊗ b1) ⊗ (a1 ⊗ b3 ⊖ a3 ⊗ b1))
                ⊕ ((a2 ⊗ b3 ⊖ a3 ⊗ b2) ⊗ (a2 ⊗ b3 ⊖ a3 ⊗ b2)))))))
    BishopProperties.≃-refl a0 a1 a2 a3 b0 b1 b2 b3

cauchySchwarzSquared4 :
  (roots : BishopSquareRootCalculus) →
  ∀ left right →
  BishopReal._≤_ (square (dot4 left right))
    (BishopReal._*_ (normSq4 left) (normSq4 right))
cauchySchwarzSquared4 roots left right =
  Cross.nonnegativeDifferenceGivesOrder
    (BishopProperties.≤-respʳ-≃
      (BishopProperties.≃-symm (lagrangeIdentity4 left right))
      (BishopProperties.nonNegx⇒0≤x
        (lagrangeSixSquaresNonnegative roots left right)))

rootDotUpper :
  (roots : BishopSquareRootCalculus) → ∀ left right →
  BishopReal._≤_ (dot4 left right)
    (BishopReal._*_ (root roots (normSq4 left)) (root roots (normSq4 right)))
rootDotUpper roots left right =
  let
    leftNonnegative = normSq4Nonnegative roots left
    rightNonnegative = normSq4Nonnegative roots right
    rootedCauchy = rootMonotone roots
      (squareNonnegative roots (dot4 left right))
      (cauchySchwarzSquared4 roots left right)
    absoluteBelowRootProduct = BishopProperties.≤-respʳ-≃
      (rootProduct roots (normSq4 left) (normSq4 right)
        leftNonnegative rightNonnegative)
      (BishopProperties.≤-respˡ-≃
        (BishopProperties.≃-symm (rootOfSquare roots (dot4 left right)))
        rootedCauchy)
  in BishopProperties.≤-trans BishopProperties.x≤∣x∣ absoluteBelowRootProduct

normSqAddExpansion : ∀ left right →
  BishopReal._≃_ (normSq4 (add4 left right))
    (BishopReal._+_ (BishopReal._+_ (normSq4 left) (normSq4 right))
      (BishopReal._+_ (dot4 left right) (dot4 left right)))
normSqAddExpansion (vec4B a0 a1 a2 a3) (vec4B b0 b1 b2 b3) =
  let open BishopProperties.ℝ-Solver
  in solve 8
    (λ a0 a1 a2 a3 b0 b1 b2 b3 →
      (((a0 ⊕ b0) ⊗ (a0 ⊕ b0))
        ⊕ (((a1 ⊕ b1) ⊗ (a1 ⊕ b1))
          ⊕ (((a2 ⊕ b2) ⊗ (a2 ⊕ b2)) ⊕ ((a3 ⊕ b3) ⊗ (a3 ⊕ b3)))))
      ⊜ (((a0 ⊗ a0) ⊕ ((a1 ⊗ a1) ⊕ ((a2 ⊗ a2) ⊕ (a3 ⊗ a3))))
        ⊕ ((b0 ⊗ b0) ⊕ ((b1 ⊗ b1) ⊕ ((b2 ⊗ b2) ⊕ (b3 ⊗ b3))))
        ⊕ ((a0 ⊗ b0 ⊕ (a1 ⊗ b1 ⊕ (a2 ⊗ b2 ⊕ a3 ⊗ b3)))
          ⊕ (a0 ⊗ b0 ⊕ (a1 ⊗ b1 ⊕ (a2 ⊗ b2 ⊕ a3 ⊗ b3))))))
    BishopProperties.≃-refl a0 a1 a2 a3 b0 b1 b2 b3

rootSumSquareExpansion :
  (roots : BishopSquareRootCalculus) → ∀ left right →
  BishopReal._≃_
    (square (BishopReal._+_ (root roots (normSq4 left))
      (root roots (normSq4 right))))
    (BishopReal._+_ (BishopReal._+_ (normSq4 left) (normSq4 right))
      (BishopReal._+_
        (BishopReal._*_ (root roots (normSq4 left)) (root roots (normSq4 right)))
        (BishopReal._*_ (root roots (normSq4 left)) (root roots (normSq4 right)))))
rootSumSquareExpansion roots left right =
  let
    rootLeft = root roots (normSq4 left)
    rootRight = root roots (normSq4 right)
    algebra =
      let open BishopProperties.ℝ-Solver
      in solve 2
        (λ x y → (x ⊕ y) ⊗ (x ⊕ y)
          ⊜ ((x ⊗ x) ⊕ (y ⊗ y)) ⊕ ((x ⊗ y) ⊕ (x ⊗ y)))
        BishopProperties.≃-refl rootLeft rootRight
  in BishopProperties.≃-trans algebra
    (BishopProperties.+-cong
      (BishopProperties.+-cong
        (rootSquare roots (normSq4 left) (normSq4Nonnegative roots left))
        (rootSquare roots (normSq4 right) (normSq4Nonnegative roots right)))
      BishopProperties.≃-refl)

minkowskiSquared4 :
  (roots : BishopSquareRootCalculus) → ∀ left right →
  BishopReal._≤_ (normSq4 (add4 left right))
    (square (BishopReal._+_ (root roots (normSq4 left))
      (root roots (normSq4 right))))
minkowskiSquared4 roots left right =
  let
    doubled = BishopProperties.+-mono-≤
      (rootDotUpper roots left right) (rootDotUpper roots left right)
    baseAdded = BishopProperties.+-mono-≤ BishopProperties.≤-refl doubled
  in BishopProperties.≤-respʳ-≃
    (BishopProperties.≃-symm (rootSumSquareExpansion roots left right))
    (BishopProperties.≤-respˡ-≃ (normSqAddExpansion left right) baseAdded)

norm4 : BishopSquareRootCalculus → Vec4B → BishopReal.ℝ
norm4 roots value = root roots (normSq4 value)

norm4Triangle :
  (roots : BishopSquareRootCalculus) → ∀ left right →
  BishopReal._≤_ (norm4 roots (add4 left right))
    (BishopReal._+_ (norm4 roots left) (norm4 roots right))
norm4Triangle roots left right =
  let
    rooted = rootMonotone roots (normSq4Nonnegative roots (add4 left right))
      (minkowskiSquared4 roots left right)
    sumNonnegative = BishopProperties.nonNegx,y⇒nonNegx+y
      (rootNonnegative roots (normSq4 left) (normSq4Nonnegative roots left))
      (rootNonnegative roots (normSq4 right) (normSq4Nonnegative roots right))
    rootSquareSum = BishopProperties.≃-trans
      (rootOfSquare roots (BishopReal._+_ (norm4 roots left) (norm4 roots right)))
      (BishopProperties.nonNegx⇒∣x∣≃x sumNonnegative)
  in BishopProperties.≤-respʳ-≃ rootSquareSum rooted

subThroughMiddleNormSq : ∀ left middle right →
  BishopReal._≃_ (normSq4 (sub4 left right))
    (normSq4 (add4 (sub4 left middle) (sub4 middle right)))
subThroughMiddleNormSq (vec4B l0 l1 l2 l3) (vec4B m0 m1 m2 m3)
    (vec4B r0 r1 r2 r3) =
  let open BishopProperties.ℝ-Solver
  in solve 12
    (λ l0 l1 l2 l3 m0 m1 m2 m3 r0 r1 r2 r3 →
      ((l0 ⊖ r0) ⊗ (l0 ⊖ r0)
        ⊕ ((l1 ⊖ r1) ⊗ (l1 ⊖ r1)
          ⊕ ((l2 ⊖ r2) ⊗ (l2 ⊖ r2) ⊕ (l3 ⊖ r3) ⊗ (l3 ⊖ r3))))
      ⊜ (((l0 ⊖ m0) ⊕ (m0 ⊖ r0)) ⊗ ((l0 ⊖ m0) ⊕ (m0 ⊖ r0))
        ⊕ (((l1 ⊖ m1) ⊕ (m1 ⊖ r1)) ⊗ ((l1 ⊖ m1) ⊕ (m1 ⊖ r1))
          ⊕ (((l2 ⊖ m2) ⊕ (m2 ⊖ r2)) ⊗ ((l2 ⊖ m2) ⊕ (m2 ⊖ r2))
            ⊕ ((l3 ⊖ m3) ⊕ (m3 ⊖ r3)) ⊗ ((l3 ⊖ m3) ⊕ (m3 ⊖ r3)))))
    BishopProperties.≃-refl l0 l1 l2 l3 m0 m1 m2 m3 r0 r1 r2 r3

chordDistance4 : BishopSquareRootCalculus → Vec4B → Vec4B → BishopReal.ℝ
chordDistance4 roots left right = norm4 roots (sub4 left right)

chordDistanceTriangle4 :
  (roots : BishopSquareRootCalculus) → ∀ left middle right →
  BishopReal._≤_ (chordDistance4 roots left right)
    (BishopReal._+_ (chordDistance4 roots left middle)
      (chordDistance4 roots middle right))
chordDistanceTriangle4 roots left middle right =
  BishopProperties.≤-respˡ-≃
    (rootCongruent roots (subThroughMiddleNormSq left middle right))
    (norm4Triangle roots (sub4 left middle) (sub4 middle right))

chordDistanceSymmetry4 :
  (roots : BishopSquareRootCalculus) → ∀ left right →
  BishopReal._≃_ (chordDistance4 roots left right)
    (chordDistance4 roots right left)
chordDistanceSymmetry4 roots (vec4B l0 l1 l2 l3) (vec4B r0 r1 r2 r3) =
  rootCongruent roots
    (let open BishopProperties.ℝ-Solver
     in solve 8
       (λ l0 l1 l2 l3 r0 r1 r2 r3 →
         ((l0 ⊖ r0) ⊗ (l0 ⊖ r0)
           ⊕ ((l1 ⊖ r1) ⊗ (l1 ⊖ r1)
             ⊕ ((l2 ⊖ r2) ⊗ (l2 ⊖ r2) ⊕ (l3 ⊖ r3) ⊗ (l3 ⊖ r3))))
         ⊜ ((r0 ⊖ l0) ⊗ (r0 ⊖ l0)
           ⊕ ((r1 ⊖ l1) ⊗ (r1 ⊖ l1)
             ⊕ ((r2 ⊖ l2) ⊗ (r2 ⊖ l2) ⊕ (r3 ⊖ l3) ⊗ (r3 ⊖ l3)))))
       BishopProperties.≃-refl l0 l1 l2 l3 r0 r1 r2 r3)

chordDistanceReflexive4 :
  (roots : BishopSquareRootCalculus) → ∀ value →
  BishopReal._≃_ (chordDistance4 roots value value) BishopReal.0ℝ
chordDistanceReflexive4 roots (vec4B a0 a1 a2 a3) =
  BishopProperties.≃-trans
    (rootCongruent roots
      (let open BishopProperties.ℝ-Solver
       in solve 4
         (λ a0 a1 a2 a3 →
           ((a0 ⊖ a0) ⊗ (a0 ⊖ a0)
             ⊕ ((a1 ⊖ a1) ⊗ (a1 ⊖ a1)
               ⊕ ((a2 ⊖ a2) ⊗ (a2 ⊖ a2) ⊕ (a3 ⊖ a3) ⊗ (a3 ⊖ a3))))
           ⊜ Κ (+ 0 / 1) ⊗ Κ (+ 0 / 1))
         BishopProperties.≃-refl a0 a1 a2 a3))
    (BishopProperties.≃-trans (rootOfSquare roots BishopReal.0ℝ)
      (BishopProperties.nonNegx⇒∣x∣≃x BishopProperties.nonNeg0))

literalQuaternionAsVec4 : Quaternion.QuaternionB → Vec4B
literalQuaternionAsVec4 value =
  let vector = Quaternion.vector value
  in vec4B (Quaternion.scalar value) (Quaternion.x vector)
    (Quaternion.y vector) (Quaternion.z vector)

literalChordSqAsNormSq : ∀ left right →
  BishopReal._≃_ (Literal.chordSquared left right)
    (normSq4 (sub4 (literalQuaternionAsVec4 left) (literalQuaternionAsVec4 right)))
literalChordSqAsNormSq
    (Quaternion.quaternionB l0 (Quaternion.vec3B l1 l2 l3))
    (Quaternion.quaternionB r0 (Quaternion.vec3B r1 r2 r3)) =
  BishopProperties.≃-refl

literalChordDistance : BishopSquareRootCalculus →
  Quaternion.QuaternionB → Quaternion.QuaternionB → BishopReal.ℝ
literalChordDistance roots left right = root roots (Literal.chordSquared left right)

literalChordSquaredNonnegative :
  (roots : BishopSquareRootCalculus) → ∀ left right →
  BishopReal.NonNegative (Literal.chordSquared left right)
literalChordSquaredNonnegative roots left right =
  BishopProperties.0≤x⇒nonNegx
    (BishopProperties.≤-respʳ-≃
      (BishopProperties.≃-symm (literalChordSqAsNormSq left right))
      (BishopProperties.nonNegx⇒0≤x
        (normSq4Nonnegative roots
          (sub4 (literalQuaternionAsVec4 left) (literalQuaternionAsVec4 right)))))

literalChordDistanceTriangle :
  (roots : BishopSquareRootCalculus) → ∀ left middle right →
  BishopReal._≤_ (literalChordDistance roots left right)
    (BishopReal._+_ (literalChordDistance roots left middle)
      (literalChordDistance roots middle right))
literalChordDistanceTriangle roots left middle right =
  let
    identify : ∀ a b →
      BishopReal._≃_ (literalChordDistance roots a b)
        (chordDistance4 roots (literalQuaternionAsVec4 a) (literalQuaternionAsVec4 b))
    identify a b = rootCongruent roots (literalChordSqAsNormSq a b)
  in BishopProperties.≤-respʳ-≃
    (BishopProperties.≃-symm
      (BishopProperties.+-cong (identify left middle) (identify middle right)))
    (BishopProperties.≤-respˡ-≃ (identify left right)
      (chordDistanceTriangle4 roots (literalQuaternionAsVec4 left)
        (literalQuaternionAsVec4 middle) (literalQuaternionAsVec4 right)))

literalExponentialChordDistanceBelowRadius :
  (roots : BishopSquareRootCalculus) → ∀ {dataSet radius}
    (inputs : Concrete.ConcreteHalfBallSeriesInputs dataSet radius)
    (radiusCase : Positive.NonnegativeRadiusCase radius)
    (radial : Literal.PureQuaternionRadius radius) →
  BishopReal._≤_
    (literalChordDistance roots
      (Literal.literalPureQuaternionExponential inputs radiusCase radial)
      Literal.oneQuaternion)
    radius
literalExponentialChordDistanceBelowRadius roots inputs radiusCase radial =
  let
    exponential = Literal.literalPureQuaternionExponential inputs radiusCase radial
    rooted = rootMonotone roots
      (literalChordSquaredNonnegative roots exponential Literal.oneQuaternion)
      (Literal.literalExponentialSquaredChordBelowRadiusSquared inputs radiusCase radial)
    rootRadiusSquare = BishopProperties.≃-trans (rootOfSquare roots _)
      (BishopProperties.nonNegx⇒∣x∣≃x (Concrete.valueNonnegative inputs))
  in BishopProperties.≤-respʳ-≃ rootRadiusSquare rooted

p33BishopR4LagrangeIdentityLevel : ProofLevel
p33BishopR4LagrangeIdentityLevel = machineChecked
p33BishopR4MinkowskiLevel : ProofLevel
p33BishopR4MinkowskiLevel = machineChecked
p33BishopChordMetricTriangleLevel : ProofLevel
p33BishopChordMetricTriangleLevel = machineChecked
p33LiteralQuaternionChordDistanceBoundLevel : ProofLevel
p33LiteralQuaternionChordDistanceBoundLevel = machineChecked
bishopSquareRootConstructionLevel : ProofLevel
bishopSquareRootConstructionLevel = conditional
