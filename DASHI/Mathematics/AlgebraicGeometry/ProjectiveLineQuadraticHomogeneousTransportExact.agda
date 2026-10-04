module DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineQuadraticHomogeneousTransportExact where

------------------------------------------------------------------------
-- A NONTRIVIAL ALGEBRAIC COORDINATE OPERATOR ON LITERAL P^1 PRESENTATIONS
--
-- On the actual homogeneous pair (z0,z1), define the degree-two map
--
--               [z0:z1] |-> [z0*z0 : z1*z1].
--
-- The source `ComplexFieldPresentation` comes with nonzero preservation,
-- associativity, and commutativity. We use these to prove:
--
-- 1. a nonzero homogeneous input remains nonzero;
-- 2. if two inputs differ by a projective rescaling s, their images
--    differ by the nonzero rescaling s*s;
-- 3. the polynomial identity (s*z)^2 = s^2*z^2 used in the transport.
--
-- This is a genuine degree-two HOMOGENEOUS POLYNOMIAL on the existing
-- literal projective coordinate object, not a toy nine-cell relabelling.
--
-- It does not construct a scheme morphism, its graph cycle in a Chow
-- group, an induced map on singular cohomology, or the degree-two
-- pullback formula there. These are distinct geometric obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHomogeneousCoordinatesExact as CP
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineHomogeneousPairExact as P1
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineChartOverlapExact as Overlap

------------------------------------------------------------------------
-- Field-law calculation: coordinatewise polynomial equivariance.
------------------------------------------------------------------------

squareScaling :
  ∀ {field}
    (laws : Overlap.ProjectiveOverlapFieldLaws field)
    (s z : CP.Complex field) →
  CP.multiply field
    (CP.multiply field s z)
    (CP.multiply field s z)
  ≡
  CP.multiply field
    (CP.multiply field s s)
    (CP.multiply field z z)
squareScaling {field} laws s z =
  trans
    (sym
      (CP.multiplyAssociative (Overlap.base laws)
        s z (CP.multiply field s z)))
    (trans
      (cong
        (CP.multiply field s)
        (sym (CP.multiplyAssociative (Overlap.base laws) z s z)))
      (trans
        (cong
          (CP.multiply field s)
          (cong
            (λ x → CP.multiply field x z)
            (Overlap.multiplyCommutative laws z s)))
        (trans
          (cong
            (CP.multiply field s)
            (sym (CP.multiplyAssociative (Overlap.base laws) s z z)))
          (CP.multiplyAssociative (Overlap.base laws)
            s s (CP.multiply field z z)))))

------------------------------------------------------------------------
-- The input is the LITERAL nonzero projective-line homogeneous pair.
------------------------------------------------------------------------

squarePair :
  ∀ {field : CP.ComplexFieldPresentation}
    (laws : Overlap.ProjectiveOverlapFieldLaws field) →
  P1.HomogeneousPair field →
  P1.HomogeneousPair field
squarePair {field} laws pair =
  P1.homogeneous-pair
    (CP.multiply field (P1.first pair) (P1.first pair))
    (CP.multiply field (P1.second pair) (P1.second pair))
    (nonzeroSquare (P1.notBothZero pair))
  where
    nonzeroSquare :
      ∀ {z0 z1} →
      CP.ContainsNonzero field (z0 ∷ z1 ∷ []) →
      CP.ContainsNonzero field
        ((CP.multiply field z0 z0)
          ∷ (CP.multiply field z1 z1) ∷ [])
    nonzeroSquare (CP.hereNonzero nz) =
      CP.hereNonzero
        (CP.multiplyNonzero (Overlap.base laws) nz nz)
    nonzeroSquare (CP.thereNonzero (CP.hereNonzero nz)) =
      CP.thereNonzero
        (CP.hereNonzero
          (CP.multiplyNonzero (Overlap.base laws) nz nz))
    nonzeroSquare (CP.thereNonzero
      (CP.thereNonzero ()))

------------------------------------------------------------------------
-- Extract two component equations from existing actual projective
-- rescaling of the length-two homogeneous coordinate lists.
------------------------------------------------------------------------

listHead :
  ∀ {A : Set} → A → List A → A
listHead default [] = default
listHead default (x ∷ xs) = x

listSecond :
  ∀ {A : Set} → A → List A → A
listSecond default [] = default
listSecond default (x ∷ []) = default
listSecond default (x ∷ y ∷ xs) = y

rescalingFirst :
  ∀ {field : CP.ComplexFieldPresentation}
    {left right : P1.HomogeneousPair field}
    (rescale :
      CP.ProjectiveRescaling
        (P1.pairToHomogeneousLine left)
        (P1.pairToHomogeneousLine right)) →
  P1.first right ≡
    CP.multiply field (CP.scalar rescale) (P1.first left)
rescalingFirst {field} rescale =
  cong
    (listHead (CP.zero field))
    (CP.coordinatewiseRescaling rescale)

rescalingSecond :
  ∀ {field : CP.ComplexFieldPresentation}
    {left right : P1.HomogeneousPair field}
    (rescale :
      CP.ProjectiveRescaling
        (P1.pairToHomogeneousLine left)
        (P1.pairToHomogeneousLine right)) →
  P1.second right ≡
    CP.multiply field (CP.scalar rescale) (P1.second left)
rescalingSecond {field} rescale =
  cong
    (listSecond (CP.zero field))
    (CP.coordinatewiseRescaling rescale)

------------------------------------------------------------------------
-- SAME-OBJECT GLUING: the squared homogeneous presentations remain
-- equivalent, with explicit transport multiplier s^2.
------------------------------------------------------------------------

squarePairRespectsProjectiveRescaling :
  ∀ {field : CP.ComplexFieldPresentation}
    (laws : Overlap.ProjectiveOverlapFieldLaws field)
    {left right : P1.HomogeneousPair field} →
  (rescale :
    CP.ProjectiveRescaling
      (P1.pairToHomogeneousLine left)
      (P1.pairToHomogeneousLine right)) →
  CP.ProjectiveRescaling
    (P1.pairToHomogeneousLine (squarePair laws left))
    (P1.pairToHomogeneousLine (squarePair laws right))
squarePairRespectsProjectiveRescaling
    {field} laws {left} {right} rescale =
  record
    { CP.scalar = CP.multiply field s s
    ; CP.scalarNonzero =
        CP.multiplyNonzero (Overlap.base laws)
          (CP.scalarNonzero rescale)
          (CP.scalarNonzero rescale)
    ; CP.coordinatewiseRescaling =
        cong₂ _∷_
          firstSquared
          (cong₂ _∷_ secondSquared refl)
    }
  where
    s : CP.Complex field
    s = CP.scalar rescale

    firstSquared :
      CP.multiply field (P1.first right) (P1.first right)
      ≡
      CP.multiply field
        (CP.multiply field s s)
        (CP.multiply field (P1.first left) (P1.first left))
    firstSquared =
      trans
        (cong₂ (CP.multiply field)
          (rescalingFirst rescale)
          (rescalingFirst rescale))
        (squareScaling laws s (P1.first left))

    secondSquared :
      CP.multiply field (P1.second right) (P1.second right)
      ≡
      CP.multiply field
        (CP.multiply field s s)
        (CP.multiply field (P1.second left) (P1.second left))
    secondSquared =
      trans
        (cong₂ (CP.multiply field)
          (rescalingSecond rescale)
          (rescalingSecond rescale))
        (squareScaling laws s (P1.second left))

------------------------------------------------------------------------
-- The next actual Hodge calculation must construct this morphism on the
-- quotient variety, obtain its graph in CH^1(P^1 x P^1), and show its
-- cohomological pullback multiplies the point class by TWO. That is a
-- geometric cycle-class theorem; equivariance alone is not such a proof.
------------------------------------------------------------------------
