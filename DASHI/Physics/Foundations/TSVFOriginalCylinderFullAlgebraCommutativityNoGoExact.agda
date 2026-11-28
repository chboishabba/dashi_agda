{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOriginalCylinderFullAlgebraCommutativityNoGoExact where

------------------------------------------------------------------------
-- HIL01/HIL07 original-source algebraic no-go:
--
-- A globally multiplicative image of a COMMUTATIVE cylinder algebra
-- lands in a COMMUTATIVE operator subalgebra. It cannot, without
-- restricting its domain or dropping multiplicativity, surject onto
-- an operator algebra with a genuinely noncommuting pair.
--
-- This is the exact scope boundary of the original TSVF M2a
-- cylinderOperator(f*g) = cylinderOperator(f) compose cylinderOperator(g).
--
-- For the true continuum OS GNS algebra, select the admissible
-- positive-time *commutative cylinder sector* separately from the
-- full noncommutative real-time observer algebra. Claiming an
-- isomorphism onto the full algebra from M2a alone would be false.
--
-- Agda --safe, no postulates, generic algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Data.Empty using (⊥)

module _
    {Cylinder Operator : Set}
    (multiplyCylinder : Cylinder → Cylinder → Cylinder)
    (composeOperator : Operator → Operator → Operator)
    (compile : Cylinder → Operator)
    (cylinderProductsCommute : ∀ f g →
      multiplyCylinder f g ≡ multiplyCylinder g f)
    (compilePreservesMultiplication : ∀ f g →
      compile (multiplyCylinder f g) ≡
        composeOperator (compile f) (compile g))
  where

  originalCylinderImagesAlwaysCommute :
    ∀ f g →
    composeOperator (compile f) (compile g) ≡
      composeOperator (compile g) (compile f)
  originalCylinderImagesAlwaysCommute f g =
    trans
      (sym (compilePreservesMultiplication f g))
      (trans
        (cong compile
          (cylinderProductsCommute f g))
        (compilePreservesMultiplication g f))

  aNoncommutingPairInTheImageIsImpossible :
    ∀ f g →
    (composeOperator (compile f) (compile g)
      ≡ composeOperator (compile g) (compile f) → ⊥) →
    ⊥
  aNoncommutingPairInTheImageIsImpossible f g noncommuting =
    noncommuting (originalCylinderImagesAlwaysCommute f g)

module _
    {Cylinder Operator : Set}
    (multiplyCylinder : Cylinder → Cylinder → Cylinder)
    (composeOperator : Operator → Operator → Operator)
    (compile : Cylinder → Operator)
    (cylinderProductsCommute : ∀ f g →
      multiplyCylinder f g ≡ multiplyCylinder g f)
    (compilePreservesMultiplication : ∀ f g →
      compile (multiplyCylinder f g) ≡
        composeOperator (compile f) (compile g))
    (selectedLift : Operator → Cylinder)
    (liftIsRightInverse : ∀ op →
      compile (selectedLift op) ≡ op)
  where

  -- Under a selected right-inverse to compile, even the ENTIRE
  -- operator algebra is forced commutative. The genuine
  -- proposition is the explicit right-inverse.
  noFullNoncommutativeOntoCylinderOperatorRepresentation :
    ∀ left right →
    composeOperator left right ≡ composeOperator right left
  noFullNoncommutativeOntoCylinderOperatorRepresentation left right =
    let
      f = selectedLift left
      g = selectedLift right
      forward =
        originalCylinderImagesAlwaysCommute
          multiplyCylinder composeOperator compile
          cylinderProductsCommute compilePreservesMultiplication f g
    in
    trans
      (sym (cong₂ composeOperator
        (liftIsRightInverse left) (liftIsRightInverse right)))
      (trans forward
        (cong₂ composeOperator
          (liftIsRightInverse right) (liftIsRightInverse left)))

-- No physical GNS/OS unitary follows from a commutative cylinder
-- subalgebra without a density/generation and continuity theorem.
