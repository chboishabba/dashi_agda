{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.EUVOptics.TransferMatrixCompositionExact where

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Algebraic carrier for ordered 2x2 transfer-matrix composition.
--
-- A real EUV multilayer calculation ultimately needs complex amplitudes,
-- refractive indices and phase factors.  This finite Nat-valued owner does not
-- pretend to be that physics.  It owns the composition law and, importantly,
-- the fact that layer order is generally non-commutative.

record Matrix2 : Set where
  constructor matrix2
  field
    m11 m12 m21 m22 : Nat

open Matrix2 public

infixl 7 _⊗_
_⊗_ : Matrix2 → Matrix2 → Matrix2
A ⊗ B =
  matrix2
    (m11 A * m11 B + m12 A * m21 B)
    (m11 A * m12 B + m12 A * m22 B)
    (m21 A * m11 B + m22 A * m21 B)
    (m21 A * m12 B + m22 A * m22 B)

identityMatrix : Matrix2
identityMatrix = matrix2 1 0 0 1

leftIdentity11 : (A : Matrix2) → m11 (identityMatrix ⊗ A) ≡ m11 A
leftIdentity11 A = refl

leftIdentity12 : (A : Matrix2) → m12 (identityMatrix ⊗ A) ≡ m12 A
leftIdentity12 A = refl

-- Small executable witness that composition order matters.
layerA : Matrix2
layerA = matrix2 1 1 0 1

layerB : Matrix2
layerB = matrix2 1 0 1 1

AB : Matrix2
AB = layerA ⊗ layerB

BA : Matrix2
BA = layerB ⊗ layerA

AB11 : m11 AB ≡ 2
AB11 = refl

BA11 : m11 BA ≡ 1
BA11 = refl

data ⊥ : Set where

orderedCompositionNotCommutativeAt11 : m11 AB ≡ m11 BA → ⊥
orderedCompositionNotCommutativeAt11 ()

-- Physics firewall:
-- Matrix composition is only the algebraic skeleton.  Reflectivity still
-- requires a physical producer for each layer/interface matrix.
