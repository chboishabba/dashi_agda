module DASHI.Physics.Closure.NSTriadKNLuoFiniteParityMatchedNonlinearityExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Qixiang Yang.
-- Title: "Symmetry and Rigidity: Only One Kind of Symmetry Allow Non-Zero
-- Real Symmetric Solution".
-- arXiv:2002.12828v2 (2020).
-- DOI: none assigned in the cited preprint version.
--
-- Source audit: arXiv:2002.12828 is the Yang symmetry paper supplied with
-- this tranche.  It is not the Kato--Ponce commutator paper; Yang cites that
-- paper as reference [11].  The Kato--Ponce DOI is recorded in the dedicated
-- commutator modules.
--
-- PURPOSE
-- Formalise the parity-signature algebra used in Yang's Sections 2--4.
-- Product and convolution signatures add in (Z/2Z)^3, one derivative adds the
-- corresponding coordinate signature, and a solenoidal component pattern
--
--   parity(u_i) = e_i + alpha
--
-- has derivative parity alpha for every component.  For two such patterns the
-- doubly differentiated quadratic term has parity alpha + beta independently
-- of the component indices.  This is the finite algebra behind matched
-- symmetric nonlinear sectors; it is not promoted to an arbitrary-data
-- regularity theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

data Bit : Set where
  b0 b1 : Bit

infixl 6 _⊕_
_⊕_ : Bit → Bit → Bit
b0 ⊕ right = right
b1 ⊕ b0 = b1
b1 ⊕ b1 = b0

xorCommutative : (left right : Bit) → left ⊕ right ≡ right ⊕ left
xorCommutative b0 b0 = refl
xorCommutative b0 b1 = refl
xorCommutative b1 b0 = refl
xorCommutative b1 b1 = refl

xorAssociative :
  (first second third : Bit) →
  (first ⊕ second) ⊕ third ≡ first ⊕ (second ⊕ third)
xorAssociative b0 b0 b0 = refl
xorAssociative b0 b0 b1 = refl
xorAssociative b0 b1 b0 = refl
xorAssociative b0 b1 b1 = refl
xorAssociative b1 b0 b0 = refl
xorAssociative b1 b0 b1 = refl
xorAssociative b1 b1 b0 = refl
xorAssociative b1 b1 b1 = refl

xorSelf : (value : Bit) → value ⊕ value ≡ b0
xorSelf b0 = refl
xorSelf b1 = refl

cancelSandwich :
  (axis base : Bit) →
  (axis ⊕ base) ⊕ axis ≡ base
cancelSandwich b0 b0 = refl
cancelSandwich b0 b1 = refl
cancelSandwich b1 b0 = refl
cancelSandwich b1 b1 = refl

fourXorCancel :
  (axisI axisJ alpha beta : Bit) →
  (((axisI ⊕ alpha) ⊕ (axisJ ⊕ beta)) ⊕ axisJ) ⊕ axisI
  ≡ alpha ⊕ beta
fourXorCancel b0 b0 b0 b0 = refl
fourXorCancel b0 b0 b0 b1 = refl
fourXorCancel b0 b0 b1 b0 = refl
fourXorCancel b0 b0 b1 b1 = refl
fourXorCancel b0 b1 b0 b0 = refl
fourXorCancel b0 b1 b0 b1 = refl
fourXorCancel b0 b1 b1 b0 = refl
fourXorCancel b0 b1 b1 b1 = refl
fourXorCancel b1 b0 b0 b0 = refl
fourXorCancel b1 b0 b0 b1 = refl
fourXorCancel b1 b0 b1 b0 = refl
fourXorCancel b1 b0 b1 b1 = refl
fourXorCancel b1 b1 b0 b0 = refl
fourXorCancel b1 b1 b0 b1 = refl
fourXorCancel b1 b1 b1 b0 = refl
fourXorCancel b1 b1 b1 b1 = refl

record Parity3 : Set where
  constructor parity3
  field
    px py pz : Bit

open Parity3 public

parityExt :
  ∀ {left right : Parity3} →
  px left ≡ px right →
  py left ≡ py right →
  pz left ≡ pz right →
  left ≡ right
parityExt {parity3 lx ly lz} {parity3 .lx .ly .lz} refl refl refl = refl

infixl 6 _⊕₃_
_⊕₃_ : Parity3 → Parity3 → Parity3
parity3 ax ay az ⊕₃ parity3 bx by bz =
  parity3 (ax ⊕ bx) (ay ⊕ by) (az ⊕ bz)

zeroParity : Parity3
zeroParity = parity3 b0 b0 b0

axis1 axis2 axis3 : Parity3
axis1 = parity3 b1 b0 b0
axis2 = parity3 b0 b1 b0
axis3 = parity3 b0 b0 b1

productParity : Parity3 → Parity3 → Parity3
productParity = _⊕₃_

derivativeParity : Parity3 → Parity3 → Parity3
derivativeParity axis signature = signature ⊕₃ axis

solenoidalComponentParity : Parity3 → Parity3 → Parity3
solenoidalComponentParity axis base = axis ⊕₃ base

componentDerivativeReturnsBase :
  (axis base : Parity3) →
  derivativeParity axis (solenoidalComponentParity axis base)
  ≡ base
componentDerivativeReturnsBase
  (parity3 ix iy iz) (parity3 ax ay az) =
  parityExt
    (cancelSandwich ix ax)
    (cancelSandwich iy ay)
    (cancelSandwich iz az)

quadraticDifferentiatedParity :
  Parity3 → Parity3 → Parity3 → Parity3 → Parity3
quadraticDifferentiatedParity axisI axisJ alpha beta =
  derivativeParity axisI
    (derivativeParity axisJ
      (productParity
        (solenoidalComponentParity axisI alpha)
        (solenoidalComponentParity axisJ beta)))

quadraticParityIndependentOfComponentIndices :
  (axisI axisJ alpha beta : Parity3) →
  quadraticDifferentiatedParity axisI axisJ alpha beta
  ≡ alpha ⊕₃ beta
quadraticParityIndependentOfComponentIndices
  (parity3 ix iy iz)
  (parity3 jx jy jz)
  (parity3 ax ay az)
  (parity3 bx by bz) =
  parityExt
    (fourXorCancel ix jx ax bx)
    (fourXorCancel iy jy ay by)
    (fourXorCancel iz jz az bz)

matchedNonlinearParity :
  (axisI axisJ firstLeft firstRight secondLeft secondRight : Parity3) →
  firstLeft ⊕₃ firstRight ≡ secondLeft ⊕₃ secondRight →
  quadraticDifferentiatedParity axisI axisJ firstLeft firstRight
  ≡ quadraticDifferentiatedParity axisI axisJ secondLeft secondRight
matchedNonlinearParity
  axisI axisJ firstLeft firstRight secondLeft secondRight matched =
  trans
    (quadraticParityIndependentOfComponentIndices
      axisI axisJ firstLeft firstRight)
    (trans
      matched
      (sym
        (quadraticParityIndependentOfComponentIndices
          axisI axisJ secondLeft secondRight)))
