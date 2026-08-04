module DASHI.Physics.Closure.NSTriadKNIntegerFourierModeAddExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Agda standard-library contributors; DASHI repository contributors.
-- Title: "Exact additive algebra of the periodic Z^3 Fourier-mode carrier".
-- DOI: not applicable to this repository adapter.
--
-- PURPOSE
-- Prove the additive group laws actually used by the periodic multiplier:
-- coordinate extensionality, left/right zero, commutativity, associativity and
-- inverse.  The laws are inherited componentwise from the standard-library
-- integer additive group and are no longer implicit facts about the record.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Properties as ℤₚ
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3

modeExt :
  ∀ {left right : Z3.FourierMode} →
  Z3.kx left ≡ Z3.kx right →
  Z3.ky left ≡ Z3.ky right →
  Z3.kz left ≡ Z3.kz right →
  left ≡ right
modeExt {Z3.mode lx ly lz} {Z3.mode rx ry rz}
  refl refl refl = refl

addZeroLeft :
  (mode : Z3.FourierMode) →
  Z3.addMode Z3.zeroMode mode ≡ mode
addZeroLeft (Z3.mode x y z) =
  modeExt
    (ℤₚ.+-identityˡ x)
    (ℤₚ.+-identityˡ y)
    (ℤₚ.+-identityˡ z)

addZeroRight :
  (mode : Z3.FourierMode) →
  Z3.addMode mode Z3.zeroMode ≡ mode
addZeroRight (Z3.mode x y z) =
  modeExt
    (ℤₚ.+-identityʳ x)
    (ℤₚ.+-identityʳ y)
    (ℤₚ.+-identityʳ z)

addCommutative :
  (left right : Z3.FourierMode) →
  Z3.addMode left right ≡ Z3.addMode right left
addCommutative
  (Z3.mode lx ly lz)
  (Z3.mode rx ry rz) =
  modeExt
    (ℤₚ.+-comm lx rx)
    (ℤₚ.+-comm ly ry)
    (ℤₚ.+-comm lz rz)

addAssociative :
  (first second third : Z3.FourierMode) →
  Z3.addMode (Z3.addMode first second) third
  ≡ Z3.addMode first (Z3.addMode second third)
addAssociative
  (Z3.mode ax ay az)
  (Z3.mode bx by bz)
  (Z3.mode cx cy cz) =
  modeExt
    (ℤₚ.+-assoc ax bx cx)
    (ℤₚ.+-assoc ay by cy)
    (ℤₚ.+-assoc az bz cz)

addNegateLeft :
  (mode : Z3.FourierMode) →
  Z3.addMode (Z3.negateMode mode) mode ≡ Z3.zeroMode
addNegateLeft (Z3.mode x y z) =
  modeExt
    (ℤₚ.+-inverseˡ x)
    (ℤₚ.+-inverseˡ y)
    (ℤₚ.+-inverseˡ z)

addNegateRight :
  (mode : Z3.FourierMode) →
  Z3.addMode mode (Z3.negateMode mode) ≡ Z3.zeroMode
addNegateRight (Z3.mode x y z) =
  modeExt
    (ℤₚ.+-inverseʳ x)
    (ℤₚ.+-inverseʳ y)
    (ℤₚ.+-inverseʳ z)

negateAdd :
  (left right : Z3.FourierMode) →
  Z3.negateMode (Z3.addMode left right)
  ≡ Z3.addMode (Z3.negateMode left) (Z3.negateMode right)
negateAdd
  (Z3.mode lx ly lz)
  (Z3.mode rx ry rz) =
  modeExt
    (ℤₚ.neg-distrib-+ lx rx)
    (ℤₚ.neg-distrib-+ ly ry)
    (ℤₚ.neg-distrib-+ lz rz)

integerFourierModeAdditiveGroupClosed : Bool
integerFourierModeAdditiveGroupClosed = true

integerFourierModeAdditiveGroupClosedIsTrue :
  integerFourierModeAdditiveGroupClosed ≡ true
integerFourierModeAdditiveGroupClosedIsTrue = refl
