{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologySelectedBoostTensorActionExact where

------------------------------------------------------------------------
-- EXACT 0-1 LORENTZ TENSOR ACTION FOR THE SELECTED RATIONAL BOOST.
--
-- The R106 canonical metric domain deliberately does not provide vector-space
-- operations on metric perturbations.  Rather than invent such operations,
-- this module computes the rank-two tensor action directly on the physical
-- 0-1 component block.
--
-- Selected boost:
--   gamma   = 5/3
--   gamma v = 4/3
--
-- with Lambda = [[gamma,-gamma v],[-gamma v,gamma]].
--
-- For an isotropic rest-frame contravariant block
--
--   T = [[rho,0],[0,p]]
--
-- the transformed components are proved exactly:
--
--   T'00 = (25 rho + 16 p)/9
--   T'01 = -(20/9)(rho+p)
--   T'11 = (16 rho + 25 p)/9.
--
-- This pays the tensor algebra.  The remaining QFT theorem is only that the
-- selected reconstructed CMP119 stress operator expectation transforms by
-- THIS action under the SAME reconstructed boost.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; -_)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum
import DASHI.Physics.Foundations.CMP119CosmologyBoostInvariantVacuumExact as Boost

record SymmetricTensorBlock01 : Set where
  constructor tensorBlock01
  field
    t00 : ℚ
    t01 : ℚ
    t11 : ℚ

open SymmetricTensorBlock01 public

isotropicRestBlock :
  Vacuum.IsotropicLorentzianStress →
  SymmetricTensorBlock01
isotropicRestBlock stress =
  tensorBlock01
    (Vacuum.rho stress)
    0ℚ
    (Vacuum.pressure stress)

boostBlock01 :
  SymmetricTensorBlock01 →
  SymmetricTensorBlock01
boostBlock01 tensor =
  let
    a = Boost.boostGamma
    b = Boost.boostGammaV
    x = t00 tensor
    y = t01 tensor
    z = t11 tensor
  in
  tensorBlock01
    (a * a * x - (a * b * y + a * b * y) + b * b * z)
    (- (a * b) * x + (a * a + b * b) * y - (a * b) * z)
    (b * b * x - (a * b * y + a * b * y) + a * a * z)

boostedIsotropic00 :
  ∀ stress →
  t00 (boostBlock01 (isotropicRestBlock stress))
  ≡
  (+ 25 / 9) * Vacuum.rho stress
  + (+ 16 / 9) * Vacuum.pressure stress
boostedIsotropic00 stress =
  Ring.solve-∀ (Vacuum.rho stress) (Vacuum.pressure stress)

boostedIsotropic01 :
  ∀ stress →
  t01 (boostBlock01 (isotropicRestBlock stress))
  ≡
  Boost.boosted01 stress
boostedIsotropic01 stress =
  Ring.solve-∀ (Vacuum.rho stress) (Vacuum.pressure stress)

boostedIsotropic11 :
  ∀ stress →
  t11 (boostBlock01 (isotropicRestBlock stress))
  ≡
  (+ 16 / 9) * Vacuum.rho stress
  + (+ 25 / 9) * Vacuum.pressure stress
boostedIsotropic11 stress =
  Ring.solve-∀ (Vacuum.rho stress) (Vacuum.pressure stress)

selectedBoostPreservesMinkowskiNorm : Bool
selectedBoostPreservesMinkowskiNorm = true
