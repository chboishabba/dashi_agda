{-# OPTIONS --safe #-}
module DASHI.Mathematics.Arithmetic.EllipticDyadicHenselSquareStepAlgebraExact where

------------------------------------------------------------------------
-- BSD K1 original E : y^2 = x^3 - x, actual dyadic x=39.
--
-- The local point exists because
--   39*38*40 = 16*3705, 3705 = 1+8*463.
-- Every 2-adic unit 1 mod 8 has a square root in Z2.
--
-- The exact algebra behind a coherent constructive Hensel lift is
--   (r + h*b)^2 = r^2 + 2*r*h*b + h^2*b^2.
-- With h=2^(n-1), n>=3, b in {0,1}, the last term vanishes
-- modulo 2^(n+1); r odd and b chosen to cancel the nth digit
-- ensures r_(n+1)^2=3705 mod 2^(n+1).
--
-- THIS FILE PAYS the unpostulated ring identity and literal
-- x=39 arithmetic on original Agda integers. It does not build
-- the complete Q2 carrier, a Cauchy limit, the actual local
-- Kummer/H1 image or Sha; these remain separate K1/K2 gates.
-- Script: scripts/check_bsd_q2_39_coherent_hensel.py.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _+_; _*_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

module RingZ = NR IntRS.ring
open RingZ using (Κ; _⊕_; _⊗_; solve)

thirtyNineCubicRHS :
  ((+ 39) * (+ 38)) * (+ 40)
    ≡ (+ 16) * (+ 3705)
thirtyNineCubicRHS = refl

unit3705OneModuloEight :
  (+ 3705) ≡ (+ 1) + ((+ 8) * (+ 463))
unit3705OneModuloEight = refl

thirtyEightHasSingleTwoFactor :
  (+ 38) ≡ (+ 2) * (+ 19)
thirtyEightHasSingleTwoFactor = refl

henselSquareStepRing :
  (r h b : ℤ) →
  (r + (h * b)) * (r + (h * b))
  ≡
  (r * r) + (((+ 2) * r) * (h * b)) + ((h * h) * (b * b))
henselSquareStepRing r h b =
  RingZ.solve 3
    (λ r h b →
      (((r ⊕ (h ⊗ b)) ⊗ (r ⊕ (h ⊗ b))) ,
       ((r ⊗ r)
        ⊕ (((Κ (+ 2) ⊗ r) ⊗ (h ⊗ b))
          ⊕ ((h ⊗ h) ⊗ (b ⊗ b))))))
    refl r h b
