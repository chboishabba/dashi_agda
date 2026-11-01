module DASHI.Physics.Closure.NSTriadKNChongPerryCantwellQRNormalizationRound79Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: M. S. Chong; A. E. Perry; B. J. Cantwell.
-- Title: "A general classification of three-dimensional flow fields".
-- Physics of Fluids A 2 (1990), 765--777.
-- DOI: 10.1063/1.857730.
--
-- Author: P. Vieillefosse.
-- Title: "Local interaction between vorticity and shear in a perfect
-- incompressible fluid".
-- DOI: 10.1051/jphys:01982004306083700.
--
-- Author: Brian J. Cantwell.
-- Title: "Exact solution of a restricted Euler equation for the velocity
-- gradient tensor".
-- DOI: 10.1063/1.858295.
--
-- ROUND79 / Q-R NORMALIZATION WELD
--
-- Round78 used the polynomial Vieillefosse first integral
--
--   V(Q,R) = 4 Q^3 + 27 R^2.
--
-- The standard Chong--Perry--Cantwell topology discriminant is often written
--
--   D(Q,R) = Q^3 + (27/4) R^2.
--
-- These are exactly the same zero/sign locus after positive scaling:
--
--   V = 4 D.
--
-- This file records that normalization identity so the restricted-Euler lane
-- and the Q-R topology literature cannot be mistaken for different invariants.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

four twentySeven oneQuarter twentySevenQuarters : ℚ
four = Int.+ 4 / 1
twentySeven = Int.+ 27 / 1
oneQuarter = Int.+ 1 / 4
twentySevenQuarters = Int.+ 27 / 4

cube : ℚ → ℚ
cube x = x * x * x

chongPerryCantwellDiscriminant : ℚ → ℚ → ℚ
chongPerryCantwellDiscriminant Q R =
  cube Q + twentySevenQuarters * R * R

vieillefossePolynomial : ℚ → ℚ → ℚ
vieillefossePolynomial Q R =
  four * cube Q + twentySeven * R * R

vieillefosseEqualsFourTimesCPCDiscriminant :
  ∀ Q R →
  vieillefossePolynomial Q R
  ≡ four * chongPerryCantwellDiscriminant Q R
vieillefosseEqualsFourTimesCPCDiscriminant Q R =
  solve (Q ∷ R ∷ [])

round79VieillefosseAndCPCUseSameQRDiscriminantLocus : Bool
round79VieillefosseAndCPCUseSameQRDiscriminantLocus = true

round79VieillefosseAndCPCUseSameQRDiscriminantLocusIsTrue :
  round79VieillefosseAndCPCUseSameQRDiscriminantLocus ≡ true
round79VieillefosseAndCPCUseSameQRDiscriminantLocusIsTrue = refl
