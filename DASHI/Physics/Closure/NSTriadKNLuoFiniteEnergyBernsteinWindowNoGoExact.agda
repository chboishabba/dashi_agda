module DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyBernsteinWindowNoGoExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Repository-original scale audit; no separate DOI is assigned.
--
-- PURPOSE
-- Test the direct energy-class route after the commutator has removed the
-- output derivative.  In three dimensions the low-frequency Bernstein step
-- has the schematic cost
--
--   ||grad u_{<q}||_infinity <= lambda_q^(3/2) ||grad u||_2.
--
-- Cauchy--Schwarz on a parabolic interval of length lambda_q^-2 supplies only
-- lambda_q^-1.  The route therefore leaves lambda_q^(1/2), which grows rather
-- than decays.
--
-- To avoid irrational exponents the exact theorem is stated on even shells
-- q=2n:
--
--   lambda_{2n}^{3/2} * lambda_{2n}^-1 = lambda_n.
--
-- Thus the commutator-plus-energy argument still needs another half-frequency
-- gain, a critical spatial norm, or stronger structure.  This is an arithmetic
-- no-go, not a claim about a particular solution.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq using (cong; sym)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNLuoFiniteEnergyCriticalScalingGapExact as Scale
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowHalfKernelExact as Near
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowScalingObstructionExact as Obstruction

-- lambda_(2n)^(3/2) = 2^(3n) is represented as
-- lambda_n * lambda_(2n), avoiding a fractional power operation.
lowGradientBernsteinEven : Nat → ℚ
lowGradientBernsteinEven n =
  Scale.dyadicScale n * Scale.dyadicScale (n + n)

parabolicCauchySchwarzEven : Nat → ℚ
parabolicCauchySchwarzEven n =
  Near.windowRoot (n + n)

energyClassResidual : Nat → ℚ
energyClassResidual n =
  lowGradientBernsteinEven n * parabolicCauchySchwarzEven n

energyClassResidualIsHalfFrequency :
  (n : Nat) →
  energyClassResidual n ≡ Scale.dyadicScale n
energyClassResidualIsHalfFrequency n =
  begin
    energyClassResidual n
  ≡⟨ solve
       ( Scale.dyadicScale n
       ∷ Scale.dyadicScale (n + n)
       ∷ Near.windowRoot (n + n)
       ∷ []) ⟩
    Scale.dyadicScale n
      * (Near.windowRoot (n + n) * Scale.dyadicScale (n + n))
  ≡⟨ cong
       (Scale.dyadicScale n *_)
       (Obstruction.reciprocalDyadicIdentity (n + n)) ⟩
    Scale.dyadicScale n * 1ℚ
  ≡⟨ solve (Scale.dyadicScale n ∷ []) ⟩
    Scale.dyadicScale n
  ∎

energyClassResidualDoubles :
  (n : Nat) →
  energyClassResidual (suc n)
  ≡ Scale.two * energyClassResidual n
energyClassResidualDoubles n =
  begin
    energyClassResidual (suc n)
  ≡⟨ energyClassResidualIsHalfFrequency (suc n) ⟩
    Scale.dyadicScale (suc n)
  ≡⟨ Scale.dyadicScaleSuccessor n ⟩
    Scale.two * Scale.dyadicScale n
  ≡⟨ cong
       (Scale.two *_)
       (Eq.sym (energyClassResidualIsHalfFrequency n)) ⟩
    Scale.two * energyClassResidual n
  ∎
