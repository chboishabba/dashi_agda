module DASHI.Physics.Closure.NSTriadKNLuoFiniteJ11PrefixEnergyExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Derive the exact finite source-shaped estimate underlying the J11 prefix
-- calculation.  With lambda_r=2^r and
--
--   A_r = lambda_r^2 u_r,
--
-- the complete prefix satisfies
--
--   (sum_{r=0}^q A_r)^2
--     <= lambda_q sum_{r=0}^q lambda_r^4 u_r^2.
--
-- The lambda_q factor is obtained from the proved prefix-cardinality bound
-- q+1<=2^q, and the fourth power is obtained by ring normalization of A_r^2.
-- No J11 target inequality is accepted as a field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Sum
import DASHI.Physics.Closure.NSTriadKNLuoFinitePrefixJensenExact as Prefix

lambda : Nat → ℚ
lambda = Prefix.powTwo

lambdaSquared : Nat → ℚ
lambdaSquared shell = lambda shell * lambda shell

lambdaFourth : Nat → ℚ
lambdaFourth shell = lambdaSquared shell * lambdaSquared shell

j11Amplitude : (Nat → ℚ) → Nat → ℚ
j11Amplitude shellL2 shell = lambdaSquared shell * shellL2 shell

j11EnergyDensity : (Nat → ℚ) → Nat → ℚ
j11EnergyDensity shellL2 shell =
  lambdaFourth shell * L2.square (shellL2 shell)

j11AmplitudeSquareMeaning :
  (shellL2 : Nat → ℚ) →
  (shell : Nat) →
  L2.square (j11Amplitude shellL2 shell)
  ≡ j11EnergyDensity shellL2 shell
j11AmplitudeSquareMeaning shellL2 shell =
  solve (lambda shell ∷ shellL2 shell ∷ [])

sumToCong :
  (left right : Nat → ℚ) →
  (cutoff : Nat) →
  ((index : Nat) → left index ≡ right index) →
  Sum.sumTo left cutoff ≡ Sum.sumTo right cutoff
sumToCong left right zero pointwise = pointwise zero
sumToCong left right (suc cutoff) pointwise
  rewrite pointwise (suc cutoff)
        | sumToCong left right cutoff pointwise = refl

j11SquareSumMeaning :
  (shellL2 : Nat → ℚ) →
  (cutoff : Nat) →
  Sum.sumTo
    (λ shell → L2.square (j11Amplitude shellL2 shell))
    cutoff
  ≡ Sum.sumTo (j11EnergyDensity shellL2) cutoff
j11SquareSumMeaning shellL2 cutoff =
  sumToCong
    (λ shell → L2.square (j11Amplitude shellL2 shell))
    (j11EnergyDensity shellL2)
    cutoff
    (j11AmplitudeSquareMeaning shellL2)

finiteJ11PrefixEnergyBound :
  (shellL2 : Nat → ℚ) →
  (outputShell : Nat) →
  L2.square
    (Sum.sumTo (j11Amplitude shellL2) outputShell)
  ≤ lambda outputShell
      * Sum.sumTo (j11EnergyDensity shellL2) outputShell
finiteJ11PrefixEnergyBound shellL2 outputShell =
  subst
    (λ squareSum →
      L2.square
        (Sum.sumTo (j11Amplitude shellL2) outputShell)
      ≤ lambda outputShell * squareSum)
    (j11SquareSumMeaning shellL2 outputShell)
    (Prefix.finiteDyadicPrefixJensen
      (j11Amplitude shellL2)
      outputShell)

finiteJ11PrefixEnergyBoundClosed : Bool
finiteJ11PrefixEnergyBoundClosed = true

finiteJ11PrefixEnergyBoundClosedIsTrue :
  finiteJ11PrefixEnergyBoundClosed ≡ true
finiteJ11PrefixEnergyBoundClosedIsTrue = refl
