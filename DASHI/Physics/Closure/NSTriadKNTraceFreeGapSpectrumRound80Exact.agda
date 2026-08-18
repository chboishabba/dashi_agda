module DASHI.Physics.Closure.NSTriadKNTraceFreeGapSpectrumRound80Exact where

------------------------------------------------------------------------
-- ROUND80 / 3D TRACE-FREE SPECTRAL GAP COORDINATES
--
-- For a three-dimensional incompressible strain spectrum, let
--
--   a = lambda1 - lambda2,
--   b = lambda2 - lambda3,
--   tau = lambda1 + lambda2 + lambda3.
--
-- Direct algebra gives the division-free reconstruction identities
--
--   3 lambda1 = 2a + b + tau,
--   3 lambda2 = b - a + tau,
--   3 lambda3 = tau - a - 2b.
--
-- On the physical trace-free carrier tau=0.  This is the key Round80 fork:
-- if one adjacent gap collapses while the other remains separated, use the
-- corresponding two-dimensional spectral-cluster projector; if both gaps are
-- small, then every strain eigenvalue is small in the exact scaled sense above,
-- so the stretching operator itself is entering a small-spectrum regime rather
-- than requiring a uniformly defined individual eigenframe.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

record ThreeSpectrum : Set where
  constructor three-spectrum
  field
    lambda1 lambda2 lambda3 : ℚ

open ThreeSpectrum public

traceDefect : ThreeSpectrum → ℚ
traceDefect spectrum =
  lambda1 spectrum + lambda2 spectrum + lambda3 spectrum

gap12 : ThreeSpectrum → ℚ
gap12 spectrum = lambda1 spectrum - lambda2 spectrum

gap23 : ThreeSpectrum → ℚ
gap23 spectrum = lambda2 spectrum - lambda3 spectrum

two : ℚ
two = 1ℚ + 1ℚ

three : ℚ
three = two + 1ℚ

lambda1GapTraceIdentity :
  (spectrum : ThreeSpectrum) →
  three * lambda1 spectrum
  ≡ two * gap12 spectrum + gap23 spectrum + traceDefect spectrum
lambda1GapTraceIdentity (three-spectrum l1 l2 l3) =
  solve (l1 ∷ l2 ∷ l3 ∷ [])

lambda2GapTraceIdentity :
  (spectrum : ThreeSpectrum) →
  three * lambda2 spectrum
  ≡ gap23 spectrum - gap12 spectrum + traceDefect spectrum
lambda2GapTraceIdentity (three-spectrum l1 l2 l3) =
  solve (l1 ∷ l2 ∷ l3 ∷ [])

lambda3GapTraceIdentity :
  (spectrum : ThreeSpectrum) →
  three * lambda3 spectrum
  ≡ traceDefect spectrum - gap12 spectrum - two * gap23 spectrum
lambda3GapTraceIdentity (three-spectrum l1 l2 l3) =
  solve (l1 ∷ l2 ∷ l3 ∷ [])

record TraceFreeThreeSpectrum : Set where
  constructor trace-free-three-spectrum
  field
    spectrum : ThreeSpectrum
    traceZero : traceDefect spectrum ≡ 0ℚ

open TraceFreeThreeSpectrum public

traceFreeLambda1FromGaps :
  (data : TraceFreeThreeSpectrum) →
  three * lambda1 (spectrum data)
  ≡ two * gap12 (spectrum data) + gap23 (spectrum data)
traceFreeLambda1FromGaps data =
  subst
    (λ tau →
      three * lambda1 (spectrum data)
      ≡ two * gap12 (spectrum data) + gap23 (spectrum data) + tau)
    (traceZero data)
    (lambda1GapTraceIdentity (spectrum data))

traceFreeLambda2FromGaps :
  (data : TraceFreeThreeSpectrum) →
  three * lambda2 (spectrum data)
  ≡ gap23 (spectrum data) - gap12 (spectrum data)
traceFreeLambda2FromGaps data =
  subst
    (λ tau →
      three * lambda2 (spectrum data)
      ≡ gap23 (spectrum data) - gap12 (spectrum data) + tau)
    (traceZero data)
    (lambda2GapTraceIdentity (spectrum data))

traceFreeLambda3FromGaps :
  (data : TraceFreeThreeSpectrum) →
  three * lambda3 (spectrum data)
  ≡ 0ℚ - gap12 (spectrum data) - two * gap23 (spectrum data)
traceFreeLambda3FromGaps data =
  subst
    (λ tau →
      three * lambda3 (spectrum data)
      ≡ tau - gap12 (spectrum data) - two * gap23 (spectrum data))
    (traceZero data)
    (lambda3GapTraceIdentity (spectrum data))

bothAdjacentGapsZeroForceScaledSpectrumZero :
  (data : TraceFreeThreeSpectrum) →
  gap12 (spectrum data) ≡ 0ℚ →
  gap23 (spectrum data) ≡ 0ℚ →
  (three * lambda1 (spectrum data) ≡ 0ℚ)
  × (three * lambda2 (spectrum data) ≡ 0ℚ)
  × (three * lambda3 (spectrum data) ≡ 0ℚ)
bothAdjacentGapsZeroForceScaledSpectrumZero data gap12Zero gap23Zero =
  first , second , third
  where
  first : three * lambda1 (spectrum data) ≡ 0ℚ
  first =
    subst
      (λ a → three * lambda1 (spectrum data) ≡ two * a + 0ℚ)
      (sym gap12Zero)
      (subst
        (λ b → three * lambda1 (spectrum data) ≡ two * gap12 (spectrum data) + b)
        (sym gap23Zero)
        (traceFreeLambda1FromGaps data))

  second : three * lambda2 (spectrum data) ≡ 0ℚ
  second =
    subst
      (λ a → three * lambda2 (spectrum data) ≡ 0ℚ - a)
      (sym gap12Zero)
      (subst
        (λ b → three * lambda2 (spectrum data) ≡ b - gap12 (spectrum data))
        (sym gap23Zero)
        (traceFreeLambda2FromGaps data))

  third : three * lambda3 (spectrum data) ≡ 0ℚ
  third =
    subst
      (λ a → three * lambda3 (spectrum data) ≡ 0ℚ - a - two * 0ℚ)
      (sym gap12Zero)
      (subst
        (λ b → three * lambda3 (spectrum data) ≡ 0ℚ - gap12 (spectrum data) - two * b)
        (sym gap23Zero)
        (traceFreeLambda3FromGaps data))

round80AdjacentGapsDetermineTraceFreeSpectrumScaled : Bool
round80AdjacentGapsDetermineTraceFreeSpectrumScaled = true

round80BothGapsCollapseImpliesWholeStrainSpectrumCollapsesScaled : Bool
round80BothGapsCollapseImpliesWholeStrainSpectrumCollapsesScaled = true

round80AdjacentGapsDetermineTraceFreeSpectrumScaledIsTrue :
  round80AdjacentGapsDetermineTraceFreeSpectrumScaled ≡ true
round80AdjacentGapsDetermineTraceFreeSpectrumScaledIsTrue = refl
