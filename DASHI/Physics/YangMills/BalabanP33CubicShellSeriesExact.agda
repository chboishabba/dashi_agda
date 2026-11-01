module DASHI.Physics.YangMills.BalabanP33CubicShellSeriesExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Leonhard Euler,
-- the Eulerian-polynomial generating-function identity for power sums.
-- Historical result; no DOI applies.
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984),
-- 223--250. DOI: 10.1007/BF01240221.
--
-- P. K. Mitter,
-- "The Exact Renormalization Group", contribution to the Encyclopedia of
-- Mathematical Physics (Elsevier, 2006), arXiv:math-ph/0505008.
--
-- DASHI CONTRIBUTION
--
-- The four-dimensional Combes--Thomas shell count uses
--
--   sum_{n>=0} (n+1)^3 r^n = (1+4r+r^2)/(1-r)^4.
--
-- Rather than importing this as symbolic arithmetic, we prove the exact finite
-- division-free identity, including the complete positive tail polynomial:
--
--   (1-r)^4 sum_{n=0}^{N-1}(n+1)^3 r^n
--     = 1+4r+r^2-r^N T_N(r).
--
-- T_N is written as a sum of four products that are manifestly nonnegative
-- when 0<=r<=1.  The infinite closed form is therefore the zero-tail limit of
-- a machine-checked finite identity, not an unchecked analytic simplification.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

natural : Nat → ℚ
natural zero = 0ℚ
natural (suc index) = 1ℚ + natural index

square cube fourthPower : ℚ → ℚ
square value = value * value
cube value = value * value * value
fourthPower value = square (square value)

power : ℚ → Nat → ℚ
power ratio zero = 1ℚ
power ratio (suc exponent) = ratio * power ratio exponent

cubicShellPartialSum : ℚ → Nat → ℚ
cubicShellPartialSum ratio zero = 0ℚ
cubicShellPartialSum ratio (suc count) =
  cubicShellPartialSum ratio count
  + cube (natural (suc count)) * power ratio count

oneMinusFourth : ℚ → ℚ
oneMinusFourth ratio = fourthPower (1ℚ - ratio)

cubicShellNumerator : ℚ → ℚ
cubicShellNumerator ratio =
  1ℚ + (+ 4 / 1) * ratio + ratio * ratio

-- Positive-factor form of the tail numerator.  Here m=N+1.
cubicShellTail : Nat → ℚ → ℚ
cubicShellTail count ratio =
  let
    m = natural (suc count)
    gap = 1ℚ - ratio
  in
  cube m * cube gap
  + (+ 3 / 1) * square m * ratio * square gap
  + (+ 3 / 1) * m * ratio * (1ℚ + ratio) * gap
  + ratio * cubicShellNumerator ratio

cubicShellTailZero : ∀ ratio →
  cubicShellTail zero ratio ≡ cubicShellNumerator ratio
cubicShellTailZero ratio = ℚRing.solve-∀ ratio

cubicShellTailRecurrence : ∀ count ratio →
  cubicShellTail count ratio
  ≡ cube (natural (suc count)) * oneMinusFourth ratio
    + ratio * cubicShellTail (suc count) ratio
cubicShellTailRecurrence count ratio =
  ℚRing.solve-∀ (natural count) ratio

cubicShellFiniteClosedForm : ∀ count ratio →
  oneMinusFourth ratio * cubicShellPartialSum ratio count
  ≡ cubicShellNumerator ratio
    - power ratio count * cubicShellTail count ratio
cubicShellFiniteClosedForm zero ratio
  rewrite cubicShellTailZero ratio =
  ℚRing.solve-∀ ratio
cubicShellFiniteClosedForm (suc count) ratio
  rewrite cubicShellFiniteClosedForm count ratio
        | cubicShellTailRecurrence count ratio =
  ℚRing.solve-∀
    (natural (suc count))
    ratio
    (power ratio count)
    (cubicShellTail (suc count) ratio)
    (cubicShellNumerator ratio)

record CubicShellClosedFormWitness (ratio total : ℚ) : Set where
  field
    scaledClosedForm :
      oneMinusFourth ratio * total ≡ cubicShellNumerator ratio

open CubicShellClosedFormWitness public

finiteErrorAgainstClosedForm :
  ∀ ratio total →
  CubicShellClosedFormWitness ratio total →
  ∀ count →
  oneMinusFourth ratio
    * (total - cubicShellPartialSum ratio count)
  ≡ power ratio count * cubicShellTail count ratio
finiteErrorAgainstClosedForm ratio total witness count =
  trans
    (ℚRing.solve-∀
      (oneMinusFourth ratio)
      total
      (cubicShellPartialSum ratio count))
    (trans
      (cong₂ _-_
        (scaledClosedForm witness)
        (cubicShellFiniteClosedForm count ratio))
      (ℚRing.solve-∀
        (cubicShellNumerator ratio)
        (power ratio count)
        (cubicShellTail count ratio)))

cubicShellFiniteIdentityLevel : ProofLevel
cubicShellFiniteIdentityLevel = machineChecked

cubicShellExactTailLevel : ProofLevel
cubicShellExactTailLevel = machineChecked

cubicShellInfiniteLimitProducerLevel : ProofLevel
cubicShellInfiniteLimitProducerLevel = conditional
