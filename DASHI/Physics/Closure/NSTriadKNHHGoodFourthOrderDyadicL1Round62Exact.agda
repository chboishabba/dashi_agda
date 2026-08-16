module DASHI.Physics.Closure.NSTriadKNHHGoodFourthOrderDyadicL1Round62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- ROUND 62 CONTRIBUTION
--
-- For the HH-good annular multiplier, four integrations by parts in R^3 give
-- the standard pointwise decay |K(x)| <= C M_4 (1+|x|)^(-4).  On the dyadic
-- shell |x|~2^j the volume costs 2^(3j), hence the shell L1 mass costs only
-- 2^(-j).  This module closes that LAST summability step exactly over Q.
--
-- If physical shell masses m_j satisfy
--
--   0 <= m_j <= M 2^(-j),
--
-- every finite partial L1 mass is <= 2 M.  The proof uses the exact invariant
--
--   sum_{j=0}^n 2^(-j) + 2 * 2^(-(n+1)) = 2.
--
-- Thus E no longer needs a separate "Schwartz decay implies L1" authority.
-- The remaining continuum theorem is only the literal fourfold inverse-Fourier
-- integration-by-parts estimate that produces the dyadic shell majorant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadDyadicScalePrimitivesRound58 as Scale

partialDyadicWeight : Nat → ℚ
partialDyadicWeight zero = 1ℚ
partialDyadicWeight (suc n) =
  partialDyadicWeight n + Scale.inverseDyadicScale (suc n)

partialDyadicWeightTailExact : ∀ n →
  partialDyadicWeight n
    + Scale.two * Scale.inverseDyadicScale (suc n)
  ≡ Scale.two
partialDyadicWeightTailExact zero = solve []
partialDyadicWeightTailExact (suc n) =
  let
    tail = Scale.inverseDyadicScale (suc n)
    regroup :
      partialDyadicWeight (suc n)
        + Scale.two * Scale.inverseDyadicScale (suc (suc n))
      ≡ partialDyadicWeight n + Scale.two * tail
    regroup = solve (partialDyadicWeight n ∷ tail ∷ [])
  in
  trans regroup (partialDyadicWeightTailExact n)

inverseDyadicScaleNonnegative : ∀ n →
  0ℚ ≤ Scale.inverseDyadicScale n
inverseDyadicScaleNonnegative zero = ℚP.0≤1
inverseDyadicScaleNonnegative (suc n) =
  let
    halfNN : 0ℚ ≤ Scale.half
    halfNN = ℚP.<⇒≤ (ℚP.positive⁻¹ Scale.half)
    tailNN = inverseDyadicScaleNonnegative n
    instance
      halfNNI = nonNegative halfNN
      tailNNI = nonNegative tailNN
      productNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg Scale.half (Scale.inverseDyadicScale n)
  in
  ℚP.nonNegative⁻¹ (Scale.inverseDyadicScale (suc n))

partialDyadicWeightBelowTwo : ∀ n →
  partialDyadicWeight n ≤ Scale.two
partialDyadicWeightBelowTwo n =
  let
    tail = Scale.two * Scale.inverseDyadicScale (suc n)
    tailNN : 0ℚ ≤ tail
    tailNN =
      let instance
        twoNNI = nonNegative Scale.twoNonnegative
        dyNNI = nonNegative (inverseDyadicScaleNonnegative (suc n))
        productNNI =
          ℚP.nonNeg*nonNeg⇒nonNeg
            Scale.two (Scale.inverseDyadicScale (suc n))
      in ℚP.nonNegative⁻¹ tail

    addTail :
      partialDyadicWeight n + 0ℚ
      ≤ partialDyadicWeight n + tail
    addTail = ℚP.+-monoˡ-≤ (partialDyadicWeight n) tailNN
  in
  subst
    (λ left → left ≤ Scale.two)
    (ℚP.+-identityʳ (partialDyadicWeight n))
    (subst
      (λ right → partialDyadicWeight n + 0ℚ ≤ right)
      (partialDyadicWeightTailExact n)
      addTail)

record FourthOrderDyadicShellMajorant : Set where
  field
    decayMass : ℚ
    decayMassNonnegative : 0ℚ ≤ decayMass
    shellMass : Nat → ℚ
    shellMassNonnegative : ∀ n → 0ℚ ≤ shellMass n
    fourthOrderThreeDimensionalShellBound : ∀ n →
      shellMass n ≤ decayMass * Scale.inverseDyadicScale n

open FourthOrderDyadicShellMajorant public

partialShellMass : FourthOrderDyadicShellMajorant → Nat → ℚ
partialShellMass majorant zero = shellMass majorant zero
partialShellMass majorant (suc n) =
  partialShellMass majorant n + shellMass majorant (suc n)

partialShellMassBelowScaledDyadicWeight :
  (majorant : FourthOrderDyadicShellMajorant) → ∀ n →
  partialShellMass majorant n
  ≤ decayMass majorant * partialDyadicWeight n
partialShellMassBelowScaledDyadicWeight majorant zero =
  subst
    (λ right → shellMass majorant zero ≤ right)
    (sym (ℚP.*-identityʳ (decayMass majorant)))
    (fourthOrderThreeDimensionalShellBound majorant zero)
partialShellMassBelowScaledDyadicWeight majorant (suc n) =
  let
    previous = partialShellMassBelowScaledDyadicWeight majorant n
    current = fourthOrderThreeDimensionalShellBound majorant (suc n)
    added = ℚP.+-mono-≤ previous current
    regroup :
      decayMass majorant * partialDyadicWeight n
        + decayMass majorant * Scale.inverseDyadicScale (suc n)
      ≡ decayMass majorant * partialDyadicWeight (suc n)
    regroup = solve
      ( decayMass majorant
      ∷ partialDyadicWeight n
      ∷ Scale.inverseDyadicScale (suc n)
      ∷ [])
  in
  subst
    (λ right → partialShellMass majorant (suc n) ≤ right)
    regroup
    added

finitePartialL1UniformBound :
  (majorant : FourthOrderDyadicShellMajorant) → ∀ n →
  partialShellMass majorant n ≤ Scale.two * decayMass majorant
finitePartialL1UniformBound majorant n =
  let
    first = partialShellMassBelowScaledDyadicWeight majorant n
    scaled :
      decayMass majorant * partialDyadicWeight n
      ≤ decayMass majorant * Scale.two
    scaled =
      let instance massNNI = nonNegative (decayMassNonnegative majorant)
      in ℚP.*-monoˡ-≤-nonNeg
        (decayMass majorant) (partialDyadicWeightBelowTwo n)
    endpoint :
      decayMass majorant * Scale.two
      ≡ Scale.two * decayMass majorant
    endpoint = solve (decayMass majorant ∷ [])
  in
  ℚP.≤-trans first
    (subst
      (λ upper → decayMass majorant * partialDyadicWeight n ≤ upper)
      endpoint
      scaled)

fourthOrderDecaySummabilityClosed : Bool
fourthOrderDecaySummabilityClosed = true

fourthOrderDecaySummabilityClosedIsTrue :
  fourthOrderDecaySummabilityClosed ≡ true
fourthOrderDecaySummabilityClosedIsTrue = refl
