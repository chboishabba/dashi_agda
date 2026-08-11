module DASHI.Physics.Closure.NSTriadKNLuoGlobalPoincareLowFrequencyNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / AUDIT CONTEXT
--
-- Ryusho Nemoto,
-- "Global Regularity of the Three-Dimensional Navier-Stokes Equations via
-- a Coupled Energy and Stability Framework".
-- PhilArchive record: NEMGRO. DOI: none located.
-- Status: manuscript/preprint and audit target only.
--
-- Roger Temam,
-- "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- The whole-space step
--
--   ||f||_2 <= C ||grad f||_2
--
-- has no universal constant without a spectral gap, mean condition,
-- confinement or frequency restriction.  The exact low-frequency model fixes
-- ||f||_2 = 1 and takes the derivative norm to be
--
--   epsilon = 1 / (C+1).
--
-- For every C >= 0,
--
--   C epsilon + epsilon = 1,
--   epsilon > 0,
--
-- and hence C epsilon < 1.  This is the division-aware finite algebra of the
-- standard long-wavelength obstruction.  It explains why the global
-- Poincare step used for Pi+ grad u cannot follow merely from absence of a
-- pointwise kernel.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; 1/_; positive)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

record PoincareCoefficient : Set where
  constructor poincareCoefficient
  field
    coefficient : ℚ
    coefficientNonnegative : 0ℚ ≤ coefficient

open PoincareCoefficient public

longWavelengthScale : PoincareCoefficient → ℚ
longWavelengthScale candidate = coefficient candidate + 1ℚ

longWavelengthScalePositive :
  ∀ candidate → 0ℚ < longWavelengthScale candidate
longWavelengthScalePositive candidate =
  let
    onePositive : 0ℚ < 1ℚ
    onePositive = ℚₚ.positive⁻¹ 1ℚ

    shifted :
      0ℚ + 0ℚ < coefficient candidate + 1ℚ
    shifted =
      ℚₚ.+-mono-≤-<
        (coefficientNonnegative candidate)
        onePositive
  in
  subst
    (λ left → left < longWavelengthScale candidate)
    (ℚₚ.+-identityˡ 0ℚ)
    shifted

longWavelengthFrequency : PoincareCoefficient → ℚ
longWavelengthFrequency candidate =
  let
    scale = longWavelengthScale candidate
    scalePositive = longWavelengthScalePositive candidate
    instance
      scaleNonzero = ℚ.>-nonZero scalePositive
  in
  ℚ.1/_ scale

scaleTimesFrequencyIsOne :
  ∀ candidate →
  longWavelengthScale candidate
    * longWavelengthFrequency candidate
  ≡ 1ℚ
scaleTimesFrequencyIsOne candidate =
  let
    scale = longWavelengthScale candidate
    scalePositive = longWavelengthScalePositive candidate
    instance
      scaleNonzero = ℚ.>-nonZero scalePositive
  in
  ℚₚ.*-inverseʳ scale

longWavelengthFrequencyPositive :
  ∀ candidate → 0ℚ < longWavelengthFrequency candidate
longWavelengthFrequencyPositive candidate =
  let
    scale = longWavelengthScale candidate
    scalePositive = longWavelengthScalePositive candidate
    instance
      scalePositiveInstance = positive scalePositive
      scaleNonzero = ℚₚ.pos⇒nonZero scale
      inversePositive = ℚₚ.1/pos⇒pos scale
  in
  ℚₚ.positive⁻¹ (longWavelengthFrequency candidate)

coefficientPlusOneFrequencyIdentity :
  ∀ candidate →
  coefficient candidate * longWavelengthFrequency candidate
    + longWavelengthFrequency candidate
  ≡ 1ℚ
coefficientPlusOneFrequencyIdentity candidate =
  let
    distributed :
      coefficient candidate * longWavelengthFrequency candidate
        + longWavelengthFrequency candidate
      ≡
      longWavelengthScale candidate
        * longWavelengthFrequency candidate
    distributed =
      solve
        ( coefficient candidate
        ∷ longWavelengthFrequency candidate
        ∷ [])
  in
  subst
    (λ value →
      coefficient candidate * longWavelengthFrequency candidate
        + longWavelengthFrequency candidate
      ≡ value)
    (scaleTimesFrequencyIsOne candidate)
    distributed

universalGlobalPoincareCoefficientFails :
  ∀ candidate →
  coefficient candidate * longWavelengthFrequency candidate < 1ℚ
universalGlobalPoincareCoefficientFails candidate =
  let
    weighted =
      coefficient candidate * longWavelengthFrequency candidate
    epsilon = longWavelengthFrequency candidate

    withPositiveFrequency : weighted + 0ℚ < weighted + epsilon
    withPositiveFrequency =
      ℚₚ.+-monoʳ-< weighted
        (longWavelengthFrequencyPositive candidate)

    leftClosed : weighted + 0ℚ ≡ weighted
    leftClosed = solve (weighted ∷ [])

    normalized : weighted < weighted + epsilon
    normalized =
      subst
        (λ left → left < weighted + epsilon)
        leftClosed
        withPositiveFrequency
  in
  subst
    (λ right → weighted < right)
    (coefficientPlusOneFrequencyIdentity candidate)
    normalized

record GlobalPoincareAuditConclusion : Set where
  constructor globalPoincareAuditConclusion
  field
    lowFrequencyCounterfamilyConstructed : Set
    universalWholeSpacePoincareFromKernelAbsence : Set
    additionalSpectralOrNormalizationInputRequired : Set

canonicalGlobalPoincareAuditConclusion : GlobalPoincareAuditConclusion
canonicalGlobalPoincareAuditConclusion =
  globalPoincareAuditConclusion ⊤ ⊥ ⊤
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
