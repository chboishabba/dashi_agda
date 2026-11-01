module DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicBernsteinRealizationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Construct the finite dyadic Bernstein estimate from the two pieces proved
-- in this round:
--
-- * explicit three-dimensional dyadic support counting;
-- * the finite Fourier coefficient L1 estimate.
--
-- Unlike the older round-thirteen carrier, the coefficient estimate below is
-- indexed by the actual retained slots.  It therefore does not ask for a
-- bound on arbitrary output-mode records unrelated to the support list.
-- For every finite Boolean shell cut from an eightfold dyadic enumeration,
--
--   sum_(k in S_q) |Fhat(k)|^2
--     <= 8^q mass(base) ||F||_1^2.
--
-- This is the radical-free finite form of the periodic L1-to-L2 Bernstein
-- estimate.  Parseval identifies the left side with ||Delta_q F||_2^2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicSupportCountExact as Support
import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourierCoefficientL1Exact as Fourier
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

sumBy : ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumBy [] value = 0ℚ
sumBy (item ∷ items) value = value item + sumBy items value

record DyadicBernsteinRealization (Slot : Set) : Set₁ where
  constructor dyadic-bernstein-realization
  field
    baseEnumeration : List Slot
    shell : Nat
    shellPredicate : Slot → Bool

    commonInputL1Squared : ℚ
    commonInputL1SquaredNonnegative : 0ℚ ≤ commonInputL1Squared

    coefficientData : Slot → Fourier.FiniteFourierCoefficientData
    commonInputMeaning :
      (slot : Slot) →
      Fourier.inputL1Squared (coefficientData slot)
      ≡ commonInputL1Squared

open DyadicBernsteinRealization public

retainedSlots :
  ∀ {Slot : Set} →
  DyadicBernsteinRealization Slot →
  List Slot
retainedSlots dataSet =
  Support.dyadicSupport
    (shellPredicate dataSet)
    (baseEnumeration dataSet)
    (shell dataSet)

coefficientSquaredAt :
  ∀ {Slot : Set} →
  DyadicBernsteinRealization Slot →
  Slot →
  ℚ
coefficientSquaredAt dataSet slot =
  Fourier.coefficientSquared (coefficientData dataSet slot)

outputL2Squared :
  ∀ {Slot : Set} →
  DyadicBernsteinRealization Slot →
  ℚ
outputL2Squared dataSet =
  sumBy (retainedSlots dataSet) (coefficientSquaredAt dataSet)

outputScaleCubed :
  ∀ {Slot : Set} →
  DyadicBernsteinRealization Slot →
  ℚ
outputScaleCubed dataSet =
  Geo.pow Support.eight (shell dataSet)
  * Support.countMass (baseEnumeration dataSet)

retainedCoefficientBound :
  ∀ {Slot : Set}
    (dataSet : DyadicBernsteinRealization Slot)
    (slot : Slot) →
  coefficientSquaredAt dataSet slot
  ≤ commonInputL1Squared dataSet
retainedCoefficientBound dataSet slot =
  subst
    (λ upper → coefficientSquaredAt dataSet slot ≤ upper)
    (commonInputMeaning dataSet slot)
    (Fourier.finiteFourierCoefficientBound
      (coefficientData dataSet slot))

outputBoundBySupportMass :
  ∀ {Slot : Set}
    (dataSet : DyadicBernsteinRealization Slot)
    (slots : List Slot) →
  sumBy slots (coefficientSquaredAt dataSet)
  ≤ Support.countMass slots * commonInputL1Squared dataSet
outputBoundBySupportMass dataSet [] = ℚₚ.≤-refl
outputBoundBySupportMass dataSet (slot ∷ slots) =
  let
    summed :
      coefficientSquaredAt dataSet slot
        + sumBy slots (coefficientSquaredAt dataSet)
      ≤ commonInputL1Squared dataSet
        + Support.countMass slots * commonInputL1Squared dataSet
    summed =
      ℚₚ.+-mono-≤
        (retainedCoefficientBound dataSet slot)
        (outputBoundBySupportMass dataSet slots)

    targetMeaning :
      commonInputL1Squared dataSet
        + Support.countMass slots * commonInputL1Squared dataSet
      ≡ (1ℚ + Support.countMass slots)
          * commonInputL1Squared dataSet
    targetMeaning =
      solve
        ( commonInputL1Squared dataSet
        ∷ Support.countMass slots
        ∷ [])
  in
  subst
    (λ upper →
      coefficientSquaredAt dataSet slot
        + sumBy slots (coefficientSquaredAt dataSet)
      ≤ upper)
    targetMeaning
    summed

supportScaleTransport :
  ∀ {Slot : Set}
    (dataSet : DyadicBernsteinRealization Slot) →
  Support.countMass (retainedSlots dataSet)
    * commonInputL1Squared dataSet
  ≤ outputScaleCubed dataSet
    * commonInputL1Squared dataSet
supportScaleTransport dataSet =
  let
    instance
      inputSquareIsNonnegative =
        nonNegative (commonInputL1SquaredNonnegative dataSet)
  in
  ℚₚ.*-monoʳ-≤-nonNeg
    (commonInputL1Squared dataSet)
    (Support.dyadicSupportCountBound
      (shellPredicate dataSet)
      (baseEnumeration dataSet)
      (shell dataSet))

finiteDyadicBernsteinSquare :
  ∀ {Slot : Set}
    (dataSet : DyadicBernsteinRealization Slot) →
  outputL2Squared dataSet
  ≤ outputScaleCubed dataSet * commonInputL1Squared dataSet
finiteDyadicBernsteinSquare dataSet =
  ℚₚ.≤-trans
    (outputBoundBySupportMass dataSet (retainedSlots dataSet))
    (supportScaleTransport dataSet)
