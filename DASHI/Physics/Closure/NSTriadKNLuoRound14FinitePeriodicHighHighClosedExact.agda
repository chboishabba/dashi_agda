module DASHI.Physics.Closure.NSTriadKNLuoRound14FinitePeriodicHighHighClosedExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
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
-- Compose the new concrete finite ingredients of the periodic HH producer:
--
-- * exact rational Leray/H^-1 cancellation for complex tensor modes;
-- * finite Fourier-coefficient L1 control;
-- * explicit 8^q support counting; and
-- * finite dyadic Bernstein summation.
--
-- For every retained finite mode list this proves
--
--   sum_k |k|^-2 |P(k)(ik . Fhat(k))|^2
--     <= 8^q mass(base) ||F||_1^2.
--
-- The only remaining continuum identification is finite Parseval/Fourier
-- synthesis between the repository's physical torus carrier and these exact
-- coefficient records.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicBernsteinRealizationExact as Bernstein
import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourierCoefficientL1Exact as Fourier
import DASHI.Physics.Closure.NSTriadKNLuoRationalLerayMultiplierContractiveExact as Leray

record FinitePeriodicHighHighClosedData (Slot : Set) : Set₁ where
  constructor finite-periodic-high-high-closed-data
  field
    bernsteinData : Bernstein.DyadicBernsteinRealization Slot
    lerayModeData : Slot → Leray.ComplexProjectedDivergenceData

    tensorCoefficientMeaning :
      (slot : Slot) →
      Leray.complexMatrixNormSquared
        (Leray.complexTensor (lerayModeData slot))
      ≡ Fourier.coefficientSquared
        (Bernstein.coefficientData bernsteinData slot)

open FinitePeriodicHighHighClosedData public

hMinusOneSquaredAt :
  ∀ {Slot : Set} →
  FinitePeriodicHighHighClosedData Slot →
  Slot →
  ℚ
hMinusOneSquaredAt dataSet slot =
  Leray.complexHMinusOneSquared (lerayModeData dataSet slot)

finiteHMinusOneSquared :
  ∀ {Slot : Set} →
  FinitePeriodicHighHighClosedData Slot →
  ℚ
finiteHMinusOneSquared dataSet =
  Bernstein.sumBy
    (Bernstein.retainedSlots (bernsteinData dataSet))
    (hMinusOneSquaredAt dataSet)

modeHMinusOneByFourierCoefficient :
  ∀ {Slot : Set}
    (dataSet : FinitePeriodicHighHighClosedData Slot)
    (slot : Slot) →
  hMinusOneSquaredAt dataSet slot
  ≤ Bernstein.coefficientSquaredAt (bernsteinData dataSet) slot
modeHMinusOneByFourierCoefficient dataSet slot =
  subst
    (λ upper → hMinusOneSquaredAt dataSet slot ≤ upper)
    (tensorCoefficientMeaning dataSet slot)
    (Leray.complexHMinusOneCancellation
      (lerayModeData dataSet slot))

sumHMinusOneByCoefficientSum :
  ∀ {Slot : Set}
    (dataSet : FinitePeriodicHighHighClosedData Slot)
    (slots : List Slot) →
  Bernstein.sumBy slots (hMinusOneSquaredAt dataSet)
  ≤ Bernstein.sumBy slots
      (Bernstein.coefficientSquaredAt (bernsteinData dataSet))
sumHMinusOneByCoefficientSum dataSet [] = ℚₚ.≤-refl
sumHMinusOneByCoefficientSum dataSet (slot ∷ slots) =
  ℚₚ.+-mono-≤
    (modeHMinusOneByFourierCoefficient dataSet slot)
    (sumHMinusOneByCoefficientSum dataSet slots)

finitePeriodicHighHighHMinusOneSquareBound :
  ∀ {Slot : Set}
    (dataSet : FinitePeriodicHighHighClosedData Slot) →
  finiteHMinusOneSquared dataSet
  ≤ Bernstein.outputScaleCubed (bernsteinData dataSet)
      * Bernstein.commonInputL1Squared (bernsteinData dataSet)
finitePeriodicHighHighHMinusOneSquareBound dataSet =
  ℚₚ.≤-trans
    (sumHMinusOneByCoefficientSum
      dataSet
      (Bernstein.retainedSlots (bernsteinData dataSet)))
    (Bernstein.finiteDyadicBernsteinSquare
      (bernsteinData dataSet))
