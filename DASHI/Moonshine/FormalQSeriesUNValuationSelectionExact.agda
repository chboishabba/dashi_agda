module DASHI.Moonshine.FormalQSeriesUNValuationSelectionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- For an integral q-series f they define v_p(f) as the minimum p-adic
-- valuation of its coefficients.  Their U_N operator selects coefficients by
--
--   c_n(f | U_N) = c_{nN}(f).
--
-- DASHI CONTRIBUTION
--
-- Formalize the order-theoretic part of that interaction independently of a
-- particular p-adic valuation implementation.
--
-- Given ANY coefficient valuation v : Z -> Nat, a series valuation witness
-- consists of
--
--   * a global lower bound k <= v(f_n) for every coefficient; and
--   * one coefficient attaining k.
--
-- U_N always preserves the lower bound because it only selects an explicit
-- subsequence.  If an attaining source index is N*m, then U_N preserves the
-- exact minimum and m is the attaining output index.
--
-- This is the precise finite/arithmetic mechanism needed by Duncan--Swisher's
-- level-lowering valuation arguments.  The genuinely p-adic theorem about the
-- particular modular functions remains source-separated.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ)
open import Data.Nat using (_≤_; _*_)

import DASHI.Moonshine.FormalQSeriesOldformDegeneracyHeckeExact as Q
import DASHI.Moonshine.FormalQSeriesUNLevelLoweringExact as U

------------------------------------------------------------------------
-- Generic coefficient-valuation witness.
------------------------------------------------------------------------

record SeriesValuationWitness
    (coefficientValuation : ℤ → Nat)
    (f : Q.FormalQSeries)
    (value : Nat) : Set where
  field
    lowerBound : (n : Nat) → value ≤ coefficientValuation (f n)
    attainingIndex : Nat
    attains : coefficientValuation (f attainingIndex) ≡ value

open SeriesValuationWitness public

------------------------------------------------------------------------
-- U_N always preserves any global coefficient-valuation lower bound.
------------------------------------------------------------------------

uNPreservesValuationLowerBound :
  (coefficientValuation : ℤ → Nat) →
  (N : Nat) → (f : Q.FormalQSeries) → (value : Nat) →
  SeriesValuationWitness coefficientValuation f value →
  (n : Nat) →
  value ≤ coefficientValuation (U.UN N f n)
uNPreservesValuationLowerBound coefficientValuation N f value witness n =
  lowerBound witness (N * n)

------------------------------------------------------------------------
-- If a minimum-attaining coefficient is on the selected N-multiple
-- subsequence, the exact series valuation is preserved.
------------------------------------------------------------------------

record NMultipleAttainment
    (N : Nat)
    {coefficientValuation : ℤ → Nat}
    {f : Q.FormalQSeries}
    {value : Nat}
    (witness : SeriesValuationWitness coefficientValuation f value) : Set where
  field
    outputIndex : Nat
    sourceAttainingIndexIsMultiple : attainingIndex witness ≡ N * outputIndex

open NMultipleAttainment public

uNPreservesExactValuationWhenMinimumSelected :
  (coefficientValuation : ℤ → Nat) →
  (N : Nat) → (f : Q.FormalQSeries) → (value : Nat) →
  (witness : SeriesValuationWitness coefficientValuation f value) →
  NMultipleAttainment N witness →
  SeriesValuationWitness coefficientValuation (U.UN N f) value
uNPreservesExactValuationWhenMinimumSelected
  coefficientValuation N f value witness selected = record
  { lowerBound =
      uNPreservesValuationLowerBound
        coefficientValuation N f value witness
  ; attainingIndex = outputIndex selected
  ; attains =
      trans
        (cong coefficientValuation
          (cong f (sym (sourceAttainingIndexIsMultiple selected))))
        (attains witness)
  }

------------------------------------------------------------------------
-- Equivalent source-index formulation when the source author supplies the
-- attaining coefficient directly rather than a pre-built valuation witness.
------------------------------------------------------------------------

record SelectedMinimumCertificate
    (coefficientValuation : ℤ → Nat)
    (N : Nat)
    (f : Q.FormalQSeries)
    (value : Nat) : Set where
  field
    lowerBoundSource : (n : Nat) → value ≤ coefficientValuation (f n)
    selectedOutputIndex : Nat
    selectedAttains :
      coefficientValuation (f (N * selectedOutputIndex)) ≡ value

open SelectedMinimumCertificate public

selectedMinimumGivesUNValuation :
  (coefficientValuation : ℤ → Nat) →
  (N : Nat) → (f : Q.FormalQSeries) → (value : Nat) →
  SelectedMinimumCertificate coefficientValuation N f value →
  SeriesValuationWitness coefficientValuation (U.UN N f) value
selectedMinimumGivesUNValuation coefficientValuation N f value certificate = record
  { lowerBound = λ n → lowerBoundSource certificate (N * n)
  ; attainingIndex = selectedOutputIndex certificate
  ; attains = selectedAttains certificate
  }

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record FormalQSeriesUNValuationSelectionBoundary : Set where
  field
    genericCoefficientValuationSupported : Bool
    lowerBoundPreservationDerived : Bool
    selectedMinimumPreservationDerived : Bool
    particularPadicValuationImplementedHere : Bool
    modularityOrDeligneRigidityImplementedHere : Bool

canonicalFormalQSeriesUNValuationSelectionBoundary :
  FormalQSeriesUNValuationSelectionBoundary
canonicalFormalQSeriesUNValuationSelectionBoundary = record
  { genericCoefficientValuationSupported = true
  ; lowerBoundPreservationDerived = true
  ; selectedMinimumPreservationDerived = true
  ; particularPadicValuationImplementedHere = false
  ; modularityOrDeligneRigidityImplementedHere = false
  }
