module DASHI.Moonshine.FormalLaurentQSeriesUNValuationSelectionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- Their valuation v_p(f) is the minimum p-adic valuation over ALL Laurent
-- coefficients of an integral modular-function q-expansion.  Since
--
--   c_n(f | U_N) = c_{nN}(f),
--
-- U_N is literally subsequence selection on signed coefficient indices.
--
-- DASHI CONTRIBUTION
--
-- Construct the exact signed-index version of the generic minimum-selection
-- theorem.  U_N preserves every lower bound; if a minimum-attaining source
-- coefficient occurs at index N*m for m in Z, then the exact minimum survives
-- and is attained at output index m.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_)
  renaming (_*_ to _*ℤ_)
open import Data.Nat using (_≤_)

import DASHI.Moonshine.FormalLaurentQSeriesUNExact as Laurent

record LaurentSeriesValuationWitness
    (coefficientValuation : ℤ → Nat)
    (f : Laurent.FormalLaurentQSeries)
    (value : Nat) : Set where
  field
    lowerBound : (n : ℤ) → value ≤ coefficientValuation (f n)
    attainingIndex : ℤ
    attains : coefficientValuation (f attainingIndex) ≡ value

open LaurentSeriesValuationWitness public

uNPreservesLowerBound :
  (coefficientValuation : ℤ → Nat) →
  (N : Nat) → (f : Laurent.FormalLaurentQSeries) → (value : Nat) →
  LaurentSeriesValuationWitness coefficientValuation f value →
  (n : ℤ) →
  value ≤ coefficientValuation (Laurent.UN N f n)
uNPreservesLowerBound coefficientValuation N f value witness n =
  lowerBound witness ((+ N) *ℤ n)

record LaurentNMultipleAttainment
    (N : Nat)
    {coefficientValuation : ℤ → Nat}
    {f : Laurent.FormalLaurentQSeries}
    {value : Nat}
    (witness : LaurentSeriesValuationWitness coefficientValuation f value) : Set where
  field
    outputIndex : ℤ
    sourceAttainingIndexIsMultiple :
      attainingIndex witness ≡ (+ N) *ℤ outputIndex

open LaurentNMultipleAttainment public

uNPreservesExactValuationWhenMinimumSelected :
  (coefficientValuation : ℤ → Nat) →
  (N : Nat) → (f : Laurent.FormalLaurentQSeries) → (value : Nat) →
  (witness : LaurentSeriesValuationWitness coefficientValuation f value) →
  LaurentNMultipleAttainment N witness →
  LaurentSeriesValuationWitness coefficientValuation (Laurent.UN N f) value
uNPreservesExactValuationWhenMinimumSelected
  coefficientValuation N f value witness selected = record
  { lowerBound =
      uNPreservesLowerBound coefficientValuation N f value witness
  ; attainingIndex = outputIndex selected
  ; attains =
      trans
        (cong (λ k → coefficientValuation (f k))
          (sym (sourceAttainingIndexIsMultiple selected)))
        (attains witness)
  }

record SelectedLaurentMinimumCertificate
    (coefficientValuation : ℤ → Nat)
    (N : Nat)
    (f : Laurent.FormalLaurentQSeries)
    (value : Nat) : Set where
  field
    lowerBoundSource : (n : ℤ) → value ≤ coefficientValuation (f n)
    selectedOutputIndex : ℤ
    selectedAttains :
      coefficientValuation (f ((+ N) *ℤ selectedOutputIndex)) ≡ value

open SelectedLaurentMinimumCertificate public

selectedMinimumGivesUNValuation :
  (coefficientValuation : ℤ → Nat) →
  (N : Nat) → (f : Laurent.FormalLaurentQSeries) → (value : Nat) →
  SelectedLaurentMinimumCertificate coefficientValuation N f value →
  LaurentSeriesValuationWitness coefficientValuation (Laurent.UN N f) value
selectedMinimumGivesUNValuation coefficientValuation N f value certificate = record
  { lowerBound = λ n → lowerBoundSource certificate ((+ N) *ℤ n)
  ; attainingIndex = selectedOutputIndex certificate
  ; attains = selectedAttains certificate
  }

record FormalLaurentQSeriesUNValuationBoundary : Set where
  field
    signedCoefficientMinimumCarrierConstructed : Bool
    lowerBoundSelectionDerived : Bool
    exactMinimumSelectionDerived : Bool
    principalPartIndicesSupported : Bool
    specificPadicCoefficientValuationImplementedHere : Bool
    analyticLevelLoweringImportedHere : Bool

canonicalFormalLaurentQSeriesUNValuationBoundary :
  FormalLaurentQSeriesUNValuationBoundary
canonicalFormalLaurentQSeriesUNValuationBoundary = record
  { signedCoefficientMinimumCarrierConstructed = true
  ; lowerBoundSelectionDerived = true
  ; exactMinimumSelectionDerived = true
  ; principalPartIndicesSupported = true
  ; specificPadicCoefficientValuationImplementedHere = false
  ; analyticLevelLoweringImportedHere = false
  }
