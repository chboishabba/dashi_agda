module DASHI.Arithmetic.ArithmeticIntegerEmbeddingBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)

open import DASHI.Arithmetic.NormalizeAddState using (NormalizeAddState)
open import DASHI.Arithmetic.NormalizeAdd using (normalizeAdd)
open import DASHI.Arithmetic.CancellationPressureFromCanonical using
  ( StateCancellationPressure
  ; StateSupportPressure
  ; normalizeAddOneStepSupportBound
  )
open import DASHI.Arithmetic.PrimeIndexedPressure using
  ( PrimeContributionVec
  ; primeIndexedPressureAt
  ; sum15
  )

------------------------------------------------------------------------
-- Bridge surface from an integer embedding into the current pressure and
-- normalization story.
--
-- The embedding itself is left abstract here. This file only packages the
-- compositional seam the new lane needs:
--   - total prime-indexed pressure on embedded states
--   - scalar cancellation pressure on embedded states
--   - the one-step normalization support bound

record IntegerEmbeddingPressureBridge : Set₁ where
  field
    IntegerState : Set
    embed : IntegerState → NormalizeAddState

    totalPrimePressure : IntegerState → Nat
    scalarCancellationPressure : IntegerState → Nat

    totalPrimePressure-law :
      ∀ x →
      totalPrimePressure x ≡
      sum15 (primeIndexedPressureAt (embed x))

    scalarCancellationPressure-law :
      ∀ x →
      scalarCancellationPressure x ≡
      StateCancellationPressure (embed x)

    oneStepSupportBound :
      ∀ x →
      StateCancellationPressure (normalizeAdd (embed x)) ≤
      StateSupportPressure (normalizeAdd (embed x))

open IntegerEmbeddingPressureBridge public

embed-totalPressure :
  (bridge : IntegerEmbeddingPressureBridge) →
  IntegerEmbeddingPressureBridge.IntegerState bridge → Nat
embed-totalPressure bridge =
  IntegerEmbeddingPressureBridge.totalPrimePressure bridge

embed-scalarCancellationPressure :
  (bridge : IntegerEmbeddingPressureBridge) →
  IntegerEmbeddingPressureBridge.IntegerState bridge → Nat
embed-scalarCancellationPressure bridge =
  IntegerEmbeddingPressureBridge.scalarCancellationPressure bridge

embed-primeContribution-law :
  (bridge : IntegerEmbeddingPressureBridge) →
  ∀ x →
  embed-totalPressure bridge x ≡
  sum15 (primeIndexedPressureAt
    (IntegerEmbeddingPressureBridge.embed bridge x))
embed-primeContribution-law bridge =
  IntegerEmbeddingPressureBridge.totalPrimePressure-law bridge

embed-scalarPressure-law :
  (bridge : IntegerEmbeddingPressureBridge) →
  ∀ x →
  embed-scalarCancellationPressure bridge x ≡
  StateCancellationPressure
    (IntegerEmbeddingPressureBridge.embed bridge x)
embed-scalarPressure-law bridge =
  IntegerEmbeddingPressureBridge.scalarCancellationPressure-law bridge

embed-oneStepSupportBound :
  (bridge : IntegerEmbeddingPressureBridge) →
  ∀ x →
  StateCancellationPressure
    (normalizeAdd (IntegerEmbeddingPressureBridge.embed bridge x)) ≤
  StateSupportPressure
    (normalizeAdd (IntegerEmbeddingPressureBridge.embed bridge x))
embed-oneStepSupportBound bridge =
  IntegerEmbeddingPressureBridge.oneStepSupportBound bridge

------------------------------------------------------------------------
-- Summary helper: normalization compatibility on an embedded state.

embed-normalizeAddOneStepSupportBound :
  (bridge : IntegerEmbeddingPressureBridge) →
  ∀ x →
  StateCancellationPressure
    (normalizeAdd (IntegerEmbeddingPressureBridge.embed bridge x)) ≤
  StateSupportPressure
    (normalizeAdd (IntegerEmbeddingPressureBridge.embed bridge x))
embed-normalizeAddOneStepSupportBound = embed-oneStepSupportBound
