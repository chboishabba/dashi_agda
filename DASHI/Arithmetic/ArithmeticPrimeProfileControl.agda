module DASHI.Arithmetic.ArithmeticPrimeProfileControl where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_)

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using
  ( Int
  ; embed
  ; embed-primeIndexedPressure
  )
open import DASHI.Arithmetic.CancellationPressureFromCanonical using
  ( StateCancellationPressure
  ; StateSupportPressure
  ; normalizeAddOneStepSupportBound
  )
open import DASHI.Arithmetic.NormalizeAdd using (normalizeAdd)
open import DASHI.Arithmetic.NormalizeAddState using
  ( NormalizeAddState
  ; normalizeAddCanonical
  )
open import DASHI.Arithmetic.PrimeIndexedPressure using
  ( sum15
  ; primeIndexedPressureAt
  )
open import DASHI.Arithmetic.PrimeIndexedPressureCanonical using
  ( normalizeAdd⇒primeIndexedCanonicalBounded
  )

------------------------------------------------------------------------
-- Control-side bridge packaging.
--
-- This module keeps the arithmetic prime-profile round thin:
-- it only bundles the existing normalization, canonicality, and pressure
-- checks for downstream consumers.

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

ArithmeticOrigin : Set
ArithmeticOrigin = Int × Int

profile : ArithmeticOrigin → NormalizeAddState
profile (x , y) = embed x y

totalTrackedPrimePressure : ArithmeticOrigin → Nat
totalTrackedPrimePressure (x , y) =
  sum15 (primeIndexedPressureAt (profile (x , y)))

scalarCancellationPressure : ArithmeticOrigin → Nat
scalarCancellationPressure (x , y) =
  StateCancellationPressure (profile (x , y))

canonicalCompatibility :
  (o : ArithmeticOrigin) →
  normalizeAddCanonical (normalizeAdd (profile o))
canonicalCompatibility (x , y) with normalizeAdd⇒primeIndexedCanonicalBounded (profile (x , y))
... | canon , _ = canon

controlPrimePressureBoundAfterNormalize :
  (o : ArithmeticOrigin) →
  sum15 (primeIndexedPressureAt (normalizeAdd (profile o))) ≤
  StateSupportPressure (normalizeAdd (profile o))
controlPrimePressureBoundAfterNormalize (x , y) with normalizeAdd⇒primeIndexedCanonicalBounded (profile (x , y))
... | _ , bound = bound

controlSupportBoundAfterNormalize :
  (o : ArithmeticOrigin) →
  StateCancellationPressure (normalizeAdd (profile o)) ≤
  StateSupportPressure (normalizeAdd (profile o))
controlSupportBoundAfterNormalize (x , y) =
  normalizeAddOneStepSupportBound (profile (x , y))

controlScalarVsTrackedPrimePressure :
  (o : ArithmeticOrigin) →
  scalarCancellationPressure o ≡ totalTrackedPrimePressure o
controlScalarVsTrackedPrimePressure (x , y) =
  sym (embed-primeIndexedPressure x y)

record ArithmeticPrimeProfileControl : Set₁ where
  field
    Origin : Set
    profileState : Origin → NormalizeAddState
    trackedPrimePressure : Origin → Nat
    scalarPressure : Origin → Nat
    canonicalAfterNormalize :
      (o : Origin) →
      normalizeAddCanonical (normalizeAdd (profileState o))
    primePressureBoundAfterNormalize :
      (o : Origin) →
      sum15 (primeIndexedPressureAt (normalizeAdd (profileState o))) ≤
      StateSupportPressure (normalizeAdd (profileState o))
    supportBoundAfterNormalize :
      (o : Origin) →
      StateCancellationPressure (normalizeAdd (profileState o)) ≤
      StateSupportPressure (normalizeAdd (profileState o))
    scalarVsTrackedPrimePressure :
      (o : Origin) →
      scalarPressure o ≡ trackedPrimePressure o

arithmeticPrimeProfileControl : ArithmeticPrimeProfileControl
arithmeticPrimeProfileControl =
  record
    { Origin = ArithmeticOrigin
    ; profileState = profile
    ; trackedPrimePressure = totalTrackedPrimePressure
    ; scalarPressure = scalarCancellationPressure
    ; canonicalAfterNormalize = canonicalCompatibility
    ; primePressureBoundAfterNormalize = controlPrimePressureBoundAfterNormalize
    ; supportBoundAfterNormalize = controlSupportBoundAfterNormalize
    ; scalarVsTrackedPrimePressure = controlScalarVsTrackedPrimePressure
    }
