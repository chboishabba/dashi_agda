module DASHI.Arithmetic.UniformConvergenceRateSurface where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Arithmetic.NormalizeAdd using
  ( normalizeAdd
  ; normalizeAdd-canonical
  )
open import DASHI.Arithmetic.NormalizeAddState using
  ( NormalizeAddState
  ; normalizeAddCanonical
  )
open import DASHI.Arithmetic.NormalizeAddSumPreservation using
  ( NormalizeAddSumPreservationReceipt
  ; canonicalNormalizeAddSumPreservationReceipt
  )

------------------------------------------------------------------------
-- W2 uniform-rate / transport support surface.
--
-- This module records the narrow local fact needed by the Newton lane:
-- the primary normalizeAdd arithmetic surface is a fixed, concrete
-- NormalizeAddState endomap.  It is not parameterised by a carrier
-- realization in the inspected arithmetic surface, and the only
-- NormalizeAddState -> NormalizeAddState arithmetic endomap found in scope
-- is normalizeAdd itself.
--
-- This is deliberately a diagnostic/support receipt, not a W2 promotion
-- authority token.  It can be consumed by the W2 authority lane as evidence
-- that the uniform-rate/transport subcondition is trivial for the current
-- local arithmetic surface.

record UniformNormalizeAddRateDiagnostic : Set₁ where
  field
    State :
      Set

    stateSurfaceFixed :
      State ≡ NormalizeAddState

    normalizeStep :
      NormalizeAddState → NormalizeAddState

    normalizeStepFixed :
      normalizeStep ≡ normalizeAdd

    convergenceRate :
      NormalizeAddState → Nat

    rateLaw :
      ∀ s → convergenceRate s ≡ suc zero

    canonicalAfterOneStep :
      ∀ s → normalizeAddCanonical (normalizeStep s)

    canonicalSelfTransport :
      NormalizeAddState → NormalizeAddState

    selfTransportIsNormalizeAdd :
      canonicalSelfTransport ≡ normalizeAdd

    selfTransportRatePreserved :
      ∀ s → convergenceRate (canonicalSelfTransport s) ≡ convergenceRate s

    sumPreservationReceipt :
      NormalizeAddSumPreservationReceipt

    noCarrierParameterFoundInPrimarySurface :
      ⊤

    noNontrivialTransportFoundInArithmeticSearch :
      ⊤

    diagnosticNotes :
      List String

    noW2PromotionAuthorityConstructed :
      ⊤

canonicalUniformNormalizeAddRateDiagnostic :
  UniformNormalizeAddRateDiagnostic
canonicalUniformNormalizeAddRateDiagnostic =
  record
    { State =
        NormalizeAddState
    ; stateSurfaceFixed =
        refl
    ; normalizeStep =
        normalizeAdd
    ; normalizeStepFixed =
        refl
    ; convergenceRate =
        λ _ → suc zero
    ; rateLaw =
        λ _ → refl
    ; canonicalAfterOneStep =
        normalizeAdd-canonical
    ; canonicalSelfTransport =
        normalizeAdd
    ; selfTransportIsNormalizeAdd =
        refl
    ; selfTransportRatePreserved =
        λ _ → refl
    ; sumPreservationReceipt =
        canonicalNormalizeAddSumPreservationReceipt
    ; noCarrierParameterFoundInPrimarySurface =
        tt
    ; noNontrivialTransportFoundInArithmeticSearch =
        tt
    ; diagnosticNotes =
        "NormalizeAddState is a concrete record in DASHI.Arithmetic.NormalizeAddState, with no carrier-realization parameter"
        ∷ "normalizeAdd has type NormalizeAddState -> NormalizeAddState and is the only arithmetic endomap found by the lane search"
        ∷ "the local rate is the one-step canonical landing already proved by normalizeAdd-canonical"
        ∷ "canonical self-transport is normalizeAdd itself, so the constant one-step rate is preserved by refl"
        ∷ "this surface supports W2 authority assembly but does not construct that authority token"
        ∷ []
    ; noW2PromotionAuthorityConstructed =
        tt
    }

newtonConsumableUniformRateSurface :
  UniformNormalizeAddRateDiagnostic
newtonConsumableUniformRateSurface =
  canonicalUniformNormalizeAddRateDiagnostic

uniformRateSurfaceDoesNotPromoteW2 :
  UniformNormalizeAddRateDiagnostic.noW2PromotionAuthorityConstructed
    canonicalUniformNormalizeAddRateDiagnostic
  ≡ tt
uniformRateSurfaceDoesNotPromoteW2 = refl
