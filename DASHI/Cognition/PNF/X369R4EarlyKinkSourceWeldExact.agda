{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.X369R4EarlyKinkSourceWeldExact where

------------------------------------------------------------------------
-- Reuse original DASHI.Cognition.ResponseKink (not the unrelated
-- DASHI.Cognition.Utterance.AdmissibilityGate).
--
-- Typed observer interface: an original R4 source consumer is only
-- promoted to the early facilitation-before-suppression contract
-- when an actual SAME-RESPONSE four-regime witness is provided.
--
-- NO theorem that GELU alone, history cap, trained router, source
-- logits, or any biological response is overload-suppressing.
-- The attached SymPy development independently supplies a rational
-- envelope candidate, not a source-checkpoint receipt.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Cognition.ResponseKink as Kink

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

record OriginalR4FourRegimeEvidence (State : Set) : Set₁ where
  field
    originalResponse : State → Nat
    originalShape : Kink.RecruitmentSuppressionProfile State
    sameOriginalResponse :
      (state : State) →
      Kink.response originalShape state ≡ originalResponse state

open OriginalR4FourRegimeEvidence public

-- This does not construct a response shape from four unrelated
-- source scores. It transports the existing canonical witness along
-- an explicitly supplied equality with the actual source observable.
sameSourceR4RiseAndOverload :
  ∀ {State : Set} (e : OriginalR4FourRegimeEvidence State) →
  (originalResponse e (Kink.lowInput (originalShape e))
   < originalResponse e (Kink.prePeakInput (originalShape e)))
  × ((originalResponse e (Kink.prePeakInput (originalShape e))
      < originalResponse e (Kink.peakInput (originalShape e)))
     × (originalResponse e (Kink.overloadInput (originalShape e))
        < originalResponse e (Kink.peakInput (originalShape e))))
sameSourceR4RiseAndOverload e
  rewrite sym (sameOriginalResponse e
    (Kink.lowInput (originalShape e)))
        | sym (sameOriginalResponse e
    (Kink.prePeakInput (originalShape e)))
        | sym (sameOriginalResponse e
    (Kink.peakInput (originalShape e)))
        | sym (sameOriginalResponse e
    (Kink.overloadInput (originalShape e))) =
  Kink.profile-shape (originalShape e)

------------------------------------------------------------------------
-- Source admission is a separate obligation: the real R4 step must
-- choose an observable/ordered load family, and prove this evidence.
-- This module does NOT assert that such a record is inhabited by
-- original HistoryOrbitMoE or by an HPA/cortisol model.
--
-- The source's GELU is a nonnegative-input increasing gate;
-- the observed decreasing overload limb must have independently
-- sourced attenuation, competition, hysteresis, feedback or
-- a measured change in the full router/expert consumer.
------------------------------------------------------------------------
