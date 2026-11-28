module DASHI.Cognition.PNF.X369JointIndexedConsumerClosureExact where

-- Complete retained joint transport, including context-sensitive readouts
-- and transitions. Reuse the original input-indexed future theorem and
-- the previous exact H × S codec. Unlike a neural-only observation,
-- the consumer may read every independently retained source coordinate.
-- Original Leech-LILA: Anatolii Kornienko. DASHI extension.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as F
import DASHI.Cognition.PNF.X369WholeSourceIndexedTransportExact as W

module Retained
  (H C S U O : Set)
  (encode : H → C)
  (decode : C → H)
  (decodeEncode : (h : H) → decode (encode h) ≡ h)
  (sourceStep : U → H × S → H × S)
  (sourceObserve : U → H × S → O)
  where

  -- Instantiate the existing product codec with identity observations.
  -- Real joint dynamics and readout are independent of this specialization.
  module Codec = W.ExactTransport H C S U H
    encode decode decodeEncode (λ _ h → h) (λ _ h → h) (λ _ s → s)

  open Codec using (Joint; Packet; pack; reopen)

  section : (j : Joint) → reopen (pack j) ≡ j
  section = Codec.exactJointReopen

  packetStep : U → Packet → Packet
  packetStep u p = pack (sourceStep u (reopen p))

  packetObserve : U → Packet → O
  packetObserve u p = sourceObserve u (reopen p)

  stepSquare : (u : U) (j : Joint) →
    packetStep u (pack j) ≡ pack (sourceStep u j)
  stepSquare u j = F.cong (λ x → pack (sourceStep u x)) (section j)

  observeSquare : (u : U) (j : Joint) →
    packetObserve u (pack j) ≡ sourceObserve u j
  observeSquare u j = F.cong (sourceObserve u) (section j)

  advance : ∀ {A : Set} → (U → A → A) → List U → A → A
  advance step [] j = j
  advance step (u ∷ us) j = advance step us (step u j)

  exactEndpoint : (us : List U) (j : Joint) →
    advance packetStep us (pack j) ≡ pack (advance sourceStep us j)
  exactEndpoint [] j = refl
  exactEndpoint (u ∷ us) j rewrite stepSquare u j =
    exactEndpoint us (sourceStep u j)

  exactJointTrace : (us : List U) (j : Joint) →
    F.trace packetStep packetObserve us (pack j) ≡
    F.trace sourceStep sourceObserve us j
  exactJointTrace [] j = refl
  exactJointTrace (u ∷ us) j rewrite observeSquare u j | stepSquare u j =
    F.cong (λ tail → sourceObserve u j ∷ tail)
      (exactJointTrace us (sourceStep u j))

  independentContext : (h : H) (s : S) →
    proj₂ (reopen (pack (h , s))) ≡ s
  independentContext h s = refl

  -- This is the exact reduced-geometry endpoint: both original joint
  -- one-step squares, not a separate assertion of semantic equivalence.
  reducedFuture :
    {Q : Set} (chart : Joint → Q) →
    ((u : U) (x y : Joint) → chart x ≡ chart y →
      sourceObserve u x ≡ sourceObserve u y) →
    ((u : U) (x y : Joint) → chart x ≡ chart y →
      chart (sourceStep u x) ≡ chart (sourceStep u y)) →
    (x y : Joint) → chart x ≡ chart y →
    F.TraceEquivalent sourceStep sourceObserve x y
  reducedFuture chart outputs transitions =
    F.everyStableCodecFibreIsTraceEquivalent
      sourceStep sourceObserve chart outputs transitions

  -- Equal history, different context: if a source consumer can
  -- distinguish at one step, any history-only code necessarily fails.
  historyOnlyRefuted :
    (h : H) (s t : S) (u : U) →
    (sourceObserve u (h , s) ≡ sourceObserve u (h , t) → ⊥) →
    ((x y : Joint) → encode (proj₁ x) ≡ encode (proj₁ y) →
      F.TraceEquivalent sourceStep sourceObserve x y) → ⊥
  historyOnlyRefuted h s t u different sound =
    different (F.traceEquivalentObserves sourceStep sourceObserve
      (h , s) (h , t) (sound (h , s) (h , t) refl) u)
