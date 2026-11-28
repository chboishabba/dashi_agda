module DASHI.Cognition.PNF.X369WholeSourceIndexedTransportExact where

-- Exact retained source transport, independent semantic context.
-- Original Leech-LILA: Anatolii Kornienko. DASHI extension.
-- Reuse original input-indexed trace semantics. The concrete section
-- must supply a genuine retraction; no reduced-state descent assumed.
-- SLR source and physical/refinement/time indices remain independent.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as Future

module ExactTransport
  (H C S U O : Set)
  (encode : H → C)
  (decode : C → H)
  (decodeEncode : (h : H) → decode (encode h) ≡ h)
  (step : U → H → H)
  (observe : U → H → O)
  (semanticStep : U → S → S) where

  Joint : Set
  Joint = H × S

  Packet : Set
  Packet = C × S

  pack : Joint → Packet
  pack (h , s) = encode h , s

  reopen : Packet → Joint
  reopen (c , s) = decode c , s

  jointStep : U → Joint → Joint
  jointStep u (h , s) = step u h , semanticStep u s

  jointObserve : U → Joint → O
  jointObserve u (h , s) = observe u h

  packetStep : U → Packet → Packet
  packetStep u p = pack (jointStep u (reopen p))

  packetObserve : U → Packet → O
  packetObserve u p = jointObserve u (reopen p)

  exactJointReopen : (j : Joint) → reopen (pack j) ≡ j
  exactJointReopen (h , s) = Future.cong (λ x → x , s) (decodeEncode h)

  sourceStepSquare : (u : U) (j : Joint) →
    packetStep u (pack j) ≡ pack (jointStep u j)
  sourceStepSquare u j =
    Future.cong (λ x → pack (jointStep u x)) (exactJointReopen j)

  sourceObserveSquare : (u : U) (j : Joint) →
    packetObserve u (pack j) ≡ jointObserve u j
  sourceObserveSquare u j = Future.cong (jointObserve u) (exactJointReopen j)

  jointAdvance : List U → Joint → Joint
  jointAdvance [] j = j
  jointAdvance (u ∷ us) j = jointAdvance us (jointStep u j)

  packetAdvance : List U → Packet → Packet
  packetAdvance [] p = p
  packetAdvance (u ∷ us) p = packetAdvance us (packetStep u p)

  everyPacketEndpoint : (us : List U) (j : Joint) →
    packetAdvance us (pack j) ≡ pack (jointAdvance us j)
  everyPacketEndpoint [] j = refl
  everyPacketEndpoint (u ∷ us) j rewrite sourceStepSquare u j =
    everyPacketEndpoint us (jointStep u j)

  everyOriginalReadout : (us : List U) (j : Joint) →
    Future.trace packetStep packetObserve us (pack j) ≡
    Future.trace jointStep jointObserve us j
  everyOriginalReadout [] j = refl
  everyOriginalReadout (u ∷ us) j
    rewrite sourceObserveSquare u j | sourceStepSquare u j =
      Future.cong (λ tail → jointObserve u j ∷ tail)
        (everyOriginalReadout us (jointStep u j))

  everyNeuralReadout : (us : List U) (h : H) (s : S) →
    Future.trace jointStep jointObserve us (h , s) ≡
    Future.trace step observe us h
  everyNeuralReadout [] h s = refl
  everyNeuralReadout (u ∷ us) h s =
    Future.cong (λ tail → observe u h ∷ tail)
      (everyNeuralReadout us (step u h) (semanticStep u s))

  -- Equal original history does not force equal semantic/index context.
  -- The retained independent index component reopens without coercion.
  independentContextReopens : (h : H) (s : S) →
    proj₂ (reopen (pack (h , s))) ≡ s
  independentContextReopens h s = refl

  equalHistoryDifferentContext : (h : H) (s t : S) →
    proj₁ (reopen (pack (h , s))) ≡ proj₁ (reopen (pack (h , t)))
  equalHistoryDifferentContext h s t = refl

-- This closes the full RETAINED transport given decodeEncode. It does
-- not inhabit the actual SLR semantic readers or the concrete Python
-- codec's Agda retraction. Reduced K+orientation still needs both
-- source squares of X369InputIndexedFutureConsumerExact.
