module DASHI.Mathematics.Complexity.Karp21MaxCutCertificateBinaryCodecExact where

------------------------------------------------------------------------
-- N21: a TOTAL, exact n-bit Boolean cut-certificate Word codec.
--
-- Reuses actual Karp21FiniteWeightedMaxCutVerifierExact (the same
-- signed finite graph, certificate vector, threshold, and verifier).
-- Reuses the repo's earlier PNotEqualsNPCookFormulaBinaryCodecExact
-- practice of List Bool bit words + exact decode/encode theorems.
--
-- Only an EXACTLY n-bit input is accepted for graph dimension n.
-- Wrong length (including appended bytes) fails closed, not silently
-- truncated. The decoder is structurally recursive and source-written.
--
-- Bit length and certificate faithfulness are proved. A *machine*
-- polynomial verifier clock and the graph's own canonical binary Word
-- encoding are still separate obligations; no InNP is fabricated.
--
-- Original N21: Richard M. Karp, 1972.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base as List using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (Σ; _,_)
open import Data.Bool.Base using (T)
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)

import Data.Vec.Base as Vec
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21FiniteCliqueVertexCoverCombinedExact as Finite

-- The existing N21 witness is Vec Bool n, so its canonical Word is
-- literally its n Boolean coordinates; no information is discarded.
encodeCutLabels :
  ∀ {n} → Vec.Vec Bool n → List Bool
encodeCutLabels = Vec.toList

-- Exact-length total parser. Reject every malformed certificate length.
decodeCutLabels :
  (n : Nat) → List Bool → Maybe (Vec.Vec Bool n)
decodeCutLabels zero [] = just Vec.[]
decodeCutLabels zero (_ ∷ _) = nothing
decodeCutLabels (suc n) [] = nothing
decodeCutLabels (suc n) (bit ∷ tail)
  with decodeCutLabels n tail
... | nothing = nothing
... | just labels = just (bit Vec.∷ labels)

-- Unique canonical bit encoding for every vector of Boolean labels.
decodeEncodeCutLabels :
  ∀ {n} (labels : Vec.Vec Bool n) →
  decodeCutLabels n (encodeCutLabels labels) ≡ just labels
decodeEncodeCutLabels Vec.[] = refl
decodeEncodeCutLabels (bit Vec.∷ tail)
  rewrite decodeEncodeCutLabels tail = refl

cutCertificateWordLength :
  ∀ {n} (labels : Vec.Vec Bool n) →
  length (encodeCutLabels labels) ≡ n
cutCertificateWordLength labels =
  Finite.selectionListLength labels

-- A word's extra trailing bit cannot be silently ignored, including
-- the empty (n=0) case. This distinguishes exact parsing from prefix
-- token decoding in the earlier Cook formula codec.
rejectTrailingCertificateBit :
  ∀ {n} (labels : Vec.Vec Bool n) (extra : Bool) →
  decodeCutLabels n
    (encodeCutLabels labels ++ (extra ∷ [])) ≡ nothing
rejectTrailingCertificateBit Vec.[] extra = refl
rejectTrailingCertificateBit (bit Vec.∷ tail) extra
  rewrite rejectTrailingCertificateBit tail extra = refl

-- There is deliberately no spare leading or ignored certificate data.
wordCutVerifier :
  ∀ {n} (graph : Cut.WeightedCutGraph n) →
  List Bool → Bool
wordCutVerifier {n} graph bits
  with decodeCutLabels n bits
... | nothing = false
... | just labels = Cut.verifyWeightedMaxCut graph labels

AcceptedWordCut :
  ∀ {n} (graph : Cut.WeightedCutGraph n) →
  List Bool → Set
AcceptedWordCut graph bits = T (wordCutVerifier graph bits)

wordAcceptanceSound :
  ∀ {n} (graph : Cut.WeightedCutGraph n)
    (bits : List Bool) →
  AcceptedWordCut graph bits →
  Cut.WeightedMaxCutYES graph
wordAcceptanceSound {n} graph bits accepted
  with decodeCutLabels n bits
... | nothing = ⊥-elim accepted
... | just labels =
  labels , Cut.weightedMaxCutVerifierSound graph labels accepted

encodeSoundWitness :
  ∀ {n} (graph : Cut.WeightedCutGraph n)
    (labels : Vec.Vec Bool n) →
  T (Cut.verifyWeightedMaxCut graph labels) →
  AcceptedWordCut graph (encodeCutLabels labels)
encodeSoundWitness graph labels verifies
  rewrite decodeEncodeCutLabels labels = verifies

wordAcceptanceComplete :
  ∀ {n} (graph : Cut.WeightedCutGraph n) →
  Cut.WeightedMaxCutYES graph →
  Σ (List Bool) (AcceptedWordCut graph)
wordAcceptanceComplete graph (labels , accepted) =
  encodeCutLabels labels ,
  encodeSoundWitness graph labels
    (Cut.weightedMaxCutVerifierComplete graph labels accepted)

-- An existential Boolean bitstring certificate witnesses *exactly*
-- the earlier graph cut predicate, not an independent approximation.
N21WordCertificateYES :
  ∀ {n} (graph : Cut.WeightedCutGraph n) → Set
N21WordCertificateYES graph =
  Σ (List Bool) (AcceptedWordCut graph)

n21PackedCertificateYESIff :
  ∀ {n} (graph : Cut.WeightedCutGraph n) →
  PR.Iff
    (Cut.WeightedMaxCutYES graph)
    (N21WordCertificateYES graph)
n21PackedCertificateYESIff graph =
  PR.iff
    (wordAcceptanceComplete graph)
    (λ { (bits , accepted) →
      wordAcceptanceSound graph bits accepted })
