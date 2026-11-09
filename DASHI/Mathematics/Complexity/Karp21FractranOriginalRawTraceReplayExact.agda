module DASHI.Mathematics.Complexity.Karp21FractranOriginalRawTraceReplayExact where

------------------------------------------------------------------------
-- Original N21: lossless score-observation trace of selected cut edges.
--
-- Replay the ACTUAL chronological endpointConsistent checks and the
-- ACTUAL exactly-two-label-bits-per-raw-edge certificate framing.
-- On a valid trace, retain the original signed ℤ contributions in
-- the same tail-recursive order as rawSparseScore. On a rejected
-- trace, return nothing. This covers arbitrary RAW edge lists,
-- histories, and certificate bits, including malformed short/long
-- certificates, without assuming a parsed graph is well formed.
--
-- This is a concrete original-ℤ trace reconstruction theorem.
-- It is NOT yet the gamma signed binary-ledger correspondence, a
-- FRACTRAN cost bound, or original graph-word parser equivalence.
-- Karp (1972); DASHI source original rawSparseScore owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.Integer.Base as Int using (ℤ; +_; _+_)
open import Relation.Binary.PropositionalEquality using (sym; cong)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime

-- Each trace row is the original signed edge weight of a selected cut
-- edge. Non-cut edges contribute no row, not an invented zero weight.
rawSelectedTrace :
  List Graph.RawEdge →
  Word.BitWord →
  List (Agda.Builtin.Nat.Nat × Bool) →
  Maybe (List ℤ)
rawSelectedTrace [] [] history = just []
rawSelectedTrace [] (_ ∷ _) history = nothing
rawSelectedTrace (_ ∷ _) [] history = nothing
rawSelectedTrace (_ ∷ _) (_ ∷ []) history = nothing
rawSelectedTrace (Graph.raw-edge u v w ∷ edges) (a ∷ b ∷ bits) history
  with Runtime.endpointConsistent u a history
     | Runtime.endpointConsistent v b history
... | false | _ = nothing
... | true | false = nothing
... | true | true
  with rawSelectedTrace edges bits ((u , a) ∷ (v , b) ∷ history)
...   | nothing = nothing
...   | just selected with Boolean.boolEqual a b
...     | true = just selected
...     | false = just (w ∷ selected)

replayOriginalSignedTrace : List ℤ → ℤ
replayOriginalSignedTrace [] = + zero
replayOriginalSignedTrace (w ∷ rest) =
  w + replayOriginalSignedTrace rest

decodeTraceScore : Maybe (List ℤ) → Maybe ℤ
decodeTraceScore nothing = nothing
decodeTraceScore (just selected) = just (replayOriginalSignedTrace selected)

-- The source recursion is matched literally, not inferred from tests
-- or an abstract score model. The IH specializes to the ACTUAL
-- twice-extended original chronological endpoint history.
rawSelectedTraceRebuildsOriginalScore :
  (edges : List Graph.RawEdge)
  (bits : Word.BitWord)
  (history : List (Agda.Builtin.Nat.Nat × Bool)) →
  decodeTraceScore (rawSelectedTrace edges bits history)
    ≡ Runtime.rawSparseScore edges bits history
rawSelectedTraceRebuildsOriginalScore [] [] history = refl
rawSelectedTraceRebuildsOriginalScore [] (_ ∷ _) history = refl
rawSelectedTraceRebuildsOriginalScore (_ ∷ _) [] history = refl
rawSelectedTraceRebuildsOriginalScore (_ ∷ _) (_ ∷ []) history = refl
rawSelectedTraceRebuildsOriginalScore
  (Graph.raw-edge u v w ∷ edges) (a ∷ b ∷ bits) history
  with Runtime.endpointConsistent u a history
     | Runtime.endpointConsistent v b history
... | false | _ = refl
... | true | false = refl
... | true | true
  with rawSelectedTrace edges bits ((u , a) ∷ (v , b) ∷ history)
     | rawSelectedTraceRebuildsOriginalScore
         edges bits ((u , a) ∷ (v , b) ∷ history)
...   | nothing | induction rewrite sym induction = refl
...   | just selected | induction with Boolean.boolEqual a b
...     | true rewrite sym induction = refl
...     | false rewrite sym induction = refl

------------------------------------------------------------------------
-- Whole ORIGINAL gamma graph-word and sparse certificate decision.
-- The grammar is not changed: use Runtime.readRawGraphWord itself,
-- including its positive-threshold and exact-end-of-word policy.
------------------------------------------------------------------------

verifyOriginalGraphWordByTrace :
  Word.BitWord → Word.BitWord → Bool
verifyOriginalGraphWordByTrace word certificate
  with Runtime.readRawGraphWord word
... | nothing = false
... | just graph
  with rawSelectedTrace (Runtime.rawEdges graph) certificate []
...   | nothing = false
...   | just trace =
  Int._≤ᵇ_ (+ (Runtime.positiveThreshold graph))
    (replayOriginalSignedTrace trace)

-- This is an exact all-word ACCEPTANCE theorem for the original-ℤ
-- trace replay against the original Fin-free rawScore verifier.
-- It deliberately does NOT assert binary-native gamma-value equality.
karpOriginalRawTraceAllWordAcceptance :
  (word certificate : Word.BitWord) →
  verifyOriginalGraphWordByTrace word certificate
    ≡ Runtime.verifyFinFreeSparseGraphWord word certificate
karpOriginalRawTraceAllWordAcceptance word certificate
  with Runtime.readRawGraphWord word
... | nothing = refl
... | just graph
  with rawSelectedTrace (Runtime.rawEdges graph) certificate []
     | rawSelectedTraceRebuildsOriginalScore
         (Runtime.rawEdges graph) certificate []
...   | nothing | equation rewrite sym equation = refl
...   | just trace | equation rewrite sym equation = refl
