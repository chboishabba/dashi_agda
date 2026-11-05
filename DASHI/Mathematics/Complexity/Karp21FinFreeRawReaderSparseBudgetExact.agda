module DASHI.Mathematics.Complexity.Karp21FinFreeRawReaderSparseBudgetExact where

------------------------------------------------------------------------
-- N21: ANY SUCCESSFUL ACTUAL FIN-FREE GRAPH WORD HAS A 2m-BIT BUDGET.
--
-- This is independent of complete E20 images and does not require the
-- caller to supply header fields, a certificate length receipt or an
-- arbitrary bounded-n assumption. The original Runtime.readRawGraphWord
-- itself runs the source 3m guard after reading gamma(n), gamma(m).
-- The source-owned readGamma/readRawEdges suffix lemmas turn this into
-- Sparse.twoPerEdge (length returned raw edges) ≤ |original word|.
--
-- Malformed inputs give a vacuous result, not a fabricated parsed
-- graph or a new graph word grammar. Still NO binary tape clock.
-- Source-written, unverified by Agda kernel. Karp 1972; DASHI codecs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Nat using (zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Nat.Base using (_≤_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
import Data.Nat.Properties as NatP
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21FinFreeGammaGeneralSparseBudgetExact as Budget

RawReaderSparseBudget :
  (word : Word.BitWord) →
  Maybe Runtime.ParsedRawGraph → Set
RawReaderSparseBudget word nothing = ⊤
RawReaderSparseBudget word (just graph) =
  Sparse.twoPerEdge (length (Runtime.rawEdges graph))
    ≤ Word.encodingSize word

rawReaderBudgetOutcome :
  (word : Word.BitWord) →
  RawReaderSparseBudget word (Runtime.readRawGraphWord word)
rawReaderBudgetOutcome word
  with Gamma.readGamma word in readN
... | nothing = tt
... | just (n , afterN)
  with Gamma.readGamma afterN in readM
...   | nothing = tt
...   | just (m , afterM)
  with NatP._≤?_ (m * suc (suc (suc zero))) (length afterM)
...     | no insufficient = tt
...     | yes tripleBudget
  with Graph.readRawEdges m afterM in readEdges
...       | nothing = tt
...       | just (raw , afterEdges)
  with Gamma.readGamma afterEdges
...         | nothing = tt
...         | just (zero , _) = tt
...         | just (suc k , [])
  with Runtime.validRawEdges n Graph.noPrevious raw
...           | false = tt
...           | true =
  Budget.originalGammaFrameHasSparseBudget
    word n m afterN afterM afterEdges raw
    readN readM tripleBudget readEdges
...         | just (suc k , _ ∷ _) = tt

actualFinFreeRawGraphSuccessHasSparseBudget :
  (word : Word.BitWord)
  (graph : Runtime.ParsedRawGraph) →
  Runtime.readRawGraphWord word ≡ just graph →
  Sparse.twoPerEdge (length (Runtime.rawEdges graph))
    ≤ Word.encodingSize word
actualFinFreeRawGraphSuccessHasSparseBudget word graph accepted =
  subst (RawReaderSparseBudget word) accepted
    (rawReaderBudgetOutcome word)
