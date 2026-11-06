module DASHI.Mathematics.Complexity.Karp21FinFreeGammaGeneralSparseBudgetExact where

------------------------------------------------------------------------
-- N21 ORIGINAL GAMMA GRAPH CODE: 2m SPARSE-CERTIFICATE BUDGET IS
-- FORCED BY THE EXISTING 3m EDGE-TRIPLE HEADER GUARD.
--
-- Unlike the E20-image certificate proof, this works for EVERY
-- successfully read original raw edge-list frame. Its vertex count n
-- may be exponentially large compared with the input bit length:
-- the bound is on m (actual listed edges), not on n.
--
-- No alternate gamma parser, graph language, oracle or constant-time
-- binary Nat operations are assumed. The actual original readers are
-- Gamma.readGamma/Graph.readRawEdges, and the actual dependent
-- certificate size is Sparse.twoPerEdge.
--
-- Source-written candidate; pinned Agda kernel check not yet run.
-- Karp (1972), Elias gamma, original DASHI literal parser owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse

nothingNotJust :
  ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothingNotJust ()

lengthAtMostSuccessor :
  (n : Nat) → n ≤ suc n
lengthAtMostSuccessor zero = z≤n
lengthAtMostSuccessor (suc n) =
  s≤s (lengthAtMostSuccessor n)

-- Literal low-bit payload recursion NEVER increases the suffix.
readLowBitsSuffixWithinInput :
  (count : Nat) (word : Word.BitWord)
  (value : Nat) (suffix : Word.BitWord) →
  Gamma.readLowBits count word ≡ just (value , suffix) →
  length suffix ≤ length word
readLowBitsSuffixWithinInput zero word .zero .word refl =
  NatP.≤-refl
readLowBitsSuffixWithinInput (suc count) [] value suffix ()
readLowBitsSuffixWithinInput
    (suc count) (bit ∷ rest) value suffix accepted
  with Gamma.readLowBits count rest
... | nothing = ⊥-elim (nothingNotJust accepted)
... | just (low , afterLow) with accepted
...   | refl =
  NatP.≤-trans
    (readLowBitsSuffixWithinInput count rest low afterLow refl)
    (lengthAtMostSuccessor (length rest))

-- Both the leading-zero prefix scanner and the binary payload
-- scanner preserve a suffix of the SAME actual input bit list.
readGammaZerosSuffixWithinInput :
  (seen : Nat) (word : Word.BitWord)
  (value : Nat) (suffix : Word.BitWord) →
  Gamma.readGammaZeros seen word ≡ just (value , suffix) →
  length suffix ≤ length word
readGammaZerosSuffixWithinInput seen [] value suffix ()
readGammaZerosSuffixWithinInput
    seen (false ∷ rest) value suffix accepted =
  NatP.≤-trans
    (readGammaZerosSuffixWithinInput
      (suc seen) rest value suffix accepted)
    (lengthAtMostSuccessor (length rest))
readGammaZerosSuffixWithinInput
    seen (true ∷ rest) value suffix accepted
  with Gamma.readLowBits seen rest
... | nothing = ⊥-elim (nothingNotJust accepted)
... | just (low , afterLow) with accepted
...   | refl =
  NatP.≤-trans
    (readLowBitsSuffixWithinInput seen rest low afterLow refl)
    (lengthAtMostSuccessor (length rest))

readGammaSuffixWithinInput :
  (word : Word.BitWord) (value : Nat) (suffix : Word.BitWord) →
  Gamma.readGamma word ≡ just (value , suffix) →
  length suffix ≤ length word
readGammaSuffixWithinInput word value suffix accepted =
  readGammaZerosSuffixWithinInput zero word value suffix accepted

-- The actual Graph.readRawEdges returns EXACTLY m raw edges after
-- consuming their original signed gamma triples.
readRawEdgesCountExact :
  (m : Nat) (word : Word.BitWord)
  (edges : List Graph.RawEdge) (suffix : Word.BitWord) →
  Graph.readRawEdges m word ≡ just (edges , suffix) →
  length edges ≡ m
readRawEdgesCountExact zero word .[] .word refl = refl
readRawEdgesCountExact (suc m) word edges suffix accepted
  with Graph.readOneRawEdge word
... | nothing = ⊥-elim (nothingNotJust accepted)
... | just (edge , afterEdge)
  with Graph.readRawEdges m afterEdge
...   | nothing = ⊥-elim (nothingNotJust accepted)
...   | just (tail , afterTail) with accepted
...     | refl =
  cong suc (readRawEdgesCountExact m afterEdge tail afterTail refl)

-- A valid listed edge needs two witness bits but at least three
-- original gamma fields. This exact unary recurrence matches the
-- *original* Graph 3m guard, without an arithmetic-resource oracle.
twoPerEdgeWithinTripleBudget :
  (m : Nat) →
  Sparse.twoPerEdge m ≤ m * suc (suc (suc zero))
twoPerEdgeWithinTripleBudget zero = z≤n
twoPerEdgeWithinTripleBudget (suc m) =
  NatP.≤-step
    (s≤s (s≤s (twoPerEdgeWithinTripleBudget m)))

-- Core generic gate: ORIGINAL two gamma header reads plus the
-- ORIGINAL 3m guard force Sparse.twoPerEdge (length returned edges)
-- ≤ length of SAME whole graph word.
originalGammaFrameHasSparseBudget :
  (word : Word.BitWord) (n m : Nat)
  (afterN afterM afterEdges : Word.BitWord)
  (raw : List Graph.RawEdge) →
  Gamma.readGamma word ≡ just (n , afterN) →
  Gamma.readGamma afterN ≡ just (m , afterM) →
  m * suc (suc (suc zero)) ≤ length afterM →
  Graph.readRawEdges m afterM ≡ just (raw , afterEdges) →
  Sparse.twoPerEdge (length raw) ≤ Word.encodingSize word
originalGammaFrameHasSparseBudget
    word n m afterN afterM afterEdges raw
    readN readM tripleGuard readEdges =
  NatP.≤-trans
    (NatP.≤-reflexive
      (cong Sparse.twoPerEdge
        (readRawEdgesCountExact m afterM raw afterEdges readEdges)))
    (NatP.≤-trans
      (twoPerEdgeWithinTripleBudget m)
      (NatP.≤-trans tripleGuard
        (NatP.≤-trans
          (readGammaSuffixWithinInput afterN m afterM readM)
          (readGammaSuffixWithinInput word n afterN readN))))
