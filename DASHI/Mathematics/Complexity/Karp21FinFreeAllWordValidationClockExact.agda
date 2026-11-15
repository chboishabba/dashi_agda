module DASHI.Mathematics.Complexity.Karp21FinFreeAllWordValidationClockExact where

------------------------------------------------------------------------
-- K05 N21 ORIGINAL GRAPH WORD: ALL-INPUT VALIDATOR COMPARISON CLOCK.
--
-- Mirror the original readRawGraphWord's actual gamma/count/edge/W
-- branches solely to COUNT primitive raw-validator comparisons.
-- All early rejections have zero raw-validator comparisons.
-- Even a word whose edge list is fully decoded but then REJECTED by
-- validRawEdges is charged for the same source-owned primitive checks.
--
-- The original 3m gamma guard and literal raw-edge count, rather
-- than a false bound on n, imply at most 5*inputBitLength tests.
-- Gamma parsing and binary arithmetic machine time are separate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21FinFreeGammaGeneralSparseBudgetExact as Budget
import DASHI.Mathematics.Complexity.Karp21FinFreeRawValidatorComparisonCountExact as Validate
open import Relation.Binary.PropositionalEquality using (cong)

-- FiniteWordSizeExact.wordLength and Data.List.length have the same
-- constructors but are distinct named recursive source functions.
inputListLengthIsWordSize :
  (word : Word.BitWord) → length word ≡ Word.encodingSize word
inputListLengthIsWordSize [] = refl
inputListLengthIsWordSize (_ ∷ rest)
  rewrite inputListLengthIsWordSize rest = refl

mBelowTriple : (m : Nat) → m ≤ m * 3
mBelowTriple m = NatP.m≤m+n m (m * 2)

-- Any successful original edge-list READ, even when graph validation
-- ultimately fails, fits in the actual source input bit budget.
rawFrameVertexCountIndependentBound :
  (word : Word.BitWord) (n m : Nat)
  (afterN afterM : Word.BitWord) →
  Gamma.readGamma word ≡ just (n , afterN) →
  Gamma.readGamma afterN ≡ just (m , afterM) →
  m * 3 ≤ length afterM →
  m ≤ Word.encodingSize word
rawFrameVertexCountIndependentBound word n m afterN afterM
  readN readM guard =
  NatP.≤-trans (mBelowTriple m)
    (NatP.≤-trans guard
      (NatP.≤-trans
        (Budget.readGammaSuffixWithinInput afterN m afterM readM)
        (NatP.≤-trans
          (Budget.readGammaSuffixWithinInput word n afterN readN)
          (NatP.≤-reflexive
            (inputListLengthIsWordSize word)))))

rawValidationCountBelowInput :
  (word : Word.BitWord) (n m : Nat)
  (afterN afterM afterEdges : Word.BitWord)
  (raw : List Graph.RawEdge) →
  Gamma.readGamma word ≡ just (n , afterN) →
  Gamma.readGamma afterN ≡ just (m , afterM) →
  m * 3 ≤ length afterM →
  Graph.readRawEdges m afterM ≡ just (raw , afterEdges) →
  proj₂ (Validate.countedRawValidatorPrimitive
    n Graph.noPrevious raw)
    ≤ 5 * Word.encodingSize word
rawValidationCountBelowInput word n m afterN afterM afterEdges raw
  readN readM guard readEdges =
  NatP.≤-trans
    (subst
      (λ count →
        proj₂ (Validate.countedRawValidatorPrimitive
          n Graph.noPrevious raw) ≤ 5 * count)
      (Budget.readRawEdgesCountExact m afterM raw afterEdges readEdges)
      (Validate.primitiveValidatorCountBound
        n Graph.noPrevious raw))
    (NatP.*-mono-≤
      NatP.≤-refl
      (rawFrameVertexCountIndependentBound
        word n m afterN afterM readN readM guard))

-- This mirrors the exact parser decision path through the point where
-- Runtime.validRawEdges is called. It is a COUNT of that validator's
-- primitive tests, not a general parser runtime cost.
originalRawValidationCountForWord : Word.BitWord → Nat
originalRawValidationCountForWord word
  with Gamma.readGamma word
... | nothing = zero
... | just (n , afterN)
  with Gamma.readGamma afterN
...   | nothing = zero
...   | just (m , afterM)
  with NatP._≤?_ (m * 3) (length afterM)
...     | no _ = zero
...     | yes _ with Graph.readRawEdges m afterM
...       | nothing = zero
...       | just (raw , afterEdges)
  with Gamma.readGamma afterEdges
...         | nothing = zero
...         | just (zero , _) = zero
...         | just (suc threshold , _ ∷ _) = zero
...         | just (suc threshold , []) =
  proj₂ (Validate.countedRawValidatorPrimitive
    n Graph.noPrevious raw)

-- Universal input-length bound, including invalid canonical edge order
-- and out-of-range endpoint cases that reach the validator and reject.
originalAllWordRawValidationCountBound :
  (word : Word.BitWord) →
  originalRawValidationCountForWord word
    ≤ 5 * Word.encodingSize word
originalAllWordRawValidationCountBound word
  with Gamma.readGamma word in readN
... | nothing = z≤n
... | just (n , afterN)
  with Gamma.readGamma afterN in readM
...   | nothing = z≤n
...   | just (m , afterM)
  with NatP._≤?_ (m * 3) (length afterM)
...     | no _ = z≤n
...     | yes tripleGuard
  with Graph.readRawEdges m afterM in readEdges
...       | nothing = z≤n
...       | just (raw , afterEdges)
  with Gamma.readGamma afterEdges
...         | nothing = z≤n
...         | just (zero , _) = z≤n
...         | just (suc threshold , _ ∷ _) = z≤n
...         | just (suc threshold , []) =
  rawValidationCountBelowInput
    word n m afterN afterM afterEdges raw
    readN readM tripleGuard readEdges
