module DASHI.Mathematics.Complexity.Karp21FinFreeAllWordDecoderAgreementExact where

------------------------------------------------------------------------
-- N21: TOTAL SAME-ORIGINAL-GRAPH-WORD DECODER ALIGNMENT.
--
-- Exhaustive case analysis follows the *actual* two nested gamma
-- readers. No alternative grammar/graph is introduced. On malformed
-- words both reject; on all accepted raw words, original 3m header
-- guard automatically supplies the original typed 2m sparse budget,
-- and both actual readers return matched signed raw/Fin edge fields.
--
-- Proof invokes the already-written general all-raw validator and
-- successful gamma-frame composition. This is semantically separate
-- from the physical binary-tape runtime clock and Golden acceptance.
-- Source-written only, no exact-head Agda compiler receipt.
-- Source: Karp (1972), original DASHI literal gamma graph readers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Nat.Base using (_≤_; z≤n)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable.Core using (yes; no)
import Data.Nat.Properties as NatP
import Data.Integer.Base as Int

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21RawGraphValidatorObservationExact as Observe
import DASHI.Mathematics.Complexity.Karp21FinFreeAllRawValidatorAgreementExact as AllRaw
import DASHI.Mathematics.Complexity.Karp21FinFreeAllGammaSuccessAgreementExact as AllFrame

-- This lemma handles the ONLY discrepant validation branch: the
-- original raw checker returns false, and the dependent original
-- decoder must reject after running its SAME numeric and Fin checks.
originalTypedDecoderRejectsInvalidRawFrame :
  (word : Word.BitWord) (n m k : Nat)
  (afterN afterM afterEdges : Word.BitWord)
  (raw : List Graph.RawEdge) →
  Gamma.readGamma word ≡ just (n , afterN) →
  Gamma.readGamma afterN ≡ just (m , afterM) →
  m * suc (suc (suc zero)) ≤ length afterM →
  Graph.readRawEdges m afterM ≡ just (raw , afterEdges) →
  Gamma.readGamma afterEdges ≡ just (suc k , []) →
  Graph.validateRawEdges n Graph.noPrevious raw ≡ nothing →
  Graph.decodeGraphWord word ≡ nothing
originalTypedDecoderRejectsInvalidRawFrame
    word n m k afterN afterM afterEdges raw
    readN readM tripleBudget readEdges readW rawReject
  rewrite readN | readM
  with NatP._≤?_ (m * suc (suc (suc zero))) (length afterM)
... | no impossible = ⊥-elim (impossible tripleBudget)
... | yes _
  rewrite readEdges | readW | rawReject = refl

-- A fully justified result about BOTH ORIGINAL functions for a given
-- original graph word. The parsed constructor retains exact returned
-- *same-word* equations plus fieldwise signed information, not graph
-- equality including offDiagonal proof functions.
data OriginalN21ReaderAgreement (word : Word.BitWord) : Set where
  jointlyRejected :
    Graph.decodeGraphWord word ≡ nothing →
    Runtime.readRawGraphWord word ≡ nothing →
    OriginalN21ReaderAgreement word
  jointlyParsed :
    (n k : Nat)
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n)) →
    Runtime.readRawGraphWord word
      ≡ just (Runtime.parsed-raw-graph n raw (suc k)) →
    Graph.decodeGraphWord word
      ≡ just (n , Cut.graph typed (Int.+ (suc k))
        (Int.+≤+ z≤n , (λ ()))) →
    Observe.RawEdgeListFieldsSame raw typed →
    OriginalN21ReaderAgreement word

-- Universal original graph-word case distinction:
--   both reject OR the same signed edge/threshold frame is returned.
-- Truncated gamma, 3m guard failure, missing edges, W=0, trailing
-- bits, loops/reversed/out-of-range/duplicate/unsorted edges included.
allOriginalN21GraphWordsAgree :
  (word : Word.BitWord) → OriginalN21ReaderAgreement word
allOriginalN21GraphWordsAgree word
  with Gamma.readGamma word in readN
... | nothing = jointlyRejected refl refl
... | just (n , afterN)
  with Gamma.readGamma afterN in readM
...   | nothing = jointlyRejected refl refl
...   | just (m , afterM)
  with NatP._≤?_ (m * suc (suc (suc zero))) (length afterM)
...     | no insufficient = jointlyRejected refl refl
...     | yes tripleBudget
  with Graph.readRawEdges m afterM in readEdges
...       | nothing = jointlyRejected refl refl
...       | just (raw , afterEdges)
  with Gamma.readGamma afterEdges in readW
...         | nothing = jointlyRejected refl refl
...         | just (zero , _) = jointlyRejected refl refl
...         | just (suc k , _ ∷ _) = jointlyRejected refl refl
...         | just (suc k , [])
  with Runtime.validRawEdges n Graph.noPrevious raw in rawValid
...           | false =
  jointlyRejected
    (originalTypedDecoderRejectsInvalidRawFrame
      word n m k afterN afterM afterEdges raw
      readN readM tripleBudget readEdges readW
      (AllRaw.rawGuardFalseImpliesTypedReject
        n Graph.noPrevious raw rawValid))
    refl
...           | true
  with AllFrame.allRawGammaFrameSuccessAgreement
    word n m k afterN afterM afterEdges raw
    readN readM tripleBudget readEdges readW rawValid
...             | typed , (rawAccepted , (graphAccepted , fields)) =
  jointlyParsed n k raw typed rawAccepted graphAccepted fields

------------------------------------------------------------------------
-- Same original word and certificate, both decision procedures.
-- This composition contains NO new external parser/certificate oracle.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.Karp21FinFreeSparseCertificateWordVerifierSameExact as Same

n21FinFreeVerifierSameWord :
  (word certificate : Word.BitWord) →
  Runtime.verifyFinFreeSparseGraphWord word certificate
    ≡ Graph.LiteralN21.verifyCanonicalSparseGraphWord word certificate
n21FinFreeVerifierSameWord word certificate
  with allOriginalN21GraphWordsAgree word
... | jointlyRejected typedRejected rawRejected =
  Same.n21FinFreeVerifierSameWordOnBothRejected
    word certificate typedRejected rawRejected
... | jointlyParsed n k raw typed rawAccepted graphAccepted fields =
  Same.n21FinFreeVerifierSameWordOnMatchedFrame
    word certificate raw typed (suc k)
    (Int.+≤+ z≤n , (λ ()))
    graphAccepted rawAccepted fields
