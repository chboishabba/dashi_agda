module DASHI.Mathematics.Complexity.Karp21FinFreeAllGammaSuccessAgreementExact where

------------------------------------------------------------------------
-- N21: THE TWO ORIGINAL GAMMA GRAPH PARSERS ACCEPT THE SAME SUCCESSFUL
-- RAW FRAME, INCLUDING ORIGINAL SIGNED FIELDS AND SPARSE EDGE BUDGET.
--
-- This is an arbitrary raw-word frame, not just an E20 complete-graph
-- image. It REUSES both existing nested decoder execution lemmas,
-- the original all-raw dependent/Fin-free validator agreement and
-- original raw edge observation/edge-count owners. No graph replacement,
-- offDiagonal proof-field equality, or fake Boolean marker appears.
--
-- The frame hypotheses are the exact actual gamma/readRawEdges
-- success results, original 3m parser guard, positive W, original
-- raw validation and 2m certificate-size inequality. Future work
-- derives these automatically from any successful whole-word read.
--
-- NOT: full n21FinFreeVerifierSameWord (its sparse consistency and
-- signed-score equality are separately pending); NOT binary tape time;
-- NOT a Golden/kernel receipt. Karp (1972); DASHI original owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n)
open import Data.List.Base using (List; []; length)
open import Data.Maybe.Base using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (subst)
import Data.Integer.Base as Int
open import Data.Integer.Base using (+_)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SparseGraphWordNPBoundaryExact as N21
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21RawGraphValidatorObservationExact as Observe
import DASHI.Mathematics.Complexity.Karp21FinFreeAllRawValidatorAgreementExact as AllRaw
import DASHI.Mathematics.Complexity.Karp21OriginalGammaCompleteGraphParserExact as TypedFrame
import DASHI.Mathematics.Complexity.Karp21FinFreeOriginalGammaFrameExact as RawFrame

-- This type and both actual read functions are original repo owners.
-- We intentionally assert no equality between dependent Fin proof fields.
allRawGammaFrameSuccessAgreement :
  (word : Word.BitWord)
  (n m k : Nat)
  (afterN afterM afterEdges : Word.BitWord)
  (raw : List Graph.RawEdge) →
  Gamma.readGamma word ≡ just (n , afterN) →
  Gamma.readGamma afterN ≡ just (m , afterM) →
  m * suc (suc (suc zero)) ≤ length afterM →
  Graph.readRawEdges m afterM ≡ just (raw , afterEdges) →
  Gamma.readGamma afterEdges ≡ just (suc k , []) →
  Sparse.twoPerEdge (length raw) ≤ Word.encodingSize word →
  Runtime.validRawEdges n Graph.noPrevious raw ≡ true →
  Σ (List (Cut.SignedUndirectedEdge n))
    (λ decoded →
      (Runtime.readRawGraphWord word
        ≡ just (Runtime.parsed-raw-graph n raw (suc k)))
      ×
      (Graph.decodeGraphWord word
        ≡ just
          (n , Cut.graph decoded (+ (suc k))
            (Int.+≤+ z≤n , (λ ()))))
      ×
      Observe.RawEdgeListFieldsSame raw decoded)
allRawGammaFrameSuccessAgreement
  word n m k afterN afterM afterEdges raw
  readN readM tripleBound readEdges readW rawBudget rawValid
  with AllRaw.rawGuardTruePreservesOriginalFields
    n Graph.noPrevious raw rawValid
... | decoded , (typedValidation , observedFields) =
  let typedBudget =
        subst
          (λ count →
            Sparse.twoPerEdge count ≤ Word.encodingSize word)
          (AllRaw.rawFieldPreservingListLength
            raw decoded observedFields)
          rawBudget
      rawAccepted =
        RawFrame.readFinFreeRawGraphFromActualFrame
          word n m k afterN afterM afterEdges raw
          readN readM tripleBound readEdges readW rawValid
      typedAccepted =
        TypedFrame.decodeGraphWordFromActualFrame
          word n m k afterN afterM afterEdges raw decoded
          readN readM tripleBound readEdges readW
          typedValidation typedBudget
  in decoded , (rawAccepted , (typedAccepted , observedFields))
