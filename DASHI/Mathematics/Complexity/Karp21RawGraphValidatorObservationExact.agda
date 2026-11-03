module DASHI.Mathematics.Complexity.Karp21RawGraphValidatorObservationExact where

------------------------------------------------------------------------
-- E20/N21: SOUNDNESS OF THE ACTUAL validateRawEdges FUNCTION.
--
-- On every successful parse, the original raw vertex addresses and
-- signed weights are recovered unchanged in the produced Fin graph.
-- This is proved by induction over the exact parser branches, not by
-- assuming a graph-decoder iff or equality of offDiagonal functions.
--
-- Consequently, if the parser succeeds on a source-owned graph's raw
-- serialization, the returned edge list has the SAME signed cut score
-- for EVERY Bool cut labeling as the source graph edge list.
--
-- This is conditional on validator success: its completeness for the
-- canonical E20 graph, global bitword/threshold replay, and machine
-- clocks remain distinct obligations.
--
-- Original: Karp 1972; DASHI signed gamma graph decoder / weighted
-- cut verifier / Fin index and edge-list observation owners.
-- Source-written only; no Agda kernel acceptance yet.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_)
import Data.Nat.Properties as NatP
import Data.Fin.Base as Fin
import Data.Fin.Properties as FinP
import Data.Vec.Base as Vec
open import Data.Integer.Base using (ℤ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)

import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Decode
import DASHI.Mathematics.Complexity.Karp21GammaWeightedEdgeListRoundTripExact as Raw
import DASHI.Mathematics.Complexity.Karp21DecodedWeightedCutSemanticBidiExact as Score

------------------------------------------------------------------------
-- Pointwise observations, including arbitrarily negative signed
-- weights. The impossible-edge/Fin range proofs are not observed.
------------------------------------------------------------------------

record RawEdgeFieldsSame
  {n : Nat}
  (raw : Decode.RawEdge)
  (decoded : Cut.SignedUndirectedEdge n) : Set where
  constructor raw-fields-same
  field
    firstAddress : Fin.toℕ (Cut.first decoded) ≡ Decode.source raw
    secondAddress : Fin.toℕ (Cut.second decoded) ≡ Decode.target raw
    signedWeight : Cut.weight decoded ≡ Decode.signedWeight raw

open RawEdgeFieldsSame public

data RawEdgeListFieldsSame {n : Nat} :
  List Decode.RawEdge → List (Cut.SignedUndirectedEdge n) → Set where
  raw-list-nil : RawEdgeListFieldsSame [] []
  raw-list-cons :
    ∀ {raw decoded rawTail decodedTail} →
    RawEdgeFieldsSame raw decoded →
    RawEdgeListFieldsSame rawTail decodedTail →
    RawEdgeListFieldsSame
      (raw ∷ rawTail) (decoded ∷ decodedTail)

-- The proof follows the REAL parser's success/failure branches.
-- On rejection, no observations are asserted.
RawValidationResult :
  ∀ {n : Nat} →
  List Decode.RawEdge →
  Maybe (List (Cut.SignedUndirectedEdge n)) → Set
RawValidationResult raw nothing = ⊤
RawValidationResult raw (just decoded) =
  RawEdgeListFieldsSame raw decoded

validateRawEdgesObservesFields :
  (n : Nat) (prev : Decode.PreviousPair)
  (raw : List Decode.RawEdge) →
  RawValidationResult raw (Decode.validateRawEdges n prev raw)
validateRawEdgesObservesFields n prev [] = raw-list-nil
validateRawEdgesObservesFields
  n prev (Decode.raw-edge u v w ∷ tail)
  with NatP._<?_ u v | NatP._<?_ v n
       | Decode.strictAfter prev u v
... | yes u<v | yes v<n | true
  with FinP._≟_
    (Fin.fromℕ< (NatP.<-trans u<v v<n))
    (Fin.fromℕ< v<n)
...   | yes _ = tt
...   | no apart
  with Decode.validateRawEdges n (Decode.previous u v) tail
     | validateRawEdgesObservesFields
         n (Decode.previous u v) tail
...     | nothing | _ = tt
...     | just decodedTail | tailSame =
  raw-list-cons
    (raw-fields-same
      (FinP.toℕ-fromℕ< (NatP.<-trans u<v v<n))
      (FinP.toℕ-fromℕ< v<n)
      refl)
    tailSame
... | _ | _ | _ = tt

validateRawEdgesSuccessFields :
  (n : Nat)
  (prev : Decode.PreviousPair)
  (raw : List Decode.RawEdge)
  (decoded : List (Cut.SignedUndirectedEdge n)) →
  Decode.validateRawEdges n prev raw ≡ just decoded →
  RawEdgeListFieldsSame raw decoded
validateRawEdgesSuccessFields n prev raw decoded accepted =
  subst (RawValidationResult raw) accepted
    (validateRawEdgesObservesFields n prev raw)

------------------------------------------------------------------------
-- The parser output's *numeric* finite indices and signed weights
-- uniquely determine the corresponding original fields. There is
-- no need to prove equality of dependent offDiagonal proof functions.
------------------------------------------------------------------------

observedEdgeHasSameCutFields :
  ∀ {n : Nat}
    (original decoded : Cut.SignedUndirectedEdge n) →
  RawEdgeFieldsSame (Raw.rawOfEdge original) decoded →
  Score.SameWeightedEdgeFields original decoded
observedEdgeHasSameCutFields original decoded fields =
  Score.same-weighted-edge
    (sym (FinP.toℕ-injective (firstAddress fields)))
    (sym (FinP.toℕ-injective (secondAddress fields)))
    (sym (signedWeight fields))

observedEdgeListHasSameCutFields :
  ∀ {n : Nat}
    (originals decoded : List (Cut.SignedUndirectedEdge n)) →
  RawEdgeListFieldsSame (Raw.rawOfEdges originals) decoded →
  Score.SameWeightedEdgeLists originals decoded
observedEdgeListHasSameCutFields [] [] raw-list-nil =
  Score.sameEdgeNil
observedEdgeListHasSameCutFields
  (original ∷ originals) (decoded ∷ decodeds)
  (raw-list-cons firstSame tailSame) =
  Score.sameEdgeCons
    (observedEdgeHasSameCutFields original decoded firstSame)
    (observedEdgeListHasSameCutFields originals decodeds tailSame)

------------------------------------------------------------------------
-- The exact actual N21 parser function, with the exact actual
-- source-owned gamma raw edge list, is cut-score-preserving on
-- EVERY successful parse, without assuming any codec reconstruction.
------------------------------------------------------------------------

validateRawEdgesSuccessPreservesCutValue :
  ∀ {n : Nat}
    (prev : Decode.PreviousPair)
    (originals decoded : List (Cut.SignedUndirectedEdge n))
    (labels : Vec.Vec Bool n) →
  Decode.validateRawEdges n prev (Raw.rawOfEdges originals)
    ≡ just decoded →
  Cut.edgeListCutValue originals labels
    ≡ Cut.edgeListCutValue decoded labels
validateRawEdgesSuccessPreservesCutValue
  {n} prev originals decoded labels accepted =
  Score.sameWeightedEdgeListScore originals decoded labels
    (observedEdgeListHasSameCutFields
      originals decoded
      (validateRawEdgesSuccessFields
        n prev (Raw.rawOfEdges originals) decoded accepted))
