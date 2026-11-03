module DASHI.Mathematics.Complexity.Karp21CanonicalRawValidatorCompleteExact where

------------------------------------------------------------------------
-- E20 / N21: SOURCE-WRITTEN COMPLETE RAW EDGE VALIDATION ON THE
-- ORIGINAL CANONICAL SIGNED KARP COMPLETE-GRAPH IMAGE.
--
-- Input: exact parser-state premises already proved from
--   Bounds.sourceIndexedScaledCompleteGraphEndpoints
--   StrictAfter.sourceIndexedScaledGraphPassesStrictAfter
--
-- Output: the EXISTING Decode.validateRawEdges returns just a
-- dependent Fin n edge list (not a hypothetical parser), and the
-- signed edge score is unchanged for EVERY Boolean vertex labeling.
--
-- Off-diagonal equality of proof functions is neither required nor
-- asserted: only actual vertex indices and signed weights matter.
-- This is not yet a complete gamma graph WORD roundtrip: the n,m
-- headers, target threshold and bit-bound guard remain to be joined.
--
-- Original Karp 1972; DASHI graph/parser/UpperPair owners; Agda Fin.
-- Source-written, not Agda-kernel accepted, no polynomial clocks.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_)
import Data.Nat.Properties as NatP
import Data.Fin.Base as Fin
import Data.Fin.Properties as FinP
import Data.Vec.Base as Vec
open import Data.Integer.Base using (ℤ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphGeneratorExact as Gen
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Decode
import DASHI.Mathematics.Complexity.Karp21GammaWeightedEdgeListRoundTripExact as Raw
import DASHI.Mathematics.Complexity.Karp21CanonicalRawValidatorPremisesExact as Valid
import DASHI.Mathematics.Complexity.Karp21DecodedWeightedCutSemanticBidiExact as Score
import DASHI.Mathematics.Complexity.Karp21RawGraphValidatorObservationExact as Observe
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Bool

------------------------------------------------------------------------
-- Run the exact ACTUAL validator, following its three guards and its
-- Fin decidable equality, on the same rawOfEdges source edge list.
------------------------------------------------------------------------

validateCanonicalRawEdgesSuccess :
  ∀ {n : Nat}
    (prev : Decode.PreviousPair)
    (originals : List (Cut.SignedUndirectedEdge n)) →
  Valid.ValidFromPrevious prev originals →
  Σ (List (Cut.SignedUndirectedEdge n))
    (λ decoded →
      Decode.validateRawEdges n prev (Raw.rawOfEdges originals)
        ≡ just decoded)
validateCanonicalRawEdgesSuccess prev [] Valid.validNil =
  [] , refl
validateCanonicalRawEdgesSuccess {n} prev
  (edge ∷ rest)
  (Valid.validCons (ordered , inRange) check tailValid)
  with NatP._<?_
         (Fin.toℕ (Cut.first edge))
         (Fin.toℕ (Cut.second edge))
     | NatP._<?_
         (Fin.toℕ (Cut.second edge)) n
     | Decode.strictAfter prev
         (Fin.toℕ (Cut.first edge))
         (Fin.toℕ (Cut.second edge))
... | yes firstLess | yes secondLess | true
  with FinP._≟_
    (Fin.fromℕ< (NatP.<-trans firstLess secondLess))
    (Fin.fromℕ< secondLess)
...   | yes equal =
  ⊥-elim
    (Score.reconstructedOffDiagonal edge
      (NatP.<-trans firstLess secondLess)
      secondLess
      equal)
...   | no apart
  with validateCanonicalRawEdgesSuccess
    (Decode.previous
      (Fin.toℕ (Cut.first edge))
      (Fin.toℕ (Cut.second edge)))
    rest tailValid
...     | decodedRest , restAccepted
  rewrite restAccepted =
  (Cut.edge
    (Fin.fromℕ< (NatP.<-trans firstLess secondLess))
    (Fin.fromℕ< secondLess)
    apart
    (Cut.weight edge)
    ∷ decodedRest)
  , refl
... | no notLess | _ | _ = ⊥-elim (notLess ordered)
... | yes _ | no notRange | _ = ⊥-elim (notRange inRange)
... | yes _ | yes _ | false = ⊥-elim (Bool.falseNotTrue check)

------------------------------------------------------------------------
-- The ORIGINAL decoder and SAME signed graph observation theorem
-- yield a semantic result, not a proxy "validation status" record.
------------------------------------------------------------------------

validateCanonicalRawEdgesSameCut :
  ∀ {n : Nat}
    (prev : Decode.PreviousPair)
    (originals : List (Cut.SignedUndirectedEdge n))
    (conditions : Valid.ValidFromPrevious prev originals) →
  Σ (List (Cut.SignedUndirectedEdge n))
    (λ decoded →
      (Decode.validateRawEdges n prev (Raw.rawOfEdges originals)
        ≡ just decoded)
      × Score.SameWeightedEdgeLists originals decoded)
validateCanonicalRawEdgesSameCut {n} prev originals conditions
  with validateCanonicalRawEdgesSuccess prev originals conditions
... | decoded , accepted =
  decoded ,
    (accepted ,
      Observe.observedEdgeListHasSameCutFields
        originals decoded
        (Observe.validateRawEdgesSuccessFields
          n prev (Raw.rawOfEdges originals) decoded accepted))

------------------------------------------------------------------------
-- Specialization to original upper-triangle construction. No access
-- to a partition witness or Boolean cut; only the source signed Vec.
------------------------------------------------------------------------

scaledCompleteRawValidatorSuccess :
  ∀ {n : Nat} (source : Vec.Vec ℤ n) →
  Σ (List (Cut.SignedUndirectedEdge n))
    (λ decoded →
      (Decode.validateRawEdges n Decode.noPrevious
        (Raw.rawOfEdges (Gen.completeScaledPairEdges source))
        ≡ just decoded)
      × Score.SameWeightedEdgeLists
          (Gen.completeScaledPairEdges source)
          decoded)
scaledCompleteRawValidatorSuccess source =
  validateCanonicalRawEdgesSameCut
    Decode.noPrevious
    (Gen.completeScaledPairEdges source)
    (Valid.scaledCompleteGraphValidatorPremises source)

scaledCompleteRawValidatorCutScore :
  ∀ {n : Nat}
    (source : Vec.Vec ℤ n) (labels : Vec.Vec Bool n) →
  Σ (List (Cut.SignedUndirectedEdge n))
    (λ decoded →
      (Decode.validateRawEdges n Decode.noPrevious
        (Raw.rawOfEdges (Gen.completeScaledPairEdges source))
        ≡ just decoded)
      × (Cut.edgeListCutValue
          (Gen.completeScaledPairEdges source) labels
          ≡ Cut.edgeListCutValue decoded labels))
scaledCompleteRawValidatorCutScore source labels
  with scaledCompleteRawValidatorSuccess source
... | decoded , (accepted , sameFields) =
  decoded ,
    (accepted ,
      Score.sameWeightedEdgeListScore
        (Gen.completeScaledPairEdges source)
        decoded labels sameFields)
