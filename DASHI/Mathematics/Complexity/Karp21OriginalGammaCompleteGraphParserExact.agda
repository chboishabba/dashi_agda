module DASHI.Mathematics.Complexity.Karp21OriginalGammaCompleteGraphParserExact where

------------------------------------------------------------------------
-- E20 / N21: FULL ORIGINAL NESTED GAMMA GRAPH DECODER, E20 IMAGE.
--
-- No replacement graph word grammar: use original decodeGraphWord,
-- its actual gamma(n), gamma(m), raw signed triples, positive gamma(W),
-- original Fin validator, and terminal 2m witness budget.
--
-- The finite E20 image already has exact raw-parser success and
-- signed score equality. This owner composes the remaining actual
-- outer fields, checks and semantic equivalence to the output Word.
-- OffDiagonal proof functions are never compared.
--
-- Source-written only: exact-head Agda/kernel receipt is still OPEN.
-- Original authorship: Karp 1972, Cook 1971, DASHI source codecs.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n)
open import Data.List.Base using (List; []; length)
open import Data.Maybe.Base using (just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (subst)
import Data.Nat.Properties as NatP
import Data.Vec.Base as Vec
import Data.Integer.Base as Int
open import Data.Integer.Base using (ℤ; +_)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SparseGraphWordNPBoundaryExact as N21
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphGeneratorExact as Gen
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21GammaZigzagWordEncodeExact as Encode
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21OriginalGammaGraphWordFieldsReplayExact as Fields
import DASHI.Mathematics.Complexity.Karp21CanonicalRawValidatorCompleteExact as Valid
import DASHI.Mathematics.Complexity.Karp21DecodedWeightedCutSemanticBidiExact as Observed
import DASHI.Mathematics.Complexity.Karp21EncodedGraphSparseBitBoundExact as Size
import DASHI.Mathematics.Complexity.Karp21ScaledThresholdExact as Threshold
import DASHI.Mathematics.Complexity.Karp21PositiveThresholdGammaExact as Positive
import DASHI.Mathematics.Complexity.Karp21SignedPartitionIndexedGraphDecisionExact as Indexed
import DASHI.Mathematics.Complexity.Karp21PartitionScaledInstanceExact as Source
import DASHI.Mathematics.Complexity.Karp21SignedPartitionActualGraphWordBoundaryExact as Boundary
import DASHI.Mathematics.Complexity.Karp21SignedPartitionActualGraphYESExact as Actual
import DASHI.Mathematics.Complexity.Karp21GammaWeightedEdgeListRoundTripExact as Raw

------------------------------------------------------------------------
-- Literal nested decoder success, from exactly its original six
-- parser and size obligations. Both numeric guards are proof-carrying:
-- their impossible branches contradict the provided inequalities.
------------------------------------------------------------------------

decodeGraphWordFromActualFrame :
  (word : Word.BitWord) (n m k : Nat)
  (afterN afterM afterEdges : Word.BitWord)
  (raw : List Graph.RawEdge)
  (decoded : List (Cut.SignedUndirectedEdge n)) →
  Gamma.readGamma word ≡ just (n , afterN) →
  Gamma.readGamma afterN ≡ just (m , afterM) →
  m * suc (suc (suc zero)) ≤ length afterM →
  Graph.readRawEdges m afterM ≡ just (raw , afterEdges) →
  Gamma.readGamma afterEdges ≡ just (suc k , []) →
  Graph.validateRawEdges n Graph.noPrevious raw ≡ just decoded →
  Sparse.twoPerEdge (length decoded) ≤ Word.encodingSize word →
  Graph.decodeGraphWord word
    ≡ just
      (n , Cut.graph decoded (+ (suc k))
        (Int.+≤+ z≤n , (λ ())))
decodeGraphWordFromActualFrame
    word n m k afterN afterM afterEdges raw decoded
    readN readM tripleBound readEdges readW validated sparseBound
  rewrite readN | readM
  with NatP._≤?_ (m * suc (suc (suc zero))) (length afterM)
... | no violatesTriple = ⊥-elim (violatesTriple tripleBound)
... | yes _
  rewrite readEdges | readW | validated
  with NatP._≤?_
    (Sparse.twoPerEdge (length decoded)) (Word.encodingSize word)
...   | no violatesSparse = ⊥-elim (violatesSparse sparseBound)
...   | yes _ = refl

------------------------------------------------------------------------
-- The REAL scaled E20 complete graph passes every original header,
-- parse, range, ordering, threshold and sparse-budget check. The
-- result graph differs only in regenerated Fin/offDiagonal witnesses.
-- The original MAX CUT YES predicate is preserved in both directions.
------------------------------------------------------------------------

completeGraphGammaGraphDecodeSameObject :
  ∀ {n : Nat}
    (source : Vec.Vec ℤ n)
    (threshold : ℤ)
    (positive : Threshold.PositiveThreshold threshold) →
  Σ (N21.GraphInstance)
    (λ decoded →
      (Graph.decodeGraphWord
        (Encode.encodeGraphWord
          (n , Cut.graph
            (Gen.completeScaledPairEdges source) threshold positive))
       ≡ just decoded)
      × PR.Iff
          (Cut.WeightedMaxCutYES
            (Cut.graph
              (Gen.completeScaledPairEdges source) threshold positive))
          (Cut.WeightedMaxCutYES (proj₂ decoded)))
completeGraphGammaGraphDecodeSameObject {n} source threshold positive
  with Positive.positiveThresholdIsSuccessor threshold positive
... | k , refl with Valid.scaledCompleteRawValidatorSuccess source
...   | decodedEdges , (validatorSuccess , sameFields) =
      let original =
            Cut.graph (Gen.completeScaledPairEdges source)
              (+ (suc k)) positive
          instance = n , original
          word = Encode.encodeGraphWord instance
          decodedGraph =
            Cut.graph decodedEdges (+ (suc k))
              (Int.+≤+ z≤n , (λ ()))
          sparseBound =
            subst
              (λ count →
                Sparse.twoPerEdge count ≤ Word.encodingSize word)
              (Observed.sameWeightedEdgeListLength
                (Gen.completeScaledPairEdges source)
                decodedEdges sameFields)
              (Size.encodedGraphAtLeastSparseBits instance)
          fullDecoder =
            decodeGraphWordFromActualFrame
              word n (length (Cut.edges original)) k
              (Fields.graphWordAfterVertexCount instance)
              (Fields.graphWordAfterEdgeCount instance)
              (Fields.graphWordThresholdBits instance)
              (Raw.rawOfEdges
                (Cut.edges original))
              decodedEdges
              (Fields.readEncodedGraphVertexCount instance)
              (Fields.readEncodedGraphEdgeCount instance)
              (Fields.readEncodedGraphEdgeCountBudget instance)
              (Fields.readEncodedGraphEdgeTriples instance)
              (Fields.readEncodedGraphThresholdMagnitude instance)
              validatorSuccess
              sparseBound
      in (n , decodedGraph) ,
          (fullDecoder ,
            Observed.sameWeightedGraphsAccept original decodedGraph
              refl sameFields)

------------------------------------------------------------------------
-- A successful *actual* Graph.decodeGraphWord identifies the original
-- graph-word language with the returned weighted MAX CUT predicate.
-- This is not an equality of irrelevant dependent proof functions.
------------------------------------------------------------------------

decodedGraphWordLanguageIff :
  (word : Word.BitWord)
  (decoded : N21.GraphInstance) →
  Graph.decodeGraphWord word ≡ just decoded →
  PR.Iff
    (PR.accepts Graph.concreteGraphWordLanguage word)
    (Cut.WeightedMaxCutYES (proj₂ decoded))
decodedGraphWordLanguageIff word decoded accepted
  rewrite accepted = PR.iff (λ witness → witness) (λ witness → witness)

------------------------------------------------------------------------
-- Instantiate the ORIGINAL E20ImageWordReceipts hole, not a parallel
-- target language. Malformed words and zero-total fixed-YES branch are
-- already treated by the source Boundary.EncodedE20 totalization.
------------------------------------------------------------------------

e20ScaledCompleteWordFaithful :
  (parts : List ℤ)
  (nonzero : Threshold.NonZero (Source.sourceTotal parts)) →
  PR.Iff
    (Actual.ActualPositiveTargetAccepts
      (Source.scaledCompletePositive parts nonzero))
    (PR.accepts Graph.concreteGraphWordLanguage
      (Encode.encodeGraphWord
        (Boundary.graphOfPositiveTarget
          (Source.scaledCompletePositive parts nonzero))))
e20ScaledCompleteWordFaithful parts nonzero
  with completeGraphGammaGraphDecodeSameObject
    (Indexed.vectorOfList parts)
    (Source.sourceTotal parts * Source.sourceTotal parts)
    (Threshold.nonzeroTotalSquareIsPositiveThreshold
      (Source.sourceTotal parts) nonzero)
... | decoded , (decodedWord , originalIff) =
  let word = Encode.encodeGraphWord
        (Boundary.graphOfPositiveTarget
          (Source.scaledCompletePositive parts nonzero))
      wordIff = decodedGraphWordLanguageIff word decoded decodedWord
  in PR.iff
       (λ accepted →
         PR.backward wordIff (PR.forward originalIff accepted))
       (λ accepted →
         PR.backward originalIff (PR.forward wordIff accepted))

sourceWrittenE20ImageWordReceipts : Boundary.E20ImageWordReceipts
sourceWrittenE20ImageWordReceipts =
  record
    { Boundary.scaledCompleteWordFaithful =
        e20ScaledCompleteWordFaithful
    }

module SourceWrittenE20 = Boundary.EncodedE20
  sourceWrittenE20ImageWordReceipts

-- Assembled *semantic* total reduction, including malformed source words.
-- Its polynomial machine cost is a SEPARATE required inhabitant of
-- PR.polynomialTimeMap under a nondegenerate executable cost model.
e20OriginalEncodedDecisionIff :
  (word : Word.BitWord) →
  PR.Iff
    (PR.accepts SourceWrittenE20.sourceLanguage word)
    (PR.accepts Graph.concreteGraphWordLanguage
      (SourceWrittenE20.totalE20WordReduction word))
e20OriginalEncodedDecisionIff =
  SourceWrittenE20.e20EncodedSignedPartitionDecisionIff
