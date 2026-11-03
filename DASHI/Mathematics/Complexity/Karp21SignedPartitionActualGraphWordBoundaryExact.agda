module DASHI.Mathematics.Complexity.Karp21SignedPartitionActualGraphWordBoundaryExact where

------------------------------------------------------------------------
-- E20: ORIGINAL SIGNED PARTITION -> REAL POSITIVE-W WEIGHTED GRAPH,
--      -> TOTAL BINARY WORD REDUCTION INCLUDING MALFORMED SOURCES.
--
-- Reuse the actual finite graph constructor and signed PARTITION iff
-- in Karp21SignedPartitionActualGraphYESExact.  Reuse the existing
-- Karp21MalformedWordTotalReductionExact TOTALIZATION compiler, not
-- an independently invented encoded language or Boolean status flag.
--
-- The unprovided representation premise is the real graph binary codec,
-- their faithful parser-to-word correspondence, and
-- the genuine polynomial-time machine clock. The target language
-- is now fixed to the literal gamma/zigzag graph decoder. The finite reduction
-- and both directions of its word-level semantic correctness are
-- independently source-written here.
-- Integration module: intentionally not --safe until its existing
-- weighted-graph and malformed-source imports become transitively safe.
--
-- Karp 1972, original signed PARTITION and weighted positive-W CUT.
-- No "in NP", polynomial resource, or kernel certification is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; _++_; length)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (Σ; _,_; proj₂)
open import Data.Maybe.Base using (Maybe; just)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21PartitionScaledInstanceExact as Source
import DASHI.Mathematics.Complexity.Karp21ScaledThresholdExact as Threshold
import DASHI.Mathematics.Complexity.Karp21SignedPartitionActualGraphYESExact as Actual
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SparseGraphWordNPBoundaryExact as N21
import DASHI.Mathematics.Complexity.Karp21MalformedWordTotalReductionExact as Malformed
import DASHI.Mathematics.Complexity.Karp21WeightedMaxCutFixedNoGraphExact as FixedNo
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as GraphWord
import DASHI.Mathematics.Complexity.Karp21GammaZigzagWordEncodeExact as Encode
import DASHI.Mathematics.Complexity.Karp21EncodedGraphSparseBitBoundExact as Size
import DASHI.Mathematics.Complexity.Karp21GammaWeightedEdgeListRoundTripExact as Raw
import DASHI.Mathematics.Complexity.Karp21ScaledCompleteGraphEndpointOrderExact as Order
import DASHI.Mathematics.Complexity.Karp21UpperPairStructuralLexOrderExact as PairLex
import DASHI.Mathematics.Complexity.Karp21ScaledCompleteGraphStrictLexExact as StrictLex
import DASHI.Mathematics.Complexity.Karp21ScaledCompleteGraphStrictAfterExact as StrictAfter
import DASHI.Mathematics.Complexity.Karp21SignedPartitionIndexedGraphDecisionExact as Indexed
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21EncodedFixedGraphWordsExact as FixedWords
open import Data.Empty using (⊥; ⊥-elim)

graphAccepts : N21.GraphInstance → Set
graphAccepts graph =
  Cut.WeightedMaxCutYES (proj₂ graph)

-- Every target has the same positive-threshold finite graph as E20,
-- including the zero-total fixed two-vertex unit-edge YES branch.
graphOfPositiveTarget :
  Source.PositiveCutTarget → N21.GraphInstance
graphOfPositiveTarget Source.unitEdgeYesPositive =
  2 , Actual.fixedUnitGraph
graphOfPositiveTarget (Source.scaledCompletePositive parts nonzero) =
  length parts , Actual.sourceIndexedWeightedGraph parts nonzero

------------------------------------------------------------------------
-- Same ACTUAL nonzero-total E20 graph: its exact signed edge list
-- is read back by the original literal gamma RAW parser, without a
-- separate family of coefficients or a parallel graph definition.
-- The lexicographic validator and threshold decoder remain open.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- All actual E20 nonzero-total graph edges satisfy numeric u < v < n.
-- This is independent of the sorted-adjacency proof still needed for
-- the literal GraphWord validator and its proof-field reconstruction.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Every earlier edge in E20's actual nonzero-total complete graph
-- has a strictly lexicographically smaller (u,v) numeric pair than
-- every later edge. This is stronger than a no-duplicate receipt.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- The ORIGINAL graph parser's Bool strictAfter guard is satisfied by
-- every earlier/later pair from E20's actual scaled complete graph.
-- This is stronger than independent endpoint validity and no-repeat.
------------------------------------------------------------------------

e20ActualScaledGraphPassesStrictAfter :
  (parts : List ℤ)
  (nonzero : Threshold.NonZero (Source.sourceTotal parts)) →
  PairLex.StrictSorted StrictAfter.ParserStrictlyAfterEdge
    (Cut.edges (Actual.sourceIndexedWeightedGraph parts nonzero))
e20ActualScaledGraphPassesStrictAfter parts nonzero =
  StrictAfter.sourceIndexedScaledGraphPassesStrictAfter
    (Indexed.vectorOfList parts)

e20ActualScaledGraphStrictLex :
  (parts : List ℤ)
  (nonzero : Threshold.NonZero (Source.sourceTotal parts)) →
  PairLex.StrictSorted StrictLex.CanonicalEdgeNumericBefore
    (Cut.edges (Actual.sourceIndexedWeightedGraph parts nonzero))
e20ActualScaledGraphStrictLex parts nonzero =
  StrictLex.sourceIndexedScaledCompleteGraphStrictLex
    (Indexed.vectorOfList parts)

e20ActualScaledGraphEndpointBounds :
  (parts : List ℤ)
  (nonzero : Threshold.NonZero (Source.sourceTotal parts)) →
  Order.AllCanonicalEdgeEndpoints
    (Cut.edges (Actual.sourceIndexedWeightedGraph parts nonzero))
e20ActualScaledGraphEndpointBounds parts nonzero =
  Order.sourceIndexedScaledCompleteGraphEndpoints
    (Indexed.vectorOfList parts)

e20ScaledActualRawEdgeRoundTrip :
  (parts : List ℤ)
  (nonzero : Threshold.NonZero (Source.sourceTotal parts))
  (suffix : Word.BitWord) →
  GraphWord.readRawEdges
    (length (Cut.edges (Actual.sourceIndexedWeightedGraph parts nonzero)))
    (Encode.encodeEdgeWords
      (Cut.edges (Actual.sourceIndexedWeightedGraph parts nonzero))
      ++ suffix)
  ≡ Data.Maybe.Base.just
      ( Raw.rawOfEdges
          (Cut.edges (Actual.sourceIndexedWeightedGraph parts nonzero))
      , suffix )
e20ScaledActualRawEdgeRoundTrip parts nonzero suffix =
  Raw.readActualEdgeListWordSuffix
    (Cut.edges (Actual.sourceIndexedWeightedGraph parts nonzero))
    suffix

positiveTargetGraphAcceptsIff :
  (target : Source.PositiveCutTarget) →
  PR.Iff (Actual.ActualPositiveTargetAccepts target)
    (graphAccepts (graphOfPositiveTarget target))
positiveTargetGraphAcceptsIff Source.unitEdgeYesPositive =
  PR.iff (λ p → p) (λ p → p)
positiveTargetGraphAcceptsIff
  (Source.scaledCompletePositive parts nonzero) =
  PR.iff (λ p → p) (λ p → p)

-- This map reads only the SOURCE signed list. It cannot inspect a
-- partition witness or a cut label. It preserves duplicate weights.
e20ActualGraphOfSignedPartition :
  List ℤ → N21.GraphInstance
e20ActualGraphOfSignedPartition parts =
  graphOfPositiveTarget (Source.totalPartitionToPositiveCut parts)

e20SignedPartitionActualGraphIff :
  (parts : List ℤ) →
  PR.Iff (Source.PartitionYES parts)
    (graphAccepts (e20ActualGraphOfSignedPartition parts))
e20SignedPartitionActualGraphIff parts =
  PR.iffTransitive
    (Actual.sourcePartitionActualPositiveGraphIff parts)
    (positiveTargetGraphAcceptsIff
      (Source.totalPartitionToPositiveCut parts))

------------------------------------------------------------------------
-- The canonical binary graph serializer does NOT
-- currently have a kernel-checked exact representation theorem.
-- The source decoder is now the actual gamma/zigzag implementation.
-- Keep their data as required REAL functions, and their
-- faithful graph acceptance correspondence as a proof obligation.
--
-- In particular a graph record carries off-diagonal impossibility
-- functions; avoid requiring literal propositional equality of its
-- erased proof fields after binary roundtrip. The theorem required
-- for many-one correctness is the actual graph-YES language iff.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- IMPORTANT: the original weighted graph type allows arbitrary
-- duplicate and unsorted edges. The canonical Python format forbids
-- them. Hence a ∀ graph encoder/decode equivalence is generally
-- FALSE. Only the E20 transform IMAGE (complete sorted graph or
-- fixed unit-YES graph) and the concrete fixed-NO malformed branch
-- require faithfulness.
--
-- The actual encoder is now a DEFINITION, not a caller-supplied map.
-- Only exact parser/YES equivalence on its two output families and
-- the genuine machine cost remain to be proved.
------------------------------------------------------------------------

record E20ImageWordReceipts : Set₁ where
  field
    -- The only still-open semantic output-fidelity premise:
    -- actual ordered weighted complete-graph image of a signed
    -- source PARTITION with nonzero total.
    scaledCompleteWordFaithful :
      (parts : List ℤ)
      (nonzero : Threshold.NonZero
        (Source.sourceTotal parts)) →
      PR.Iff
        (Actual.ActualPositiveTargetAccepts
          (Source.scaledCompletePositive parts nonzero))
        (PR.accepts GraphWord.concreteGraphWordLanguage
          (Encode.encodeGraphWord
            (graphOfPositiveTarget
              (Source.scaledCompletePositive parts nonzero))))

open E20ImageWordReceipts public

-- A smaller typed target family comprising exactly the output image
-- of E20 together with its actual malformed-source NO word.
data E20OutputMode : Set where
  positiveTarget : Source.PositiveCutTarget → E20OutputMode
  malformedFixedNo : E20OutputMode

e20OutputAccepts : E20OutputMode → Set
e20OutputAccepts (positiveTarget target) =
  Actual.ActualPositiveTargetAccepts target
e20OutputAccepts malformedFixedNo = ⊥

e20OutputFromPartition : List ℤ → E20OutputMode
e20OutputFromPartition parts =
  positiveTarget (Source.totalPartitionToPositiveCut parts)

e20OutputWord : E20OutputMode → Word.BitWord
e20OutputWord (positiveTarget target) =
  Encode.encodeGraphWord (graphOfPositiveTarget target)
e20OutputWord malformedFixedNo =
  Encode.encodeGraphWord FixedNo.fixedNoGraphInstance

------------------------------------------------------------------------
-- The actual E20 output modes share the SAME underlying N21 graph:
-- fixed zero-sum YES; nonzero signed complete graph; and malformed NO.
-- The original emitted word is exactly the literal graph serialization,
-- so sparse 2m witnesses fit into each E20 output's own binary length.
-- This is a true serializer-size fact, not the missing graph-parser
-- same-object iff and not a machine polynomial-time certificate.
------------------------------------------------------------------------

e20OutputGraph : E20OutputMode → N21.GraphInstance
e20OutputGraph (positiveTarget target) =
  graphOfPositiveTarget target
e20OutputGraph malformedFixedNo =
  FixedNo.fixedNoGraphInstance

e20OutputWordUsesSameGraph :
  (output : E20OutputMode) →
  e20OutputWord output ≡ Encode.encodeGraphWord (e20OutputGraph output)
e20OutputWordUsesSameGraph (positiveTarget target) = refl
e20OutputWordUsesSameGraph malformedFixedNo = refl

e20OutputWordSparseBitBound :
  (output : E20OutputMode) →
  Sparse.twoPerEdge (length (Cut.edges (proj₂ (e20OutputGraph output))))
    ≤ Word.encodingSize (e20OutputWord output)
e20OutputWordSparseBitBound output
  rewrite e20OutputWordUsesSameGraph output =
  Size.encodedGraphAtLeastSparseBits (e20OutputGraph output)

-- The real signed PARTITION source map has the same size receipt,
-- regardless of the exceptional total-zero dispatch.
e20SignedPartitionOutputSparseBitBound :
  (parts : List ℤ) →
  Sparse.twoPerEdge
    (length (Cut.edges
      (proj₂ (e20OutputGraph (e20OutputFromPartition parts)))))
    ≤ Word.encodingSize
      (e20OutputWord (e20OutputFromPartition parts))
e20SignedPartitionOutputSparseBitBound parts =
  e20OutputWordSparseBitBound (e20OutputFromPartition parts)


e20SourceOutputModeIff :
  (parts : List ℤ) →
  PR.Iff (Source.PartitionYES parts)
    (e20OutputAccepts (e20OutputFromPartition parts))
e20SourceOutputModeIff =
  Actual.sourcePartitionActualPositiveGraphIff

module EncodedE20 (receipts : E20ImageWordReceipts) where

  outputWordFaithful :
    (target : E20OutputMode) →
    PR.Iff (e20OutputAccepts target)
      (PR.accepts GraphWord.concreteGraphWordLanguage
        (e20OutputWord target))
  outputWordFaithful (positiveTarget Source.unitEdgeYesPositive) =
    FixedWords.fixedUnitWordFaithful
  outputWordFaithful
    (positiveTarget (Source.scaledCompletePositive parts nonzero)) =
    scaledCompleteWordFaithful receipts parts nonzero
  outputWordFaithful malformedFixedNo =
    PR.iff
      (λ ())
      (λ accepted → FixedWords.encodedFixedNoWordRejects accepted)

  module Total =
    Malformed.TotalMalformedSource
      Gamma.decodePartitionWord
      Source.PartitionYES
      e20OutputAccepts
      e20OutputFromPartition
      malformedFixedNo
      (λ ())
      e20OutputWord
      GraphWord.concreteGraphWordLanguage
      e20SourceOutputModeIff
      outputWordFaithful

  sourceLanguage : PR.Language Word.BitWord
  sourceLanguage = Total.sourceLanguage

  totalE20WordReduction : Word.BitWord → Word.BitWord
  totalE20WordReduction = Total.totalReduce

  -- Includes actual malformed source words using the literal fixed-NO
  -- encoded graph, not a flag, invented language or guessed witness.
  e20EncodedSignedPartitionDecisionIff :
    (word : Word.BitWord) →
    PR.Iff (PR.accepts sourceLanguage word)
      (PR.accepts GraphWord.concreteGraphWordLanguage
        (totalE20WordReduction word))
  e20EncodedSignedPartitionDecisionIff =
    Total.totalMalformedReductionIff

  e20EncodedPolynomialReductionFromClock :
    (cost : PR.PolynomialCostModel Word.BitWord) →
    PR.polynomialTimeMap cost totalE20WordReduction →
    PR.PolynomialManyOneReduction
      cost sourceLanguage GraphWord.concreteGraphWordLanguage
  e20EncodedPolynomialReductionFromClock =
    Total.makeCostedTotalReduction
