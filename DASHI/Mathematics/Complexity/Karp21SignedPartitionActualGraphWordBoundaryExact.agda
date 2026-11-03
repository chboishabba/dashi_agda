{-# OPTIONS --safe #-}
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
--
-- Karp 1972, original signed PARTITION and weighted positive-W CUT.
-- No "in NP", polynomial resource, or kernel certification is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; length)
open import Data.Product using (Σ; _,_; proj₂)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21PartitionScaledInstanceExact as Source
import DASHI.Mathematics.Complexity.Karp21SignedPartitionActualGraphYESExact as Actual
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SparseGraphWordNPBoundaryExact as N21
import DASHI.Mathematics.Complexity.Karp21MalformedWordTotalReductionExact as Malformed
import DASHI.Mathematics.Complexity.Karp21WeightedMaxCutFixedNoGraphExact as FixedNo
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as GraphWord
import DASHI.Mathematics.Complexity.Karp21GammaZigzagWordEncodeExact as Encode
open import Relation.Binary.PropositionalEquality using (refl)
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
    positiveTargetWordFaithful :
      (target : Source.PositiveCutTarget) →
      PR.Iff (Actual.ActualPositiveTargetAccepts target)
        (PR.accepts GraphWord.concreteGraphWordLanguage
          (Encode.encodeGraphWord (graphOfPositiveTarget target)))

    fixedNoWordRejects :
      PR.accepts GraphWord.concreteGraphWordLanguage
        (Encode.encodeGraphWord FixedNo.fixedNoGraphInstance) → ⊥

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
  outputWordFaithful (positiveTarget target) =
    positiveTargetWordFaithful receipts target
  outputWordFaithful malformedFixedNo =
    PR.iff
      (λ ())
      (λ accepted → fixedNoWordRejects receipts accepted)

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
