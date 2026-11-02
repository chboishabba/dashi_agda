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
-- The only unprovided premises are the real canonical binary codecs,
-- their faithful parser-to-word correspondence, and
-- the genuine polynomial-time machine clock. The finite reduction
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
-- The canonical binary source decoder and graph serializer do NOT
-- currently have kernel-checked exact representation theorems.
-- Keep their data as required REAL functions, and their
-- faithful graph acceptance correspondence as a proof obligation.
--
-- In particular a graph record carries off-diagonal impossibility
-- functions; avoid requiring literal propositional equality of its
-- erased proof fields after binary roundtrip. The theorem required
-- for many-one correctness is the actual graph-YES language iff.
------------------------------------------------------------------------

record E20GraphWordBoundary : Set₁ where
  field
    decodePartition : Word.BitWord → Maybe (List ℤ)
    encodeGraph : N21.GraphInstance → Word.BitWord
    graphLanguage : PR.Language Word.BitWord
    faithfulGraphWord :
      (graph : N21.GraphInstance) →
      PR.Iff (graphAccepts graph)
        (PR.accepts graphLanguage (encodeGraph graph))

open E20GraphWordBoundary public

module EncodedE20
  (boundary : E20GraphWordBoundary) where

  module Total =
    Malformed.TotalMalformedSource
      (decodePartition boundary)
      Source.PartitionYES
      graphAccepts
      e20ActualGraphOfSignedPartition
      FixedNo.fixedNoGraphInstance
      FixedNo.fixedNoGraphInstanceRejects
      (encodeGraph boundary)
      (graphLanguage boundary)
      e20SignedPartitionActualGraphIff
      (faithfulGraphWord boundary)

  sourceLanguage : PR.Language Word.BitWord
  sourceLanguage = Total.sourceLanguage

  totalE20WordReduction : Word.BitWord → Word.BitWord
  totalE20WordReduction = Total.totalReduce

  -- Includes all malformed source words, not only canonical PARTITION.
  e20EncodedSignedPartitionDecisionIff :
    (word : Word.BitWord) →
    PR.Iff (PR.accepts sourceLanguage word)
      (PR.accepts (graphLanguage boundary)
        (totalE20WordReduction word))
  e20EncodedSignedPartitionDecisionIff =
    Total.totalMalformedReductionIff

  -- Last machine-resource condition is named and explicit; this is not
  -- a proof that graph output is polynomially bounded or runnable.
  e20EncodedPolynomialReductionFromClock :
    (cost : PR.PolynomialCostModel Word.BitWord) →
    PR.polynomialTimeMap cost totalE20WordReduction →
    PR.PolynomialManyOneReduction
      cost sourceLanguage (graphLanguage boundary)
  e20EncodedPolynomialReductionFromClock =
    Total.makeCostedTotalReduction
