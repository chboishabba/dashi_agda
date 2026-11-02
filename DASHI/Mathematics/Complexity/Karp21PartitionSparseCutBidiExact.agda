{-# OPTIONS --safe #-}

module DASHI.Mathematics.Complexity.Karp21PartitionSparseCutBidiExact where

------------------------------------------------------------------------
-- E20 x N21: ORIGINAL SIGNED PARTITION <-> ACTUAL SPARSE CUT WORD.
--
-- Reuse, without cloning:
--  * Source.PartitionYES on signed List Integer, preserving multiplicity;
--  * Actual.sourcePartitionActualPositiveGraphIff on the real
--    Karp weighted edge-list graph, including the total-zero YES branch;
--  * Sparse.verifySparseCutBitWord with TWO bits per listed edge;
--  * N21.sparseAcceptedBitWordImpliesFullGraphYES (arbitrary local code).
--
-- This module makes the E20->N21 finite search/decision BIDI commute
-- with the exact graph produced by the original E20 construction.
-- It also certifies the witness's exact 2m bit count and the actual
-- complete-graph upper-triangle count in the nonzero-total branch.
--
-- NOT YET: a canonical binary graph INPUT parser/encoder, signed
-- integer bit-complexity clock, Agda kernel acceptance, or a
-- PolynomialManyOneReduction on BitWord. No NP-completeness claim.
--
-- Authorities: Cook (1971), Leonid Levin (1973 search), Karp (1972).
-- DASHI source proof owners: E20 actual graph and N21 sparse extension.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; length)
open import Data.List.Properties as ListP using (length-map)
open import Data.Product using (Σ; _×_; _,_)

open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21PartitionScaledInstanceExact as Source
import DASHI.Mathematics.Complexity.Karp21ScaledThresholdExact as Threshold
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SignedPartitionIndexedGraphDecisionExact as Indexed
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphGeneratorExact as Gen
import DASHI.Mathematics.Complexity.Karp21SignedGraphScaleAndAppendExact as Scale
import DASHI.Mathematics.Complexity.Karp21SignedPartitionActualGraphYESExact as Actual
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21SparseEndpointConsistencySoundExact as N21

------------------------------------------------------------------------
-- No bound on the total declared number of vertices n is used.
-- The witness contains exactly two bits for each listed edge.
------------------------------------------------------------------------

SizeExactSparseCutYES :
  ∀ {n} → Cut.WeightedCutGraph n → Set
SizeExactSparseCutYES graph =
  Σ Word.BitWord (λ bits →
    (Word.encodingSize bits
      ≡ Sparse.twoPerEdge (length (Cut.edges graph)))
    × (Sparse.verifySparseCutBitWord graph bits ≡ true))

actualCutToSizeExactSparse :
  ∀ {n} (graph : Cut.WeightedCutGraph n) →
  Cut.WeightedMaxCutYES graph → SizeExactSparseCutYES graph
actualCutToSizeExactSparse graph (labels , accepted) =
  Sparse.encodeSparseEdgeBits
    (Sparse.projectEdgeBits (Cut.edges graph) labels)
  ,
    ( Sparse.fullWitnessHasTwoBitsPerListedEdge graph labels
    , trans
        (Sparse.projectedSparseBitWordVerifierEqualsOriginal
          graph labels)
        (N21.boolTImpliesTrue
          (Cut.verifyWeightedMaxCut graph labels)
          (Cut.weightedMaxCutVerifierComplete graph labels accepted))
    )

sizeExactSparseToActualCut :
  ∀ {n} (graph : Cut.WeightedCutGraph n) →
  SizeExactSparseCutYES graph → Cut.WeightedMaxCutYES graph
sizeExactSparseToActualCut graph (bits , (_ , accepted)) =
  N21.sparseAcceptedBitWordImpliesFullGraphYES graph bits accepted

actualCutSizeExactSparseIff :
  ∀ {n} (graph : Cut.WeightedCutGraph n) →
  PR.Iff (Cut.WeightedMaxCutYES graph) (SizeExactSparseCutYES graph)
actualCutSizeExactSparseIff graph =
  PR.iff (actualCutToSizeExactSparse graph)
         (sizeExactSparseToActualCut graph)

------------------------------------------------------------------------
-- E20 uses the ORIGINAL typed positive-threshold target.
-- The exceptional source-total-zero case is a fixed unit-edge YES
-- graph; no graph-only marker or witness-dependent branch is used.
------------------------------------------------------------------------

E20SizeExactSparseTargetYES : Source.PositiveCutTarget → Set
E20SizeExactSparseTargetYES Source.unitEdgeYesPositive =
  SizeExactSparseCutYES Actual.fixedUnitGraph
E20SizeExactSparseTargetYES
  (Source.scaledCompletePositive parts nonzero) =
  SizeExactSparseCutYES (Actual.sourceIndexedWeightedGraph parts nonzero)

actualTargetSizeExactSparseIff :
  (target : Source.PositiveCutTarget) →
  PR.Iff (Actual.ActualPositiveTargetAccepts target)
    (E20SizeExactSparseTargetYES target)
actualTargetSizeExactSparseIff Source.unitEdgeYesPositive =
  actualCutSizeExactSparseIff Actual.fixedUnitGraph
actualTargetSizeExactSparseIff
  (Source.scaledCompletePositive parts nonzero) =
  actualCutSizeExactSparseIff
    (Actual.sourceIndexedWeightedGraph parts nonzero)

-- Both translations are on the SAME source integer list and the SAME
-- constructed finite weighted graph, not independently chosen objects.
e20PartitionSizeExactSparseBidi :
  (parts : List ℤ) →
  PR.Iff (Source.PartitionYES parts)
    (E20SizeExactSparseTargetYES
      (Source.totalPartitionToPositiveCut parts))
e20PartitionSizeExactSparseBidi parts =
  PR.iffTransitive
    (Actual.sourcePartitionActualPositiveGraphIff parts)
    (actualTargetSizeExactSparseIff
      (Source.totalPartitionToPositiveCut parts))

e20PartitionToSparseSearch :
  (parts : List ℤ) →
  Source.PartitionYES parts →
  E20SizeExactSparseTargetYES
    (Source.totalPartitionToPositiveCut parts)
e20PartitionToSparseSearch parts =
  PR.forward (e20PartitionSizeExactSparseBidi parts)

e20SparseSearchToPartition :
  (parts : List ℤ) →
  E20SizeExactSparseTargetYES
    (Source.totalPartitionToPositiveCut parts) →
  Source.PartitionYES parts
e20SparseSearchToPartition parts =
  PR.backward (e20PartitionSizeExactSparseBidi parts)

------------------------------------------------------------------------
-- The nonzero-total graph has exactly n(n-1)/2 edge occurrences,
-- where n = length parts; scaling weights adds NO extra edges.
-- This is an exact count, not a full bit-machine complexity proof.
------------------------------------------------------------------------

scaledGraphUpperPairCount :
  (parts : List ℤ)
  (nonzero : Threshold.NonZero (Source.sourceTotal parts)) →
  length (Cut.edges (Actual.sourceIndexedWeightedGraph parts nonzero))
    ≡ Gen.triangularPairCount (length parts)
scaledGraphUpperPairCount parts nonzero =
  trans
    (ListP.length-map Scale.scaleEdgeWeightFour
      (Gen.completePairEdges (Indexed.vectorOfList parts)))
    (Gen.completePairCount (Indexed.vectorOfList parts))

scaledGraphSparseSearchExactTriangularBits :
  (parts : List ℤ)
  (nonzero : Threshold.NonZero (Source.sourceTotal parts)) →
  Cut.WeightedMaxCutYES
    (Actual.sourceIndexedWeightedGraph parts nonzero) →
  Σ Word.BitWord (λ bits →
    (Word.encodingSize bits
      ≡ Sparse.twoPerEdge (Gen.triangularPairCount (length parts)))
    × (Sparse.verifySparseCutBitWord
         (Actual.sourceIndexedWeightedGraph parts nonzero) bits ≡ true))
scaledGraphSparseSearchExactTriangularBits parts nonzero accepted
  with actualCutToSizeExactSparse
    (Actual.sourceIndexedWeightedGraph parts nonzero) accepted
... | bits , (size , verified) =
  bits ,
    ( trans size
        (cong Sparse.twoPerEdge
          (scaledGraphUpperPairCount parts nonzero))
    , verified )
