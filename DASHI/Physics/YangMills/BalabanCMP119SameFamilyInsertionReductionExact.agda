module DASHI.Physics.YangMills.BalabanCMP119SameFamilyInsertionReductionExact where

------------------------------------------------------------------------
-- ROUND82: ONE SOURCE INSERTION CLASS FOR ORDINARY + CHARACTERISTIC RESPONSE
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
-- Sect. 3, especially (3.44)--(3.47), is the normalized anchored expectation
-- expansion used here.
--
-- DASHI CONTRIBUTION
--
-- Round81 had two independent-looking physical hypotheses saying that ordinary
-- and characteristic differences lie below the generated localized tail.  That
-- duplicates the real source mechanism.  Both consumers are normalized local
-- insertions into the SAME finite-cutoff density.  This module makes the only
-- honest new seam a single kind-indexed source-insertion dictionary plus one
-- common scale-tail estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119AnchoredNormalizedExpectationSourceExact as Source
import DASHI.Physics.YangMills.BalabanTopDownSummableRGIncrementExact as Sum
import DASHI.Physics.YangMills.BalabanClayT2UrsellCauchyExact as Ursell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo


data ResponseKind : Set where
  ordinary characteristic : ResponseKind

record SameFamilyCMP119InsertionReduction
    (source : Source.CMP119AnchoredNormalizedExpectationSource) : Set₁ where
  field
    RepositoryInsertion : ResponseKind → Set

    insertionAnchor : ∀ kind →
      RepositoryInsertion kind → Source.Anchor source

    sourceLocalAnalytic : ∀ kind →
      RepositoryInsertion kind → Set

    normalizedExpectation :
      ∀ kind (scale : Source.Scale source) (insertion : RepositoryInsertion kind) →
      Source.NormalizedExpectation source scale (insertionAnchor kind insertion)

    sourceRepresentation :
      ∀ kind scale insertion →
      sourceLocalAnalytic kind insertion →
      Source.representedByAnchoredTerms source scale
        (insertionAnchor kind insertion)
        (normalizedExpectation kind scale insertion)

    -- ONE source-shaped generated increment for the same density.  This is the
    -- remaining analytic quantity after source denominator cancellation.
    generatedIncrement : Nat → ℚ
    generatedIncrementNonnegative : ∀ scale →
      0ℚ ≤ generatedIncrement scale

    coefficient : ℚ
    coefficientNonnegative : 0ℚ ≤ coefficient

    generatedIncrementDyadic : ∀ scale →
      generatedIncrement scale
      ≤ coefficient * (Ursell.quarter * Geo.halfPower scale)

    responseDifference : ResponseKind → Nat → Nat → ℚ
    responseDifferenceNonnegative : ∀ kind start count →
      0ℚ ≤ responseDifference kind start count

    -- The same connected anchored tail controls both kinds.  This is no longer
    -- a separate cluster-expansion theorem per consumer.
    responseBelowGeneratedTail : ∀ kind start count →
      responseDifference kind start count
      ≤ Sum.generatedTail generatedIncrement start count

open SameFamilyCMP119InsertionReduction public

asPublishedTailToCommonIncrement :
  ∀ {source} →
  SameFamilyCMP119InsertionReduction source →
  Sum.PublishedTailToCommonIncrement
asPublishedTailToCommonIncrement dataSet = record
  { Sum.PublishedTailToCommonIncrement.sourceGeneratedIncrement =
      generatedIncrement dataSet
  ; Sum.PublishedTailToCommonIncrement.sourceGeneratedIncrementNonnegative =
      generatedIncrementNonnegative dataSet
  ; Sum.PublishedTailToCommonIncrement.coefficient = coefficient dataSet
  ; Sum.PublishedTailToCommonIncrement.coefficientNonnegative =
      coefficientNonnegative dataSet
  ; Sum.PublishedTailToCommonIncrement.generatedIncrementDyadic =
      generatedIncrementDyadic dataSet
  ; Sum.PublishedTailToCommonIncrement.ordinaryDifference =
      responseDifference dataSet ordinary
  ; Sum.PublishedTailToCommonIncrement.characteristicDifference =
      responseDifference dataSet characteristic
  ; Sum.PublishedTailToCommonIncrement.ordinaryDifferenceNonnegative =
      responseDifferenceNonnegative dataSet ordinary
  ; Sum.PublishedTailToCommonIncrement.characteristicDifferenceNonnegative =
      responseDifferenceNonnegative dataSet characteristic
  ; Sum.PublishedTailToCommonIncrement.ordinaryResponseBelowGeneratedTail =
      responseBelowGeneratedTail dataSet ordinary
  ; Sum.PublishedTailToCommonIncrement.characteristicResponseBelowGeneratedTail =
      responseBelowGeneratedTail dataSet characteristic
  }

sameFamilyInsertionReductionCompilerLevel : ProofLevel
sameFamilyInsertionReductionCompilerLevel = machineChecked

-- Source-owned after CMP119 (3.44)--(3.47): numerator/denominator cluster
-- cancellation and anchored exponential localization.
normalizedExpectationClusterCancellationLevel : ProofLevel
normalizedExpectationClusterCancellationLevel = standardImported

-- Remaining L2 seam after Round82: instantiate the ordinary and compact-support
-- characteristic insertions in this one source class and prove that the change
-- between successive UV cutoffs is the source generated tail with its dyadic
-- scale factor.  No second normalized-cluster theorem is required.
sameFamilySourceInsertionScaleTailLevel : ProofLevel
sameFamilySourceInsertionScaleTailLevel = conditional
