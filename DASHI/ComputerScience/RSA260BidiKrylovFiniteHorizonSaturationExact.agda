module DASHI.ComputerScience.RSA260BidiKrylovFiniteHorizonSaturationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiKrylovReachableRankExact as Rank
import DASHI.ComputerScience.RSA260BidiDynamicRankRepairPresentationTransferExact as Transfer

------------------------------------------------------------------------
-- FINITE-HORIZON KRYLOV SATURATION FIBRE
--
-- Define, for the tested 80-step horizon,
--
--   h80 = min { h <= 80 : r_h = r_80 }.
--
-- This is not an infinite-time saturation theorem.  It is the first tested
-- horizon at which the observed finite-horizon reachable rank attains its
-- value at step 80.
--
-- Exact-byte synthetic observation across 39 cases:
--   18 training carriers
--    6 held-out carriers
--   15 preparation/projection validation cases
--
--   d - h80 in {-1,0,1}.
--
-- All six held-out cases have d-h80 = 1.  The presentation-cross surface has
-- d-h80 in {0,1}.  This envelope is tighter than the earlier r80/block-width
-- ceiling diagnostic but remains experimental rather than a universal formula.
------------------------------------------------------------------------

rankBoundary : Rank.DynamicRankInterpretationBoundary
rankBoundary = Rank.canonicalDynamicRankInterpretationBoundary

transferBoundary : Transfer.PresentationTransferBoundary
transferBoundary = Transfer.canonicalPresentationTransferBoundary

record FiniteHorizonRuntimeSource : Set where
  constructor finite-horizon-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    dependencyPath : String
    dependencyGitBlob : String
    exactTopLevelBlobExecuted : Bool
    exactDependencyBlobExecuted : Bool
open FiniteHorizonRuntimeSource public

currentFiniteHorizonRuntimeSource : FiniteHorizonRuntimeSource
currentFiniteHorizonRuntimeSource = finite-horizon-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_krylov_h80.py"
  "b953d65d94cfe60f5d499f97b7f69b04c7cab5d3"
  "80509498988c47f13a3602c431e60bcca65006af"
  "rsa260_bidi_dynamic_rank_repair_heldout.py"
  "de5ada889c4d06c91b6c5c05f2f966f14d359e51"
  true true

record FiniteHorizonReceipt : Set where
  constructor finite-horizon-receipt
  field
    horizon : Nat
    blockWidth : Nat
    trainingCases : Nat
    heldoutCases : Nat
    presentationCases : Nat
    totalCases : Nat
    combinedMinimumDegreeMinusHorizon : String
    combinedMaximumDegreeMinusHorizon : String
    allCombinedOffsetsWithinMinusOneToPlusOne : Bool
    allHeldoutOffsetsPlusOne : Bool
    presentationMinimumOffset : Nat
    presentationMaximumOffset : Nat
open FiniteHorizonReceipt public

currentFiniteHorizonReceipt : FiniteHorizonReceipt
currentFiniteHorizonReceipt = finite-horizon-receipt
  80 8
  18 6 15 39
  "-1" "1"
  true true
  0 1

record FiniteHorizonInterpretationBoundary : Set where
  constructor finite-horizon-interpretation-boundary
  field
    finiteHorizonCoordinateTighterThanRank80CeilingOnTestedPortfolio : Bool
    finiteHorizonCoordinateIsInfiniteTimeSaturationTheorem : Bool
    degreeAlwaysEqualsH80PlusOne : Bool
    sameObjectKrylovSequenceCanConstrainFiniteHorizonCoordinate : Bool
    finiteHorizonCoordinatePaysMatrixCustody : Bool
    finiteHorizonCoordinatePaysHistoricalIdentity : Bool
    syntheticFiniteHorizonIsProductionMeasurement : Bool
open FiniteHorizonInterpretationBoundary public

canonicalFiniteHorizonInterpretationBoundary : FiniteHorizonInterpretationBoundary
canonicalFiniteHorizonInterpretationBoundary = finite-horizon-interpretation-boundary
  true false false true false false false

data FiniteHorizonResidual : Set where
  explainMinusOneAndZeroOffsets : FiniteHorizonResidual
  extendHorizonBeyond80 : FiniteHorizonResidual
  testIndependentBlockWidths : FiniteHorizonResidual
  measureFiniteHorizonCoordinateOnSameObjectProductionASequence : FiniteHorizonResidual

firstFiniteHorizonResidual : FiniteHorizonResidual
firstFiniteHorizonResidual = explainMinusOneAndZeroOffsets

data FiniteHorizonFitImpliesInfiniteSaturation : Set where
data TightEnvelopeImpliesUniversalFormula : Set where
data FiniteHorizonDiagnosticImpliesMatrixCustody : Set where

finiteHorizonFitDoesNotCreateInfiniteSaturation : FiniteHorizonFitImpliesInfiniteSaturation → ⊥
finiteHorizonFitDoesNotCreateInfiniteSaturation ()

tightEnvelopeDoesNotCreateUniversalFormula : TightEnvelopeImpliesUniversalFormula → ⊥
tightEnvelopeDoesNotCreateUniversalFormula ()

finiteHorizonDiagnosticDoesNotCreateMatrixCustody : FiniteHorizonDiagnosticImpliesMatrixCustody → ⊥
finiteHorizonDiagnosticDoesNotCreateMatrixCustody ()
