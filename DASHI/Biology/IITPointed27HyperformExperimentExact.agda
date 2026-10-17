module DASHI.Biology.IITPointed27HyperformExperimentExact where

open import DASHI.Core.Prelude

import DASHI.Biology.IITPointedTernary27FaceGluingExact as Face
import DASHI.Biology.IITPointedTernary27Origin26Exact as Origin26
import DASHI.Biology.IITPointedTernary27CyclotomicCellExact as Cyclotomic
import DASHI.Biology.IITPointedTernary27Recentered26Exact as Recenter
import DASHI.Biology.IITPointedTernary27TriadicNonDescentExact as Triadic
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

------------------------------------------------------------------------
-- POINTED-27 EXPERIMENT ENVELOPE
--
-- The geometry supplies a finite carrier and admissibility constraints, not a
-- transition probability function.  The executable scan therefore audits the
-- complete incidence envelope while refusing to manufacture IIT probabilities
-- from geometric adjacency.
------------------------------------------------------------------------

canonicalOriginPlus26 : Origin26.PointedOriginShape27
canonicalOriginPlus26 = Origin26.toOriginPlus26 Geometry.origin

originPlusTwentySixRoundTrip :
  Origin26.fromOriginPlus26 canonicalOriginPlus26 ≡ Geometry.origin
originPlusTwentySixRoundTrip = Origin26.originPlus26FromAfterTo Geometry.origin

outerFaceIsNine : 1 + Face.outerFacePunctureCount ≡ Face.outerFaceSheetCount
outerFaceIsNine = Face.outerFaceSheetIsOnePlusEight

centreHasNoOuterFace :
  (face : Geometry.Face6) → Geometry.OnFace face Geometry.origin → ⊥
centreHasNoOuterFace = Face.originNotOnOuterFace

threeSelectedChoiceCount : Face.threeActiveCubieChoiceCount ≡ Geometry.hyperfabricStateCount
threeSelectedChoiceCount = Face.threeActiveCubieChoiceCountIsHyperformCount

selectedCubiesStillDoNotDetermineTriadicFace :
  Descent.FactorsThrough Triadic.selectedCubiesObserver Triadic.triadicFaceConsumer → ⊥
selectedCubiesStillDoNotDetermineTriadicFace =
  Triadic.selectedCubiesDoNotDetermineTriadicFace

------------------------------------------------------------------------
-- Cyclotomic chart is an exact carrier chart but not geometric recentering.
------------------------------------------------------------------------

selectedCellRecoversCubie :
  (cube : Face.PointedTernary27Cube) →
  Cyclotomic.cell27ToPoint (Cyclotomic.activeCell27 cube)
  ≡ Face.activeCubie cube
selectedCellRecoversCubie = Cyclotomic.activeCellRecoversSelectedCubie

recentringNotGeometricSymmetry :
  Recenter.recenteringPreservesNonperiodicGridAdjacencyByDefinition
    Recenter.canonicalRecentered26Boundary ≡ false
recentringNotGeometricSymmetry = Recenter.recentringDoesNotManufactureGeometricSymmetry

------------------------------------------------------------------------
-- Numerical combinatorics receipt.
------------------------------------------------------------------------

record Pointed27ScanReceipt : Set where
  constructor pointed27ScanReceipt
  field
    carrierSize : Nat
    zeroFacePointCount : Nat
    oneFacePointCount : Nat
    twoFacePointCount : Nat
    threeFacePointCount : Nat
    totalPointFaceIncidences : Nat
    pairwiseFaceOverlapCount : Nat
    cornerTripleCount : Nat
    threeSelectedCubieChoices : Nat
    scanner : String

open Pointed27ScanReceipt public

currentPointed27ScanReceipt : Pointed27ScanReceipt
currentPointed27ScanReceipt =
  pointed27ScanReceipt 27 1 6 12 8 54 12 8 19683
    "scripts/iit_pointed27_gluing_scan.py"

record Pointed27ExperimentBoundary : Set where
  constructor pointed27ExperimentBoundary
  field
    exactCarrierAndIncidenceReused : Bool
    activeFaceWitnessRequired : Bool
    edgeTransportRequiredForFaceGluing : Bool
    cornerCocycleRequiredForTripleCompatibility : Bool
    selectedCubieAloneDeterminesGluing : Bool
    geometryAloneDefinesIITTransitionProbability : Bool
    c3RecentringCanonicalForNonperiodicGeometry : Bool
    pythonIncidenceReceiptIsKernelProof : Bool

open Pointed27ExperimentBoundary public

canonicalPointed27ExperimentBoundary : Pointed27ExperimentBoundary
canonicalPointed27ExperimentBoundary =
  pointed27ExperimentBoundary true true true true false false false false

geometryDoesNotManufactureTPM :
  geometryAloneDefinesIITTransitionProbability
    canonicalPointed27ExperimentBoundary ≡ false
geometryDoesNotManufactureTPM = refl

selectionDoesNotManufactureGluing :
  selectedCubieAloneDeterminesGluing
    canonicalPointed27ExperimentBoundary ≡ false
selectionDoesNotManufactureGluing = refl
