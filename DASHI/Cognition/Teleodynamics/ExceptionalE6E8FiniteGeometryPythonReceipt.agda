module DASHI.Cognition.Teleodynamics.ExceptionalE6E8FiniteGeometryPythonReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.Teleodynamics.ExceptionalE6Mod3FiniteGeometryExact as E6

------------------------------------------------------------------------
-- LOCAL PYTHON FINITE-COMPUTATION RECEIPT
--
-- Evidence only. This file intentionally does not turn a local Python run into
-- an Agda theorem. It records the exact checks performed after the formal
-- target surface was written.
------------------------------------------------------------------------

record E6WeylComputationReceipt : Set where
  constructor e6-weyl-computation-receipt
  field
    grade : E6.EvidenceGrade
    generatedWeylMatrices : Nat
    expectedWeylOrder : Nat
    simpleReflectionNullFixedCount : Nat
    allSixSimpleReflectionsHaveSameNullFixedCount : Bool
    rootLineOrthogonalNeighborhoodSize : Nat
    orthogonalNeighborhoodIsKG62 : Bool
    localPythonReproduced : Bool
    provenance : String
open E6WeylComputationReceipt public

canonicalE6WeylComputationReceipt : E6WeylComputationReceipt
canonicalE6WeylComputationReceipt =
  e6-weyl-computation-receipt
    E6.localFiniteComputation
    51840 51840 20 true 15 true true
    "generated from the six standard E6 simple reflections; quotient matrices preserve the mod-3 bilinear form; finite BFS and graph isomorphism checked locally"

record HyperfabricNormalizerComputationReceipt : Set where
  constructor hyperfabric-normalizer-computation-receipt
  field
    grade : E6.EvidenceGrade
    h4Count h3Count h2Count h1Count : Nat
    h4Stabilizer h3Stabilizer h2Stabilizer h1Stabilizer : Nat
    h3ReflectionCoreOrder h2ReflectionCoreOrder : Nat
    h4h3Edges h3h2Edges h2h1Edges : Nat
    completeFlags completeFlagStabilizer : Nat
    rootNeighborhoodIsKG62 : Bool
    localPythonReproduced : Bool
    provenance : String
open HyperfabricNormalizerComputationReceipt public

canonicalHyperfabricNormalizerComputationReceipt :
  HyperfabricNormalizerComputationReceipt
canonicalHyperfabricNormalizerComputationReceipt =
  hyperfabric-normalizer-computation-receipt
    E6.localFiniteComputation
    36 120 270 36
    1440 432 192 1440
    216 96
    360 1080 540
    6480 8
    true true
    "exhaustive projective-subspace enumeration plus reduced W(E6) BFS; H3 reflection core has order 216 = |W(A2^3)| and H2 core order 96 = |W(A1^2 x A3)|"

record A2CubedRadicalComputationReceipt : Set where
  constructor a2-cubed-radical-computation-receipt
  field
    grade : E6.EvidenceGrade
    h3PatchCount : Nat
    distinctA2CubedSubsystems : Nat
    patchesPerA2CubedSubsystem : Nat
    nullProjectiveLines : Nat
    uniqueRadicalPerH3 : Bool
    sameRadicalIffSameA2CubedSubsystem : Bool
    localPythonReproduced : Bool
    provenance : String
open A2CubedRadicalComputationReceipt public

canonicalA2CubedRadicalComputationReceipt : A2CubedRadicalComputationReceipt
canonicalA2CubedRadicalComputationReceipt =
  a2-cubed-radical-computation-receipt
    E6.localFiniteComputation
    120 40 3 40
    true true true
    "each H3 has one radical null line and a 9-projective-root A2^3 subsystem; the 120 H3 patches collapse to 40 subsystem classes, exactly three patches per radical/subsystem class"

record E8OrderThreeComputationReceipt : Set where
  constructor e8-order-three-computation-receipt
  field
    grade : E6.EvidenceGrade
    e8RootCount : Nat
    fixedRoots : Nat
    orderThreeOrbitCount : Nat
    orbitSize : Nat
    smithUnitFactors : Nat
    smithThreeFactors : Nat
    quotientDimensionOverF3 : Nat
    nonzeroQuotientClasses : Nat
    rootsPerNonzeroClass : Nat
    allNonzeroClassesHit : Bool
    localPythonReproduced : Bool
    provenance : String
open E8OrderThreeComputationReceipt public

canonicalE8OrderThreeComputationReceipt : E8OrderThreeComputationReceipt
canonicalE8OrderThreeComputationReceipt =
  e8-order-three-computation-receipt
    E6.localFiniteComputation
    240 0 80 3
    4 4 4 80 3
    true true
    "fixed-point-free order-three E8 Weyl element from four mutually orthogonal A2 Coxeter factors; SNF(1-w)=diag(1,1,1,1,3,3,3,3)"

record DualGeneralizedQuadrangleComputationReceipt : Set where
  constructor dual-generalized-quadrangle-computation-receipt
  field
    grade : E6.EvidenceGrade
    e6NullProjectivePoints : Nat
    e8SymplecticProjectivePoints : Nat
    e8SymplecticLines : Nat
    e6NullPointGraphIsomorphicToE8PointGraph : Bool
    e6NullPointGraphIsomorphicToE8LineIntersectionGraph : Bool
    a2CubedGraphIsomorphicToE8LineIntersectionGraph : Bool
    localPythonReproduced : Bool
    provenance : String
open DualGeneralizedQuadrangleComputationReceipt public

canonicalDualGeneralizedQuadrangleComputationReceipt :
  DualGeneralizedQuadrangleComputationReceipt
canonicalDualGeneralizedQuadrangleComputationReceipt =
  dual-generalized-quadrangle-computation-receipt
    E6.localFiniteComputation
    40 40 40
    false true true true
    "E6 null projective graph is not the W(3,3) point graph; it is isomorphic to the W(3,3) line-intersection graph. Reindexing the same E6 null graph by its canonical 40 A2^3 radical classes gives the same tested dual-line weld."

record T4LinearObstructionComputationReceipt : Set where
  constructor t4-linear-obstruction-computation-receipt
  field
    grade : E6.EvidenceGrade
    e6SimpleReflectionFixedSignedNullStates : Nat
    possibleLinearF3FourNonzeroFixedCounts : String
    observedCountOccursInLinearList : Bool
    naiveLinearT4IdentificationSurvives : Bool
    provenance : String
open T4LinearObstructionComputationReceipt public

canonicalT4LinearObstructionComputationReceipt :
  T4LinearObstructionComputationReceipt
canonicalT4LinearObstructionComputationReceipt =
  t4-linear-obstruction-computation-receipt
    E6.localFiniteComputation
    20
    "0,2,8,26,80"
    false false
    "a linear endomorphism of F3^4 fixes 3^d vectors, hence 3^d-1 nonzero vectors; 20 is impossible"
