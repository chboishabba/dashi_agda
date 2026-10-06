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
    localPythonReproduced : Bool
    provenance : String
open DualGeneralizedQuadrangleComputationReceipt public

canonicalDualGeneralizedQuadrangleComputationReceipt :
  DualGeneralizedQuadrangleComputationReceipt
canonicalDualGeneralizedQuadrangleComputationReceipt =
  dual-generalized-quadrangle-computation-receipt
    E6.localFiniteComputation
    40 40 40
    false true true
    "E6 null projective graph and standard symplectic W(3,3) point graph are non-isomorphic; E6 null graph is isomorphic to the W(3,3) line-intersection graph, consistent with Q(4,3) duality"

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
