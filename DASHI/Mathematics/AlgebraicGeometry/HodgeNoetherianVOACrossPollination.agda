module DASHI.Mathematics.AlgebraicGeometry.HodgeNoetherianVOACrossPollination where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Claire Voisin,
-- "Hodge Theory and Complex Algebraic Geometry I".
-- DOI: 10.1017/CBO9780511615344.
--
-- Emmy Noether,
-- "Idealtheorie in Ringbereichen".
-- DOI: 10.1007/BF01464225.
--
-- DASHI CONTRIBUTION
--
-- Connect the native Hodge/cycle-class surface to the existing Noetherian
-- obligation layer and the new graded-VOA layer.  Noetherianity controls finite
-- algebraic presentation; it does not prove analytic Hodge decomposition or
-- cycle-class surjectivity.  A VOA/elliptic-genus bridge likewise requires
-- separate geometric and modularity inputs.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Algebra.NoetherianityMeaningSeparationExact as N
import DASHI.Mathematics.AlgebraicGeometry.HodgeDecompositionCycleClassExact as H
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as VOA

record HodgeNoetherianBridge
    (variety : H.SmoothProjectiveComplexVariety)
    (comparison : H.SingularDeRhamComparison variety)
    (hodge : H.HodgeDecomposition variety comparison)
    (cycleMap : H.CycleClassMap variety comparison hodge) : Setω where
  field
    coordinateRingNoetherianity : N.NoetherianEquivalenceObligation
    coherentSheafFinitePresentation : Set
    cycleGroupFinitePresentationAtDegree : Nat → Set
    cycleRelationsNoetherian : Set
    analyticHodgeDecompositionIndependentInput : Set

record HodgeVOABridge
    (variety : H.SmoothProjectiveComplexVariety) : Setω where
  field
    Scalar GroupCarrier : Set
    gradedVOAAction : VOA.VOAWithGroupAction GroupCarrier Scalar
    chiralDeRhamOrEllipticGenusConstruction : Set
    cohomologicalGradingMatchesVOAGrading : Set
    ellipticGenusAsGradedSupertrace : Set
    modularityTheorem : Set
    cycleClassCompatibility : Set

hodgeConjectureRepresentativeReused :
  ∀ {variety : H.SmoothProjectiveComplexVariety}
    {comparison : H.SingularDeRhamComparison variety}
    {hodge : H.HodgeDecomposition variety comparison}
    {cycleMap : H.CycleClassMap variety comparison hodge}
    {codimension : Nat} →
  (conjecture : H.HodgeConjectureAtCodimension
    {variety = variety}
    {comparison = comparison}
    {hodge = hodge}
    cycleMap codimension) →
  (hodgeClass : H.RationalHodgeClass hodge codimension) →
  H.cycleClass cycleMap codimension
    (H.everyRationalHodgeClassHasCycle conjecture hodgeClass)
  ≡ H.hodgeClassValue hodgeClass
hodgeConjectureRepresentativeReused =
  H.hodgeConjectureGivesCycleRepresentative

data HodgeProofOwner : Set where
  noetherianFinitePresentation
  analyticHodgeDecomposition
  algebraicCycleClassConstruction
  rationalHodgeClassSurjectivity
  voaEllipticGenusModularity

noetherianityDoesNotProveHodgeDecomposition :
  noetherianFinitePresentation ≡ analyticHodgeDecomposition → ⊥
noetherianityDoesNotProveHodgeDecomposition ()

voaModularityDoesNotProveCycleSurjectivity :
  voaEllipticGenusModularity ≡ rationalHodgeClassSurjectivity → ⊥
voaModularityDoesNotProveCycleSurjectivity ()
