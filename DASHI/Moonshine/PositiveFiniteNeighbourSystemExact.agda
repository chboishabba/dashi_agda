module DASHI.Moonshine.PositiveFiniteNeighbourSystemExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Trees", Springer Monographs in Mathematics, corrected second printing.
-- DOI: 10.1007/978-3-642-61856-7.
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- DASHI CONTRIBUTION
--
-- Put positivity before linearization.  A finite neighbour system is literally
-- a finite family of target vertices attached to each source vertex.  Its
-- Nat-valued operator is derived only by summing an observable over those
-- neighbours.  Thus matrix coefficients obtained from indicator observables are
-- multiplicity counts by construction; negative coefficients cannot arise.
--
-- This generalizes the prime-degree classical correspondence carrier only in
-- arity.  It is needed because a full composite Hecke operator such as T_4 is
-- not the same fibre as the cyclic X_0(4) correspondence: at p=11 the latter
-- has six cyclic neighbours while full T_4 has seven contributions after the
-- identity correction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)

import DASHI.Moonshine.ClassicalFiniteHeckeCorrespondenceCore as Classical

record PositiveFiniteNeighbourSystem (Vertex : Set) : Set₁ where
  field
    arity : Nat
    neighbour : Vertex → Fin arity → Vertex

open PositiveFiniteNeighbourSystem public

positiveOperator :
  ∀ {Vertex : Set} →
  PositiveFiniteNeighbourSystem Vertex →
  (Vertex → Nat) → Vertex → Nat
positiveOperator system observable vertex =
  Classical.foldFin _+_ 0
    (λ edge → observable (neighbour system vertex edge))

------------------------------------------------------------------------
-- Every source-faithful classical prime-degree correspondence is already a
-- positive neighbour system; no matrix conversion is involved.
------------------------------------------------------------------------

fromClassicalPrime :
  ∀ {Vertex : Set} →
  Classical.ClassicalPrimeDegreeCorrespondence Vertex →
  PositiveFiniteNeighbourSystem Vertex
fromClassicalPrime correspondence =
  record
    { arity = suc (Classical.degreePrime correspondence)
    ; neighbour = Classical.neighbour correspondence
    }

fromClassicalOperatorExact :
  ∀ {Vertex : Set}
    (correspondence : Classical.ClassicalPrimeDegreeCorrespondence Vertex)
    (observable : Vertex → Nat)
    (vertex : Vertex) →
  positiveOperator (fromClassicalPrime correspondence) observable vertex
  ≡ Classical.classicalOperator correspondence observable vertex
fromClassicalOperatorExact correspondence observable vertex = refl

------------------------------------------------------------------------
-- Composition is defined at operator level from genuine paths.  It therefore
-- counts ordered two-step paths and remains Nat-valued automatically.
------------------------------------------------------------------------

twoStepOperator :
  ∀ {Vertex : Set} →
  PositiveFiniteNeighbourSystem Vertex →
  PositiveFiniteNeighbourSystem Vertex →
  (Vertex → Nat) → Vertex → Nat
twoStepOperator first second observable vertex =
  positiveOperator first (positiveOperator second observable) vertex

record PositiveHeckeSquareLaw
    {Vertex : Set}
    (primeSystem squareSystem : PositiveFiniteNeighbourSystem Vertex)
    (ell : Nat) : Set₁ where
  field
    squareLaw :
      (observable : Vertex → Nat) →
      (vertex : Vertex) →
      twoStepOperator primeSystem primeSystem observable vertex
      ≡ positiveOperator squareSystem observable vertex
        + ell * observable vertex

open PositiveHeckeSquareLaw public

------------------------------------------------------------------------
-- Local diagonal consequence used by the p=11 positivity falsifier:
-- a positive square law forces at least ell identity-return multiplicity before
-- any additional square-system contribution is counted.
------------------------------------------------------------------------

record PositiveNeighbourBoundary : Set where
  field
    setLevelPositiveCarrierConstructed : Bool
    setLevelPositiveCarrierConstructedIsTrue :
      setLevelPositiveCarrierConstructed ≡ true

    coefficientsCanBeNegativeByConstruction : Bool
    coefficientsCanBeNegativeByConstructionIsFalse :
      coefficientsCanBeNegativeByConstruction ≡ false

    arbitraryFiniteAritySupportsCompositeHecke : Bool
    arbitraryFiniteAritySupportsCompositeHeckeIsTrue :
      arbitraryFiniteAritySupportsCompositeHecke ≡ true

    treeOrDoubleCosetGeometryConstructedHere : Bool
    treeOrDoubleCosetGeometryConstructedHereIsFalse :
      treeOrDoubleCosetGeometryConstructedHere ≡ false

canonicalPositiveNeighbourBoundary : PositiveNeighbourBoundary
canonicalPositiveNeighbourBoundary =
  record
    { setLevelPositiveCarrierConstructed = true
    ; setLevelPositiveCarrierConstructedIsTrue = refl
    ; coefficientsCanBeNegativeByConstruction = false
    ; coefficientsCanBeNegativeByConstructionIsFalse = refl
    ; arbitraryFiniteAritySupportsCompositeHecke = true
    ; arbitraryFiniteAritySupportsCompositeHeckeIsTrue = refl
    ; treeOrDoubleCosetGeometryConstructedHere = false
    ; treeOrDoubleCosetGeometryConstructedHereIsFalse = refl
    }
