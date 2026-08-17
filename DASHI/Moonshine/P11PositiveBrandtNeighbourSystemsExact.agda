module DASHI.Moonshine.P11PositiveBrandtNeighbourSystemsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- Reinier Bröker, Kristin Lauter and Andrew V. Sutherland,
-- "Modular polynomials via isogeny volcanoes",
-- Mathematics of Computation 81 (2012), 1201--1231.
-- DOI: 10.1090/S0025-5718-2011-02508-1.
--
-- Andrew V. Sutherland,
-- classical modular-polynomial coefficient datasets Phi_2, Phi_3, Phi_5.
-- No DOI asserted for the datasets themselves.
--
-- DASHI CONTRIBUTION
--
-- Realize the already-verified characteristic-11 Brandt matrices as literal
-- positive neighbour systems on the actual supersingular carrier before any
-- linearization.  The operator coefficients below are therefore counts of
-- concrete neighbours and are Nat-valued by construction.
--
--   B_11(2) = [[0,3],[2,1]]
--   B_11(3) = [[1,3],[2,2]]
--   B_11(5) = [[3,3],[2,4]].
--
-- This is the source-facing positive arithmetic target that a future tree,
-- double-coset or representation geometry must map to.  No representation-side
-- lift is manufactured here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)

import DASHI.Moonshine.ClassicalFiniteHeckeCorrespondenceCore as Classical
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo
import DASHI.Moonshine.P11BrandtPrimeGeneratorsExact as Brandt

------------------------------------------------------------------------
-- Indicators on the actual two supersingular classes.
------------------------------------------------------------------------

indicatorJ0 : Geo.P11SupersingularJ → Nat
indicatorJ0 Geo.jZeroSS = 1
indicatorJ0 Geo.j1728SS = 0

indicatorJ1728 : Geo.P11SupersingularJ → Nat
indicatorJ1728 Geo.jZeroSS = 0
indicatorJ1728 Geo.j1728SS = 1

------------------------------------------------------------------------
-- ell = 2: three actual neighbours counted with multiplicity.
------------------------------------------------------------------------

ell2Neighbour : Geo.P11SupersingularJ → Fin 3 → Geo.P11SupersingularJ
ell2Neighbour Geo.jZeroSS zero = Geo.j1728SS
ell2Neighbour Geo.jZeroSS (suc zero) = Geo.j1728SS
ell2Neighbour Geo.jZeroSS (suc (suc zero)) = Geo.j1728SS
ell2Neighbour Geo.j1728SS zero = Geo.jZeroSS
ell2Neighbour Geo.j1728SS (suc zero) = Geo.jZeroSS
ell2Neighbour Geo.j1728SS (suc (suc zero)) = Geo.j1728SS

B11ell2Positive : Classical.ClassicalPrimeDegreeCorrespondence Geo.P11SupersingularJ
B11ell2Positive =
  record
    { Classical.degreePrime = 2
    ; Classical.neighbour = ell2Neighbour
    }

ell2J0ToJ0 :
  Classical.classicalOperator B11ell2Positive indicatorJ0 Geo.jZeroSS ≡ 0
ell2J0ToJ0 = refl

ell2J0ToJ1728 :
  Classical.classicalOperator B11ell2Positive indicatorJ1728 Geo.jZeroSS ≡ 3
ell2J0ToJ1728 = refl

ell2J1728ToJ0 :
  Classical.classicalOperator B11ell2Positive indicatorJ0 Geo.j1728SS ≡ 2
ell2J1728ToJ0 = refl

ell2J1728ToJ1728 :
  Classical.classicalOperator B11ell2Positive indicatorJ1728 Geo.j1728SS ≡ 1
ell2J1728ToJ1728 = refl

------------------------------------------------------------------------
-- ell = 3: four positive neighbours.
------------------------------------------------------------------------

ell3Neighbour : Geo.P11SupersingularJ → Fin 4 → Geo.P11SupersingularJ
ell3Neighbour Geo.jZeroSS zero = Geo.jZeroSS
ell3Neighbour Geo.jZeroSS (suc zero) = Geo.j1728SS
ell3Neighbour Geo.jZeroSS (suc (suc zero)) = Geo.j1728SS
ell3Neighbour Geo.jZeroSS (suc (suc (suc zero))) = Geo.j1728SS
ell3Neighbour Geo.j1728SS zero = Geo.jZeroSS
ell3Neighbour Geo.j1728SS (suc zero) = Geo.jZeroSS
ell3Neighbour Geo.j1728SS (suc (suc zero)) = Geo.j1728SS
ell3Neighbour Geo.j1728SS (suc (suc (suc zero))) = Geo.j1728SS

B11ell3Positive : Classical.ClassicalPrimeDegreeCorrespondence Geo.P11SupersingularJ
B11ell3Positive =
  record
    { Classical.degreePrime = 3
    ; Classical.neighbour = ell3Neighbour
    }

ell3J0ToJ0 :
  Classical.classicalOperator B11ell3Positive indicatorJ0 Geo.jZeroSS ≡ 1
ell3J0ToJ0 = refl

ell3J0ToJ1728 :
  Classical.classicalOperator B11ell3Positive indicatorJ1728 Geo.jZeroSS ≡ 3
ell3J0ToJ1728 = refl

ell3J1728ToJ0 :
  Classical.classicalOperator B11ell3Positive indicatorJ0 Geo.j1728SS ≡ 2
ell3J1728ToJ0 = refl

ell3J1728ToJ1728 :
  Classical.classicalOperator B11ell3Positive indicatorJ1728 Geo.j1728SS ≡ 2
ell3J1728ToJ1728 = refl

------------------------------------------------------------------------
-- ell = 5: six positive neighbours.
------------------------------------------------------------------------

ell5Neighbour : Geo.P11SupersingularJ → Fin 6 → Geo.P11SupersingularJ
ell5Neighbour Geo.jZeroSS zero = Geo.jZeroSS
ell5Neighbour Geo.jZeroSS (suc zero) = Geo.jZeroSS
ell5Neighbour Geo.jZeroSS (suc (suc zero)) = Geo.jZeroSS
ell5Neighbour Geo.jZeroSS (suc (suc (suc zero))) = Geo.j1728SS
ell5Neighbour Geo.jZeroSS (suc (suc (suc (suc zero)))) = Geo.j1728SS
ell5Neighbour Geo.jZeroSS (suc (suc (suc (suc (suc zero))))) = Geo.j1728SS
ell5Neighbour Geo.j1728SS zero = Geo.jZeroSS
ell5Neighbour Geo.j1728SS (suc zero) = Geo.jZeroSS
ell5Neighbour Geo.j1728SS (suc (suc zero)) = Geo.j1728SS
ell5Neighbour Geo.j1728SS (suc (suc (suc zero))) = Geo.j1728SS
ell5Neighbour Geo.j1728SS (suc (suc (suc (suc zero)))) = Geo.j1728SS
ell5Neighbour Geo.j1728SS (suc (suc (suc (suc (suc zero))))) = Geo.j1728SS

B11ell5Positive : Classical.ClassicalPrimeDegreeCorrespondence Geo.P11SupersingularJ
B11ell5Positive =
  record
    { Classical.degreePrime = 5
    ; Classical.neighbour = ell5Neighbour
    }

ell5J0ToJ0 :
  Classical.classicalOperator B11ell5Positive indicatorJ0 Geo.jZeroSS ≡ 3
ell5J0ToJ0 = refl

ell5J0ToJ1728 :
  Classical.classicalOperator B11ell5Positive indicatorJ1728 Geo.jZeroSS ≡ 3
ell5J0ToJ1728 = refl

ell5J1728ToJ0 :
  Classical.classicalOperator B11ell5Positive indicatorJ0 Geo.j1728SS ≡ 2
ell5J1728ToJ0 = refl

ell5J1728ToJ1728 :
  Classical.classicalOperator B11ell5Positive indicatorJ1728 Geo.j1728SS ≡ 4
ell5J1728ToJ1728 = refl

------------------------------------------------------------------------
-- Exact comparison with the already-constructed Brandt matrices.
------------------------------------------------------------------------

ell2CountMatrixMatchesBrandt :
  Brandt.B11_2 ≡ Brandt.brandtMatrix 0 3 2 1
ell2CountMatrixMatchesBrandt = refl

ell3CountMatrixMatchesBrandt :
  Brandt.B11_3 ≡ Brandt.brandtMatrix 1 3 2 2
ell3CountMatrixMatchesBrandt = refl

ell5CountMatrixMatchesBrandt :
  Brandt.B11_5 ≡ Brandt.brandtMatrix 3 3 2 4
ell5CountMatrixMatchesBrandt = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record P11PositiveBrandtNeighbourBoundary : Set where
  field
    ell2PositiveNeighbourSystemConstructed : Bool
    ell2PositiveNeighbourSystemConstructedIsTrue :
      ell2PositiveNeighbourSystemConstructed ≡ true

    ell3PositiveNeighbourSystemConstructed : Bool
    ell3PositiveNeighbourSystemConstructedIsTrue :
      ell3PositiveNeighbourSystemConstructed ≡ true

    ell5PositiveNeighbourSystemConstructed : Bool
    ell5PositiveNeighbourSystemConstructedIsTrue :
      ell5PositiveNeighbourSystemConstructed ≡ true

    brandtCoefficientsDerivedAsNeighbourCounts : Bool
    brandtCoefficientsDerivedAsNeighbourCountsIsTrue :
      brandtCoefficientsDerivedAsNeighbourCounts ≡ true

    representationGeometryIdentifiedHere : Bool
    representationGeometryIdentifiedHereIsFalse :
      representationGeometryIdentifiedHere ≡ false

canonicalP11PositiveBrandtNeighbourBoundary : P11PositiveBrandtNeighbourBoundary
canonicalP11PositiveBrandtNeighbourBoundary =
  record
    { ell2PositiveNeighbourSystemConstructed = true
    ; ell2PositiveNeighbourSystemConstructedIsTrue = refl
    ; ell3PositiveNeighbourSystemConstructed = true
    ; ell3PositiveNeighbourSystemConstructedIsTrue = refl
    ; ell5PositiveNeighbourSystemConstructed = true
    ; ell5PositiveNeighbourSystemConstructedIsTrue = refl
    ; brandtCoefficientsDerivedAsNeighbourCounts = true
    ; brandtCoefficientsDerivedAsNeighbourCountsIsTrue = refl
    ; representationGeometryIdentifiedHere = false
    ; representationGeometryIdentifiedHereIsFalse = refl
    }
