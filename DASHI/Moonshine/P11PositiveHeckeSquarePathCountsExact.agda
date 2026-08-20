module DASHI.Moonshine.P11PositiveHeckeSquarePathCountsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- DASHI CONTRIBUTION
--
-- Reprove the p=11, ell=2 Hecke square without signed matrices.  The prime
-- operator is a literal three-neighbour system.  Full T_4 is a literal
-- seven-neighbour system with multiplicity matrix [[4,3],[2,5]].  The four
-- source/target indicator equations prove
--
--   T_2^2 = T_4 + 2 I
--
-- as equality of positive path counts on the complete two-state carrier.
--
-- This is stronger semantically than a matrix calculation: every coefficient
-- is a cardinality/multiplicity count before linearization.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)

import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo
import DASHI.Moonshine.P11PositiveBrandtNeighbourSystemsExact as Prime

------------------------------------------------------------------------
-- Full T_4 = cyclic Phi_4 + identity has seven positive contributions.
------------------------------------------------------------------------

fullT4Neighbour : Geo.P11SupersingularJ → Fin 7 → Geo.P11SupersingularJ
fullT4Neighbour Geo.jZeroSS zero = Geo.jZeroSS
fullT4Neighbour Geo.jZeroSS (suc zero) = Geo.jZeroSS
fullT4Neighbour Geo.jZeroSS (suc (suc zero)) = Geo.jZeroSS
fullT4Neighbour Geo.jZeroSS (suc (suc (suc zero))) = Geo.jZeroSS
fullT4Neighbour Geo.jZeroSS (suc (suc (suc (suc zero)))) = Geo.j1728SS
fullT4Neighbour Geo.jZeroSS (suc (suc (suc (suc (suc zero))))) = Geo.j1728SS
fullT4Neighbour Geo.jZeroSS (suc (suc (suc (suc (suc (suc zero)))))) = Geo.j1728SS

fullT4Neighbour Geo.j1728SS zero = Geo.jZeroSS
fullT4Neighbour Geo.j1728SS (suc zero) = Geo.jZeroSS
fullT4Neighbour Geo.j1728SS (suc (suc zero)) = Geo.j1728SS
fullT4Neighbour Geo.j1728SS (suc (suc (suc zero))) = Geo.j1728SS
fullT4Neighbour Geo.j1728SS (suc (suc (suc (suc zero)))) = Geo.j1728SS
fullT4Neighbour Geo.j1728SS (suc (suc (suc (suc (suc zero))))) = Geo.j1728SS
fullT4Neighbour Geo.j1728SS (suc (suc (suc (suc (suc (suc zero)))))) = Geo.j1728SS

fullT4Positive : Positive.PositiveFiniteNeighbourSystem Geo.P11SupersingularJ
fullT4Positive =
  record
    { Positive.arity = 7
    ; Positive.neighbour = fullT4Neighbour
    }

ell2Positive : Positive.PositiveFiniteNeighbourSystem Geo.P11SupersingularJ
ell2Positive = Positive.fromClassicalPrime Prime.B11ell2Positive

------------------------------------------------------------------------
-- Full T4 multiplicities are themselves positive neighbour counts.
------------------------------------------------------------------------

fullT4J0ToJ0 :
  Positive.positiveOperator fullT4Positive Prime.indicatorJ0 Geo.jZeroSS ≡ 4
fullT4J0ToJ0 = refl

fullT4J0ToJ1728 :
  Positive.positiveOperator fullT4Positive Prime.indicatorJ1728 Geo.jZeroSS ≡ 3
fullT4J0ToJ1728 = refl

fullT4J1728ToJ0 :
  Positive.positiveOperator fullT4Positive Prime.indicatorJ0 Geo.j1728SS ≡ 2
fullT4J1728ToJ0 = refl

fullT4J1728ToJ1728 :
  Positive.positiveOperator fullT4Positive Prime.indicatorJ1728 Geo.j1728SS ≡ 5
fullT4J1728ToJ1728 = refl

------------------------------------------------------------------------
-- Ordered length-two path counts under T2.
------------------------------------------------------------------------

twoStepJ0ToJ0 :
  Positive.twoStepOperator ell2Positive ell2Positive
    Prime.indicatorJ0 Geo.jZeroSS ≡ 6
twoStepJ0ToJ0 = refl

twoStepJ0ToJ1728 :
  Positive.twoStepOperator ell2Positive ell2Positive
    Prime.indicatorJ1728 Geo.jZeroSS ≡ 3
twoStepJ0ToJ1728 = refl

twoStepJ1728ToJ0 :
  Positive.twoStepOperator ell2Positive ell2Positive
    Prime.indicatorJ0 Geo.j1728SS ≡ 2
twoStepJ1728ToJ0 = refl

twoStepJ1728ToJ1728 :
  Positive.twoStepOperator ell2Positive ell2Positive
    Prime.indicatorJ1728 Geo.j1728SS ≡ 7
twoStepJ1728ToJ1728 = refl

------------------------------------------------------------------------
-- Hecke square on the complete indicator basis.
------------------------------------------------------------------------

heckeSquareJ0ToJ0 :
  Positive.twoStepOperator ell2Positive ell2Positive
    Prime.indicatorJ0 Geo.jZeroSS
  ≡ Positive.positiveOperator fullT4Positive Prime.indicatorJ0 Geo.jZeroSS
      + 2 * Prime.indicatorJ0 Geo.jZeroSS
heckeSquareJ0ToJ0 = refl

heckeSquareJ0ToJ1728 :
  Positive.twoStepOperator ell2Positive ell2Positive
    Prime.indicatorJ1728 Geo.jZeroSS
  ≡ Positive.positiveOperator fullT4Positive Prime.indicatorJ1728 Geo.jZeroSS
      + 2 * Prime.indicatorJ1728 Geo.jZeroSS
heckeSquareJ0ToJ1728 = refl

heckeSquareJ1728ToJ0 :
  Positive.twoStepOperator ell2Positive ell2Positive
    Prime.indicatorJ0 Geo.j1728SS
  ≡ Positive.positiveOperator fullT4Positive Prime.indicatorJ0 Geo.j1728SS
      + 2 * Prime.indicatorJ0 Geo.j1728SS
heckeSquareJ1728ToJ0 = refl

heckeSquareJ1728ToJ1728 :
  Positive.twoStepOperator ell2Positive ell2Positive
    Prime.indicatorJ1728 Geo.j1728SS
  ≡ Positive.positiveOperator fullT4Positive Prime.indicatorJ1728 Geo.j1728SS
      + 2 * Prime.indicatorJ1728 Geo.j1728SS
heckeSquareJ1728ToJ1728 = refl

------------------------------------------------------------------------
-- Boundary: the relation is complete on the two indicator basis states, while
-- generic semimodule linear-extension is deliberately a separate theorem.
------------------------------------------------------------------------

record P11PositiveHeckeSquareBoundary : Set where
  field
    fullT4SevenNeighbourSystemConstructed : Bool
    fullT4SevenNeighbourSystemConstructedIsTrue :
      fullT4SevenNeighbourSystemConstructed ≡ true

    orderedTwoStepCountsConstructed : Bool
    orderedTwoStepCountsConstructedIsTrue :
      orderedTwoStepCountsConstructed ≡ true

    completeTwoStateIndicatorHeckeSquareConstructed : Bool
    completeTwoStateIndicatorHeckeSquareConstructedIsTrue :
      completeTwoStateIndicatorHeckeSquareConstructed ≡ true

    signedMatrixNeededForPositivity : Bool
    signedMatrixNeededForPositivityIsFalse :
      signedMatrixNeededForPositivity ≡ false

    arbitraryRepresentationGeometryConstructedHere : Bool
    arbitraryRepresentationGeometryConstructedHereIsFalse :
      arbitraryRepresentationGeometryConstructedHere ≡ false

canonicalP11PositiveHeckeSquareBoundary : P11PositiveHeckeSquareBoundary
canonicalP11PositiveHeckeSquareBoundary =
  record
    { fullT4SevenNeighbourSystemConstructed = true
    ; fullT4SevenNeighbourSystemConstructedIsTrue = refl
    ; orderedTwoStepCountsConstructed = true
    ; orderedTwoStepCountsConstructedIsTrue = refl
    ; completeTwoStateIndicatorHeckeSquareConstructed = true
    ; completeTwoStateIndicatorHeckeSquareConstructedIsTrue = refl
    ; signedMatrixNeededForPositivity = false
    ; signedMatrixNeededForPositivityIsFalse = refl
    ; arbitraryRepresentationGeometryConstructedHere = false
    ; arbitraryRepresentationGeometryConstructedHereIsFalse = refl
    }
