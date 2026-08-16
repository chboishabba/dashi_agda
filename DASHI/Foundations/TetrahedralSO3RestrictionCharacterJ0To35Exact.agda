module DASHI.Foundations.TetrahedralSO3RestrictionCharacterJ0To35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Exhaustively verify all 36 x 4 tetrahedral/A4 restriction character cases.
-- The conjugate order-three classes are evaluated in exact Z[omega].
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.TetrahedralSO3RestrictionJ0To35Exact as Tet

branchingCharacterExact :
  (j : Spin.AngularMomentum0To35) →
  (class : Tet.TetrahedralClass) →
  Tet.branchingCharacter (Tet.branchingSpectrum j) class
  ≡ Tet.restrictedCharacter j class
branchingCharacterExact Spin.j0 Tet.identityClass = refl
branchingCharacterExact Spin.j0 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j0 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j0 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j1 Tet.identityClass = refl
branchingCharacterExact Spin.j1 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j1 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j1 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j2 Tet.identityClass = refl
branchingCharacterExact Spin.j2 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j2 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j2 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j3 Tet.identityClass = refl
branchingCharacterExact Spin.j3 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j3 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j3 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j4 Tet.identityClass = refl
branchingCharacterExact Spin.j4 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j4 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j4 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j5 Tet.identityClass = refl
branchingCharacterExact Spin.j5 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j5 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j5 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j6 Tet.identityClass = refl
branchingCharacterExact Spin.j6 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j6 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j6 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j7 Tet.identityClass = refl
branchingCharacterExact Spin.j7 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j7 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j7 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j8 Tet.identityClass = refl
branchingCharacterExact Spin.j8 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j8 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j8 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j9 Tet.identityClass = refl
branchingCharacterExact Spin.j9 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j9 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j9 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j10 Tet.identityClass = refl
branchingCharacterExact Spin.j10 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j10 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j10 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j11 Tet.identityClass = refl
branchingCharacterExact Spin.j11 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j11 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j11 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j12 Tet.identityClass = refl
branchingCharacterExact Spin.j12 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j12 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j12 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j13 Tet.identityClass = refl
branchingCharacterExact Spin.j13 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j13 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j13 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j14 Tet.identityClass = refl
branchingCharacterExact Spin.j14 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j14 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j14 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j15 Tet.identityClass = refl
branchingCharacterExact Spin.j15 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j15 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j15 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j16 Tet.identityClass = refl
branchingCharacterExact Spin.j16 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j16 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j16 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j17 Tet.identityClass = refl
branchingCharacterExact Spin.j17 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j17 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j17 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j18 Tet.identityClass = refl
branchingCharacterExact Spin.j18 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j18 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j18 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j19 Tet.identityClass = refl
branchingCharacterExact Spin.j19 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j19 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j19 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j20 Tet.identityClass = refl
branchingCharacterExact Spin.j20 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j20 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j20 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j21 Tet.identityClass = refl
branchingCharacterExact Spin.j21 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j21 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j21 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j22 Tet.identityClass = refl
branchingCharacterExact Spin.j22 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j22 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j22 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j23 Tet.identityClass = refl
branchingCharacterExact Spin.j23 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j23 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j23 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j24 Tet.identityClass = refl
branchingCharacterExact Spin.j24 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j24 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j24 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j25 Tet.identityClass = refl
branchingCharacterExact Spin.j25 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j25 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j25 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j26 Tet.identityClass = refl
branchingCharacterExact Spin.j26 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j26 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j26 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j27 Tet.identityClass = refl
branchingCharacterExact Spin.j27 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j27 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j27 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j28 Tet.identityClass = refl
branchingCharacterExact Spin.j28 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j28 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j28 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j29 Tet.identityClass = refl
branchingCharacterExact Spin.j29 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j29 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j29 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j30 Tet.identityClass = refl
branchingCharacterExact Spin.j30 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j30 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j30 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j31 Tet.identityClass = refl
branchingCharacterExact Spin.j31 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j31 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j31 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j32 Tet.identityClass = refl
branchingCharacterExact Spin.j32 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j32 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j32 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j33 Tet.identityClass = refl
branchingCharacterExact Spin.j33 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j33 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j33 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j34 Tet.identityClass = refl
branchingCharacterExact Spin.j34 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j34 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j34 Tet.thirdTurnInverseClass = refl
branchingCharacterExact Spin.j35 Tet.identityClass = refl
branchingCharacterExact Spin.j35 Tet.halfTurnClass = refl
branchingCharacterExact Spin.j35 Tet.thirdTurnClass = refl
branchingCharacterExact Spin.j35 Tet.thirdTurnInverseClass = refl
