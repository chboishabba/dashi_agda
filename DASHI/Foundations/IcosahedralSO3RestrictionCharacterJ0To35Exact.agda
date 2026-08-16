module DASHI.Foundations.IcosahedralSO3RestrictionCharacterJ0To35Exact where

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
-- Exhaustively verify the icosahedral/A5 branching table against the
-- restricted SO(3) class character: 36 angular momenta times five conjugacy
-- classes.  The two order-five classes use exact Z[phi] arithmetic from the
-- companion module.  Every case reduces definitionally to `refl`.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.IcosahedralSO3RestrictionJ0To35Exact as Ico
import DASHI.Foundations.PolyhedralRestrictionCriticalCharacterExact as Character

branchingCharacterExact :
  (j : Spin.AngularMomentum0To35) →
  (class : Ico.IcosahedralClass) →
  Character.icosahedralBranchingCharacter (Ico.branchingSpectrum j) class
  ≡ Character.restrictedIcosahedralCharacter j class
branchingCharacterExact Spin.j0 Ico.identityClass = refl
branchingCharacterExact Spin.j0 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j0 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j0 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j0 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j1 Ico.identityClass = refl
branchingCharacterExact Spin.j1 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j1 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j1 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j1 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j2 Ico.identityClass = refl
branchingCharacterExact Spin.j2 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j2 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j2 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j2 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j3 Ico.identityClass = refl
branchingCharacterExact Spin.j3 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j3 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j3 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j3 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j4 Ico.identityClass = refl
branchingCharacterExact Spin.j4 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j4 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j4 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j4 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j5 Ico.identityClass = refl
branchingCharacterExact Spin.j5 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j5 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j5 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j5 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j6 Ico.identityClass = refl
branchingCharacterExact Spin.j6 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j6 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j6 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j6 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j7 Ico.identityClass = refl
branchingCharacterExact Spin.j7 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j7 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j7 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j7 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j8 Ico.identityClass = refl
branchingCharacterExact Spin.j8 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j8 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j8 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j8 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j9 Ico.identityClass = refl
branchingCharacterExact Spin.j9 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j9 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j9 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j9 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j10 Ico.identityClass = refl
branchingCharacterExact Spin.j10 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j10 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j10 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j10 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j11 Ico.identityClass = refl
branchingCharacterExact Spin.j11 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j11 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j11 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j11 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j12 Ico.identityClass = refl
branchingCharacterExact Spin.j12 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j12 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j12 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j12 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j13 Ico.identityClass = refl
branchingCharacterExact Spin.j13 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j13 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j13 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j13 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j14 Ico.identityClass = refl
branchingCharacterExact Spin.j14 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j14 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j14 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j14 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j15 Ico.identityClass = refl
branchingCharacterExact Spin.j15 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j15 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j15 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j15 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j16 Ico.identityClass = refl
branchingCharacterExact Spin.j16 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j16 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j16 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j16 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j17 Ico.identityClass = refl
branchingCharacterExact Spin.j17 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j17 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j17 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j17 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j18 Ico.identityClass = refl
branchingCharacterExact Spin.j18 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j18 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j18 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j18 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j19 Ico.identityClass = refl
branchingCharacterExact Spin.j19 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j19 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j19 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j19 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j20 Ico.identityClass = refl
branchingCharacterExact Spin.j20 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j20 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j20 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j20 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j21 Ico.identityClass = refl
branchingCharacterExact Spin.j21 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j21 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j21 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j21 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j22 Ico.identityClass = refl
branchingCharacterExact Spin.j22 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j22 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j22 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j22 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j23 Ico.identityClass = refl
branchingCharacterExact Spin.j23 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j23 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j23 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j23 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j24 Ico.identityClass = refl
branchingCharacterExact Spin.j24 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j24 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j24 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j24 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j25 Ico.identityClass = refl
branchingCharacterExact Spin.j25 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j25 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j25 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j25 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j26 Ico.identityClass = refl
branchingCharacterExact Spin.j26 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j26 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j26 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j26 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j27 Ico.identityClass = refl
branchingCharacterExact Spin.j27 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j27 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j27 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j27 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j28 Ico.identityClass = refl
branchingCharacterExact Spin.j28 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j28 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j28 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j28 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j29 Ico.identityClass = refl
branchingCharacterExact Spin.j29 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j29 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j29 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j29 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j30 Ico.identityClass = refl
branchingCharacterExact Spin.j30 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j30 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j30 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j30 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j31 Ico.identityClass = refl
branchingCharacterExact Spin.j31 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j31 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j31 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j31 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j32 Ico.identityClass = refl
branchingCharacterExact Spin.j32 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j32 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j32 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j32 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j33 Ico.identityClass = refl
branchingCharacterExact Spin.j33 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j33 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j33 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j33 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j34 Ico.identityClass = refl
branchingCharacterExact Spin.j34 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j34 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j34 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j34 Ico.fifthTurnSquaredClass = refl
branchingCharacterExact Spin.j35 Ico.identityClass = refl
branchingCharacterExact Spin.j35 Ico.halfTurnClass = refl
branchingCharacterExact Spin.j35 Ico.thirdTurnClass = refl
branchingCharacterExact Spin.j35 Ico.fifthTurnClass = refl
branchingCharacterExact Spin.j35 Ico.fifthTurnSquaredClass = refl
