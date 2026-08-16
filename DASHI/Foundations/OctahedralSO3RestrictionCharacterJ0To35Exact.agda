module DASHI.Foundations.OctahedralSO3RestrictionCharacterJ0To35Exact where

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
-- Exhaustively verify the octahedral/S4 branching table against the restricted
-- SO(3) class character: 36 angular momenta times five conjugacy classes.
-- Every proof is constructor-normalization (`refl`) on exact integer data.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.OctahedralSO3RestrictionJ0To35Exact as Oct
import DASHI.Foundations.PolyhedralRestrictionCriticalCharacterExact as Character

branchingCharacterExact :
  (j : Spin.AngularMomentum0To35) →
  (class : Oct.OctahedralClass) →
  Character.octahedralBranchingCharacter (Oct.branchingSpectrum j) class
  ≡ Character.restrictedOctahedralCharacter j class
branchingCharacterExact Spin.j0 Oct.identityClass = refl
branchingCharacterExact Spin.j0 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j0 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j0 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j0 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j1 Oct.identityClass = refl
branchingCharacterExact Spin.j1 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j1 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j1 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j1 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j2 Oct.identityClass = refl
branchingCharacterExact Spin.j2 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j2 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j2 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j2 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j3 Oct.identityClass = refl
branchingCharacterExact Spin.j3 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j3 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j3 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j3 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j4 Oct.identityClass = refl
branchingCharacterExact Spin.j4 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j4 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j4 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j4 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j5 Oct.identityClass = refl
branchingCharacterExact Spin.j5 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j5 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j5 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j5 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j6 Oct.identityClass = refl
branchingCharacterExact Spin.j6 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j6 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j6 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j6 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j7 Oct.identityClass = refl
branchingCharacterExact Spin.j7 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j7 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j7 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j7 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j8 Oct.identityClass = refl
branchingCharacterExact Spin.j8 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j8 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j8 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j8 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j9 Oct.identityClass = refl
branchingCharacterExact Spin.j9 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j9 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j9 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j9 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j10 Oct.identityClass = refl
branchingCharacterExact Spin.j10 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j10 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j10 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j10 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j11 Oct.identityClass = refl
branchingCharacterExact Spin.j11 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j11 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j11 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j11 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j12 Oct.identityClass = refl
branchingCharacterExact Spin.j12 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j12 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j12 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j12 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j13 Oct.identityClass = refl
branchingCharacterExact Spin.j13 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j13 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j13 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j13 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j14 Oct.identityClass = refl
branchingCharacterExact Spin.j14 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j14 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j14 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j14 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j15 Oct.identityClass = refl
branchingCharacterExact Spin.j15 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j15 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j15 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j15 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j16 Oct.identityClass = refl
branchingCharacterExact Spin.j16 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j16 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j16 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j16 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j17 Oct.identityClass = refl
branchingCharacterExact Spin.j17 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j17 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j17 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j17 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j18 Oct.identityClass = refl
branchingCharacterExact Spin.j18 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j18 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j18 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j18 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j19 Oct.identityClass = refl
branchingCharacterExact Spin.j19 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j19 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j19 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j19 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j20 Oct.identityClass = refl
branchingCharacterExact Spin.j20 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j20 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j20 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j20 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j21 Oct.identityClass = refl
branchingCharacterExact Spin.j21 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j21 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j21 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j21 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j22 Oct.identityClass = refl
branchingCharacterExact Spin.j22 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j22 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j22 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j22 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j23 Oct.identityClass = refl
branchingCharacterExact Spin.j23 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j23 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j23 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j23 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j24 Oct.identityClass = refl
branchingCharacterExact Spin.j24 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j24 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j24 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j24 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j25 Oct.identityClass = refl
branchingCharacterExact Spin.j25 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j25 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j25 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j25 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j26 Oct.identityClass = refl
branchingCharacterExact Spin.j26 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j26 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j26 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j26 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j27 Oct.identityClass = refl
branchingCharacterExact Spin.j27 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j27 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j27 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j27 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j28 Oct.identityClass = refl
branchingCharacterExact Spin.j28 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j28 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j28 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j28 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j29 Oct.identityClass = refl
branchingCharacterExact Spin.j29 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j29 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j29 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j29 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j30 Oct.identityClass = refl
branchingCharacterExact Spin.j30 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j30 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j30 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j30 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j31 Oct.identityClass = refl
branchingCharacterExact Spin.j31 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j31 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j31 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j31 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j32 Oct.identityClass = refl
branchingCharacterExact Spin.j32 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j32 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j32 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j32 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j33 Oct.identityClass = refl
branchingCharacterExact Spin.j33 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j33 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j33 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j33 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j34 Oct.identityClass = refl
branchingCharacterExact Spin.j34 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j34 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j34 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j34 Oct.quarterTurnClass = refl
branchingCharacterExact Spin.j35 Oct.identityClass = refl
branchingCharacterExact Spin.j35 Oct.edgeHalfTurnClass = refl
branchingCharacterExact Spin.j35 Oct.faceHalfTurnClass = refl
branchingCharacterExact Spin.j35 Oct.thirdTurnClass = refl
branchingCharacterExact Spin.j35 Oct.quarterTurnClass = refl
