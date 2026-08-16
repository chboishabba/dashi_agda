module DASHI.Foundations.D4SO3RestrictionCharacterJ0To35Exact where

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
-- Exhaustively verify the rotational-D4 branching scan against the restricted
-- SO(3) class character for all 36 angular momenta and all five D4 classes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_)
  renaming (_+_ to _+ℤ_)

import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.D4SO3RestrictionJ0To35Exact as Scan
import DASHI.Foundations.D4SO3NineIrrepRestrictionExact as D4
import DASHI.Foundations.PolyhedralFixedSpaceSpectrumJ0To35Exact as Fixed
import DASHI.Foundations.PolyhedralRestrictionCriticalCharacterExact as Poly

scaleInt : Nat → ℤ → ℤ
scaleInt 0 value = + 0
scaleInt (suc n) value = value +ℤ scaleInt n value

branchingCharacter : Scan.D4Spectrum → D4.D4RotationClass → ℤ
branchingCharacter spectrum class =
  scaleInt (Scan.multiplicityA1 spectrum) (D4.d4Character DASHI.Biology.TernaryMonsterSymmetryCandidateExact.A1 class)
  +ℤ scaleInt (Scan.multiplicityA2 spectrum) (D4.d4Character DASHI.Biology.TernaryMonsterSymmetryCandidateExact.A2 class)
  +ℤ scaleInt (Scan.multiplicityB1 spectrum) (D4.d4Character DASHI.Biology.TernaryMonsterSymmetryCandidateExact.B1 class)
  +ℤ scaleInt (Scan.multiplicityB2 spectrum) (D4.d4Character DASHI.Biology.TernaryMonsterSymmetryCandidateExact.B2 class)
  +ℤ scaleInt (Scan.multiplicityE spectrum) (D4.d4Character DASHI.Biology.TernaryMonsterSymmetryCandidateExact.E2 class)

restrictedCharacter : Spin.AngularMomentum0To35 → D4.D4RotationClass → ℤ
restrictedCharacter j D4.identityClass = + (Spin.jDimension j)
restrictedCharacter j D4.centralHalfTurnClass = Fixed.halfTurnCharacter (Spin.jNat j)
restrictedCharacter j D4.quarterTurnPairClass = Poly.quarterTurnCharacter (Spin.jNat j)
restrictedCharacter j D4.axisHalfTurnPairClass = Fixed.halfTurnCharacter (Spin.jNat j)
restrictedCharacter j D4.diagonalHalfTurnPairClass = Fixed.halfTurnCharacter (Spin.jNat j)

branchingCharacterExact :
  (j : Spin.AngularMomentum0To35) →
  (class : D4.D4RotationClass) →
  branchingCharacter (Scan.branchingSpectrum j) class ≡ restrictedCharacter j class
branchingCharacterExact Spin.j0 D4.identityClass = refl
branchingCharacterExact Spin.j0 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j0 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j0 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j0 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j1 D4.identityClass = refl
branchingCharacterExact Spin.j1 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j1 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j1 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j1 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j2 D4.identityClass = refl
branchingCharacterExact Spin.j2 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j2 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j2 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j2 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j3 D4.identityClass = refl
branchingCharacterExact Spin.j3 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j3 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j3 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j3 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j4 D4.identityClass = refl
branchingCharacterExact Spin.j4 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j4 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j4 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j4 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j5 D4.identityClass = refl
branchingCharacterExact Spin.j5 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j5 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j5 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j5 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j6 D4.identityClass = refl
branchingCharacterExact Spin.j6 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j6 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j6 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j6 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j7 D4.identityClass = refl
branchingCharacterExact Spin.j7 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j7 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j7 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j7 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j8 D4.identityClass = refl
branchingCharacterExact Spin.j8 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j8 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j8 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j8 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j9 D4.identityClass = refl
branchingCharacterExact Spin.j9 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j9 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j9 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j9 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j10 D4.identityClass = refl
branchingCharacterExact Spin.j10 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j10 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j10 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j10 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j11 D4.identityClass = refl
branchingCharacterExact Spin.j11 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j11 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j11 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j11 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j12 D4.identityClass = refl
branchingCharacterExact Spin.j12 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j12 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j12 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j12 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j13 D4.identityClass = refl
branchingCharacterExact Spin.j13 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j13 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j13 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j13 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j14 D4.identityClass = refl
branchingCharacterExact Spin.j14 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j14 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j14 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j14 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j15 D4.identityClass = refl
branchingCharacterExact Spin.j15 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j15 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j15 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j15 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j16 D4.identityClass = refl
branchingCharacterExact Spin.j16 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j16 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j16 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j16 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j17 D4.identityClass = refl
branchingCharacterExact Spin.j17 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j17 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j17 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j17 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j18 D4.identityClass = refl
branchingCharacterExact Spin.j18 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j18 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j18 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j18 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j19 D4.identityClass = refl
branchingCharacterExact Spin.j19 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j19 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j19 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j19 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j20 D4.identityClass = refl
branchingCharacterExact Spin.j20 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j20 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j20 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j20 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j21 D4.identityClass = refl
branchingCharacterExact Spin.j21 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j21 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j21 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j21 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j22 D4.identityClass = refl
branchingCharacterExact Spin.j22 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j22 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j22 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j22 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j23 D4.identityClass = refl
branchingCharacterExact Spin.j23 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j23 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j23 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j23 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j24 D4.identityClass = refl
branchingCharacterExact Spin.j24 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j24 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j24 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j24 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j25 D4.identityClass = refl
branchingCharacterExact Spin.j25 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j25 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j25 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j25 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j26 D4.identityClass = refl
branchingCharacterExact Spin.j26 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j26 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j26 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j26 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j27 D4.identityClass = refl
branchingCharacterExact Spin.j27 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j27 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j27 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j27 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j28 D4.identityClass = refl
branchingCharacterExact Spin.j28 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j28 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j28 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j28 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j29 D4.identityClass = refl
branchingCharacterExact Spin.j29 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j29 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j29 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j29 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j30 D4.identityClass = refl
branchingCharacterExact Spin.j30 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j30 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j30 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j30 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j31 D4.identityClass = refl
branchingCharacterExact Spin.j31 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j31 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j31 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j31 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j32 D4.identityClass = refl
branchingCharacterExact Spin.j32 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j32 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j32 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j32 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j33 D4.identityClass = refl
branchingCharacterExact Spin.j33 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j33 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j33 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j33 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j34 D4.identityClass = refl
branchingCharacterExact Spin.j34 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j34 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j34 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j34 D4.diagonalHalfTurnPairClass = refl
branchingCharacterExact Spin.j35 D4.identityClass = refl
branchingCharacterExact Spin.j35 D4.centralHalfTurnClass = refl
branchingCharacterExact Spin.j35 D4.quarterTurnPairClass = refl
branchingCharacterExact Spin.j35 D4.axisHalfTurnPairClass = refl
branchingCharacterExact Spin.j35 D4.diagonalHalfTurnPairClass = refl
