module DASHI.Moonshine.P11MarkedX2T7HeckeCollisionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Annals of Mathematics Studies 108,
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- EXECUTABLE ARITHMETIC REFERENCE
-- LMFDB level-11 weight-2 newform / elliptic curve isogeny class 11.a:
-- a_7 = -2.  No DOI is asserted for the database.
--
-- DASHI CONTRIBUTION
--
-- Extend the source-native marked p=11 calculation from T3,T5 to T7.
--
-- Coarse degree eight + reciprocal 2:3 stack balance + a_7=-2 force
--
--   B_11(7) = [[2,6],[4,4]].
--
-- P11MarkedQuaternionThetaEll7Exact independently gives marked identity-loop
-- counts
--
--   j=0 : 2,   j=1728 : 0.
--
-- In the existing six deck-S3 orbitals this forces
--
--   (AA_id,AA_off,A->B,B->A,BB_id,BB_off)
--     = (2,0,2,2,0,2).
--
-- This is a Nat-valued positive correspondence before linearization.  Its
-- simultaneous deck-sector eigenvalues are
--
--   constant/Perron :  8,
--   A-sign          :  2,
--   Brandt newform  : -2,
--   B-standard      : -2  (multiplicity two).
--
-- Thus the exact Brandt-newform/deck-standard collision survives the next
-- genuine odd Hecke prime.  The live infinite-prime frontier is the marked
-- j=1728 theta-series identity, not blind prime-by-prime searching.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)

import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11Level2DoubleCosetHeckeBasisExact as Orbital
import DASHI.Moonshine.P11MarkedQuaternionThetaEll7Exact as Theta7
import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact as S3

------------------------------------------------------------------------
-- Coarse Brandt row data at ell=7.
------------------------------------------------------------------------

p11Ell7Degree : Nat
p11Ell7Degree = 8

p11Ell7CrossUnit : Nat
p11Ell7CrossUnit = 2

p11Ell7J0Row : Nat × Nat
p11Ell7J0Row = 2 , 6

p11Ell7J1728Row : Nat × Nat
p11Ell7J1728Row = 4 , 4

p11Ell7RowsHaveDegreeEight :
  (2 + 6 ≡ p11Ell7Degree) × (4 + 4 ≡ p11Ell7Degree)
p11Ell7RowsHaveDegreeEight = refl , refl

-- Reciprocal stack sheet multiplicities are 2 over j=0 and 3 over j=1728.
p11Ell7ReciprocalStackBalance : 2 * 6 ≡ 3 * 4
p11Ell7ReciprocalStackBalance = refl

------------------------------------------------------------------------
-- Marked T7 as an actual Nat-valued deck-orbital correspondence.
------------------------------------------------------------------------

markedT7OrbitalCoefficients : Orbital.OrbitalCoefficients
markedT7OrbitalCoefficients = Orbital.orbitalCoefficients 2 0 2 2 0 2

markedT7Multiplicity : Fine.P11Fine5 → Fine.P11Fine5 → Nat
markedT7Multiplicity = Orbital.orbitalMultiplicity markedT7OrbitalCoefficients

markedT7IdentityCountsAreThetaCounts :
  Orbital.aaId markedT7OrbitalCoefficients ≡ Theta7.j0MarkedT7LoopCount
  × Orbital.bbId markedT7OrbitalCoefficients ≡ Theta7.j1728MarkedT7LoopCount
markedT7IdentityCountsAreThetaCounts = refl , refl

-- Exact coarse aggregation through the existing 2+3 fine fibres.
markedT7AtoAIsTwo :
  Orbital.aaId markedT7OrbitalCoefficients
  + Orbital.aaOff markedT7OrbitalCoefficients ≡ 2
markedT7AtoAIsTwo = refl

markedT7AtoBIsSix : 3 * Orbital.ab markedT7OrbitalCoefficients ≡ 6
markedT7AtoBIsSix = refl

markedT7BtoAIsFour : 2 * Orbital.ba markedT7OrbitalCoefficients ≡ 4
markedT7BtoAIsFour = refl

markedT7BtoBIsFour :
  Orbital.bbId markedT7OrbitalCoefficients
  + 2 * Orbital.bbOff markedT7OrbitalCoefficients ≡ 4
markedT7BtoBIsFour = refl

------------------------------------------------------------------------
-- Integer linearization on the already-constructed complete S3 basis.
------------------------------------------------------------------------

markedT7Action : S3.Int5 → S3.Int5
markedT7Action v = S3.int5
  (((+ 2) *ℤ S3.a0c v)
    +ℤ ((+ 2) *ℤ S3.b0c v) +ℤ ((+ 2) *ℤ S3.b1c v) +ℤ ((+ 2) *ℤ S3.b2c v))
  (((+ 2) *ℤ S3.a1c v)
    +ℤ ((+ 2) *ℤ S3.b0c v) +ℤ ((+ 2) *ℤ S3.b1c v) +ℤ ((+ 2) *ℤ S3.b2c v))
  (((+ 2) *ℤ S3.a0c v) +ℤ ((+ 2) *ℤ S3.a1c v)
    +ℤ ((+ 2) *ℤ S3.b1c v) +ℤ ((+ 2) *ℤ S3.b2c v))
  (((+ 2) *ℤ S3.a0c v) +ℤ ((+ 2) *ℤ S3.a1c v)
    +ℤ ((+ 2) *ℤ S3.b0c v) +ℤ ((+ 2) *ℤ S3.b2c v))
  (((+ 2) *ℤ S3.a0c v) +ℤ ((+ 2) *ℤ S3.a1c v)
    +ℤ ((+ 2) *ℤ S3.b0c v) +ℤ ((+ 2) *ℤ S3.b1c v))

T7ConstantEigen :
  markedT7Action S3.constantVector ≡ S3.scale5 (+ 8) S3.constantVector
T7ConstantEigen = refl

T7SignEigen :
  markedT7Action S3.signVector ≡ S3.scale5 (+ 2) S3.signVector
T7SignEigen = refl

T7BrandtNewformEigen :
  markedT7Action S3.brandtNewformVector
  ≡ S3.scale5 (-[1+ 1 ]) S3.brandtNewformVector
T7BrandtNewformEigen = refl

T7Standard1Eigen :
  markedT7Action S3.standardVector1
  ≡ S3.scale5 (-[1+ 1 ]) S3.standardVector1
T7Standard1Eigen = refl

T7Standard2Eigen :
  markedT7Action S3.standardVector2
  ≡ S3.scale5 (-[1+ 1 ]) S3.standardVector2
T7Standard2Eigen = refl

------------------------------------------------------------------------
-- The old collision survives the new genuine Hecke coordinate.
------------------------------------------------------------------------

record JointT3T5T7FDeckBlindFingerprint : Set where
  constructor joint357F
  field
    t3 t5 t7 frobenius : ℤ

brandt357FFingerprint : JointT3T5T7FDeckBlindFingerprint
brandt357FFingerprint = joint357F (-[1+ 0 ]) (+ 1) (-[1+ 1 ]) (+ 1)

standard357FFingerprint : JointT3T5T7FDeckBlindFingerprint
standard357FFingerprint = joint357F (-[1+ 0 ]) (+ 1) (-[1+ 1 ]) (+ 1)

brandtAndStandardStillCollideAtT7 :
  brandt357FFingerprint ≡ standard357FFingerprint
brandtAndStandardStillCollideAtT7 = refl

record P11MarkedX2T7CollisionBoundary : Set where
  field
    directNormSevenThetaLoopsConstructed : Bool
    directNormSevenThetaLoopsConstructedIsTrue :
      directNormSevenThetaLoopsConstructed ≡ true

    positiveNatMarkedT7Constructed : Bool
    positiveNatMarkedT7ConstructedIsTrue : positiveNatMarkedT7Constructed ≡ true

    t7FailsToSeparateBrandtAndStandard : Bool
    t7FailsToSeparateBrandtAndStandardIsTrue :
      t7FailsToSeparateBrandtAndStandard ≡ true

    allOddPrimeCollisionProvedHere : Bool
    allOddPrimeCollisionProvedHereIsFalse : allOddPrimeCollisionProvedHere ≡ false

canonicalP11MarkedX2T7CollisionBoundary : P11MarkedX2T7CollisionBoundary
canonicalP11MarkedX2T7CollisionBoundary = record
  { directNormSevenThetaLoopsConstructed = true
  ; directNormSevenThetaLoopsConstructedIsTrue = refl
  ; positiveNatMarkedT7Constructed = true
  ; positiveNatMarkedT7ConstructedIsTrue = refl
  ; t7FailsToSeparateBrandtAndStandard = true
  ; t7FailsToSeparateBrandtAndStandardIsTrue = refl
  ; allOddPrimeCollisionProvedHere = false
  ; allOddPrimeCollisionProvedHereIsFalse = refl
  }
