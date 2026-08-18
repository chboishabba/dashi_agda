module DASHI.Moonshine.P11MarkedX2T7HeckeCollisionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Brandt matrices / supersingular ideal-class Hecke operators.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Annals of Mathematics Studies 108,
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Prime-to-level isogenies transport full level structures.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- EXECUTABLE ARITHMETIC REFERENCE
-- LMFDB level-11 weight-2 newform / elliptic curve isogeny class 11.a:
-- the normalized newform has a_7 = -2.  No DOI is asserted for the database.
--
-- DASHI CONTRIBUTION
--
-- Test the first genuinely new odd Hecke prime against the p=11 collision
-- discovered in P11MarkedX2S3HeckeDecompositionExact.
--
-- Coarse Brandt constraints at ell=7 are:
--
--   row degree = 8,
--   reciprocal stack sheet sizes = 2,3,
--   nonconstant eigenvalue a_7 = -2.
--
-- Weighted integrality forces the cross multiplicities to be 6 and 4, hence
--
--   B_11(7) = [[2,6],[4,4]].
--
-- The direct quaternion theta calculation in
-- P11MarkedQuaternionThetaEll7Exact gives marked identity-orbital counts
--
--   j=0 : 2,     j=1728 : 0.
--
-- Deck-S3 orbital rigidity then forces the full marked correspondence:
--
--   (AA_id,AA_off,A->B,B->A,BB_id,BB_off)
--     = (1,1,2,2,0,2).
--
-- Its complete S3-sector spectrum contains
--
--   constant/Perron :  8,
--   A-sign          :  0,
--   Brandt newform  : -2,
--   B-standard      : -2  (multiplicity two).
--
-- Therefore T7 FAILS to separate the exact Brandt-newform / deck-standard
-- collision already seen at T3,T5,F.  The next frontier is not "try one more
-- prime" blindly: it is the marked j=1728 theta-series identity governing all
-- prime-to-2 Hecke operators.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)

import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive
import DASHI.Moonshine.ClassicalFiniteHeckeCorrespondenceCore as Classical
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11Level2DoubleCosetHeckeBasisExact as Orbital
import DASHI.Moonshine.P11MarkedQuaternionThetaEll7Exact as Theta7
import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact as S3

------------------------------------------------------------------------
-- Coarse ell=7 Brandt neighbour system: [[2,6],[4,4]].
------------------------------------------------------------------------

indicatorJ0 : Geo.P11SupersingularJ → Nat
indicatorJ0 Geo.jZeroSS = 1
indicatorJ0 Geo.j1728SS = 0

indicatorJ1728 : Geo.P11SupersingularJ → Nat
indicatorJ1728 Geo.jZeroSS = 0
indicatorJ1728 Geo.j1728SS = 1

ell7Neighbour : Geo.P11SupersingularJ → Fin 8 → Geo.P11SupersingularJ
ell7Neighbour Geo.jZeroSS zero = Geo.jZeroSS
ell7Neighbour Geo.jZeroSS (suc zero) = Geo.jZeroSS
ell7Neighbour Geo.jZeroSS (suc (suc zero)) = Geo.j1728SS
ell7Neighbour Geo.jZeroSS (suc (suc (suc zero))) = Geo.j1728SS
ell7Neighbour Geo.jZeroSS (suc (suc (suc (suc zero)))) = Geo.j1728SS
ell7Neighbour Geo.jZeroSS (suc (suc (suc (suc (suc zero))))) = Geo.j1728SS
ell7Neighbour Geo.jZeroSS (suc (suc (suc (suc (suc (suc zero)))))) = Geo.j1728SS
ell7Neighbour Geo.jZeroSS (suc (suc (suc (suc (suc (suc (suc zero))))))) = Geo.j1728SS
ell7Neighbour Geo.j1728SS zero = Geo.jZeroSS
ell7Neighbour Geo.j1728SS (suc zero) = Geo.jZeroSS
ell7Neighbour Geo.j1728SS (suc (suc zero)) = Geo.jZeroSS
ell7Neighbour Geo.j1728SS (suc (suc (suc zero))) = Geo.jZeroSS
ell7Neighbour Geo.j1728SS (suc (suc (suc (suc zero)))) = Geo.j1728SS
ell7Neighbour Geo.j1728SS (suc (suc (suc (suc (suc zero))))) = Geo.j1728SS
ell7Neighbour Geo.j1728SS (suc (suc (suc (suc (suc (suc zero)))))) = Geo.j1728SS
ell7Neighbour Geo.j1728SS (suc (suc (suc (suc (suc (suc (suc zero))))))) = Geo.j1728SS

B11ell7Positive : Classical.ClassicalPrimeDegreeCorrespondence Geo.P11SupersingularJ
B11ell7Positive = record
  { Classical.degreePrime = 7
  ; Classical.neighbour = ell7Neighbour
  }

ell7J0ToJ0 :
  Classical.classicalOperator B11ell7Positive indicatorJ0 Geo.jZeroSS ≡ 2
ell7J0ToJ0 = refl

ell7J0ToJ1728 :
  Classical.classicalOperator B11ell7Positive indicatorJ1728 Geo.jZeroSS ≡ 6
ell7J0ToJ1728 = refl

ell7J1728ToJ0 :
  Classical.classicalOperator B11ell7Positive indicatorJ0 Geo.j1728SS ≡ 4
ell7J1728ToJ0 = refl

ell7J1728ToJ1728 :
  Classical.classicalOperator B11ell7Positive indicatorJ1728 Geo.j1728SS ≡ 4
ell7J1728ToJ1728 = refl

------------------------------------------------------------------------
-- Marked deck-orbital coefficients forced by the theta loops + coarse rows.
------------------------------------------------------------------------

markedT7OrbitalCoefficients : Orbital.OrbitalCoefficients
markedT7OrbitalCoefficients = Orbital.orbitalCoefficients 1 1 2 2 0 2

markedT7ThetaIdentityCounts :
  Orbital.aaId markedT7OrbitalCoefficients ≡ 1
  × Orbital.bbId markedT7OrbitalCoefficients ≡ Theta7.j1728MarkedT7LoopCount
markedT7ThetaIdentityCounts = refl , refl

------------------------------------------------------------------------
-- Literal positive marked T7 neighbour system, arity eight.
------------------------------------------------------------------------

markedT7Neighbour : Fine.P11Fine5 → Fin 8 → Fine.P11Fine5
markedT7Neighbour Fine.a0 zero = Fine.a0
markedT7Neighbour Fine.a0 (suc zero) = Fine.a1
markedT7Neighbour Fine.a0 (suc (suc zero)) = Fine.b0
markedT7Neighbour Fine.a0 (suc (suc (suc zero))) = Fine.b0
markedT7Neighbour Fine.a0 (suc (suc (suc (suc zero)))) = Fine.b1
markedT7Neighbour Fine.a0 (suc (suc (suc (suc (suc zero))))) = Fine.b1
markedT7Neighbour Fine.a0 (suc (suc (suc (suc (suc (suc zero)))))) = Fine.b2
markedT7Neighbour Fine.a0 (suc (suc (suc (suc (suc (suc (suc zero))))))) = Fine.b2

markedT7Neighbour Fine.a1 zero = Fine.a1
markedT7Neighbour Fine.a1 (suc zero) = Fine.a0
markedT7Neighbour Fine.a1 (suc (suc zero)) = Fine.b0
markedT7Neighbour Fine.a1 (suc (suc (suc zero))) = Fine.b0
markedT7Neighbour Fine.a1 (suc (suc (suc (suc zero)))) = Fine.b1
markedT7Neighbour Fine.a1 (suc (suc (suc (suc (suc zero))))) = Fine.b1
markedT7Neighbour Fine.a1 (suc (suc (suc (suc (suc (suc zero)))))) = Fine.b2
markedT7Neighbour Fine.a1 (suc (suc (suc (suc (suc (suc (suc zero))))))) = Fine.b2

markedT7Neighbour Fine.b0 zero = Fine.a0
markedT7Neighbour Fine.b0 (suc zero) = Fine.a0
markedT7Neighbour Fine.b0 (suc (suc zero)) = Fine.a1
markedT7Neighbour Fine.b0 (suc (suc (suc zero))) = Fine.a1
markedT7Neighbour Fine.b0 (suc (suc (suc (suc zero)))) = Fine.b1
markedT7Neighbour Fine.b0 (suc (suc (suc (suc (suc zero))))) = Fine.b1
markedT7Neighbour Fine.b0 (suc (suc (suc (suc (suc (suc zero)))))) = Fine.b2
markedT7Neighbour Fine.b0 (suc (suc (suc (suc (suc (suc (suc zero))))))) = Fine.b2

markedT7Neighbour Fine.b1 zero = Fine.a0
markedT7Neighbour Fine.b1 (suc zero) = Fine.a0
markedT7Neighbour Fine.b1 (suc (suc zero)) = Fine.a1
markedT7Neighbour Fine.b1 (suc (suc (suc zero))) = Fine.a1
markedT7Neighbour Fine.b1 (suc (suc (suc (suc zero)))) = Fine.b0
markedT7Neighbour Fine.b1 (suc (suc (suc (suc (suc zero))))) = Fine.b0
markedT7Neighbour Fine.b1 (suc (suc (suc (suc (suc (suc zero)))))) = Fine.b2
markedT7Neighbour Fine.b1 (suc (suc (suc (suc (suc (suc (suc zero))))))) = Fine.b2

markedT7Neighbour Fine.b2 zero = Fine.a0
markedT7Neighbour Fine.b2 (suc zero) = Fine.a0
markedT7Neighbour Fine.b2 (suc (suc zero)) = Fine.a1
markedT7Neighbour Fine.b2 (suc (suc (suc zero))) = Fine.a1
markedT7Neighbour Fine.b2 (suc (suc (suc (suc zero)))) = Fine.b0
markedT7Neighbour Fine.b2 (suc (suc (suc (suc (suc zero))))) = Fine.b0
markedT7Neighbour Fine.b2 (suc (suc (suc (suc (suc (suc zero)))))) = Fine.b1
markedT7Neighbour Fine.b2 (suc (suc (suc (suc (suc (suc (suc zero))))))) = Fine.b1

MarkedT7Positive : Positive.PositiveFiniteNeighbourSystem Fine.P11Fine5
MarkedT7Positive = record
  { Positive.arity = 8
  ; Positive.neighbour = markedT7Neighbour
  }

------------------------------------------------------------------------
-- Exact quotient to the coarse B_11(7) neighbour slots.
------------------------------------------------------------------------

markedT7ProjectsToBrandt :
  (x : Fine.P11Fine5) → (edge : Fin 8) →
  Fine.projectFine5 (markedT7Neighbour x edge)
  ≡ ell7Neighbour (Fine.projectFine5 x) edge
markedT7ProjectsToBrandt Fine.a0 zero = refl
markedT7ProjectsToBrandt Fine.a0 (suc zero) = refl
markedT7ProjectsToBrandt Fine.a0 (suc (suc zero)) = refl
markedT7ProjectsToBrandt Fine.a0 (suc (suc (suc zero))) = refl
markedT7ProjectsToBrandt Fine.a0 (suc (suc (suc (suc zero)))) = refl
markedT7ProjectsToBrandt Fine.a0 (suc (suc (suc (suc (suc zero))))) = refl
markedT7ProjectsToBrandt Fine.a0 (suc (suc (suc (suc (suc (suc zero)))))) = refl
markedT7ProjectsToBrandt Fine.a0 (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
markedT7ProjectsToBrandt Fine.a1 zero = refl
markedT7ProjectsToBrandt Fine.a1 (suc zero) = refl
markedT7ProjectsToBrandt Fine.a1 (suc (suc zero)) = refl
markedT7ProjectsToBrandt Fine.a1 (suc (suc (suc zero))) = refl
markedT7ProjectsToBrandt Fine.a1 (suc (suc (suc (suc zero)))) = refl
markedT7ProjectsToBrandt Fine.a1 (suc (suc (suc (suc (suc zero))))) = refl
markedT7ProjectsToBrandt Fine.a1 (suc (suc (suc (suc (suc (suc zero)))))) = refl
markedT7ProjectsToBrandt Fine.a1 (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
markedT7ProjectsToBrandt Fine.b0 zero = refl
markedT7ProjectsToBrandt Fine.b0 (suc zero) = refl
markedT7ProjectsToBrandt Fine.b0 (suc (suc zero)) = refl
markedT7ProjectsToBrandt Fine.b0 (suc (suc (suc zero))) = refl
markedT7ProjectsToBrandt Fine.b0 (suc (suc (suc (suc zero)))) = refl
markedT7ProjectsToBrandt Fine.b0 (suc (suc (suc (suc (suc zero))))) = refl
markedT7ProjectsToBrandt Fine.b0 (suc (suc (suc (suc (suc (suc zero)))))) = refl
markedT7ProjectsToBrandt Fine.b0 (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
markedT7ProjectsToBrandt Fine.b1 zero = refl
markedT7ProjectsToBrandt Fine.b1 (suc zero) = refl
markedT7ProjectsToBrandt Fine.b1 (suc (suc zero)) = refl
markedT7ProjectsToBrandt Fine.b1 (suc (suc (suc zero))) = refl
markedT7ProjectsToBrandt Fine.b1 (suc (suc (suc (suc zero)))) = refl
markedT7ProjectsToBrandt Fine.b1 (suc (suc (suc (suc (suc zero))))) = refl
markedT7ProjectsToBrandt Fine.b1 (suc (suc (suc (suc (suc (suc zero)))))) = refl
markedT7ProjectsToBrandt Fine.b1 (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
markedT7ProjectsToBrandt Fine.b2 zero = refl
markedT7ProjectsToBrandt Fine.b2 (suc zero) = refl
markedT7ProjectsToBrandt Fine.b2 (suc (suc zero)) = refl
markedT7ProjectsToBrandt Fine.b2 (suc (suc (suc zero))) = refl
markedT7ProjectsToBrandt Fine.b2 (suc (suc (suc (suc zero)))) = refl
markedT7ProjectsToBrandt Fine.b2 (suc (suc (suc (suc (suc zero))))) = refl
markedT7ProjectsToBrandt Fine.b2 (suc (suc (suc (suc (suc (suc zero)))))) = refl
markedT7ProjectsToBrandt Fine.b2 (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl

------------------------------------------------------------------------
-- Integer linearization and exact S3-sector eigenvalues.
------------------------------------------------------------------------

markedT7Action : S3.Int5 → S3.Int5
markedT7Action v = S3.int5
  (S3.a0c v +ℤ S3.a1c v
    +ℤ ((+ 2) *ℤ S3.b0c v) +ℤ ((+ 2) *ℤ S3.b1c v) +ℤ ((+ 2) *ℤ S3.b2c v))
  (S3.a0c v +ℤ S3.a1c v
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
  markedT7Action S3.signVector ≡ S3.scale5 (+ 0) S3.signVector
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

    positiveMarkedT7Constructed : Bool
    positiveMarkedT7ConstructedIsTrue : positiveMarkedT7Constructed ≡ true

    markedT7ProjectsToCoarseBrandt : Bool
    markedT7ProjectsToCoarseBrandtIsTrue : markedT7ProjectsToCoarseBrandt ≡ true

    t7FailsToSeparateBrandtAndStandard : Bool
    t7FailsToSeparateBrandtAndStandardIsTrue :
      t7FailsToSeparateBrandtAndStandard ≡ true

    allOddPrimeCollisionProvedHere : Bool
    allOddPrimeCollisionProvedHereIsFalse : allOddPrimeCollisionProvedHere ≡ false

canonicalP11MarkedX2T7CollisionBoundary : P11MarkedX2T7CollisionBoundary
canonicalP11MarkedX2T7CollisionBoundary = record
  { directNormSevenThetaLoopsConstructed = true
  ; directNormSevenThetaLoopsConstructedIsTrue = refl
  ; positiveMarkedT7Constructed = true
  ; positiveMarkedT7ConstructedIsTrue = refl
  ; markedT7ProjectsToCoarseBrandt = true
  ; markedT7ProjectsToCoarseBrandtIsTrue = refl
  ; t7FailsToSeparateBrandtAndStandard = true
  ; t7FailsToSeparateBrandtAndStandardIsTrue = refl
  ; allOddPrimeCollisionProvedHere = false
  ; allOddPrimeCollisionProvedHereIsFalse = refl
  }
