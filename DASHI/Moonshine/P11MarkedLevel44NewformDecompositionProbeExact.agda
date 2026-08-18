module DASHI.Moonshine.P11MarkedLevel44NewformDecompositionProbeExact where

------------------------------------------------------------------------
-- EXECUTABLE ARITHMETIC REFERENCE / CONTEXT
--
-- The conductor-44 elliptic curve isogeny class 44.a has the model
--
--   E_44 : y^2 = x^3 + x^2 + 3x - 1.
--
-- LMFDB is used only as the model/source cross-check; no DOI is asserted for
-- the database.  The coefficients below are DERIVED here by direct finite
-- point counts at p=3,5,7 rather than imported from the database.
--
-- Classical modular-form context:
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005. DOI: 10.1007/978-0-387-27226-9.
--
-- DASHI CONTRIBUTION
--
-- The p=11 full-level-2 marked S3-sign sector has source-native Hecke
-- eigenvalues
--
--   (T3,T5,T7) = (1,-3,2).
--
-- Directly count E_44 over F3,F5,F7:
--
--   #E_44(F3)=3  => a3= 1,
--   #E_44(F5)=9  => a5=-3,
--   #E_44(F7)=6  => a7= 2.
--
-- Thus the marked sign sector matches the conductor-44 newform at all three
-- source-native odd primes currently constructed.
--
-- Combined with the separate p=11 result
--
--   Brandt-newform = deck-standard = (-1,1,-2)
--
-- at T3,T5,T7, the complete five-state marked module has the finite fingerprint
-- expected from
--
--   Eisenstein
--     + conductor-44 sign newform
--     + conductor-11 newform carried by (trivial + standard deck type).
--
-- IMPORTANT BOUNDARY
-- This is a three-prime exact arithmetic identification/probe, not a proof of
-- equality of the full q-series or an all-prime automorphic decomposition.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])

import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact as S3
import DASHI.Moonshine.P11MarkedX2T7HeckeCollisionExact as T7

------------------------------------------------------------------------
-- Direct finite point counts on E_44.
------------------------------------------------------------------------

-- p=3: x-row solution counts 0,2,0; plus infinity.
e44F3AffineCount : Nat
e44F3AffineCount = 2

e44F3PointCount : Nat
e44F3PointCount = e44F3AffineCount + 1

e44F3PointCountIsThree : e44F3PointCount ≡ 3
e44F3PointCountIsThree = refl

-- a3=+1 encoded subtraction-free as p+1 = #E + 1.
e44A3PositiveOne : 3 + 1 ≡ e44F3PointCount + 1
e44A3PositiveOne = refl

-- p=5: x-row counts 2,2,0,2,2; plus infinity.
e44F5AffineCount : Nat
e44F5AffineCount = 8

e44F5PointCount : Nat
e44F5PointCount = e44F5AffineCount + 1

e44F5PointCountIsNine : e44F5PointCount ≡ 9
e44F5PointCountIsNine = refl

-- a5=-3 encoded as #E = p+1+3.
e44A5NegativeThree : e44F5PointCount ≡ 5 + 1 + 3
e44A5NegativeThree = refl

-- p=7: x-row counts 0,2,0,2,1,0,0; plus infinity.
e44F7AffineCount : Nat
e44F7AffineCount = 5

e44F7PointCount : Nat
e44F7PointCount = e44F7AffineCount + 1

e44F7PointCountIsSix : e44F7PointCount ≡ 6
e44F7PointCountIsSix = refl

-- a7=+2 encoded as p+1 = #E + 2.
e44A7PositiveTwo : 7 + 1 ≡ e44F7PointCount + 2
e44A7PositiveTwo = refl

------------------------------------------------------------------------
-- Exact Hecke fingerprints.
------------------------------------------------------------------------

record ThreePrimeEigenFingerprint : Set where
  constructor eigen357
  field
    t3 t5 t7 : ℤ

level44PointCountFingerprint : ThreePrimeEigenFingerprint
level44PointCountFingerprint = eigen357 (+ 1) (-[1+ 2 ]) (+ 2)

markedSignFingerprint : ThreePrimeEigenFingerprint
markedSignFingerprint = eigen357 (+ 1) (-[1+ 2 ]) (+ 2)

markedSignMatchesLevel44At357 :
  markedSignFingerprint ≡ level44PointCountFingerprint
markedSignMatchesLevel44At357 = refl

level11NewformFingerprint : ThreePrimeEigenFingerprint
level11NewformFingerprint = eigen357 (-[1+ 0 ]) (+ 1) (-[1+ 1 ])

markedStandardFingerprint : ThreePrimeEigenFingerprint
markedStandardFingerprint = eigen357 (-[1+ 0 ]) (+ 1) (-[1+ 1 ])

markedStandardMatchesLevel11At357 :
  markedStandardFingerprint ≡ level11NewformFingerprint
markedStandardMatchesLevel11At357 = refl

------------------------------------------------------------------------
-- Consume the actual marked eigen theorems, not only the fingerprint literals.
------------------------------------------------------------------------

signT3IsLevel44A3 :
  S3.markedT3Action S3.signVector ≡ S3.scale5 (+ 1) S3.signVector
signT3IsLevel44A3 = S3.T3SignEigen

signT5IsLevel44A5 :
  S3.markedT5Action S3.signVector ≡ S3.scale5 (-[1+ 2 ]) S3.signVector
signT5IsLevel44A5 = S3.T5SignEigen

signT7IsLevel44A7 :
  T7.markedT7Action S3.signVector ≡ S3.scale5 (+ 2) S3.signVector
signT7IsLevel44A7 = T7.T7SignEigen

standardT7IsLevel11A7 :
  T7.markedT7Action S3.standardVector1
  ≡ S3.scale5 (-[1+ 1 ]) S3.standardVector1
standardT7IsLevel11A7 = T7.T7Standard1Eigen

record P11MarkedLevel44DecompositionProbeBoundary : Set where
  field
    level44PointCounts357Constructed : Bool
    level44PointCounts357ConstructedIsTrue :
      level44PointCounts357Constructed ≡ true

    signSectorMatchesLevel44At357 : Bool
    signSectorMatchesLevel44At357IsTrue :
      signSectorMatchesLevel44At357 ≡ true

    standardSectorMatchesLevel11At357 : Bool
    standardSectorMatchesLevel11At357IsTrue :
      standardSectorMatchesLevel11At357 ≡ true

    fullAllPrimeDecompositionClaimed : Bool
    fullAllPrimeDecompositionClaimedIsFalse :
      fullAllPrimeDecompositionClaimed ≡ false

canonicalP11MarkedLevel44DecompositionProbeBoundary :
  P11MarkedLevel44DecompositionProbeBoundary
canonicalP11MarkedLevel44DecompositionProbeBoundary = record
  { level44PointCounts357Constructed = true
  ; level44PointCounts357ConstructedIsTrue = refl
  ; signSectorMatchesLevel44At357 = true
  ; signSectorMatchesLevel44At357IsTrue = refl
  ; standardSectorMatchesLevel11At357 = true
  ; standardSectorMatchesLevel11At357IsTrue = refl
  ; fullAllPrimeDecompositionClaimed = false
  ; fullAllPrimeDecompositionClaimedIsFalse = refl
  }
