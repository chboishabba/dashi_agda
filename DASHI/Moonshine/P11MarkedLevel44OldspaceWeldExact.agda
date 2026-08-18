module DASHI.Moonshine.P11MarkedLevel44OldspaceWeldExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005. DOI: 10.1007/978-0-387-27226-9.
-- Oldforms/degeneracy maps and Hecke operators away from the added level.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer.
-- DOI: 10.1007/978-1-4684-9458-7.
-- The three-point permutation representation of S3 decomposes as 1 + std.
--
-- John Voight,
-- "Quaternion Algebras", GTM 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Eichler/Brandt theta and Hecke eigenvalue-system context.
--
-- DASHI CONTRIBUTION
--
-- Make the level-44 oldspace explanation precise at every source-native prime
-- currently constructed on the p=11 marked carrier.
--
-- Raising level 11 by the factor 4 gives three classical degeneracy copies
-- indexed by d=1,2,4.  For primes ell not dividing 44, a level-11 Hecke
-- eigenform has the SAME eigenvalue a_ell on all three old copies.  The three
-- copy labels carry the natural S3 permutation representation 1 + std.
--
-- The actual marked p=11 five-state carrier already has exactly three vectors
--
--   Brandt newform, standard1, standard2
--
-- spanning deck types 1 + std.  At T3,T5,T7 all three carry the same exact
-- level-11 fingerprint (-1,1,-2).
--
-- This file welds those two finite structures.  The remaining global theorem is
-- the same-object identification of this marked three-space with the actual
-- level-11 oldspace inside the level-44 Eichler/Jacquet-Langlands module.  Once
-- that map is constructed, prime-to-44 Hecke-isospectrality follows from the
-- oldform theorem rather than a prime-by-prime theta calculation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])

import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact as S3
import DASHI.Moonshine.P11MarkedX2T7HeckeCollisionExact as T7

------------------------------------------------------------------------
-- Three oldform copies d=1,2,4 and their S3 permutation action.
------------------------------------------------------------------------

data OldCopy44 : Set where
  copy1 copy2 copy4 : OldCopy44

oldDeckR : OldCopy44 → OldCopy44
oldDeckR copy1 = copy2
oldDeckR copy2 = copy4
oldDeckR copy4 = copy1

oldDeckS : OldCopy44 → OldCopy44
oldDeckS copy1 = copy1
oldDeckS copy2 = copy4
oldDeckS copy4 = copy2

oldDeckR3 : (x : OldCopy44) → oldDeckR (oldDeckR (oldDeckR x)) ≡ x
oldDeckR3 copy1 = refl
oldDeckR3 copy2 = refl
oldDeckR3 copy4 = refl

oldDeckS2 : (x : OldCopy44) → oldDeckS (oldDeckS x) ≡ x
oldDeckS2 copy1 = refl
oldDeckS2 copy2 = refl
oldDeckS2 copy4 = refl

oldDeckSRS :
  (x : OldCopy44) → oldDeckS (oldDeckR (oldDeckS x)) ≡ oldDeckR (oldDeckR x)
oldDeckSRS copy1 = refl
oldDeckSRS copy2 = refl
oldDeckSRS copy4 = refl

------------------------------------------------------------------------
-- Abstract away-from-44 oldform action: a fixed global eigencharacter is
-- copied unchanged across d=1,2,4.  This is the exact algebraic consequence
-- used from classical degeneracy-map theory.
------------------------------------------------------------------------

data ProbePrime357 : Set where
  ell3 ell5 ell7 : ProbePrime357

level11ProbeEigenvalue : ProbePrime357 → ℤ
level11ProbeEigenvalue ell3 = -[1+ 0 ]
level11ProbeEigenvalue ell5 = + 1
level11ProbeEigenvalue ell7 = -[1+ 1 ]

oldCopyHeckeEigenvalue : ProbePrime357 → OldCopy44 → ℤ
oldCopyHeckeEigenvalue ell copy = level11ProbeEigenvalue ell

oldCopiesHeckeIndistinguishable :
  (ell : ProbePrime357) → (x y : OldCopy44) →
  oldCopyHeckeEigenvalue ell x ≡ oldCopyHeckeEigenvalue ell y
oldCopiesHeckeIndistinguishable ell x y = refl

------------------------------------------------------------------------
-- Actual marked three-space basis with the same prime fingerprints.
------------------------------------------------------------------------

data MarkedOldBasis : Set where
  markedTrivial
  markedStandard1
  markedStandard2 : MarkedOldBasis

markedOldVector : MarkedOldBasis → S3.Int5
markedOldVector markedTrivial = S3.brandtNewformVector
markedOldVector markedStandard1 = S3.standardVector1
markedOldVector markedStandard2 = S3.standardVector2

markedProbeAction : ProbePrime357 → S3.Int5 → S3.Int5
markedProbeAction ell3 = S3.markedT3Action
markedProbeAction ell5 = S3.markedT5Action
markedProbeAction ell7 = T7.markedT7Action

markedOldBasisHasLevel11Eigenvalue :
  (ell : ProbePrime357) → (basis : MarkedOldBasis) →
  markedProbeAction ell (markedOldVector basis)
  ≡ S3.scale5 (level11ProbeEigenvalue ell) (markedOldVector basis)
markedOldBasisHasLevel11Eigenvalue ell3 markedTrivial = S3.T3BrandtEigen
markedOldBasisHasLevel11Eigenvalue ell3 markedStandard1 = S3.T3Standard1Eigen
markedOldBasisHasLevel11Eigenvalue ell3 markedStandard2 = S3.T3Standard2Eigen
markedOldBasisHasLevel11Eigenvalue ell5 markedTrivial = S3.T5BrandtEigen
markedOldBasisHasLevel11Eigenvalue ell5 markedStandard1 = S3.T5Standard1Eigen
markedOldBasisHasLevel11Eigenvalue ell5 markedStandard2 = S3.T5Standard2Eigen
markedOldBasisHasLevel11Eigenvalue ell7 markedTrivial = T7.T7BrandtNewformEigen
markedOldBasisHasLevel11Eigenvalue ell7 markedStandard1 = T7.T7Standard1Eigen
markedOldBasisHasLevel11Eigenvalue ell7 markedStandard2 = T7.T7Standard2Eigen

------------------------------------------------------------------------
-- Explicit copy/basis correspondence at the level of the three-state pattern.
------------------------------------------------------------------------

oldCopyToMarkedBasis : OldCopy44 → MarkedOldBasis
oldCopyToMarkedBasis copy1 = markedTrivial
oldCopyToMarkedBasis copy2 = markedStandard1
oldCopyToMarkedBasis copy4 = markedStandard2

markedBasisToOldCopy : MarkedOldBasis → OldCopy44
markedBasisToOldCopy markedTrivial = copy1
markedBasisToOldCopy markedStandard1 = copy2
markedBasisToOldCopy markedStandard2 = copy4

oldMarkedRoundTrip :
  (x : OldCopy44) → markedBasisToOldCopy (oldCopyToMarkedBasis x) ≡ x
oldMarkedRoundTrip copy1 = refl
oldMarkedRoundTrip copy2 = refl
oldMarkedRoundTrip copy4 = refl

markedOldRoundTrip :
  (x : MarkedOldBasis) → oldCopyToMarkedBasis (markedBasisToOldCopy x) ≡ x
markedOldRoundTrip markedTrivial = refl
markedOldRoundTrip markedStandard1 = refl
markedOldRoundTrip markedStandard2 = refl

record P11MarkedLevel44OldspaceBoundary : Set where
  field
    threeCopyOldspacePatternConstructed : Bool
    threeCopyOldspacePatternConstructedIsTrue :
      threeCopyOldspacePatternConstructed ≡ true

    markedOnePlusStandardPatternConstructed : Bool
    markedOnePlusStandardPatternConstructedIsTrue :
      markedOnePlusStandardPatternConstructed ≡ true

    t3t5t7OldspaceFingerprintMatched : Bool
    t3t5t7OldspaceFingerprintMatchedIsTrue :
      t3t5t7OldspaceFingerprintMatched ≡ true

    globalJacquetLanglandsSameObjectMapConstructed : Bool
    globalJacquetLanglandsSameObjectMapConstructedIsFalse :
      globalJacquetLanglandsSameObjectMapConstructed ≡ false

canonicalP11MarkedLevel44OldspaceBoundary : P11MarkedLevel44OldspaceBoundary
canonicalP11MarkedLevel44OldspaceBoundary = record
  { threeCopyOldspacePatternConstructed = true
  ; threeCopyOldspacePatternConstructedIsTrue = refl
  ; markedOnePlusStandardPatternConstructed = true
  ; markedOnePlusStandardPatternConstructedIsTrue = refl
  ; t3t5t7OldspaceFingerprintMatched = true
  ; t3t5t7OldspaceFingerprintMatchedIsTrue = refl
  ; globalJacquetLanglandsSameObjectMapConstructed = false
  ; globalJacquetLanglandsSameObjectMapConstructedIsFalse = refl
  }
