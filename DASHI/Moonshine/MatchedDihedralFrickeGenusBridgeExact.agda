module DASHI.Moonshine.MatchedDihedralFrickeGenusBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires",
-- Seminaire Delange-Pisot-Poitou 16 (1974-1975), expose 7, pp. 1-8.
-- MR 417184; no DOI assigned.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230-239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Feed the candidate-indexed matched-dihedral branching spectrum into the
-- existing representation/Fricke coupling.
--
-- For p=2j+1, V_j|D_p has exactly j+1 occurring sectors.  Hence
--
--   2 * sectorCount = p + 1.
--
-- The existing SO(3) character lane independently supplies the order-two and
-- order-three elliptic counts e2,e3.  Therefore the prime-level genus formula
-- can be reconstructed as
--
--   12*g_rep = 2*sectorCount - 3*e2 - 4*e3,
--
-- replacing the raw p+1 term by a genuine reduced-representation observable.
-- The arithmetic Fricke fixed-point/class-number column is then reused without
-- change.  This strengthens the coupling but does not claim a global Ogg
-- theorem beyond the finite control universe already constructed in-repo.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_∸_; _/_)

import DASHI.Foundations.MatchedDihedralSO3RestrictionExact as Dihedral
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.PrimeFrickeGenusControlExact as Fricke
import DASHI.Moonshine.PrimeRepresentationFrickeCouplingExact as Existing

------------------------------------------------------------------------
-- Reduced-representation sector count at each odd prime control.
------------------------------------------------------------------------

matchedSectorCount : Matrix.OddPrimeCandidateUnder72 → Nat
matchedSectorCount prime =
  Dihedral.occurringSectorCount
    (Spin.jNat (Matrix.primeAngularMomentum prime))

matchedSectorCountSuppliesLevelPlusOne :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  2 * matchedSectorCount prime ≡ Matrix.primeLevel prime + 1
matchedSectorCountSuppliesLevelPlusOne Matrix.prime3 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime5 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime7 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime11 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime13 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime17 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime19 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime23 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime29 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime31 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime37 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime41 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime43 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime47 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime53 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime59 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime61 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime67 = refl
matchedSectorCountSuppliesLevelPlusOne Matrix.prime71 = refl

------------------------------------------------------------------------
-- Genus reconstructed from matched branching count + C2/C3 characters.
------------------------------------------------------------------------

matchedRepresentationX0Genus :
  Matrix.OddPrimeCandidateUnder72 → Nat
matchedRepresentationX0Genus prime =
  ((2 * matchedSectorCount prime)
    ∸ 3 * Existing.representationEllipticOrder2 prime
    ∸ 4 * Existing.representationEllipticOrder3 prime)
  / 12

matchedRepresentationGenusMatchesExisting :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  matchedRepresentationX0Genus prime
  ≡ Existing.representationX0Genus prime
matchedRepresentationGenusMatchesExisting Matrix.prime3 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime5 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime7 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime11 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime13 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime17 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime19 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime23 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime29 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime31 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime37 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime41 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime43 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime47 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime53 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime59 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime61 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime67 = refl
matchedRepresentationGenusMatchesExisting Matrix.prime71 = refl

matchedRepresentationGenusMatchesFrickeTable :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  matchedRepresentationX0Genus prime
  ≡ Fricke.genusX0 (Fricke.frickeRow prime)
matchedRepresentationGenusMatchesFrickeTable prime =
  trans
    (matchedRepresentationGenusMatchesExisting prime)
    (Existing.representationX0GenusMatchesFricke prime)

------------------------------------------------------------------------
-- Fricke defect with the representation-derived p+1 term.
------------------------------------------------------------------------

matchedRepresentationArithmeticFrickeDefect :
  Matrix.OddPrimeCandidateUnder72 → Nat
matchedRepresentationArithmeticFrickeDefect prime =
  (2 * matchedRepresentationX0Genus prime + 2)
  ∸ Fricke.frickeFixedPointCount (Fricke.frickeRow prime)

matchedDefectMatchesExisting :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  matchedRepresentationArithmeticFrickeDefect prime
  ≡ Existing.representationArithmeticFrickeDefect prime
matchedDefectMatchesExisting Matrix.prime3 = refl
matchedDefectMatchesExisting Matrix.prime5 = refl
matchedDefectMatchesExisting Matrix.prime7 = refl
matchedDefectMatchesExisting Matrix.prime11 = refl
matchedDefectMatchesExisting Matrix.prime13 = refl
matchedDefectMatchesExisting Matrix.prime17 = refl
matchedDefectMatchesExisting Matrix.prime19 = refl
matchedDefectMatchesExisting Matrix.prime23 = refl
matchedDefectMatchesExisting Matrix.prime29 = refl
matchedDefectMatchesExisting Matrix.prime31 = refl
matchedDefectMatchesExisting Matrix.prime37 = refl
matchedDefectMatchesExisting Matrix.prime41 = refl
matchedDefectMatchesExisting Matrix.prime43 = refl
matchedDefectMatchesExisting Matrix.prime47 = refl
matchedDefectMatchesExisting Matrix.prime53 = refl
matchedDefectMatchesExisting Matrix.prime59 = refl
matchedDefectMatchesExisting Matrix.prime61 = refl
matchedDefectMatchesExisting Matrix.prime67 = refl
matchedDefectMatchesExisting Matrix.prime71 = refl

matchedDefectIsFourTimesFrickeGenus :
  (prime : Matrix.OddPrimeCandidateUnder72) →
  matchedRepresentationArithmeticFrickeDefect prime
  ≡ 4 * Fricke.genusX0Plus (Fricke.frickeRow prime)
matchedDefectIsFourTimesFrickeGenus prime =
  trans
    (matchedDefectMatchesExisting prime)
    (Existing.representationArithmeticDefectIsFourTimesFrickeGenus prime)

record MatchedDihedralFrickeBridgeBoundary : Set where
  field
    rawLevelPlusOneReplacedByBranchSectorCount : Bool
    rawLevelPlusOneReplacedByBranchSectorCountIsTrue :
      rawLevelPlusOneReplacedByBranchSectorCount ≡ true
    allOddPrimeControlsChecked : Bool
    allOddPrimeControlsCheckedIsTrue : allOddPrimeControlsChecked ≡ true
    arithmeticFrickeFixedPointInputStillIndependent : Bool
    arithmeticFrickeFixedPointInputStillIndependentIsTrue :
      arithmeticFrickeFixedPointInputStillIndependent ≡ true
    globalOggClassificationPromoted : Bool
    globalOggClassificationPromotedIsFalse :
      globalOggClassificationPromoted ≡ false

canonicalMatchedDihedralFrickeBridgeBoundary :
  MatchedDihedralFrickeBridgeBoundary
canonicalMatchedDihedralFrickeBridgeBoundary =
  record
    { rawLevelPlusOneReplacedByBranchSectorCount = true
    ; rawLevelPlusOneReplacedByBranchSectorCountIsTrue = refl
    ; allOddPrimeControlsChecked = true
    ; allOddPrimeControlsCheckedIsTrue = refl
    ; arithmeticFrickeFixedPointInputStillIndependent = true
    ; arithmeticFrickeFixedPointInputStillIndependentIsTrue = refl
    ; globalOggClassificationPromoted = false
    ; globalOggClassificationPromotedIsFalse = refl
    }
