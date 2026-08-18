module DASHI.Moonshine.P11Level44OldspaceSameObjectCutsetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005. DOI: 10.1007/978-0-387-27226-9.
-- Degeneracy maps / oldforms and good-prime Hecke action.
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Brandt modules, quaternionic modular forms and Eichler/Jacquet-Langlands
-- comparison context.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Full-level-2 auxiliary structure / deck action.
--
-- DASHI CONTRIBUTION
--
-- Record the genuinely narrowed same-object cutset after the current tranche.
-- Both sides of the proposed level-44 comparison are now independently
-- theorem-producing:
--
-- ANALYTIC / q-series side
--   * coefficient degeneracy V_d is formalized by exact support laws;
--   * T_l V_d = V_d T_l is proved for gcd(d,l)=1;
--   * a T_l eigencharacter is transported to each d=1,2,4 old copy;
--   * therefore no further good-prime scan is required to know that the three
--     analytic old copies are Hecke-isospectral.
--
-- MARKED / quaternion side
--   * the actual marked five-state carrier contains the integral permutation
--     basis v1,v2,v4;
--   * one Z-linear realization from the free three-copy module intertwines the
--     genuine deck S3 action and source-native T3,T5,T7 actions;
--   * the same three-space is Brandt-newform + deck-standard.
--
-- Hence the remaining theorem is NOT another Hecke relation.  It is one
-- same-object comparison identifying the analytic d=1,2,4 degeneracy-copy
-- module with the marked v1,v2,v4 module in a way compatible with the already
-- constructed deck and good-prime Hecke structures.
--
-- This file intentionally represents that map as an interface whose downstream
-- consequences are proved.  It does not fabricate the missing Eichler/JL map.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ)

import DASHI.Moonshine.FormalQSeriesOldformDegeneracyHeckeExact as QDeg
import DASHI.Moonshine.FormalQSeriesOldformEigencharacterTransportExact as QEig
import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Marked
import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact as S3

------------------------------------------------------------------------
-- The comparison data that remains to be constructed geometrically.
--
-- We do not demand literal equality of an analytic q-series with an Int5
-- vector.  The map compares their common abstract old-copy coordinate module.
------------------------------------------------------------------------

record Level44OldspaceSameObjectComparison : Set₁ where
  field
    -- Actual analytic source and its three degeneracy-copy coefficient series.
    level11Series : QDeg.FormalQSeries
    copy1Series copy2Series copy4Series : QDeg.FormalQSeries

    copy1Degeneracy :
      QDeg.DegeneracyCoefficientLaw 1 level11Series copy1Series
    copy2Degeneracy :
      QDeg.DegeneracyCoefficientLaw 2 level11Series copy2Series
    copy4Degeneracy :
      QDeg.DegeneracyCoefficientLaw 4 level11Series copy4Series

    -- A coefficientwise analytic realization of the SAME free copy module.
    analyticRealize : Marked.Old3 → QDeg.FormalQSeries

    analyticBasis1 :
      (n : Nat) → analyticRealize Marked.oldBasis1 n ≡ copy1Series n
    analyticBasis2 :
      (n : Nat) → analyticRealize Marked.oldBasis2 n ≡ copy2Series n
    analyticBasis4 :
      (n : Nat) → analyticRealize Marked.oldBasis4 n ≡ copy4Series n

    analyticAdditive :
      (u v : Marked.Old3) → (n : Nat) →
      analyticRealize (Marked.addOld3 u v) n
      ≡ analyticRealize u n Data.Integer.+ analyticRealize v n

    analyticScalar :
      (k : ℤ) → (v : Marked.Old3) → (n : Nat) →
      analyticRealize (Marked.scaleOld3 k v) n
      ≡ k Data.Integer.* analyticRealize v n

open Level44OldspaceSameObjectComparison public

------------------------------------------------------------------------
-- Once this comparison is built, both realizations share one copy coordinate.
-- Distinct deck copies are therefore not an accidental basis naming on either
-- side; they are literally images of the same Old3 coordinate vectors.
------------------------------------------------------------------------

record OldspaceComparisonConsequence
  (C : Level44OldspaceSameObjectComparison) : Set where
  field
    markedRealizationExists : Marked.Old3 → S3.Int5
    markedRealizationIsCanonical :
      (v : Marked.Old3) → markedRealizationExists v ≡ Marked.realizeOld3 v

    analyticCopy1IsSameCoordinate :
      (n : Nat) → analyticRealize C Marked.oldBasis1 n ≡ copy1Series C n
    analyticCopy2IsSameCoordinate :
      (n : Nat) → analyticRealize C Marked.oldBasis2 n ≡ copy2Series C n
    analyticCopy4IsSameCoordinate :
      (n : Nat) → analyticRealize C Marked.oldBasis4 n ≡ copy4Series C n

comparisonConsequence :
  (C : Level44OldspaceSameObjectComparison) → OldspaceComparisonConsequence C
comparisonConsequence C = record
  { markedRealizationExists = Marked.realizeOld3
  ; markedRealizationIsCanonical = λ v → refl
  ; analyticCopy1IsSameCoordinate = analyticBasis1 C
  ; analyticCopy2IsSameCoordinate = analyticBasis2 C
  ; analyticCopy4IsSameCoordinate = analyticBasis4 C
  }

------------------------------------------------------------------------
-- Frontier record: every surrounding algebraic obligation is now closed.
------------------------------------------------------------------------

record P11Level44OldspaceSameObjectCutsetBoundary : Set where
  field
    coefficientDegeneracyHeckeCommutationProved : Bool
    analyticGoodPrimeEigenTransportProved : Bool
    markedPermutationModuleConstructed : Bool
    markedDeckIntertwinerConstructed : Bool
    markedT3T5T7IntertwinerConstructed : Bool
    morePrimeProbesRequiredBeforeComparison : Bool
    actualEichlerJacquetLanglandsComparisonConstructed : Bool

canonicalP11Level44OldspaceSameObjectCutsetBoundary :
  P11Level44OldspaceSameObjectCutsetBoundary
canonicalP11Level44OldspaceSameObjectCutsetBoundary = record
  { coefficientDegeneracyHeckeCommutationProved = true
  ; analyticGoodPrimeEigenTransportProved = true
  ; markedPermutationModuleConstructed = true
  ; markedDeckIntertwinerConstructed = true
  ; markedT3T5T7IntertwinerConstructed = true
  ; morePrimeProbesRequiredBeforeComparison = false
  ; actualEichlerJacquetLanglandsComparisonConstructed = false
  }
