module DASHI.Moonshine.P11Level44TwoAdicAveragingNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Kimball Martin,
-- "The basis problem revisited", Transactions of the American Mathematical
-- Society 373 (2020), 4523--4559. DOI: 10.1090/tran/8077.
-- Local/global new- and old-vector structure and the non-canonical oldspace JL
-- comparison.
--
-- Jean-Pierre Serre,
-- "Trees", Springer, 1980/2003. DOI: 10.1007/978-3-642-61856-7.
-- Bruhat--Tits / compact-double-coset context.
--
-- DASHI CONTRIBUTION
--
-- Test the most obvious local comparison between the principal-level-2 and
-- Gamma_0(4) three-dimensional fixed-vector models: compact averaging.
--
-- A reproducible finite computation in
--
--   scripts/verify_p11_two_adic_local_averaging.py
--
-- works on the exact finite quotient
--
--   B(Z/4) \ GL_2(Z/4).
--
-- It has six left cosets.  Right K(2) has three two-point orbits, while right
-- B=K_0(4) has orbit sizes 4,1,1.  Relative to the three orbit-indicator bases,
-- right-B averaging is
--
--        [ 1/2  1/2  0 ]
--   A  = [  0    0   1 ]
--        [  0    0   1 ].
--
-- Clear denominator two:
--
--        [ 1  1  0 ]
--   2A = [ 0  0  2 ]
--        [ 0  0  2 ].
--
-- This file encodes that exact denominator-cleared map and proves it collapses
-- the first two principal-level-2 basis vectors.  Therefore compact averaging
-- cannot be the missing three-dimensional local isomorphism.
--
-- The next constructive target must use genuinely extra local-at-2 structure,
-- e.g. a noncompact double-coset/test-vector operator carrying the Satake/U_2
-- datum, rather than only the compact finite deck quotient.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_)
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)

import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Old

------------------------------------------------------------------------
-- A separate codomain: the three Gamma_0(4) / Bruhat orbit coordinates.
------------------------------------------------------------------------

record Bruhat3 : Set where
  constructor bruhat3
  field
    wide left right : ℤ
open Bruhat3 public

clearedCompactAverage : Old.Old3 → Bruhat3
clearedCompactAverage v = bruhat3
  (Old.x1 v +ℤ Old.x2 v)
  ((+ 2) *ℤ Old.x4 v)
  ((+ 2) *ℤ Old.x4 v)

------------------------------------------------------------------------
-- Exact denominator-cleared matrix columns.
------------------------------------------------------------------------

averageBasis1 :
  clearedCompactAverage Old.oldBasis1 ≡ bruhat3 (+ 1) (+ 0) (+ 0)
averageBasis1 = refl

averageBasis2 :
  clearedCompactAverage Old.oldBasis2 ≡ bruhat3 (+ 1) (+ 0) (+ 0)
averageBasis2 = refl

averageBasis4 :
  clearedCompactAverage Old.oldBasis4 ≡ bruhat3 (+ 0) (+ 2) (+ 2)
averageBasis4 = refl

firstTwoPrincipalBasisVectorsCollapse :
  clearedCompactAverage Old.oldBasis1
  ≡ clearedCompactAverage Old.oldBasis2
firstTwoPrincipalBasisVectorsCollapse = refl

------------------------------------------------------------------------
-- Noninjectivity is theorem-level rather than a rank comment.
------------------------------------------------------------------------

data Impossible : Set where

oldBasis1IsNotOldBasis2 : Old.oldBasis1 ≡ Old.oldBasis2 → Impossible
oldBasis1IsNotOldBasis2 ()

record NonInjectiveWitness
    {A B : Set} (f : A → B) : Set where
  field
    first second : A
    sameImage : f first ≡ f second
    distinct : first ≡ second → Impossible

compactAveragingNonInjective : NonInjectiveWitness clearedCompactAverage
compactAveragingNonInjective = record
  { first = Old.oldBasis1
  ; second = Old.oldBasis2
  ; sameImage = firstTwoPrincipalBasisVectorsCollapse
  ; distinct = oldBasis1IsNotOldBasis2
  }

------------------------------------------------------------------------
-- A direct no-isomorphism consequence for any proposed inverse.
------------------------------------------------------------------------

record LeftInverseCandidate : Set where
  field
    recover : Bruhat3 → Old.Old3
    leftInverse :
      (v : Old.Old3) → recover (clearedCompactAverage v) ≡ v
open LeftInverseCandidate public

compactAveragingHasNoLeftInverse : LeftInverseCandidate → Impossible
compactAveragingHasNoLeftInverse C =
  oldBasis1IsNotOldBasis2
    (trans
      (sym (leftInverse C Old.oldBasis1))
      (trans
        (cong (recover C) firstTwoPrincipalBasisVectorsCollapse)
        (leftInverse C Old.oldBasis2)))

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record P11Level44TwoAdicAveragingNoGoBoundary : Set where
  field
    finiteLevel4OrbitComputationReproducedByScript : Bool
    denominatorClearedAveragingEncoded : Bool
    explicitKernelCollisionConstructed : Bool
    compactAveragingInjective : Bool
    compactAveragingCanBeLocalIsomorphism : Bool
    noncompactTwoAdicOperatorStillRequired : Bool

canonicalP11Level44TwoAdicAveragingNoGoBoundary :
  P11Level44TwoAdicAveragingNoGoBoundary
canonicalP11Level44TwoAdicAveragingNoGoBoundary = record
  { finiteLevel4OrbitComputationReproducedByScript = true
  ; denominatorClearedAveragingEncoded = true
  ; explicitKernelCollisionConstructed = true
  ; compactAveragingInjective = false
  ; compactAveragingCanBeLocalIsomorphism = false
  ; noncompactTwoAdicOperatorStillRequired = true
  }
