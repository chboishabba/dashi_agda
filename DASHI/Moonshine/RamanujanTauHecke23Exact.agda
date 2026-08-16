module DASHI.Moonshine.RamanujanTauHecke23Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "A Course in Arithmetic", Graduate Texts in Mathematics 7,
-- Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- DASHI CONTRIBUTION
--
-- Give the Aristotle Hecke/Delta lane an exact executable checksum surface
-- inside DASHI.  The source coefficients of Ramanujan's normalized weight-12
-- cusp form Delta are recorded at the small indices used by the supplied Lean
-- development, and the relevant Hecke consequences are reduced to closed
-- integer equalities:
--
--   tau(6)  = tau(2) tau(3)
--   tau(9)  = tau(3)^2 - 3^11
--   tau(12) = tau(2)^2 tau(3) - 2^11 tau(3)
--   tau(27) = tau(3)^3 - 2*3^11 tau(3).
--
-- This module does NOT claim to construct the analytic modular form Delta or
-- the global Hecke algebra.  It makes the concrete coefficient identities
-- themselves kernel-reducible rather than leaving them as prose receipts.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming
    ( _+_ to _+ℤ_
    ; _-_ to _-ℤ_
    ; _*_ to _*ℤ_
    )

------------------------------------------------------------------------
-- Concrete coefficient lane.
------------------------------------------------------------------------

tau2 : ℤ
tau2 = -[1+ 23 ]

tau3 : ℤ
tau3 = + 252

tau6 : ℤ
tau6 = -[1+ 6047 ]

tau9 : ℤ
tau9 = -[1+ 113642 ]

tau12 : ℤ
tau12 = -[1+ 370943 ]

tau27 : ℤ
tau27 = -[1+ 73279079 ]

pow2Eleven : ℤ
pow2Eleven = + 2048

pow3Eleven : ℤ
pow3Eleven = + 177147

------------------------------------------------------------------------
-- Hecke identities at the supplied small indices.
------------------------------------------------------------------------

tau6CoprimeMultiplicative :
  tau6 ≡ tau2 *ℤ tau3
tau6CoprimeMultiplicative = refl

tau9PrimeSquareRecurrence :
  tau9 ≡ tau3 *ℤ tau3 -ℤ pow3Eleven
tau9PrimeSquareRecurrence = refl

tau12MixedWordRecurrence :
  tau12
  ≡ (tau2 *ℤ tau2 *ℤ tau3)
      -ℤ (pow2Eleven *ℤ tau3)
tau12MixedWordRecurrence = refl

tau27PrimeCubeRecurrence :
  tau27
  ≡ (tau3 *ℤ tau3 *ℤ tau3)
      -ℤ ((+ 2 *ℤ pow3Eleven) *ℤ tau3)
tau27PrimeCubeRecurrence = refl

------------------------------------------------------------------------
-- Operator-word coefficients behind the same formulas.
------------------------------------------------------------------------

weight12HeckePrimeSquareCorrectionAt2 : ℤ
weight12HeckePrimeSquareCorrectionAt2 = pow2Eleven

weight12HeckePrimeSquareCorrectionAt3 : ℤ
weight12HeckePrimeSquareCorrectionAt3 = pow3Eleven

weight12HeckePrimeCubeLinearCorrectionAt3 : ℤ
weight12HeckePrimeCubeLinearCorrectionAt3 = + 2 *ℤ pow3Eleven

primeSquareCorrection2Is2048 :
  weight12HeckePrimeSquareCorrectionAt2 ≡ + 2048
primeSquareCorrection2Is2048 = refl

primeSquareCorrection3Is177147 :
  weight12HeckePrimeSquareCorrectionAt3 ≡ + 177147
primeSquareCorrection3Is177147 = refl

primeCubeCorrection3Is354294 :
  weight12HeckePrimeCubeLinearCorrectionAt3 ≡ + 354294
primeCubeCorrection3Is354294 = refl

------------------------------------------------------------------------
-- Compact authority boundary: concrete identities yes; analytic/global
-- construction no.
------------------------------------------------------------------------

record RamanujanTauHecke23Boundary : Set where
  field
    concreteTauIdentitiesConstructed : Bool
    concreteTauIdentitiesConstructedIsTrue :
      concreteTauIdentitiesConstructed ≡ true
    analyticDeltaConstructedHere : Bool
    analyticDeltaConstructedHereIsFalse :
      analyticDeltaConstructedHere ≡ false
    globalClassicalHeckeAlgebraConstructedHere : Bool
    globalClassicalHeckeAlgebraConstructedHereIsFalse :
      globalClassicalHeckeAlgebraConstructedHere ≡ false

canonicalRamanujanTauHecke23Boundary :
  RamanujanTauHecke23Boundary
canonicalRamanujanTauHecke23Boundary =
  record
    { concreteTauIdentitiesConstructed = true
    ; concreteTauIdentitiesConstructedIsTrue = refl
    ; analyticDeltaConstructedHere = false
    ; analyticDeltaConstructedHereIsFalse = refl
    ; globalClassicalHeckeAlgebraConstructedHere = false
    ; globalClassicalHeckeAlgebraConstructedHereIsFalse = refl
    }
