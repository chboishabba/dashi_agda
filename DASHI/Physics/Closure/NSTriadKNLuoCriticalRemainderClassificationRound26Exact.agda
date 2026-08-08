module DASHI.Physics.Closure.NSTriadKNLuoCriticalRemainderClassificationRound26Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- A finite remainder is not accepted merely because it is finite.  Every atom
-- is classified as data-controlled, time-integrable, small, or telescoping.
-- The finite list recomposes exactly into these four coordinates.  A separate
-- Gronwall-admissible representation records the only allowed generic shape
--
--   remainder = A_T + B * integralCriticalEnergy,
--
-- without a critical supremum or hidden cutoff constant.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

data RemainderClass : Set where
  dataControlled timeIntegrable smallRemainder telescoping : RemainderClass

record RemainderAtom : Set where
  constructor remainder-atom
  field
    remainderClass : RemainderClass
    remainderValue : ℚ

open RemainderAtom public

totalRemainder : List RemainderAtom → ℚ
totalRemainder [] = 0ℚ
totalRemainder (atom ∷ rest) =
  remainderValue atom + totalRemainder rest

dataRemainder : List RemainderAtom → ℚ
dataRemainder [] = 0ℚ
dataRemainder (atom ∷ rest) with remainderClass atom
... | dataControlled = remainderValue atom + dataRemainder rest
... | timeIntegrable = dataRemainder rest
... | smallRemainder = dataRemainder rest
... | telescoping = dataRemainder rest

integrableRemainder : List RemainderAtom → ℚ
integrableRemainder [] = 0ℚ
integrableRemainder (atom ∷ rest) with remainderClass atom
... | dataControlled = integrableRemainder rest
... | timeIntegrable = remainderValue atom + integrableRemainder rest
... | smallRemainder = integrableRemainder rest
... | telescoping = integrableRemainder rest

smallRemainderTotal : List RemainderAtom → ℚ
smallRemainderTotal [] = 0ℚ
smallRemainderTotal (atom ∷ rest) with remainderClass atom
... | dataControlled = smallRemainderTotal rest
... | timeIntegrable = smallRemainderTotal rest
... | smallRemainder = remainderValue atom + smallRemainderTotal rest
... | telescoping = smallRemainderTotal rest

telescopingRemainder : List RemainderAtom → ℚ
telescopingRemainder [] = 0ℚ
telescopingRemainder (atom ∷ rest) with remainderClass atom
... | dataControlled = telescopingRemainder rest
... | timeIntegrable = telescopingRemainder rest
... | smallRemainder = telescopingRemainder rest
... | telescoping = remainderValue atom + telescopingRemainder rest

remainderClassificationExact :
  (atoms : List RemainderAtom) →
  totalRemainder atoms
  ≡
  dataRemainder atoms
  + integrableRemainder atoms
  + smallRemainderTotal atoms
  + telescopingRemainder atoms
remainderClassificationExact [] = solve []
remainderClassificationExact (atom ∷ rest)
  with remainderClass atom
... | dataControlled
  rewrite remainderClassificationExact rest =
  solve
    ( remainderValue atom
    ∷ dataRemainder rest ∷ integrableRemainder rest
    ∷ smallRemainderTotal rest ∷ telescopingRemainder rest ∷ [])
... | timeIntegrable
  rewrite remainderClassificationExact rest =
  solve
    ( remainderValue atom
    ∷ dataRemainder rest ∷ integrableRemainder rest
    ∷ smallRemainderTotal rest ∷ telescopingRemainder rest ∷ [])
... | smallRemainder
  rewrite remainderClassificationExact rest =
  solve
    ( remainderValue atom
    ∷ dataRemainder rest ∷ integrableRemainder rest
    ∷ smallRemainderTotal rest ∷ telescopingRemainder rest ∷ [])
... | telescoping
  rewrite remainderClassificationExact rest =
  solve
    ( remainderValue atom
    ∷ dataRemainder rest ∷ integrableRemainder rest
    ∷ smallRemainderTotal rest ∷ telescopingRemainder rest ∷ [])

record GronwallAdmissibleRemainder : Set where
  constructor gronwall-admissible-remainder
  field
    remainder : ℚ
    dataAndTimeBudget : ℚ
    linearCoefficient : ℚ
    integratedCriticalEnergy : ℚ
    admissibleMeaning :
      remainder
      ≡ dataAndTimeBudget
      + linearCoefficient * integratedCriticalEnergy

open GronwallAdmissibleRemainder public

gronwallRemainderHasDeclaredShape :
  (R : GronwallAdmissibleRemainder) →
  remainder R
  ≡ dataAndTimeBudget R
    + linearCoefficient R * integratedCriticalEnergy R
gronwallRemainderHasDeclaredShape = admissibleMeaning
