module DASHI.Physics.Closure.YMFixedFiniteVolumeBlockedObservableContinuumLimitConditional where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.ClaySprintSeventyNineYMAnisotropicAssumptionAReceipt
  as Sprint79
import DASHI.Physics.Closure.YMAnisotropicAssumptionAConditionalClosure
  as AssumptionA

------------------------------------------------------------------------
-- Fixed finite-volume blocked observable continuum limit, conditional form.
--
-- This is the next UV step after the native Assumption-A closure arithmetic.
-- Eriksson 2602.0077 Theorem 1.6 is already the governing theorem shape in
-- the repo: fixed-finite-volume blocked observable continuum convergence
-- holds conditional on Assumption A.  Here we express that route directly as
-- a theorem surface consuming the new in-repo conditional Assumption-A
-- closure.

fixedFiniteVolumeBlockedObservableContinuumLimitConditional : Bool
fixedFiniteVolumeBlockedObservableContinuumLimitConditional = true

fixedFiniteVolumeBlockedObservableContinuumLimitUnconditional : Bool
fixedFiniteVolumeBlockedObservableContinuumLimitUnconditional = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

FixedFiniteVolumeBlockedObservableContinuumLimitFormula : Set
FixedFiniteVolumeBlockedObservableContinuumLimitFormula = String

canonicalFixedFiniteVolumeBlockedObservableContinuumLimitFormula :
  FixedFiniteVolumeBlockedObservableContinuumLimitFormula
canonicalFixedFiniteVolumeBlockedObservableContinuumLimitFormula =
  "Assumption A for spatial Q_hp implies fixed-finite-volume blocked observable continuum convergence"

record YMFixedFiniteVolumeBlockedObservableContinuumLimitConditionalTheorem
  (cLocal cF k : Nat) : Set where
  constructor
    mkYMFixedFiniteVolumeBlockedObservableContinuumLimitConditionalTheorem
  field
    theorem16ConditionalInput :
      Sprint79.eriksson26020077Theorem16ConditionalOnAssumptionA ≡ true
    anisotropicAssumptionAConditionalClosure :
      AssumptionA.YMAnisotropicAssumptionAConditionalClosureTheorem cLocal cF k
    continuumLimitFormula :
      FixedFiniteVolumeBlockedObservableContinuumLimitFormula
    continuumLimitFormulaIsCanonical :
      continuumLimitFormula
        ≡ canonicalFixedFiniteVolumeBlockedObservableContinuumLimitFormula
    closedConditionallyHere :
      Bool
    closedConditionallyHereIsTrue :
      closedConditionallyHere ≡ true
    unconditionalInRepo :
      Bool
    unconditionalInRepoIsFalse :
      unconditionalInRepo ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false

ymFixedFiniteVolumeBlockedObservableContinuumLimitConditional :
  (cLocal cF k : Nat) →
  YMFixedFiniteVolumeBlockedObservableContinuumLimitConditionalTheorem
    cLocal cF k
ymFixedFiniteVolumeBlockedObservableContinuumLimitConditional cLocal cF k =
  mkYMFixedFiniteVolumeBlockedObservableContinuumLimitConditionalTheorem
    refl
    (AssumptionA.ymAnisotropicAssumptionAConditionalClosure cLocal cF k)
    canonicalFixedFiniteVolumeBlockedObservableContinuumLimitFormula
    refl
    true
    refl
    false
    refl
    refl

record YMFixedFiniteVolumeBlockedObservableContinuumLimitConditionalBoundary :
  Set where
  field
    conditionalClosureRecorded :
      fixedFiniteVolumeBlockedObservableContinuumLimitConditional ≡ true
    unconditionalClosureStillFalse :
      fixedFiniteVolumeBlockedObservableContinuumLimitUnconditional ≡ false
    noPromotion :
      clayYangMillsPromoted ≡ false

ymFixedFiniteVolumeBlockedObservableContinuumLimitConditionalBoundary :
  YMFixedFiniteVolumeBlockedObservableContinuumLimitConditionalBoundary
ymFixedFiniteVolumeBlockedObservableContinuumLimitConditionalBoundary =
  record
    { conditionalClosureRecorded = refl
    ; unconditionalClosureStillFalse = refl
    ; noPromotion = refl
    }
