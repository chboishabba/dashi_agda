module DASHI.Physics.Closure.NSTriadKNDualResourceScaleLedgerRound35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Keep the Round-32 analytic resource ledger and dyadic scale accounting as
-- two independent coordinates.  A resource estimate is not absorbable merely
-- because its eta/data bookkeeping is admissible: the shell and viscosity
-- homogeneities must also match the target.
--
-- Signed shell exponents are represented without integer subtraction by a
-- pair (growth,decay).  Two valuations have the same net shell degree exactly
-- when
--
--   growth_left + decay_right = growth_right + decay_left.
--
-- The Round-33/34 HH-bad obstruction is then a type-level arithmetic fact:
--
--   raw ratio lambda^(+1)
--     * critical dissipation (nu lambda^(-1))
--       has the same scale as nu,
--
-- while
--
--   raw ratio lambda^(+1)
--     * a scale-free nu gain
--
-- cannot have the target scale.  Thus the missing inverse shell power is a
-- fail-closed ledger mismatch, independent of the analytic resource grammar.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSTriadKNResourceLatticeRound32Exact as Resource

record ScaleValuation : Set where
  constructor scale-valuation
  field
    shellGrowth : Nat
    shellDecay : Nat
    viscosityDegree : Nat

open ScaleValuation public

_⊗s_ : ScaleValuation → ScaleValuation → ScaleValuation
left ⊗s right = scale-valuation
  (shellGrowth left + shellGrowth right)
  (shellDecay left + shellDecay right)
  (viscosityDegree left + viscosityDegree right)

infixr 6 _⊗s_

SameScale : ScaleValuation → ScaleValuation → Set
SameScale left right =
  (shellGrowth left + shellDecay right
    ≡ shellGrowth right + shellDecay left)
  × (viscosityDegree left ≡ viscosityDegree right)

rawHHBadRatioScale : ScaleValuation
rawHHBadRatioScale = scale-valuation 1 0 0

criticalLocalizedDissipationScale : ScaleValuation
criticalLocalizedDissipationScale = scale-valuation 0 1 1

scaleFreeViscousGainScale : ScaleValuation
scaleFreeViscousGainScale = scale-valuation 0 0 1

absorbedViscosityScale : ScaleValuation
absorbedViscosityScale = scale-valuation 0 0 1

criticalInverseScaleBalancesRawHHBad :
  SameScale
    (rawHHBadRatioScale ⊗s criticalLocalizedDissipationScale)
    absorbedViscosityScale
criticalInverseScaleBalancesRawHHBad = refl , refl

scaleFreeGainCannotBalanceRawHHBad :
  SameScale
    (rawHHBadRatioScale ⊗s scaleFreeViscousGainScale)
    absorbedViscosityScale → ⊥
scaleFreeGainCannotBalanceRawHHBad (() , viscosityMatch)

record DualOwnerValuation : Set where
  constructor dual-owner-valuation
  field
    analytic : Resource.ResourceVector
    scale : ScaleValuation

open DualOwnerValuation public

record FailClosedAbsorption
    (source target : DualOwnerValuation) : Set where
  field
    noForbiddenSource :
      Resource.forbiddenCoordinate (analytic source) ≡ 0
    scaleMatches : SameScale (scale source) (scale target)

open FailClosedAbsorption public

hhBadCriticalScaleAbsorptionWitness :
  (analyticSource analyticTarget : Resource.ResourceVector) →
  Resource.forbiddenCoordinate analyticSource ≡ 0 →
  FailClosedAbsorption
    (dual-owner-valuation analyticSource
      (rawHHBadRatioScale ⊗s criticalLocalizedDissipationScale))
    (dual-owner-valuation analyticTarget absorbedViscosityScale)
hhBadCriticalScaleAbsorptionWitness analyticSource analyticTarget sourceClean = record
  { noForbiddenSource = sourceClean
  ; scaleMatches = criticalInverseScaleBalancesRawHHBad
  }

hhBadScaleFreeAbsorptionImpossible :
  (analyticSource analyticTarget : Resource.ResourceVector) →
  FailClosedAbsorption
    (dual-owner-valuation analyticSource
      (rawHHBadRatioScale ⊗s scaleFreeViscousGainScale))
    (dual-owner-valuation analyticTarget absorbedViscosityScale)
  → ⊥
hhBadScaleFreeAbsorptionImpossible analyticSource analyticTarget absorption =
  scaleFreeGainCannotBalanceRawHHBad (scaleMatches absorption)

dualResourceScaleLedgerClosed : Bool
dualResourceScaleLedgerClosed = true

hhBadMissingInverseScaleFailsClosed : Bool
hhBadMissingInverseScaleFailsClosed = true

dualResourceScaleLedgerClosedIsTrue :
  dualResourceScaleLedgerClosed ≡ true
dualResourceScaleLedgerClosedIsTrue = refl

hhBadMissingInverseScaleFailsClosedIsTrue :
  hhBadMissingInverseScaleFailsClosed ≡ true
hhBadMissingInverseScaleFailsClosedIsTrue = refl
