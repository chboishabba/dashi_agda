module DASHI.Moonshine.JInvariantEisensteinCoefficientTowerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_; -_) renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)

import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Divisor
import DASHI.Moonshine.JInvariantEisensteinDivisorPowerSourceAtlasExact as SourceAtlas
import DASHI.Physics.Closure.TriadicSectorQSeries as QS

------------------------------------------------------------------------
-- EXACT FINITE E4/E6 COEFFICIENT TOWER
------------------------------------------------------------------------

integerQSeriesCarrier : QS.QSeriesCarrier
integerQSeriesCarrier = record
  { QS.Coeff = ℤ
  ; QS.zeroᶜ = + 0
  ; QS.oneᶜ = + 1
  ; QS._+ᶜ_ = _+ℤ_
  ; QS._*ᶜ_ = _*ℤ_
  }

e4Coefficient : Nat -> ℤ
e4Coefficient zero = + 1
e4Coefficient (suc n) = + (240 * Divisor.sigma3 (suc n))

e6Coefficient : Nat -> ℤ
e6Coefficient zero = + 1
e6Coefficient (suc n) = - (+ (504 * Divisor.sigma5 (suc n)))

data EisensteinCoefficientSector : Set where
  e4Sector : EisensteinCoefficientSector
  e6Sector : EisensteinCoefficientSector

coefficientAt : Nat -> EisensteinCoefficientSector -> ℤ
coefficientAt n e4Sector = e4Coefficient n
coefficientAt n e6Sector = e6Coefficient n

eisensteinCoefficientTower : QS.SectorTraceTower integerQSeriesCarrier
eisensteinCoefficientTower = record
  { QS.Sector = EisensteinCoefficientSector
  ; QS.traceCoefficient = coefficientAt
  }

e4Prefix : (n : Nat) -> QS.Vec ℤ n
e4Prefix n =
  QS.qSeriesPrefix integerQSeriesCarrier eisensteinCoefficientTower e4Sector n

e6Prefix : (n : Nat) -> QS.Vec ℤ n
e6Prefix n =
  QS.qSeriesPrefix integerQSeriesCarrier eisensteinCoefficientTower e6Sector n

------------------------------------------------------------------------
-- Retain source/parity provenance without letting it define the tower.
------------------------------------------------------------------------

sourceAtlasNonPromoting :
  SourceAtlas.citationsCreateAuthority
    SourceAtlas.canonicalEisensteinDivisorPowerAttributionBoundary
  ≡ false
sourceAtlasNonPromoting = refl

record EisensteinCoefficientTowerBoundary : Set where
  constructor eisenstein-coefficient-tower-boundary
  field
    existingQSeriesPrefixCarrierReused : Bool
    internalSigma3Used : Bool
    internalSigma5Used : Bool
    normalizedE4CoefficientsExecutable : Bool
    normalizedE6CoefficientsExecutable : Bool
    oeisParityCoordinatesRetained : Bool
    finiteCoefficientTowerEqualsAnalyticEisenstein : Bool
    finitePrefixCreatesConvergence : Bool
    finitePrefixCreatesModularity : Bool
    reading : String
open EisensteinCoefficientTowerBoundary public

canonicalEisensteinCoefficientTowerBoundary : EisensteinCoefficientTowerBoundary
canonicalEisensteinCoefficientTowerBoundary =
  eisenstein-coefficient-tower-boundary
    true true true true true true
    false false false
    "the exact finite integer E4/E6 coefficient sequences now inhabit the repository's existing q-series prefix tower; A004009/A013973 are parity coordinates only, while equality with the analytic Eisenstein lattice sum and convergence remain unpaid"
