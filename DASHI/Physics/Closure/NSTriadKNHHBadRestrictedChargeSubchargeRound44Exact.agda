module DASHI.Physics.Closure.NSTriadKNHHBadRestrictedChargeSubchargeRound44Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 43's direct HH-bad owner still accepted
--
--   restricted bad viscous charge <= physical dissipation
--
-- as a field.  The bad charge is a Bool restriction of ordinary shell energy,
-- so most of that field is unnecessary.  This file proves on the literal same
-- finite samples that masking can only decrease viscous charge:
--
--   sum chi_bad E_i * nu * lambda_q^2
--     <= sum E_i * nu * lambda_q^2.
--
-- Consequently the direct owner only needs a domination theorem for the
-- corresponding *unmasked* shell charge.  This is a strictly more physical and
-- easier final seam: no independent bad-set allocation remains on the
-- dissipation side.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as LuoBridge
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedDissipationRound38Exact as Bad
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadDirectOwnerRound43Exact as Direct

maskedEnergyBelowShellEnergy :
  ∀ sample → Bad.maskedEnergy sample ≤ Bad.shellEnergy sample
maskedEnergyBelowShellEnergy sample with Bad.isBad sample
... | true = ℚP.≤-refl
... | false = Bad.shellEnergyNonnegative sample

shellViscousFactor : ℚ → Nat → ℚ
shellViscousFactor effectiveViscosity shell =
  effectiveViscosity
  * (Sharp.dyadicScale shell * Sharp.dyadicScale shell)

shellViscousFactorNonnegative :
  ∀ effectiveViscosity shell →
  0ℚ ≤ effectiveViscosity →
  0ℚ ≤ shellViscousFactor effectiveViscosity shell
shellViscousFactorNonnegative effectiveViscosity shell viscosityNN =
  let
    scaleNN = LuoBridge.dyadicScaleNonnegative shell
    scaleSquareNN :
      0ℚ ≤ Sharp.dyadicScale shell * Sharp.dyadicScale shell
    scaleSquareNN =
      let instance
        leftNN = nonNegative scaleNN
        rightNN = nonNegative scaleNN
        squareNN =
          ℚP.nonNeg*nonNeg⇒nonNeg
            (Sharp.dyadicScale shell) (Sharp.dyadicScale shell)
      in
      ℚP.nonNegative⁻¹
        (Sharp.dyadicScale shell * Sharp.dyadicScale shell)
  in
  let instance
    viscosityNNI = nonNegative viscosityNN
    squareNNI = nonNegative scaleSquareNN
    factorNN =
      ℚP.nonNeg*nonNeg⇒nonNeg
        effectiveViscosity
        (Sharp.dyadicScale shell * Sharp.dyadicScale shell)
  in
  ℚP.nonNegative⁻¹ (shellViscousFactor effectiveViscosity shell)

unmaskedViscousCharge :
  ℚ → Nat → Bad.BadTaggedEnergySample → ℚ
unmaskedViscousCharge effectiveViscosity shell sample =
  Bad.shellEnergy sample * effectiveViscosity
    * (Sharp.dyadicScale shell * Sharp.dyadicScale shell)

maskedViscousChargeBelowUnmasked :
  ∀ effectiveViscosity shell sample →
  0ℚ ≤ effectiveViscosity →
  Bad.maskedViscousCharge effectiveViscosity shell sample
  ≤ unmaskedViscousCharge effectiveViscosity shell sample
maskedViscousChargeBelowUnmasked effectiveViscosity shell sample viscosityNN =
  let
    factor = shellViscousFactor effectiveViscosity shell
    factorNN = shellViscousFactorNonnegative effectiveViscosity shell viscosityNN
    scaled :
      Bad.maskedEnergy sample * factor
      ≤ Bad.shellEnergy sample * factor
    scaled =
      let instance factorNNI = nonNegative factorNN
      in ℚP.*-monoʳ-≤-nonNeg factor (maskedEnergyBelowShellEnergy sample)

    leftMeaning :
      Bad.maskedViscousCharge effectiveViscosity shell sample
      ≡ Bad.maskedEnergy sample * factor
    leftMeaning = solve
      ( Bad.maskedEnergy sample
      ∷ effectiveViscosity
      ∷ Sharp.dyadicScale shell
      ∷ [])

    rightMeaning :
      unmaskedViscousCharge effectiveViscosity shell sample
      ≡ Bad.shellEnergy sample * factor
    rightMeaning = solve
      ( Bad.shellEnergy sample
      ∷ effectiveViscosity
      ∷ Sharp.dyadicScale shell
      ∷ [])
  in
  subst
    (λ lower → lower ≤ unmaskedViscousCharge effectiveViscosity shell sample)
    (sym leftMeaning)
    (subst
      (λ upper → Bad.maskedEnergy sample * factor ≤ upper)
      (sym rightMeaning)
      scaled)

sumCellUnmaskedViscousCharge :
  ∀ {density} →
  (effectiveViscosity : ℚ) →
  (shell : Nat) →
  List (Gain.RestrictedGainDensityCell effectiveViscosity density shell) → ℚ
sumCellUnmaskedViscousCharge effectiveViscosity shell [] = 0ℚ
sumCellUnmaskedViscousCharge effectiveViscosity shell (cell ∷ rest) =
  unmaskedViscousCharge effectiveViscosity shell
    (Gain.energySample (Gain.sample cell))
  + sumCellUnmaskedViscousCharge effectiveViscosity shell rest

restrictedCellChargeBelowUnmaskedCellCharge :
  ∀ {effectiveViscosity density shell}
    (cells : List
      (Gain.RestrictedGainDensityCell effectiveViscosity density shell)) →
  0ℚ ≤ effectiveViscosity →
  Gain.sumCellViscousCharge cells
  ≤ sumCellUnmaskedViscousCharge effectiveViscosity shell cells
restrictedCellChargeBelowUnmaskedCellCharge [] viscosityNN = ℚP.≤-refl
restrictedCellChargeBelowUnmaskedCellCharge
    {effectiveViscosity} {density} {shell}
    (cell ∷ rest) viscosityNN =
  ℚP.+-mono-≤
    (maskedViscousChargeBelowUnmasked
      effectiveViscosity shell
      (Gain.energySample (Gain.sample cell))
      viscosityNN)
    (restrictedCellChargeBelowUnmaskedCellCharge rest viscosityNN)

record HHBadFullChargeDominationInput
    (environment : Owner.TaxEnvironment)
    (effectiveViscosity eta : ℚ)
    (shell : Nat) : Set where
  field
    etaNonnegative : 0ℚ ≤ eta
    viscosityNonnegative : 0ℚ ≤ effectiveViscosity

    densityCertificate :
      Gain.InverseShellRestrictedGainDensity effectiveViscosity shell

    inverseShellTargetMeaning :
      Gain.inverseShellTarget densityCertificate
      ≡ Sharp.requiredHHBadGain eta shell

    unmaskedChargeBelowPhysicalDissipation :
      sumCellUnmaskedViscousCharge
        effectiveViscosity shell (Gain.cells densityCertificate)
      ≤ Owner.dissipation environment

open HHBadFullChargeDominationInput public

restrictedChargeBelowPhysicalDissipation :
  ∀ {environment effectiveViscosity eta shell}
    (input : HHBadFullChargeDominationInput
      environment effectiveViscosity eta shell) →
  Gain.sumCellViscousCharge (Gain.cells (densityCertificate input))
  ≤ Owner.dissipation environment
restrictedChargeBelowPhysicalDissipation
    {effectiveViscosity = effectiveViscosity} input =
  ℚP.≤-trans
    (restrictedCellChargeBelowUnmaskedCellCharge
      (Gain.cells (densityCertificate input))
      (viscosityNonnegative input))
    (unmaskedChargeBelowPhysicalDissipation input)

asDirectHHBadOwnerInput :
  ∀ {environment effectiveViscosity eta shell} →
  HHBadFullChargeDominationInput environment effectiveViscosity eta shell →
  Direct.DirectHHBadOwnerInput environment effectiveViscosity eta shell
asDirectHHBadOwnerInput input = record
  { etaNonnegative = etaNonnegative input
  ; densityCertificate = densityCertificate input
  ; inverseShellTargetMeaning = inverseShellTargetMeaning input
  ; restrictedChargeBelowPhysicalDissipation =
      restrictedChargeBelowPhysicalDissipation input
  }

physicalHHBadOwnerEstimateFromUnmaskedCharge :
  ∀ {environment effectiveViscosity eta shell} →
  HHBadFullChargeDominationInput environment effectiveViscosity eta shell →
  Owner.AdmissibleOwnerEstimate environment
physicalHHBadOwnerEstimateFromUnmaskedCharge input =
  Direct.physicalHHBadOwnerEstimate (asDirectHHBadOwnerInput input)

hhBadRestrictedChargeIsLiteralSubcharge : Bool
hhBadRestrictedChargeIsLiteralSubcharge = true

hhBadRestrictedChargeIsLiteralSubchargeIsTrue :
  hhBadRestrictedChargeIsLiteralSubcharge ≡ true
hhBadRestrictedChargeIsLiteralSubchargeIsTrue = refl
