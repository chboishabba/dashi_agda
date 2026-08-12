module DASHI.Physics.Closure.NSTriadKNHHBadLiteralProductionDissipationScalingRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- DOI: 10.1007/BF01240221.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- The preceding Round-42 same-object audit proves that the literal Fourier
-- vorticity interaction and its fixed-output enstrophy-production scalar are
-- order zero under a common frequency rescaling with vorticity amplitudes
-- fixed.
--
-- This file compares that production directly with the literal viscous
-- enstrophy charge
--
--   D_k = nu |k|^2 |omega_k|^2.
--
-- Under k -> r k, omega fixed,
--
--   D_(r k) = r^2 D_k,
--
-- whereas the nonlinear production is unchanged.  Consequently the exact
-- coefficient transporting a base-scale production/dissipation inequality to
-- the scaled modes is r^-2, not r^-1:
--
--   P <= C D
--     ==>
--   P_r <= C r^-2 D_r.
--
-- This does NOT by itself prove the physical HH-bad owner estimate: the base
-- coefficient C still contains the amplitude/geometric information and the
-- actual Round-39 `rawGain` has not yet been identified with this literal
-- production.  It does prove a sharper scale diagnostic.  The `2 lambda_q`
-- obstruction of the half-kernel/Bernstein lane has lost one inverse power
-- relative to the literal per-mode production-versus-viscous-charge scaling.
-- The highest-alpha next theorem is therefore to locate that lost power in the
-- exact same-object passage to the shell/bad-gain quantity, rather than assume
-- it is intrinsic to the vorticity equation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicBiotSavartMultiplierExact as Biot
import DASHI.Physics.Closure.NSTriadKNHHBadLiteralVorticityInteractionScalingRound42Exact as Literal

viscousEnstrophyCharge : ℚ → Biot.NonzeroVorticityMode → ℚ
viscousEnstrophyCharge viscosity mode =
  viscosity
  * Gram.normSquared (Biot.wavevector mode)
  * Gram.normSquared (Biot.vorticity mode)

scaledViscousEnstrophyCharge :
  ∀ viscosity scale mode →
  viscousEnstrophyCharge viscosity
      (Literal.scaledNonzeroVorticityMode scale mode)
  ≡
  Threshold.threshold scale * Threshold.threshold scale
    * viscousEnstrophyCharge viscosity mode
scaledViscousEnstrophyCharge viscosity scale mode =
  let
    r = Threshold.threshold scale
    k = Biot.wavevector mode
    omega = Biot.vorticity mode

    expose :
      viscousEnstrophyCharge viscosity
          (Literal.scaledNonzeroVorticityMode scale mode)
      ≡
      viscosity * Gram.normSquared (Literal.scaleVec r k)
        * Gram.normSquared omega
    expose =
      cong₂
        (λ wave vort → viscosity * Gram.normSquared wave * Gram.normSquared vort)
        (Literal.scaledWavevector scale mode)
        (Literal.scaledVorticity scale mode)

    scaleNorm :
      viscosity * Gram.normSquared (Literal.scaleVec r k)
        * Gram.normSquared omega
      ≡
      viscosity * (r * r * Gram.normSquared k)
        * Gram.normSquared omega
    scaleNorm =
      cong
        (λ norm → viscosity * norm * Gram.normSquared omega)
        (Literal.normSquaredScale r k)

    regroup :
      viscosity * (r * r * Gram.normSquared k)
        * Gram.normSquared omega
      ≡
      r * r
        * (viscosity * Gram.normSquared k * Gram.normSquared omega)
    regroup = solve
      ( viscosity ∷ r
      ∷ Gram.normSquared k
      ∷ Gram.normSquared omega
      ∷ [])
  in
  trans expose (trans scaleNorm regroup)

inverseSquareScaledChargeExact :
  ∀ viscosity scale mode →
  (Threshold.thresholdInverse scale * Threshold.thresholdInverse scale)
    * viscousEnstrophyCharge viscosity
        (Literal.scaledNonzeroVorticityMode scale mode)
  ≡ viscousEnstrophyCharge viscosity mode
inverseSquareScaledChargeExact viscosity scale mode =
  let
    r = Threshold.threshold scale
    rinv = Threshold.thresholdInverse scale
    base = viscousEnstrophyCharge viscosity mode
    scaledMeaning = scaledViscousEnstrophyCharge viscosity scale mode

    expose :
      (rinv * rinv)
        * viscousEnstrophyCharge viscosity
            (Literal.scaledNonzeroVorticityMode scale mode)
      ≡ (rinv * rinv) * (r * r * base)
    expose = cong ((rinv * rinv) *_) scaledMeaning

    regroup :
      (rinv * rinv) * (r * r * base)
      ≡ (rinv * r) * (rinv * r) * base
    regroup = solve (rinv ∷ r ∷ base ∷ [])

    cancel :
      (rinv * r) * (rinv * r) * base ≡ base
    cancel rewrite Threshold.inverseMeaning scale = solve (base ∷ [])
  in
  trans expose (trans regroup cancel)

orderedProductionAllModesScaleInvariant :
  ∀ scale output left right →
  Literal.orderedEnstrophyProduction
    (Biot.vorticity (Literal.scaledNonzeroVorticityMode scale output))
    (Literal.scaledNonzeroVorticityMode scale left)
    (Literal.scaledNonzeroVorticityMode scale right)
  ≡ Literal.orderedEnstrophyProduction
      (Biot.vorticity output) left right
orderedProductionAllModesScaleInvariant scale output left right =
  trans
    (cong
      (λ outputVorticity →
        Literal.orderedEnstrophyProduction outputVorticity
          (Literal.scaledNonzeroVorticityMode scale left)
          (Literal.scaledNonzeroVorticityMode scale right))
      (Literal.scaledVorticity scale output))
    (Literal.orderedEnstrophyProductionScaleInvariant
      (Biot.vorticity output) scale left right)

symmetrizedProductionAllModesScaleInvariant :
  ∀ scale output left right →
  Literal.symmetrizedEnstrophyProduction
    (Biot.vorticity (Literal.scaledNonzeroVorticityMode scale output))
    (Literal.scaledNonzeroVorticityMode scale left)
    (Literal.scaledNonzeroVorticityMode scale right)
  ≡ Literal.symmetrizedEnstrophyProduction
      (Biot.vorticity output) left right
symmetrizedProductionAllModesScaleInvariant scale output left right =
  trans
    (cong
      (λ outputVorticity →
        Literal.symmetrizedEnstrophyProduction outputVorticity
          (Literal.scaledNonzeroVorticityMode scale left)
          (Literal.scaledNonzeroVorticityMode scale right))
      (Literal.scaledVorticity scale output))
    (Literal.symmetrizedEnstrophyProductionScaleInvariant
      (Biot.vorticity output) scale left right)

orderedBaseBoundTransfersWithInverseSquare :
  ∀ viscosity scale output left right coefficient →
  Literal.orderedEnstrophyProduction (Biot.vorticity output) left right
  ≤ coefficient * viscousEnstrophyCharge viscosity output →
  Literal.orderedEnstrophyProduction
      (Biot.vorticity (Literal.scaledNonzeroVorticityMode scale output))
      (Literal.scaledNonzeroVorticityMode scale left)
      (Literal.scaledNonzeroVorticityMode scale right)
  ≤
  coefficient
    * (Threshold.thresholdInverse scale * Threshold.thresholdInverse scale)
    * viscousEnstrophyCharge viscosity
        (Literal.scaledNonzeroVorticityMode scale output)
orderedBaseBoundTransfersWithInverseSquare
    viscosity scale output left right coefficient baseBound =
  let
    productionMeaning =
      orderedProductionAllModesScaleInvariant scale output left right

    chargeCollapse = inverseSquareScaledChargeExact viscosity scale output

    rightMeaning :
      coefficient
        * (Threshold.thresholdInverse scale * Threshold.thresholdInverse scale)
        * viscousEnstrophyCharge viscosity
            (Literal.scaledNonzeroVorticityMode scale output)
      ≡ coefficient * viscousEnstrophyCharge viscosity output
    rightMeaning =
      trans
        (solve
          ( coefficient
          ∷ Threshold.thresholdInverse scale
          ∷ viscousEnstrophyCharge viscosity
              (Literal.scaledNonzeroVorticityMode scale output)
          ∷ []))
        (cong (coefficient *_)
          (inverseSquareScaledChargeExact viscosity scale output))
  in
  subst
    (λ lower →
      lower
      ≤ coefficient
        * (Threshold.thresholdInverse scale * Threshold.thresholdInverse scale)
        * viscousEnstrophyCharge viscosity
            (Literal.scaledNonzeroVorticityMode scale output))
    (sym productionMeaning)
    (subst
      (λ upper →
        Literal.orderedEnstrophyProduction (Biot.vorticity output) left right
        ≤ upper)
      (sym rightMeaning)
      baseBound)

literalProductionToViscousChargeInverseSquareScalingClosed : Bool
literalProductionToViscousChargeInverseSquareScalingClosed = true

halfKernelBernsteinLaneLosesOneInverseScaleRelativeToLiteralProduction : Bool
halfKernelBernsteinLaneLosesOneInverseScaleRelativeToLiteralProduction = true

physicalRawBadGainSameObjectTraceStillRequired : Bool
physicalRawBadGainSameObjectTraceStillRequired = true

literalProductionToViscousChargeInverseSquareScalingClosedIsTrue :
  literalProductionToViscousChargeInverseSquareScalingClosed ≡ true
literalProductionToViscousChargeInverseSquareScalingClosedIsTrue = refl
