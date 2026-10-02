{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650HHOrbitProfileRound777Exact where

------------------------------------------------------------------------
-- ROUND777 / HH ENERGY-ORBIT PROFILE IS EXACTLY (HH,LH,LH)
--
-- The literal shell index is invariant under Fourier-mode negation because
-- infinityNorm is max(|kx|,|ky|,|kz|).  An R25 HH certificate supplies
--
--   shell(k)+3 < shell(p),   shell(k)+3 < shell(q)
--
-- in the executable natLess form.  Under pEnergyLeg/qEnergyLeg the first input
-- is old k and the second input is respectively -q/-p, so those same strict
-- tests become LOW-HIGH tests after the shell-negation rewrite.
--
-- Hence
--
--   Pi(beta) = (HH,LH,LH)
--
-- for every literal R25 HH triad.  This is exact class transport, not an
-- analytic estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Properties as Int
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSPeriodicNearTriadClassification as Near
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as R25
import DASHI.Physics.Closure.NSTriadKNPhysicalBonySwapEquivarianceRound129Exact as R129
import DASHI.Physics.Closure.NSTriadKNR650EnergyOrbitBonyProfileRound775Exact as R775

infinityNormNegate :
  (mode : Z3.FourierMode) →
  Infinity.infinityNorm (Z3.negateMode mode)
  ≡ Infinity.infinityNorm mode
infinityNormNegate (Z3.mode x y z)
  rewrite Int.∣-i∣≡∣i∣ x
        | Int.∣-i∣≡∣i∣ y
        | Int.∣-i∣≡∣i∣ z =
  refl

literalShellIndexNegate :
  (mode : Z3.FourierMode) →
  Shell.shellIndex (Z3.negateMode mode)
  ≡ Shell.shellIndex mode
literalShellIndexNegate mode =
  cong Shell.shellIndexMagnitude (infinityNormNegate mode)

hhBaseRegime :
  ∀ {beta} →
  R25.TriadicClassCertificate beta R25.HH →
  Scale.classifyScale R25.literalShellPolicy beta ≡ Scale.highHigh
hhBaseRegime certificate =
  R129.scaleConditionForcesComputedRegime
    (R25.classMeaning certificate)

hhPEnergyLegIsLowHigh :
  ∀ {beta} →
  R25.TriadicClassCertificate beta R25.HH →
  Scale.classifyScale R25.literalShellPolicy (Orbit.pEnergyLeg beta)
  ≡ Scale.lowHigh
hhPEnergyLegIsLowHigh {beta} certificate
  with R25.classMeaning certificate
... | Scale.highHighCondition notLH notHL outputBelowP outputBelowQ =
  R129.scaleConditionForcesComputedRegime
    (Scale.lowHighCondition transformed)
  where
  transformed :
    Near.natLess
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.p (Orbit.pEnergyLeg beta))
        + Scale.overlapRadius R25.literalShellPolicy)
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.q (Orbit.pEnergyLeg beta)))
    ≡ true
  transformed
    rewrite Orbit.pEnergyLegFirstInput beta
          | Orbit.pEnergyLegSecondInput beta
          | literalShellIndexNegate (Physical.q beta) =
    outputBelowQ

hhQEnergyLegIsLowHigh :
  ∀ {beta} →
  R25.TriadicClassCertificate beta R25.HH →
  Scale.classifyScale R25.literalShellPolicy (Orbit.qEnergyLeg beta)
  ≡ Scale.lowHigh
hhQEnergyLegIsLowHigh {beta} certificate
  with R25.classMeaning certificate
... | Scale.highHighCondition notLH notHL outputBelowP outputBelowQ =
  R129.scaleConditionForcesComputedRegime
    (Scale.lowHighCondition transformed)
  where
  transformed :
    Near.natLess
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.p (Orbit.qEnergyLeg beta))
        + Scale.overlapRadius R25.literalShellPolicy)
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.q (Orbit.qEnergyLeg beta)))
    ≡ true
  transformed
    rewrite Orbit.qEnergyLegFirstInput beta
          | Orbit.qEnergyLegSecondInput beta
          | literalShellIndexNegate (Physical.p beta) =
    outputBelowP

hhOrbitProfileExact :
  ∀ {beta} →
  R25.TriadicClassCertificate beta R25.HH →
  R775.orbitProfile beta
  ≡ R775.orbit-profile
      Scale.highHigh
      Scale.lowHigh
      Scale.lowHigh
hhOrbitProfileExact {beta} certificate
  rewrite hhBaseRegime certificate
        | hhPEnergyLegIsLowHigh certificate
        | hhQEnergyLegIsLowHigh certificate =
  refl

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round777LiteralShellIndexNegationInvariant : Bool
round777LiteralShellIndexNegationInvariant = true

round777HHPEnergyLegIsLowHigh : Bool
round777HHPEnergyLegIsLowHigh = true

round777HHQEnergyLegIsLowHigh : Bool
round777HHQEnergyLegIsLowHigh = true

round777HHOrbitProfileIsHHLHLH : Bool
round777HHOrbitProfileIsHHLHLH = true

round777IntroducesEstimate : Bool
round777IntroducesEstimate = false

round777W2Closed : Bool
round777W2Closed = false

round777ClayPromotion : Bool
round777ClayPromotion = false

round777LiteralShellIndexNegationInvariantIsTrue :
  round777LiteralShellIndexNegationInvariant ≡ true
round777LiteralShellIndexNegationInvariantIsTrue = refl

round777HHOrbitProfileIsHHLHLHIsTrue :
  round777HHOrbitProfileIsHHLHLH ≡ true
round777HHOrbitProfileIsHHLHLHIsTrue = refl

round777IntroducesEstimateIsFalse :
  round777IntroducesEstimate ≡ false
round777IntroducesEstimateIsFalse = refl

round777W2ClosedIsFalse :
  round777W2Closed ≡ false
round777W2ClosedIsFalse = refl

round777ClayPromotionIsFalse :
  round777ClayPromotion ≡ false
round777ClayPromotionIsFalse = refl
