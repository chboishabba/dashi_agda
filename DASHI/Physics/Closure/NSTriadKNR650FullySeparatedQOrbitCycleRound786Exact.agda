{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650FullySeparatedQOrbitCycleRound786Exact where

------------------------------------------------------------------------
-- ROUND786 / THE THREE FULLY-SEPARATED PROFILES FORM AN EXACT q-ENERGY CYCLE
--
-- After correcting the old R38 q-energy action, the literal map has order six
-- and its third iterate is Fourier conjugation.  On the R782 fully-separated
-- support the profile action is sharper:
--
--   (LH,HH,HL) --qE--> (HL,HL,HH)
--   (HL,HL,HH) --qE--> (HH,LH,LH)
--   (HH,LH,LH) --qE--> (LH,HH,HL).
--
-- Thus the fully-separated mask is closed under qEnergyLeg.  This is the exact
-- finite transition graph sought after R781.  No global ccTouched invariance is
-- assumed, and no estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as R25
import DASHI.Physics.Closure.NSTriadKNPhysicalBonySwapEquivarianceRound129Exact as R129
import DASHI.Physics.Closure.NSTriadKNR650EnergyOrbitBonyProfileRound775Exact as R775
import DASHI.Physics.Closure.NSTriadKNR650HHOrbitProfileRound777Exact as R777
import DASHI.Physics.Closure.NSTriadKNR650LHOrbitProfileSplitRound779Exact as R779
import DASHI.Physics.Closure.NSTriadKNR650HLOrbitProfileSplitRound780Exact as R780
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNR650FullySeparatedOrbitProfileSupportRound782Exact as R782
import DASHI.Physics.Closure.NSTriadKNR650EnergyLegConjugationEquivarianceRound785Exact as R785

regimeCertificate :
  ∀ {beta regime} →
  Scale.classifyScale R25.literalShellPolicy beta ≡ regime →
  R25.TriadicClassCertificate beta (R25.classForRegime regime)
regimeCertificate {beta} {regime} equality =
  R25.triadic-class-certificate
    (cong R25.classForRegime equality)
    (subst
      (Scale.ScaleCondition R25.literalShellPolicy beta)
      equality
      (Scale.scaleClassificationSound R25.literalShellPolicy beta))

lowHighNotComparable : Scale.lowHigh ≡ Scale.comparable → ⊥
lowHighNotComparable ()

highLowNotComparable : Scale.highLow ≡ Scale.comparable → ⊥
highLowNotComparable ()

highHighNotComparable : Scale.highHigh ≡ Scale.comparable → ⊥
highHighNotComparable ()

qBaseFromProfile :
  (beta : Physical.PhysicalTriadIncidence) →
  Scale.classifyScale R25.literalShellPolicy (Orbit.qEnergyLeg beta)
  ≡ R775.qClass (R775.orbitProfile beta)
qBaseFromProfile beta = refl

qPClassFromBase :
  (beta : Physical.PhysicalTriadIncidence) →
  Scale.classifyScale R25.literalShellPolicy
    (Orbit.pEnergyLeg (Orbit.qEnergyLeg beta))
  ≡
  R129.swapRegime
    (Scale.classifyScale R25.literalShellPolicy beta)
qPClassFromBase beta
  rewrite R785.pAfterQIsSwap beta
        | R129.classifyScaleSwapEquivariant R25.literalShellPolicy beta =
  refl

lhShapeQStep :
  ∀ {beta} →
  R775.orbitProfile beta
    ≡ R775.orbit-profile
        Scale.lowHigh Scale.highHigh Scale.highLow →
  R775.orbitProfile (Orbit.qEnergyLeg beta)
    ≡ R775.orbit-profile
        Scale.highLow Scale.highLow Scale.highHigh
lhShapeQStep {beta} shape =
  decide (R780.hlInterior (Orbit.qEnergyLeg beta)) refl
  where
  qBaseHL :
    Scale.classifyScale R25.literalShellPolicy (Orbit.qEnergyLeg beta)
    ≡ Scale.highLow
  qBaseHL =
    trans
      (qBaseFromProfile beta)
      (cong R775.qClass shape)

  certificate :
    R25.TriadicClassCertificate (Orbit.qEnergyLeg beta) R25.HL
  certificate = regimeCertificate qBaseHL

  betaBaseLH :
    Scale.classifyScale R25.literalShellPolicy beta ≡ Scale.lowHigh
  betaBaseLH =
    trans
      (sym (R775.orbitProfileBase beta))
      (cong R775.baseClass shape)

  qPClassHL :
    Scale.classifyScale R25.literalShellPolicy
      (Orbit.pEnergyLeg (Orbit.qEnergyLeg beta))
    ≡ Scale.highLow
  qPClassHL =
    trans
      (qPClassFromBase beta)
      (cong R129.swapRegime betaBaseLH)

  decide :
    (value : Bool) →
    R780.hlInterior (Orbit.qEnergyLeg beta) ≡ value →
    R775.orbitProfile (Orbit.qEnergyLeg beta)
      ≡ R775.orbit-profile
          Scale.highLow Scale.highLow Scale.highHigh
  decide true interior =
    R780.hlInteriorOrbitProfile certificate interior
  decide false boundary =
    ⊥-elim
      (highLowNotComparable
        (trans
          (sym qPClassHL)
          (cong R775.pClass
            (R780.hlBoundaryOrbitProfile certificate boundary))))

hlShapeQStep :
  ∀ {beta} →
  R775.orbitProfile beta
    ≡ R775.orbit-profile
        Scale.highLow Scale.highLow Scale.highHigh →
  R775.orbitProfile (Orbit.qEnergyLeg beta)
    ≡ R775.orbit-profile
        Scale.highHigh Scale.lowHigh Scale.lowHigh
hlShapeQStep {beta} shape =
  R777.hhOrbitProfileExact certificate
  where
  qBaseHH :
    Scale.classifyScale R25.literalShellPolicy (Orbit.qEnergyLeg beta)
    ≡ Scale.highHigh
  qBaseHH =
    trans
      (qBaseFromProfile beta)
      (cong R775.qClass shape)

  certificate :
    R25.TriadicClassCertificate (Orbit.qEnergyLeg beta) R25.HH
  certificate = regimeCertificate qBaseHH

hhShapeQStep :
  ∀ {beta} →
  R775.orbitProfile beta
    ≡ R775.orbit-profile
        Scale.highHigh Scale.lowHigh Scale.lowHigh →
  R775.orbitProfile (Orbit.qEnergyLeg beta)
    ≡ R775.orbit-profile
        Scale.lowHigh Scale.highHigh Scale.highLow
hhShapeQStep {beta} shape =
  decide (R779.lhInterior (Orbit.qEnergyLeg beta)) refl
  where
  qBaseLH :
    Scale.classifyScale R25.literalShellPolicy (Orbit.qEnergyLeg beta)
    ≡ Scale.lowHigh
  qBaseLH =
    trans
      (qBaseFromProfile beta)
      (cong R775.qClass shape)

  certificate :
    R25.TriadicClassCertificate (Orbit.qEnergyLeg beta) R25.LH
  certificate = regimeCertificate qBaseLH

  betaBaseHH :
    Scale.classifyScale R25.literalShellPolicy beta ≡ Scale.highHigh
  betaBaseHH =
    trans
      (sym (R775.orbitProfileBase beta))
      (cong R775.baseClass shape)

  qPClassHH :
    Scale.classifyScale R25.literalShellPolicy
      (Orbit.pEnergyLeg (Orbit.qEnergyLeg beta))
    ≡ Scale.highHigh
  qPClassHH =
    trans
      (qPClassFromBase beta)
      (cong R129.swapRegime betaBaseHH)

  decide :
    (value : Bool) →
    R779.lhInterior (Orbit.qEnergyLeg beta) ≡ value →
    R775.orbitProfile (Orbit.qEnergyLeg beta)
      ≡ R775.orbit-profile
          Scale.lowHigh Scale.highHigh Scale.highLow
  decide true interior =
    R779.lhInteriorOrbitProfile certificate interior
  decide false boundary =
    ⊥-elim
      (highHighNotComparable
        (trans
          (sym qPClassHH)
          (cong R775.pClass
            (R779.lhBoundaryOrbitProfile certificate boundary))))

fullySeparatedQStep :
  (beta : Physical.PhysicalTriadIncidence) →
  R781.ccTouched beta ≡ false →
  R781.ccTouched (Orbit.qEnergyLeg beta) ≡ false
fullySeparatedQStep beta separated
  with R782.fullySeparatedOrbitShape beta separated
... | R782.lhInteriorShape shape
  rewrite lhShapeQStep shape =
  refl
... | R782.hlInteriorShape shape
  rewrite hlShapeQStep shape =
  refl
... | R782.hhShape shape
  rewrite hhShapeQStep shape =
  refl

round786FullySeparatedProfilesFormThreeCycle : Bool
round786FullySeparatedProfilesFormThreeCycle = true

round786FullySeparatedClosedUnderQEnergyLeg : Bool
round786FullySeparatedClosedUnderQEnergyLeg = true

round786UsesCorrectedOrderSixQOrbit : Bool
round786UsesCorrectedOrderSixQOrbit = true

round786IntroducesEstimate : Bool
round786IntroducesEstimate = false

round786W2Closed : Bool
round786W2Closed = false

round786ClayPromotion : Bool
round786ClayPromotion = false

round786FullySeparatedProfilesFormThreeCycleIsTrue :
  round786FullySeparatedProfilesFormThreeCycle ≡ true
round786FullySeparatedProfilesFormThreeCycleIsTrue = refl

round786FullySeparatedClosedUnderQEnergyLegIsTrue :
  round786FullySeparatedClosedUnderQEnergyLeg ≡ true
round786FullySeparatedClosedUnderQEnergyLegIsTrue = refl

round786UsesCorrectedOrderSixQOrbitIsTrue :
  round786UsesCorrectedOrderSixQOrbit ≡ true
round786UsesCorrectedOrderSixQOrbitIsTrue = refl

round786IntroducesEstimateIsFalse :
  round786IntroducesEstimate ≡ false
round786IntroducesEstimateIsFalse = refl

round786W2ClosedIsFalse :
  round786W2Closed ≡ false
round786W2ClosedIsFalse = refl

round786ClayPromotionIsFalse :
  round786ClayPromotion ≡ false
round786ClayPromotionIsFalse = refl
