{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650HLOrbitProfileSplitRound780Exact where

------------------------------------------------------------------------
-- ROUND780 / HL PROFILE SPLIT IS THE EXACT SWAP MIRROR OF R779
--
-- R129 transports an HL scale condition across swapTriad to LH.
-- R775 gives
--
--   Pi(swap beta) = swapProfile(Pi(beta)),
--
-- and swapProfile is involutive.  Therefore R779 transports without
-- duplicating shell arithmetic:
--
--   HL interior  -> (HL,HL,HH)
--   HL boundary  -> (HL,CC,CC).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as R25
import DASHI.Physics.Closure.NSTriadKNPhysicalBonySwapEquivarianceRound129Exact as R129
import DASHI.Physics.Closure.NSTriadKNR650EnergyOrbitBonyProfileRound775Exact as R775
import DASHI.Physics.Closure.NSTriadKNR650LHOrbitProfileSplitRound779Exact as R779

hlInterior :
  Physical.PhysicalTriadIncidence → Bool
hlInterior beta =
  R779.lhInterior (Symmetry.swapTriad beta)

hlSwapCertificate :
  ∀ {beta} →
  R25.TriadicClassCertificate beta R25.HL →
  R25.TriadicClassCertificate (Symmetry.swapTriad beta) R25.LH
hlSwapCertificate {beta} certificate =
  R25.triadic-class-certificate computed meaning
  where
  betaRegime :
    Scale.classifyScale R25.literalShellPolicy beta ≡ Scale.highLow
  betaRegime =
    R129.scaleConditionForcesComputedRegime
      (R25.classMeaning certificate)

  swapRegime :
    Scale.classifyScale R25.literalShellPolicy (Symmetry.swapTriad beta)
    ≡ Scale.lowHigh
  swapRegime =
    trans
      (R129.classifyScaleSwapEquivariant R25.literalShellPolicy beta)
      (cong R129.swapRegime betaRegime)

  computed :
    R25.triadicSourceClass (Symmetry.swapTriad beta) ≡ R25.LH
  computed =
    cong R25.classForRegime swapRegime

  meaning :
    R25.TriadicClassMeaning (Symmetry.swapTriad beta) R25.LH
  meaning =
    R129.swapScaleCondition (R25.classMeaning certificate)

profileIsSwapOfSwapProfile :
  (beta : Physical.PhysicalTriadIncidence) →
  R775.orbitProfile beta
  ≡ R775.swapOrbitProfile
      (R775.orbitProfile (Symmetry.swapTriad beta))
profileIsSwapOfSwapProfile beta =
  sym
    (trans
      (cong R775.swapOrbitProfile (R775.orbitProfileSwap beta))
      (R775.swapOrbitProfileInvolutive (R775.orbitProfile beta)))

hlInteriorOrbitProfile :
  ∀ {beta} →
  (certificate : R25.TriadicClassCertificate beta R25.HL) →
  hlInterior beta ≡ true →
  R775.orbitProfile beta
  ≡ R775.orbit-profile
      Scale.highLow
      Scale.highLow
      Scale.highHigh
hlInteriorOrbitProfile {beta} certificate interior =
  trans
    (profileIsSwapOfSwapProfile beta)
    (cong
      R775.swapOrbitProfile
      (R779.lhInteriorOrbitProfile
        (hlSwapCertificate certificate) interior))

hlBoundaryOrbitProfile :
  ∀ {beta} →
  (certificate : R25.TriadicClassCertificate beta R25.HL) →
  hlInterior beta ≡ false →
  R775.orbitProfile beta
  ≡ R775.orbit-profile
      Scale.highLow
      Scale.comparable
      Scale.comparable
hlBoundaryOrbitProfile {beta} certificate boundary =
  trans
    (profileIsSwapOfSwapProfile beta)
    (cong
      R775.swapOrbitProfile
      (R779.lhBoundaryOrbitProfile
        (hlSwapCertificate certificate) boundary))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round780HLInteriorProfileIsHL_HL_HH : Bool
round780HLInteriorProfileIsHL_HL_HH = true

round780HLBoundaryProfileIsHL_CC_CC : Bool
round780HLBoundaryProfileIsHL_CC_CC = true

round780UsesNoNewShellArithmetic : Bool
round780UsesNoNewShellArithmetic = true

round780IntroducesEstimate : Bool
round780IntroducesEstimate = false

round780W2Closed : Bool
round780W2Closed = false

round780ClayPromotion : Bool
round780ClayPromotion = false

round780HLInteriorProfileIsHL_HL_HHIsTrue :
  round780HLInteriorProfileIsHL_HL_HH ≡ true
round780HLInteriorProfileIsHL_HL_HHIsTrue = refl

round780HLBoundaryProfileIsHL_CC_CCIsTrue :
  round780HLBoundaryProfileIsHL_CC_CC ≡ true
round780HLBoundaryProfileIsHL_CC_CCIsTrue = refl

round780UsesNoNewShellArithmeticIsTrue :
  round780UsesNoNewShellArithmetic ≡ true
round780UsesNoNewShellArithmeticIsTrue = refl

round780IntroducesEstimateIsFalse :
  round780IntroducesEstimate ≡ false
round780IntroducesEstimateIsFalse = refl

round780W2ClosedIsFalse :
  round780W2Closed ≡ false
round780W2ClosedIsFalse = refl

round780ClayPromotionIsFalse :
  round780ClayPromotion ≡ false
round780ClayPromotionIsFalse = refl
