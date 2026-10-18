{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650FullySeparatedOrbitProfileSupportRound782Exact where

------------------------------------------------------------------------
-- ROUND782 / FULLY-SEPARATED ORBITS HAVE EXACTLY THREE PROFILE SHAPES
--
-- R777:
--   HH -> (HH,LH,LH).
--
-- R779:
--   LH interior -> (LH,HH,HL)
--   LH boundary -> (LH,CC,CC).
--
-- R780:
--   HL interior -> (HL,HL,HH)
--   HL boundary -> (HL,CC,CC).
--
-- R781 defines fullySeparated by the exact negation of "some orbit coordinate
-- is CC".  Therefore every fully-separated incidence has one of exactly three
-- surviving profile shapes:
--
--   (LH,HH,HL), (HL,HL,HH), (HH,LH,LH).
--
-- A CC base incidence is excluded immediately, and the LH/HL boundary branches
-- are excluded by their exact profile theorems.  This is finite classifier
-- algebra only: no sign, norm, or estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as R25
import DASHI.Physics.Closure.NSTriadKNPhysicalBonySwapEquivarianceRound129Exact as R129
import DASHI.Physics.Closure.NSTriadKNR650EnergyOrbitBonyProfileRound775Exact as R775
import DASHI.Physics.Closure.NSTriadKNR650HHOrbitProfileRound777Exact as R777
import DASHI.Physics.Closure.NSTriadKNR650LHOrbitProfileSplitRound779Exact as R779
import DASHI.Physics.Closure.NSTriadKNR650HLOrbitProfileSplitRound780Exact as R780
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

data FullySeparatedOrbitShape
    (beta : Physical.PhysicalTriadIncidence) : Set where
  lhInteriorShape :
    R775.orbitProfile beta
    ≡ R775.orbit-profile
        Scale.lowHigh
        Scale.highHigh
        Scale.highLow →
    FullySeparatedOrbitShape beta

  hlInteriorShape :
    R775.orbitProfile beta
    ≡ R775.orbit-profile
        Scale.highLow
        Scale.highLow
        Scale.highHigh →
    FullySeparatedOrbitShape beta

  hhShape :
    R775.orbitProfile beta
    ≡ R775.orbit-profile
        Scale.highHigh
        Scale.lowHigh
        Scale.lowHigh →
    FullySeparatedOrbitShape beta

lhBoundaryTouchesComparable :
  ∀ {beta} →
  (certificate : R25.TriadicClassCertificate beta R25.LH) →
  R779.lhInterior beta ≡ false →
  R781.ccTouched beta ≡ true
lhBoundaryTouchesComparable certificate boundary
  rewrite R779.lhBoundaryOrbitProfile certificate boundary =
  refl

hlBoundaryTouchesComparable :
  ∀ {beta} →
  (certificate : R25.TriadicClassCertificate beta R25.HL) →
  R780.hlInterior beta ≡ false →
  R781.ccTouched beta ≡ true
hlBoundaryTouchesComparable certificate boundary
  rewrite R780.hlBoundaryOrbitProfile certificate boundary =
  refl

ccBaseTouchesComparable :
  ∀ {beta} →
  R25.TriadicClassCertificate beta R25.CC →
  R781.ccTouched beta ≡ true
ccBaseTouchesComparable {beta} certificate
  rewrite R775.orbitProfileBase beta
        | R129.scaleConditionForcesComputedRegime
            (R25.classMeaning certificate) =
  refl

fullySeparatedOrbitShape :
  (beta : Physical.PhysicalTriadIncidence) →
  R781.ccTouched beta ≡ false →
  FullySeparatedOrbitShape beta
fullySeparatedOrbitShape beta separated
  with R25.classifyPhysicalTriad beta
... | R25.LH , certificate
  with R779.lhInterior beta in interior
... | true =
  lhInteriorShape
    (R779.lhInteriorOrbitProfile certificate interior)
... | false =
  ⊥-elim
    (trueNotFalse
      (trans
        (sym (lhBoundaryTouchesComparable certificate interior))
        separated))
... | R25.HL , certificate
  with R780.hlInterior beta in interior
... | true =
  hlInteriorShape
    (R780.hlInteriorOrbitProfile certificate interior)
... | false =
  ⊥-elim
    (trueNotFalse
      (trans
        (sym (hlBoundaryTouchesComparable certificate interior))
        separated))
... | R25.HH , certificate =
  hhShape (R777.hhOrbitProfileExact certificate)
... | R25.CC , certificate =
  ⊥-elim
    (trueNotFalse
      (trans
        (sym (ccBaseTouchesComparable certificate))
        separated))

round782FullySeparatedProfileSupportFinite : Bool
round782FullySeparatedProfileSupportFinite = true

round782FullySeparatedProfileShapeCountIsThree : Bool
round782FullySeparatedProfileShapeCountIsThree = true

round782LHBoundaryExcludedFromFullySeparated : Bool
round782LHBoundaryExcludedFromFullySeparated = true

round782HLBoundaryExcludedFromFullySeparated : Bool
round782HLBoundaryExcludedFromFullySeparated = true

round782CCBaseExcludedFromFullySeparated : Bool
round782CCBaseExcludedFromFullySeparated = true

round782IntroducesEstimate : Bool
round782IntroducesEstimate = false

round782W2Closed : Bool
round782W2Closed = false

round782ClayPromotion : Bool
round782ClayPromotion = false

round782FullySeparatedProfileSupportFiniteIsTrue :
  round782FullySeparatedProfileSupportFinite ≡ true
round782FullySeparatedProfileSupportFiniteIsTrue = refl

round782FullySeparatedProfileShapeCountIsThreeIsTrue :
  round782FullySeparatedProfileShapeCountIsThree ≡ true
round782FullySeparatedProfileShapeCountIsThreeIsTrue = refl

round782IntroducesEstimateIsFalse :
  round782IntroducesEstimate ≡ false
round782IntroducesEstimateIsFalse = refl

round782W2ClosedIsFalse :
  round782W2Closed ≡ false
round782W2ClosedIsFalse = refl

round782ClayPromotionIsFalse :
  round782ClayPromotion ≡ false
round782ClayPromotionIsFalse = refl
