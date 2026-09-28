{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650LHOrbitProfileSplitRound779Exact where

------------------------------------------------------------------------
-- ROUND779 / LH ENERGY-ORBIT PROFILE SPLITS EXACTLY INTO INTERIOR AND COLLAR
--
-- For an R25 LH triad, q is the high input and the literal dyadic theorem gives
--
--   |shell(k)-shell(q)| <= 1.
--
-- Use one additional EXISTING executable comparison:
--
--   interior(beta) := natLess (shell(p)+3) shell(k).
--
-- If interior=true, then:
--   * pEnergyLeg has two comparable high inputs k,-q and low output p: HH;
--   * qEnergyLeg has high first input k, low second input -p: HL.
--
-- If interior=false, then:
--   * pEnergyLeg fails its HH output-below-k test: CC;
--   * qEnergyLeg fails its HL p-below-k test and cannot be HH: CC.
--
-- Thus exactly
--
--   LH interior  -> (LH,HH,HL)
--   LH boundary  -> (LH,CC,CC).
--
-- No estimate is introduced.  The split is finite shell/classifier algebra on
-- the authoritative R25 carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as Nat
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicNearTriadClassification as Near
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicConsequencesClosed as Dyadic
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as R25
import DASHI.Physics.Closure.NSTriadKNPhysicalBonySwapEquivarianceRound129Exact as R129
import DASHI.Physics.Closure.NSTriadKNR650EnergyOrbitBonyProfileRound775Exact as R775
import DASHI.Physics.Closure.NSTriadKNR650HHOrbitProfileRound777Exact as R777

distanceOneLeftUpper :
  ∀ {left right : Nat} →
  Data.Nat.Base.∣ left - right ∣ ≤ 1 →
  left ≤ suc right
distanceOneLeftUpper {zero} {right} proof = z≤n
distanceOneLeftUpper {suc left} {zero} proof = proof
distanceOneLeftUpper {suc left} {suc right} proof =
  s≤s (distanceOneLeftUpper {left} {right} proof)

distanceOneRightUpper :
  ∀ {left right : Nat} →
  Data.Nat.Base.∣ left - right ∣ ≤ 1 →
  right ≤ suc left
distanceOneRightUpper {left} {zero} proof = z≤n
distanceOneRightUpper {zero} {suc right} proof = proof
distanceOneRightUpper {suc left} {suc right} proof =
  s≤s (distanceOneRightUpper {left} {right} proof)

gapThreeFalseFromDistanceOneLeft :
  ∀ {left right : Nat} →
  Data.Nat.Base.∣ left - right ∣ ≤ 1 →
  Near.natLess (left + 3) right ≡ false
gapThreeFalseFromDistanceOneLeft {left} {right} close
  with Near.natLess (left + 3) right in gap
... | false = refl
... | true =
  ⊥-elim
    (Dyadic.gapThreeContradictsUpperSuccessor
      (R25.natLessTrueToLe gap)
      (distanceOneRightUpper close))

gapThreeFalseFromDistanceOneRight :
  ∀ {left right : Nat} →
  Data.Nat.Base.∣ left - right ∣ ≤ 1 →
  Near.natLess (right + 3) left ≡ false
gapThreeFalseFromDistanceOneRight {left} {right} close
  with Near.natLess (right + 3) left in gap
... | false = refl
... | true =
  ⊥-elim
    (Dyadic.gapThreeContradictsUpperSuccessor
      (R25.natLessTrueToLe gap)
      (distanceOneLeftUpper close))

oppositeGapFalse :
  ∀ {low high : Nat} →
  Near.natLess (low + 3) high ≡ true →
  Near.natLess (high + 3) low ≡ false
oppositeGapFalse {low} {high} forward
  with Near.natLess (high + 3) low in reverse
... | false = refl
... | true =
  let
    forwardLe : low + 3 ≤ high
    forwardLe = R25.natLessTrueToLe forward

    low≤high : low ≤ high
    low≤high = Dyadic.shellGapThreeImpliesLowerShellLeHigher forwardLe

    reverseLe : high + 3 ≤ low
    reverseLe = R25.natLessTrueToLe reverse

    lowUpper : low ≤ suc high
    lowUpper = Nat.≤-trans low≤high (Nat.n≤1+n high)
  in
  ⊥-elim (Dyadic.gapThreeContradictsUpperSuccessor reverseLe lowUpper)

lhInterior :
  Physical.PhysicalTriadIncidence → Bool
lhInterior beta =
  Near.natLess
    (Shell.shellIndex (Physical.p beta) + Shell.Csep)
    (Shell.shellIndex (Physical.k beta))

lhBaseRegime :
  ∀ {beta} →
  R25.TriadicClassCertificate beta R25.LH →
  Scale.classifyScale R25.literalShellPolicy beta ≡ Scale.lowHigh
lhBaseRegime certificate =
  R129.scaleConditionForcesComputedRegime
    (R25.classMeaning certificate)

lhPInteriorIsHighHigh :
  ∀ {beta} →
  (certificate : R25.TriadicClassCertificate beta R25.LH) →
  lhInterior beta ≡ true →
  Scale.classifyScale R25.literalShellPolicy (Orbit.pEnergyLeg beta)
  ≡ Scale.highHigh
lhPInteriorIsHighHigh {beta} certificate interior
  with R25.classMeaning certificate
... | Scale.lowHighCondition pBelowQ =
  R129.scaleConditionForcesComputedRegime
    (Scale.highHighCondition notKBelowQ notQBelowK pBelowK pBelowQ′)
  where
  close :
    Data.Nat.Base.∣
      Shell.shellIndex (Physical.k beta)
      - Shell.shellIndex (Physical.q beta) ∣ ≤ 1
  close = R25.lowHighOutputTracksHighOne certificate

  notKBelowQ :
    Near.natLess
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.p (Orbit.pEnergyLeg beta))
        + Scale.overlapRadius R25.literalShellPolicy)
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.q (Orbit.pEnergyLeg beta)))
    ≡ false
  notKBelowQ
    rewrite Orbit.pEnergyLegFirstInput beta
          | Orbit.pEnergyLegSecondInput beta
          | R777.literalShellIndexNegate (Physical.q beta) =
    gapThreeFalseFromDistanceOneLeft close

  notQBelowK :
    Near.natLess
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.q (Orbit.pEnergyLeg beta))
        + Scale.overlapRadius R25.literalShellPolicy)
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.p (Orbit.pEnergyLeg beta)))
    ≡ false
  notQBelowK
    rewrite Orbit.pEnergyLegFirstInput beta
          | Orbit.pEnergyLegSecondInput beta
          | R777.literalShellIndexNegate (Physical.q beta) =
    gapThreeFalseFromDistanceOneRight close

  pBelowK :
    Near.natLess
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.k (Orbit.pEnergyLeg beta))
        + Scale.overlapRadius R25.literalShellPolicy)
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.p (Orbit.pEnergyLeg beta)))
    ≡ true
  pBelowK
    rewrite Orbit.pEnergyLegOutput beta
          | Orbit.pEnergyLegFirstInput beta =
    interior

  pBelowQ′ :
    Near.natLess
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.k (Orbit.pEnergyLeg beta))
        + Scale.overlapRadius R25.literalShellPolicy)
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.q (Orbit.pEnergyLeg beta)))
    ≡ true
  pBelowQ′
    rewrite Orbit.pEnergyLegOutput beta
          | Orbit.pEnergyLegSecondInput beta
          | R777.literalShellIndexNegate (Physical.q beta) =
    pBelowQ

lhQInteriorIsHighLow :
  ∀ {beta} →
  (certificate : R25.TriadicClassCertificate beta R25.LH) →
  lhInterior beta ≡ true →
  Scale.classifyScale R25.literalShellPolicy (Orbit.qEnergyLeg beta)
  ≡ Scale.highLow
lhQInteriorIsHighLow {beta} certificate interior =
  R129.scaleConditionForcesComputedRegime
    (Scale.highLowCondition notKBelowP pBelowK)
  where
  notKBelowP :
    Near.natLess
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.p (Orbit.qEnergyLeg beta))
        + Scale.overlapRadius R25.literalShellPolicy)
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.q (Orbit.qEnergyLeg beta)))
    ≡ false
  notKBelowP
    rewrite Orbit.qEnergyLegFirstInput beta
          | Orbit.qEnergyLegSecondInput beta
          | R777.literalShellIndexNegate (Physical.p beta) =
    oppositeGapFalse interior

  pBelowK :
    Near.natLess
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.q (Orbit.qEnergyLeg beta))
        + Scale.overlapRadius R25.literalShellPolicy)
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.p (Orbit.qEnergyLeg beta)))
    ≡ true
  pBelowK
    rewrite Orbit.qEnergyLegFirstInput beta
          | Orbit.qEnergyLegSecondInput beta
          | R777.literalShellIndexNegate (Physical.p beta) =
    interior

lhInteriorOrbitProfile :
  ∀ {beta} →
  (certificate : R25.TriadicClassCertificate beta R25.LH) →
  lhInterior beta ≡ true →
  R775.orbitProfile beta
  ≡ R775.orbit-profile
      Scale.lowHigh
      Scale.highHigh
      Scale.highLow
lhInteriorOrbitProfile {beta} certificate interior
  rewrite lhBaseRegime certificate
        | lhPInteriorIsHighHigh certificate interior
        | lhQInteriorIsHighLow certificate interior =
  refl

lhPBoundaryIsComparable :
  ∀ {beta} →
  (certificate : R25.TriadicClassCertificate beta R25.LH) →
  lhInterior beta ≡ false →
  Scale.classifyScale R25.literalShellPolicy (Orbit.pEnergyLeg beta)
  ≡ Scale.comparable
lhPBoundaryIsComparable {beta} certificate boundary
  with R25.classMeaning certificate
... | Scale.lowHighCondition pBelowQ =
  R129.scaleConditionForcesComputedRegime
    (Scale.comparableCondition notKBelowQ notQBelowK
      (Data.Sum.Base.inj₁ pNotBelowK))
  where
  close :
    Data.Nat.Base.∣
      Shell.shellIndex (Physical.k beta)
      - Shell.shellIndex (Physical.q beta) ∣ ≤ 1
  close = R25.lowHighOutputTracksHighOne certificate

  notKBelowQ :
    Near.natLess
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.p (Orbit.pEnergyLeg beta))
        + Scale.overlapRadius R25.literalShellPolicy)
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.q (Orbit.pEnergyLeg beta)))
    ≡ false
  notKBelowQ
    rewrite Orbit.pEnergyLegFirstInput beta
          | Orbit.pEnergyLegSecondInput beta
          | R777.literalShellIndexNegate (Physical.q beta) =
    gapThreeFalseFromDistanceOneLeft close

  notQBelowK :
    Near.natLess
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.q (Orbit.pEnergyLeg beta))
        + Scale.overlapRadius R25.literalShellPolicy)
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.p (Orbit.pEnergyLeg beta)))
    ≡ false
  notQBelowK
    rewrite Orbit.pEnergyLegFirstInput beta
          | Orbit.pEnergyLegSecondInput beta
          | R777.literalShellIndexNegate (Physical.q beta) =
    gapThreeFalseFromDistanceOneRight close

  pNotBelowK :
    Near.natLess
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.k (Orbit.pEnergyLeg beta))
        + Scale.overlapRadius R25.literalShellPolicy)
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.p (Orbit.pEnergyLeg beta)))
    ≡ false
  pNotBelowK
    rewrite Orbit.pEnergyLegOutput beta
          | Orbit.pEnergyLegFirstInput beta =
    boundary

lhQBoundaryIsComparable :
  ∀ {beta} →
  (certificate : R25.TriadicClassCertificate beta R25.LH) →
  lhInterior beta ≡ false →
  Scale.classifyScale R25.literalShellPolicy (Orbit.qEnergyLeg beta)
  ≡ Scale.comparable
lhQBoundaryIsComparable {beta} certificate boundary
  with R25.classMeaning certificate
... | Scale.lowHighCondition pBelowQ =
  R129.scaleConditionForcesComputedRegime
    (Scale.comparableCondition notKBelowP boundary′
      (Data.Sum.Base.inj₂ qNotBelowP))
  where
  pGapLe :
    Shell.shellIndex (Physical.p beta) + Shell.Csep
    ≤ Shell.shellIndex (Physical.q beta)
  pGapLe = R25.natLessTrueToLe pBelowQ

  p≤q :
    Shell.shellIndex (Physical.p beta)
    ≤ Shell.shellIndex (Physical.q beta)
  p≤q = Dyadic.shellGapThreeImpliesLowerShellLeHigher pGapLe

  notKBelowP :
    Near.natLess
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.p (Orbit.qEnergyLeg beta))
        + Scale.overlapRadius R25.literalShellPolicy)
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.q (Orbit.qEnergyLeg beta)))
    ≡ false
  notKBelowP
    rewrite Orbit.qEnergyLegFirstInput beta
          | Orbit.qEnergyLegSecondInput beta
          | R777.literalShellIndexNegate (Physical.p beta)
    with Near.natLess
      (Shell.shellIndex (Physical.k beta) + Shell.Csep)
      (Shell.shellIndex (Physical.p beta)) in reverse
  ... | false = refl
  ... | true =
    ⊥-elim
      (Dyadic.gapThreeContradictsUpperSuccessor
        (R25.natLessTrueToLe reverse)
        (Nat.≤-trans p≤q
          (distanceOneRightUpper
            (R25.lowHighOutputTracksHighOne certificate))))

  boundary′ :
    Near.natLess
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.q (Orbit.qEnergyLeg beta))
        + Scale.overlapRadius R25.literalShellPolicy)
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.p (Orbit.qEnergyLeg beta)))
    ≡ false
  boundary′
    rewrite Orbit.qEnergyLegFirstInput beta
          | Orbit.qEnergyLegSecondInput beta
          | R777.literalShellIndexNegate (Physical.p beta) =
    boundary

  qNotBelowP :
    Near.natLess
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.k (Orbit.qEnergyLeg beta))
        + Scale.overlapRadius R25.literalShellPolicy)
      (Scale.shellLevel R25.literalShellPolicy
        (Physical.q (Orbit.qEnergyLeg beta)))
    ≡ false
  qNotBelowP
    rewrite Orbit.qEnergyLegOutput beta
          | Orbit.qEnergyLegSecondInput beta
          | R777.literalShellIndexNegate (Physical.p beta) =
    oppositeGapFalse pBelowQ

lhBoundaryOrbitProfile :
  ∀ {beta} →
  (certificate : R25.TriadicClassCertificate beta R25.LH) →
  lhInterior beta ≡ false →
  R775.orbitProfile beta
  ≡ R775.orbit-profile
      Scale.lowHigh
      Scale.comparable
      Scale.comparable
lhBoundaryOrbitProfile {beta} certificate boundary
  rewrite lhBaseRegime certificate
        | lhPBoundaryIsComparable certificate boundary
        | lhQBoundaryIsComparable certificate boundary =
  refl

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round779LHInteriorProfileIsLH_HH_HL : Bool
round779LHInteriorProfileIsLH_HH_HL = true

round779LHBoundaryProfileIsLH_CC_CC : Bool
round779LHBoundaryProfileIsLH_CC_CC = true

round779LHOrbitHasExactlyOneAdditionalClassifierBit : Bool
round779LHOrbitHasExactlyOneAdditionalClassifierBit = true

round779IntroducesEstimate : Bool
round779IntroducesEstimate = false

round779W2Closed : Bool
round779W2Closed = false

round779ClayPromotion : Bool
round779ClayPromotion = false

round779LHInteriorProfileIsLH_HH_HLIsTrue :
  round779LHInteriorProfileIsLH_HH_HL ≡ true
round779LHInteriorProfileIsLH_HH_HLIsTrue = refl

round779LHBoundaryProfileIsLH_CC_CCIsTrue :
  round779LHBoundaryProfileIsLH_CC_CC ≡ true
round779LHBoundaryProfileIsLH_CC_CCIsTrue = refl

round779LHOrbitHasExactlyOneAdditionalClassifierBitIsTrue :
  round779LHOrbitHasExactlyOneAdditionalClassifierBit ≡ true
round779LHOrbitHasExactlyOneAdditionalClassifierBitIsTrue = refl

round779IntroducesEstimateIsFalse :
  round779IntroducesEstimate ≡ false
round779IntroducesEstimateIsFalse = refl

round779W2ClosedIsFalse :
  round779W2Closed ≡ false
round779W2ClosedIsFalse = refl

round779ClayPromotionIsFalse :
  round779ClayPromotion ≡ false
round779ClayPromotionIsFalse = refl
