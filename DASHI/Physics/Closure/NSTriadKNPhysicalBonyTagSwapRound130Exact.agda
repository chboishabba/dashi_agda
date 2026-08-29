module DASHI.Physics.Closure.NSTriadKNPhysicalBonyTagSwapRound130Exact where

------------------------------------------------------------------------
-- ROUND130 / AUTHORITATIVE BONY TAG TRANSPORT UNDER THE SHARED-FIBRE PARTNER
--
-- Round129 proved equivariance of the strict executable scale classifier under
-- p/q swap.  This file lifts that theorem to the literal Round63 Bony tags
-- consumed by the signed output-fibre decomposition:
--
--     LH          <-> HL
--     HH -> low    <-> HH -> low
--     comparable  <-> comparable.
--
-- Thus the same shared-fibre partner used by the pure Waleffe commutator is
-- class-compatible before absolute values.  This is the Agda-side structural
-- counterpart of the classwise partner-invariance theorem in the Lean lane.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support
import DASHI.Physics.Closure.NSTriadKNComLiteralBonyOutputFibrePartitionRound63Exact as Bony
import DASHI.Physics.Closure.NSTriadKNPhysicalBonySwapEquivarianceRound129Exact as R129

swapBonyTag : Bony.BonyTag → Bony.BonyTag
swapBonyTag Bony.lhTag = Bony.hlTag
swapBonyTag Bony.hlTag = Bony.lhTag
swapBonyTag Bony.hhToLowTag = Bony.hhToLowTag
swapBonyTag Bony.comparableTag = Bony.comparableTag

swapBonyTagInvolutive : ∀ tag → swapBonyTag (swapBonyTag tag) ≡ tag
swapBonyTagInvolutive Bony.lhTag = refl
swapBonyTagInvolutive Bony.hlTag = refl
swapBonyTagInvolutive Bony.hhToLowTag = refl
swapBonyTagInvolutive Bony.comparableTag = refl

regimeTag : Scale.ScaleRegime → Bony.BonyTag
regimeTag Scale.lowHigh = Bony.lhTag
regimeTag Scale.highLow = Bony.hlTag
regimeTag Scale.highHigh = Bony.hhToLowTag
regimeTag Scale.comparable = Bony.comparableTag

regimeTagSwap : ∀ regime →
  regimeTag (R129.swapRegime regime) ≡ swapBonyTag (regimeTag regime)
regimeTagSwap Scale.lowHigh = refl
regimeTagSwap Scale.highLow = refl
regimeTagSwap Scale.highHigh = refl
regimeTagSwap Scale.comparable = refl

bonyTagIsComputedScaleTag :
  (tau : Physical.PhysicalTriadIncidence) →
  Bony.bonyTag tau
  ≡ regimeTag
      (Scale.classifyScale Shell.literalDyadicShellPolicy tau)
bonyTagIsComputedScaleTag tau with Support.classifyPhysicalTriad tau
... | Support.LH , certificate = refl
... | Support.HL , certificate = refl
... | Support.HH , certificate = refl
... | Support.CC , certificate = refl

bonyTagSwapEquivariant :
  (tau : Physical.PhysicalTriadIncidence) →
  Bony.bonyTag (Symmetry.swapTriad tau)
  ≡ swapBonyTag (Bony.bonyTag tau)
bonyTagSwapEquivariant tau =
  trans
    (bonyTagIsComputedScaleTag (Symmetry.swapTriad tau))
    (trans
      (cong regimeTag
        (R129.classifyScaleSwapEquivariant
          Shell.literalDyadicShellPolicy tau))
      (trans
        (regimeTagSwap
          (Scale.classifyScale Shell.literalDyadicShellPolicy tau))
        (cong swapBonyTag (sym (bonyTagIsComputedScaleTag tau)))))

lowHighPartnerIsHighLow :
  ∀ {tau} →
  Bony.bonyTag tau ≡ Bony.lhTag →
  Bony.bonyTag (Symmetry.swapTriad tau) ≡ Bony.hlTag
lowHighPartnerIsHighLow {tau} proof =
  trans
    (bonyTagSwapEquivariant tau)
    (cong swapBonyTag proof)

highLowPartnerIsLowHigh :
  ∀ {tau} →
  Bony.bonyTag tau ≡ Bony.hlTag →
  Bony.bonyTag (Symmetry.swapTriad tau) ≡ Bony.lhTag
highLowPartnerIsLowHigh {tau} proof =
  trans
    (bonyTagSwapEquivariant tau)
    (cong swapBonyTag proof)

highHighPartnerInvariant :
  ∀ {tau} →
  Bony.bonyTag tau ≡ Bony.hhToLowTag →
  Bony.bonyTag (Symmetry.swapTriad tau) ≡ Bony.hhToLowTag
highHighPartnerInvariant {tau} proof =
  trans
    (bonyTagSwapEquivariant tau)
    (cong swapBonyTag proof)

comparablePartnerInvariant :
  ∀ {tau} →
  Bony.bonyTag tau ≡ Bony.comparableTag →
  Bony.bonyTag (Symmetry.swapTriad tau) ≡ Bony.comparableTag
comparablePartnerInvariant {tau} proof =
  trans
    (bonyTagSwapEquivariant tau)
    (cong swapBonyTag proof)

round130AuthoritativeBonyTagSwapEquivarianceClosed : Bool
round130AuthoritativeBonyTagSwapEquivarianceClosed = true

round130LowHighHighLowExchangeClosed : Bool
round130LowHighHighLowExchangeClosed = true

round130HighHighPartnerInvariantClosed : Bool
round130HighHighPartnerInvariantClosed = true

round130ComparablePartnerInvariantClosed : Bool
round130ComparablePartnerInvariantClosed = true

round130ClasswiseAbsoluteValueIntroduced : Bool
round130ClasswiseAbsoluteValueIntroduced = false

round130AuthoritativeBonyTagSwapEquivarianceClosedIsTrue :
  round130AuthoritativeBonyTagSwapEquivarianceClosed ≡ true
round130AuthoritativeBonyTagSwapEquivarianceClosedIsTrue = refl

round130ClasswiseAbsoluteValueIntroducedIsFalse :
  round130ClasswiseAbsoluteValueIntroduced ≡ false
round130ClasswiseAbsoluteValueIntroducedIsFalse = refl
