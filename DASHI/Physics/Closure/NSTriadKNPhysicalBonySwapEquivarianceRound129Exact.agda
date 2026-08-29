module DASHI.Physics.Closure.NSTriadKNPhysicalBonySwapEquivarianceRound129Exact where

------------------------------------------------------------------------
-- ROUND129 / EXACT PARTNER EQUIVARIANCE OF THE PHYSICAL BONY CLASSES
--
-- The companion Lean lane identified the shared-fibre partner
--
--     a |-> k-a
--
-- with the ordered p/q swap and observed that it exchanges LH <-> HL while
-- preserving HH->low and comparable.  This file proves that statement on the
-- repository's AUTHORITATIVE strict physical scale classifier, before any
-- absolute value or analytic estimate is introduced.
--
-- The proof is generic in the shell policy.  The only subtle point is that a
-- strict separated relation in one direction forces the opposite separated
-- test to be false; this is proved directly from the executable `natLess`.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as Nat
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSPeriodicNearTriadClassification as Near
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale

sucNotLeSelf : ∀ {n} → suc n ≤ n → ⊥
sucNotLeSelf {0} ()
sucNotLeSelf {suc n} (s≤s proof) = sucNotLeSelf proof

successorLeImpliesLe : ∀ {m n} → suc m ≤ n → m ≤ n
successorLeImpliesLe {0} proof = z≤n
successorLeImpliesLe {suc m} {0} ()
successorLeImpliesLe {suc m} {suc n} (s≤s proof) =
  s≤s (successorLeImpliesLe proof)

natLessTrueToSuccessorLe :
  ∀ {m n} → Near.natLess m n ≡ true → suc m ≤ n
natLessTrueToSuccessorLe {0} {0} ()
natLessTrueToSuccessorLe {0} {suc n} proof = s≤s z≤n
natLessTrueToSuccessorLe {suc m} {0} ()
natLessTrueToSuccessorLe {suc m} {suc n} proof =
  s≤s (natLessTrueToSuccessorLe proof)

strictSeparatedReverseIsFalse :
  ∀ a b radius →
  Near.natLess (a + radius) b ≡ true →
  Near.natLess (b + radius) a ≡ false
strictSeparatedReverseIsFalse a b radius forward
  with Near.natLess (b + radius) a in reverse
... | false = refl
... | true = ⊥-elim contradiction
  where
  aPlusBelowB : suc (a + radius) ≤ b
  aPlusBelowB = natLessTrueToSuccessorLe forward

  bPlusBelowA : suc (b + radius) ≤ a
  bPlusBelowA = natLessTrueToSuccessorLe reverse

  aBelowAPlus : a ≤ a + radius
  aBelowAPlus = Nat.m≤m+n a radius

  bBelowBPlus : b ≤ b + radius
  bBelowBPlus = Nat.m≤m+n b radius

  sucABelowB : suc a ≤ b
  sucABelowB = Nat.≤-trans (s≤s aBelowAPlus) aPlusBelowB

  bBelowA : b ≤ a
  bBelowA = successorLeImpliesLe bPlusBelowA

  contradiction : ⊥
  contradiction = sucNotLeSelf (Nat.≤-trans sucABelowB bBelowA)

swapRegime : Scale.ScaleRegime → Scale.ScaleRegime
swapRegime Scale.lowHigh = Scale.highLow
swapRegime Scale.highLow = Scale.lowHigh
swapRegime Scale.highHigh = Scale.highHigh
swapRegime Scale.comparable = Scale.comparable

swapRegimeInvolutive : ∀ regime → swapRegime (swapRegime regime) ≡ regime
swapRegimeInvolutive Scale.lowHigh = refl
swapRegimeInvolutive Scale.highLow = refl
swapRegimeInvolutive Scale.highHigh = refl
swapRegimeInvolutive Scale.comparable = refl

swapScaleCondition :
  ∀ {policy tau regime} →
  Scale.ScaleCondition policy tau regime →
  Scale.ScaleCondition policy (Symmetry.swapTriad tau) (swapRegime regime)
swapScaleCondition {policy} {tau} {Scale.lowHigh}
    (Scale.lowHighCondition pFarBelowQ) =
  Scale.highLowCondition reverseFalse pFarBelowQ
  where
  jp = Scale.shellLevel policy (Physical.p tau)
  jq = Scale.shellLevel policy (Physical.q tau)
  radius = Scale.overlapRadius policy
  reverseFalse = strictSeparatedReverseIsFalse jp jq radius pFarBelowQ
swapScaleCondition {regime = Scale.highLow}
    (Scale.highLowCondition pNotFarBelowQ qFarBelowP) =
  Scale.lowHighCondition qFarBelowP
swapScaleCondition {regime = Scale.highHigh}
    (Scale.highHighCondition pNotFarBelowQ qNotFarBelowP kBelowP kBelowQ) =
  Scale.highHighCondition qNotFarBelowP pNotFarBelowQ kBelowQ kBelowP
swapScaleCondition {regime = Scale.comparable}
    (Scale.comparableCondition pNotFarBelowQ qNotFarBelowP (inj₁ kNotBelowP)) =
  Scale.comparableCondition qNotFarBelowP pNotFarBelowQ (inj₂ kNotBelowP)
swapScaleCondition {regime = Scale.comparable}
    (Scale.comparableCondition pNotFarBelowQ qNotFarBelowP (inj₂ kNotBelowQ)) =
  Scale.comparableCondition qNotFarBelowP pNotFarBelowQ (inj₁ kNotBelowQ)

scaleConditionForcesComputedRegime :
  ∀ {policy tau regime} →
  Scale.ScaleCondition policy tau regime →
  Scale.classifyScale policy tau ≡ regime
scaleConditionForcesComputedRegime
    (Scale.lowHighCondition pFarBelowQ)
  rewrite pFarBelowQ = refl
scaleConditionForcesComputedRegime
    (Scale.highLowCondition pNotFarBelowQ qFarBelowP)
  rewrite pNotFarBelowQ | qFarBelowP = refl
scaleConditionForcesComputedRegime
    (Scale.highHighCondition pNotFarBelowQ qNotFarBelowP kBelowP kBelowQ)
  rewrite pNotFarBelowQ | qNotFarBelowP | kBelowP | kBelowQ = refl
scaleConditionForcesComputedRegime {policy} {tau} {Scale.comparable}
    (Scale.comparableCondition pNotFarBelowQ qNotFarBelowP (inj₁ kNotBelowP))
  rewrite pNotFarBelowQ | qNotFarBelowP | kNotBelowP = refl
scaleConditionForcesComputedRegime {policy} {tau} {Scale.comparable}
    (Scale.comparableCondition pNotFarBelowQ qNotFarBelowP (inj₂ kNotBelowQ))
  rewrite pNotFarBelowQ | qNotFarBelowP
  with Near.natLess
    (Scale.shellLevel policy (Physical.k tau) + Scale.overlapRadius policy)
    (Scale.shellLevel policy (Physical.p tau))
... | true rewrite kNotBelowQ = refl
... | false = refl

classifyScaleSwapEquivariant :
  ∀ policy tau →
  Scale.classifyScale policy (Symmetry.swapTriad tau)
  ≡ swapRegime (Scale.classifyScale policy tau)
classifyScaleSwapEquivariant policy tau =
  scaleConditionForcesComputedRegime
    (swapScaleCondition (Scale.scaleClassificationSound policy tau))

classifyScaleSwapTwiceReturns :
  ∀ policy tau →
  swapRegime
    (Scale.classifyScale policy (Symmetry.swapTriad tau))
  ≡ Scale.classifyScale policy tau
classifyScaleSwapTwiceReturns policy tau =
  trans
    (cong swapRegime (classifyScaleSwapEquivariant policy tau))
    (swapRegimeInvolutive (Scale.classifyScale policy tau))

round129StrictScalePartnerEquivarianceClosed : Bool
round129StrictScalePartnerEquivarianceClosed = true

round129LowHighHighLowExchangeClosed : Bool
round129LowHighHighLowExchangeClosed = true

round129HighHighPartnerInvariantClosed : Bool
round129HighHighPartnerInvariantClosed = true

round129ComparablePartnerInvariantClosed : Bool
round129ComparablePartnerInvariantClosed = true

round129AbsoluteValueIntroduced : Bool
round129AbsoluteValueIntroduced = false

round129StrictScalePartnerEquivarianceClosedIsTrue :
  round129StrictScalePartnerEquivarianceClosed ≡ true
round129StrictScalePartnerEquivarianceClosedIsTrue = refl

round129AbsoluteValueIntroducedIsFalse :
  round129AbsoluteValueIntroduced ≡ false
round129AbsoluteValueIntroducedIsFalse = refl
