module DASHI.Physics.Closure.NSTriadKNHardBaseCanonicalSoftSplitRound46Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- Proceedings of the Royal Society of London. Series A 87 (1912).
-- DOI: 10.1098/rspa.1912.0086.
--
-- Author: Gyula Farkas.
-- Title: "Theorie der einfachen Ungleichungen".
-- Journal fuer die reine und angewandte Mathematik 124 (1902), 1--27.
-- DOI: no DOI assigned to the historical article.
--
-- DASHI CONTRIBUTION
--
-- Round 45 proved that HH-good is Young-soft and that every strict physical
-- reserve implies the hard-base inequality
--
--   H = 2 C_* + eta_Com + eta_kernel + 4/64 < 1.
--
-- Round 46 proves the converse finite allocation step.  From H<1 it constructs
-- the positive rational split
--
--   epsilon_HHg = (1-H)/2
--
-- internally, including its reciprocal required by PositiveThreshold.  The
-- resulting total is
--
--   H + epsilon_HHg = (1+H)/2 < 1,
--
-- with remaining viscosity exactly epsilon_HHg.  Therefore, once the physical
-- owner core and tail input exist, the strict nine-owner budget needs no
-- external epsilon optimizer: H<1 is the complete finite reserve gate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; 1/_; positive)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNBonyTailOwnerRound44Exact as Tail
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHardSoftReserveRound45Exact as HardSoft
import DASHI.Physics.Closure.NSTriadKNHardBaseNecessaryReserveRound45Exact as HardBase
import DASHI.Physics.Closure.NSTriadKNFiveOwnerReserveReductionRound44Exact as Five

halfPositive : 0ℚ < Sharp.half
halfPositive = toWitness {a? = 0ℚ <? Sharp.half} _

halfLessThanOne : Sharp.half < 1ℚ
halfLessThanOne = toWitness {a? = Sharp.half <? 1ℚ} _

hardMargin :
  ∀ {environment} →
  HardSoft.HardSoftOwnerCore environment → ℚ
hardMargin core = 1ℚ - HardBase.hardBaseEtaTotal core

hardMarginPositive :
  ∀ {environment}
    (core : HardSoft.HardSoftOwnerCore environment) →
  HardBase.hardBaseEtaTotal core < 1ℚ →
  0ℚ < hardMargin core
hardMarginPositive core hardStrict = ℚP.-positiveˡ hardStrict

halfMarginValue :
  ∀ {environment} →
  HardSoft.HardSoftOwnerCore environment → ℚ
halfMarginValue core = Sharp.half * hardMargin core

halfMarginPositive :
  ∀ {environment}
    (core : HardSoft.HardSoftOwnerCore environment) →
  HardBase.hardBaseEtaTotal core < 1ℚ →
  0ℚ < halfMarginValue core
halfMarginPositive core hardStrict =
  let
    instance
      halfPosI = positive halfPositive
      marginPosI = positive (hardMarginPositive core hardStrict)
      productPosI = ℚP.pos*pos⇒pos Sharp.half (hardMargin core)
  in
  ℚP.positive⁻¹ (halfMarginValue core)

halfMarginSplit :
  ∀ {environment}
    (core : HardSoft.HardSoftOwnerCore environment) →
  HardBase.hardBaseEtaTotal core < 1ℚ →
  Threshold.PositiveThreshold
halfMarginSplit core hardStrict =
  let
    value = halfMarginValue core
    valuePositive = halfMarginPositive core hardStrict
    instance
      valuePositiveI = positive valuePositive
      valueNonzeroI = ℚP.pos⇒nonZero value
      inversePositiveI = ℚP.1/pos⇒pos value

    inverseNonnegative : 0ℚ ≤ ℚ.1/_ value
    inverseNonnegative = ℚP.<⇒≤ (ℚP.positive⁻¹ (ℚ.1/_ value))

    inverseLaw : ℚ.1/_ value * value ≡ 1ℚ
    inverseLaw = ℚP.*-inverseˡ value
  in
  Threshold.positive-threshold
    value
    (ℚ.1/_ value)
    valuePositive
    inverseNonnegative
    inverseLaw

halfMarginSplitValue :
  ∀ {environment}
    (core : HardSoft.HardSoftOwnerCore environment)
    (hardStrict : HardBase.hardBaseEtaTotal core < 1ℚ) →
  Threshold.threshold (halfMarginSplit core hardStrict)
  ≡ halfMarginValue core
halfMarginSplitValue core hardStrict = refl

halfMarginBelowFullHardMargin :
  ∀ {environment}
    (core : HardSoft.HardSoftOwnerCore environment)
    (hardStrict : HardBase.hardBaseEtaTotal core < 1ℚ) →
  halfMarginValue core < hardMargin core
halfMarginBelowFullHardMargin core hardStrict =
  let
    marginPositive = hardMarginPositive core hardStrict
    instance marginPositiveI = positive marginPositive
    scaled :
      Sharp.half * hardMargin core
      < 1ℚ * hardMargin core
    scaled = ℚP.*-monoˡ-<-pos (hardMargin core) halfLessThanOne
  in
  subst
    (λ upper → halfMarginValue core < upper)
    (solve (hardMargin core ∷ []))
    scaled

hardSoftTotalAtCanonicalSplitStrict :
  ∀ {environment}
    (core : HardSoft.HardSoftOwnerCore environment)
    (hardStrict : HardBase.hardBaseEtaTotal core < 1ℚ) →
  HardSoft.hardSoftEtaTotal core (halfMarginSplit core hardStrict) < 1ℚ
hardSoftTotalAtCanonicalSplitStrict core hardStrict =
  let
    splitBelowMargin = halfMarginBelowFullHardMargin core hardStrict

    shifted :
      halfMarginValue core + HardBase.hardBaseEtaTotal core
      < hardMargin core + HardBase.hardBaseEtaTotal core
    shifted =
      ℚP.+-mono-<-≤ splitBelowMargin ℚP.≤-refl

    leftMeaning :
      halfMarginValue core + HardBase.hardBaseEtaTotal core
      ≡ HardSoft.hardSoftEtaTotal core (halfMarginSplit core hardStrict)
    leftMeaning =
      solve
        ( halfMarginValue core
        ∷ HardSoft.hhBadProfileCeiling core
        ∷ Owner.eta (HardSoft.comEstimate core)
        ∷ Owner.eta (HardSoft.kernelEstimate core)
        ∷ [])

    rightMeaning :
      hardMargin core + HardBase.hardBaseEtaTotal core ≡ 1ℚ
    rightMeaning = solve (HardBase.hardBaseEtaTotal core ∷ [])
  in
  subst₂ _<_ leftMeaning rightMeaning shifted

canonicalRemainingViscosityIsHalfMargin :
  ∀ {environment}
    (core : HardSoft.HardSoftOwnerCore environment)
    (hardStrict : HardBase.hardBaseEtaTotal core < 1ℚ) →
  1ℚ - HardSoft.hardSoftEtaTotal core (halfMarginSplit core hardStrict)
  ≡ halfMarginValue core
canonicalRemainingViscosityIsHalfMargin core hardStrict =
  solve
    ( halfMarginValue core
    ∷ HardSoft.hhBadProfileCeiling core
    ∷ Owner.eta (HardSoft.comEstimate core)
    ∷ Owner.eta (HardSoft.kernelEstimate core)
    ∷ [])

canonicalHardSoftReserve :
  ∀ {environment}
    (core : HardSoft.HardSoftOwnerCore environment)
    (hardStrict : HardBase.hardBaseEtaTotal core < 1ℚ) →
  HardSoft.HardSoftStrictReserveAtSplit
    core (halfMarginSplit core hardStrict)
canonicalHardSoftReserve core hardStrict = record
  { reducedTotalStrict = hardSoftTotalAtCanonicalSplitStrict core hardStrict
  ; reducedRemainingPositive =
      subst
        (0ℚ <_)
        (sym (canonicalRemainingViscosityIsHalfMargin core hardStrict))
        (halfMarginPositive core hardStrict)
  }

strictNineOwnerBudgetFromHardBaseBelowOne :
  ∀ {environment}
    (core : HardSoft.HardSoftOwnerCore environment)
    (tailInput : Tail.PhysicalTailCriticalOwnerInput environment)
    (hardStrict : HardBase.hardBaseEtaTotal core < 1ℚ) →
  Owner.StrictAdmissibleOwnerBudget
    (Owner.nineOwnerList
      (Five.physicalNineOwnerEstimateFamily
        (HardSoft.remainingOwnersAtSplit core
          (halfMarginSplit core hardStrict))
        tailInput))
strictNineOwnerBudgetFromHardBaseBelowOne core tailInput hardStrict =
  HardSoft.strictPhysicalNineOwnerBudgetFromHardSoftReserve
    core
    (halfMarginSplit core hardStrict)
    tailInput
    (canonicalHardSoftReserve core hardStrict)

hardBaseBelowOneIsCompleteFiniteReserveGate : Bool
hardBaseBelowOneIsCompleteFiniteReserveGate = true

hardBaseBelowOneIsCompleteFiniteReserveGateIsTrue :
  hardBaseBelowOneIsCompleteFiniteReserveGate ≡ true
hardBaseBelowOneIsCompleteFiniteReserveGateIsTrue = refl
