module DASHI.Physics.Closure.NSTriadKNComSoftHardGateRound47Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- Proceedings of the Royal Society of London. Series A 87 (1912).
-- DOI: 10.1098/rspa.1912.0086.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Gyula Farkas.
-- Title: "Theorie der einfachen Ungleichungen".
-- Journal fuer die reine und angewandte Mathematik 124 (1902), 1--27.
-- DOI: no DOI assigned to the historical article.
--
-- DASHI CONTRIBUTION
--
-- Make the H2 -> H1 gate transition operational.  If Com is proved Young-soft
-- while kernel remains a fixed physical owner, define
--
--   H1 = 2 C_* + eta_kernel + 4/64.
--
-- From H1<1 choose the SAME split
--
--   epsilon_HHg = epsilon_Com = (1-H1)/4.
--
-- The two soft taxes sum to (1-H1)/2, hence total eta is
--
--   (1+H1)/2 < 1
--
-- with residual viscosity (1-H1)/2.  Thus a Com softness proof really removes
-- eta_Com from the hard gate; it is not replaced by a tiny provisional floor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_; _≤_; _<_; 1/_; positive; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCriticalFourClassClosureExact as Critical
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as Scale
import DASHI.Physics.Closure.NSTriadKNHHGoodYoungSoftTaxRound45Exact as Soft
import DASHI.Physics.Closure.NSTriadKNFiveOwnerReserveReductionRound44Exact as Five
import DASHI.Physics.Closure.NSTriadKNBonyTailOwnerRound44Exact as Tail

oneFourth : ℚ
oneFourth = Int.+ 1 / 4

oneFourthPositive : 0ℚ < oneFourth
oneFourthPositive = toWitness {a? = 0ℚ <? oneFourth} _

record ComSoftKernelHardCore
    (environment : Owner.TaxEnvironment) : Set₁ where
  field
    hhGoodSoft : Soft.YoungSoftOwnerFamily environment Tax.HH-good
    comSoft : Soft.YoungSoftOwnerFamily environment Tax.Com

    hhBadEstimate : Owner.AdmissibleOwnerEstimate environment
    hhBadOwner : Owner.owner hhBadEstimate ≡ Tax.HH-bad
    hhBadProfileCeiling : ℚ
    hhBadProfileCeilingNonnegative : 0ℚ ≤ hhBadProfileCeiling
    hhBadEtaExact : Owner.eta hhBadEstimate ≡ Sharp.two * hhBadProfileCeiling

    kernelEstimate : Owner.AdmissibleOwnerEstimate environment
    kernelOwner : Owner.owner kernelEstimate ≡ Tax.kernel
    kernelEtaNonnegative : 0ℚ ≤ Owner.eta kernelEstimate

    boundaryEstimate : Owner.AdmissibleOwnerEstimate environment
    boundaryOwner : Owner.owner boundaryEstimate ≡ Tax.boundary
    boundaryEtaZero : Owner.eta boundaryEstimate ≡ 0ℚ

open ComSoftKernelHardCore public

hardGateH1 :
  ∀ {environment} → ComSoftKernelHardCore environment → ℚ
hardGateH1 core =
  Sharp.two * hhBadProfileCeiling core
  + Owner.eta (kernelEstimate core)
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth

h1Margin :
  ∀ {environment} → ComSoftKernelHardCore environment → ℚ
h1Margin core = 1ℚ - hardGateH1 core

h1MarginPositive :
  ∀ {environment} (core : ComSoftKernelHardCore environment) →
  hardGateH1 core < 1ℚ → 0ℚ < h1Margin core
h1MarginPositive core strict = ℚP.-positiveˡ strict

softSplitValue :
  ∀ {environment} → ComSoftKernelHardCore environment → ℚ
softSplitValue core = oneFourth * h1Margin core

softSplitValuePositive :
  ∀ {environment} (core : ComSoftKernelHardCore environment) →
  hardGateH1 core < 1ℚ → 0ℚ < softSplitValue core
softSplitValuePositive core strict =
  let instance
    fourthPosI = positive oneFourthPositive
    marginPosI = positive (h1MarginPositive core strict)
    productPosI = ℚP.pos*pos⇒pos oneFourth (h1Margin core)
  in ℚP.positive⁻¹ (softSplitValue core)

canonicalSoftSplit :
  ∀ {environment} (core : ComSoftKernelHardCore environment) →
  hardGateH1 core < 1ℚ → Threshold.PositiveThreshold
canonicalSoftSplit core strict =
  let
    value = softSplitValue core
    valuePositive = softSplitValuePositive core strict
    instance
      valuePosI = positive valuePositive
      valueNonzeroI = ℚP.pos⇒nonZero value
      inversePositiveI = ℚP.1/pos⇒pos value
  in
  Threshold.positive-threshold
    value
    (ℚ.1/_ value)
    valuePositive
    (ℚP.<⇒≤ (ℚP.positive⁻¹ (ℚ.1/_ value)))
    (ℚP.*-inverseˡ value)

remainingOwners :
  ∀ {environment}
    (core : ComSoftKernelHardCore environment)
    (strict : hardGateH1 core < 1ℚ) →
  Five.FiveRemainingPhysicalOwners environment
remainingOwners core strict =
  let split = canonicalSoftSplit core strict
  in record
  { hhGoodEstimate = Soft.estimateAtSplit (hhGoodSoft core) split
  ; hhBadEstimate = hhBadEstimate core
  ; comEstimate = Soft.estimateAtSplit (comSoft core) split
  ; kernelEstimate = kernelEstimate core
  ; boundaryEstimate = boundaryEstimate core
  ; hhGoodOwner = Soft.ownerAtSplit (hhGoodSoft core) split
  ; hhBadOwner = hhBadOwner core
  ; comOwner = Soft.ownerAtSplit (comSoft core) split
  ; kernelOwner = kernelOwner core
  ; boundaryOwner = boundaryOwner core
  }

fiveOwnerTotalExact :
  ∀ {environment}
    (core : ComSoftKernelHardCore environment)
    (strict : hardGateH1 core < 1ℚ) →
  Five.fiveOwnerEtaTotal (remainingOwners core strict)
  ≡ hardGateH1 core + Sharp.half * h1Margin core
fiveOwnerTotalExact core strict
  rewrite Soft.etaAtSplit (hhGoodSoft core) (canonicalSoftSplit core strict)
        | Soft.etaAtSplit (comSoft core) (canonicalSoftSplit core strict)
        | hhBadEtaExact core
        | boundaryEtaZero core =
  solve
    ( hhBadProfileCeiling core
    ∷ Owner.eta (kernelEstimate core)
    ∷ Critical.oneSixtyFourth
    ∷ hardGateH1 core
    ∷ [])

halfMarginPositive :
  ∀ {environment} (core : ComSoftKernelHardCore environment) →
  hardGateH1 core < 1ℚ →
  0ℚ < Sharp.half * h1Margin core
halfMarginPositive core strict =
  let
    halfPositive : 0ℚ < Sharp.half
    halfPositive = toWitness {a? = 0ℚ <? Sharp.half} _
    instance
      halfPosI = positive halfPositive
      marginPosI = positive (h1MarginPositive core strict)
      productPosI = ℚP.pos*pos⇒pos Sharp.half (h1Margin core)
  in ℚP.positive⁻¹ (Sharp.half * h1Margin core)

fiveOwnerTotalStrict :
  ∀ {environment}
    (core : ComSoftKernelHardCore environment)
    (strict : hardGateH1 core < 1ℚ) →
  Five.fiveOwnerEtaTotal (remainingOwners core strict) < 1ℚ
fiveOwnerTotalStrict core strict =
  let
    halfLessOne : Sharp.half < 1ℚ
    halfLessOne = toWitness {a? = Sharp.half <? 1ℚ} _
    instance marginPosI = positive (h1MarginPositive core strict)

    halfBelowMargin :
      Sharp.half * h1Margin core < h1Margin core
    halfBelowMargin =
      subst
        (λ upper → Sharp.half * h1Margin core < upper)
        (solve (h1Margin core ∷ []))
        (ℚP.*-monoˡ-<-pos (h1Margin core) halfLessOne)

    shifted :
      hardGateH1 core + Sharp.half * h1Margin core
      < hardGateH1 core + h1Margin core
    shifted = ℚP.+-mono-≤-< ℚP.≤-refl halfBelowMargin

    rightMeaning : hardGateH1 core + h1Margin core ≡ 1ℚ
    rightMeaning = solve (hardGateH1 core ∷ [])
  in
  subst₂ _<_
    (sym (fiveOwnerTotalExact core strict))
    rightMeaning
    shifted

remainingViscosityExact :
  ∀ {environment}
    (core : ComSoftKernelHardCore environment)
    (strict : hardGateH1 core < 1ℚ) →
  1ℚ - Five.fiveOwnerEtaTotal (remainingOwners core strict)
  ≡ Sharp.half * h1Margin core
remainingViscosityExact core strict
  rewrite fiveOwnerTotalExact core strict =
  solve (hardGateH1 core ∷ [])

hhBadEtaNonnegative :
  ∀ {environment} (core : ComSoftKernelHardCore environment) →
  0ℚ ≤ Owner.eta (hhBadEstimate core)
hhBadEtaNonnegative core =
  let instance
    twoNNI = nonNegative Scale.twoNonnegative
    ceilingNNI = nonNegative (hhBadProfileCeilingNonnegative core)
    productNNI =
      ℚP.nonNeg*nonNeg⇒nonNeg Sharp.two (hhBadProfileCeiling core)
  in
  subst (0ℚ ≤_)
    (sym (hhBadEtaExact core))
    (ℚP.nonNegative⁻¹ (Sharp.two * hhBadProfileCeiling core))

reserveInput :
  ∀ {environment}
    (core : ComSoftKernelHardCore environment)
    (strict : hardGateH1 core < 1ℚ) →
  Five.FiveOwnerStrictReserveInput (remainingOwners core strict)
reserveInput core strict =
  let
    split = canonicalSoftSplit core strict
    splitNN = Threshold.thresholdNonnegative split
    residualPositive :
      0ℚ < 1ℚ - Five.fiveOwnerEtaTotal (remainingOwners core strict)
    residualPositive =
      subst
        (0ℚ <_)
        (sym (remainingViscosityExact core strict))
        (halfMarginPositive core strict)
  in record
  { hhGoodEtaNonnegative =
      subst (0ℚ ≤_) (sym (Soft.etaAtSplit (hhGoodSoft core) split)) splitNN
  ; hhBadEtaNonnegative = hhBadEtaNonnegative core
  ; comEtaNonnegative =
      subst (0ℚ ≤_) (sym (Soft.etaAtSplit (comSoft core) split)) splitNN
  ; kernelEtaNonnegative = kernelEtaNonnegative core
  ; boundaryEtaNonnegative =
      subst (0ℚ ≤_) (sym (boundaryEtaZero core)) ℚP.≤-refl
  ; fiveOwnerTotalStrict = fiveOwnerTotalStrict core strict
  ; fiveOwnerRemainingPositive = residualPositive
  }

strictNineOwnerBudgetFromH1BelowOne :
  ∀ {environment}
    (core : ComSoftKernelHardCore environment)
    (tailInput : Tail.PhysicalTailCriticalOwnerInput environment)
    (strict : hardGateH1 core < 1ℚ) →
  Owner.StrictAdmissibleOwnerBudget
    (Owner.nineOwnerList
      (Five.physicalNineOwnerEstimateFamily
        (remainingOwners core strict) tailInput))
strictNineOwnerBudgetFromH1BelowOne core tailInput strict =
  Five.strictPhysicalNineOwnerBudget
    (remainingOwners core strict)
    tailInput
    (reserveInput core strict)

comSoftnessRemovesComFromHardGate : Bool
comSoftnessRemovesComFromHardGate = true

comSoftnessRemovesComFromHardGateIsTrue :
  comSoftnessRemovesComFromHardGate ≡ true
comSoftnessRemovesComFromHardGateIsTrue = refl
