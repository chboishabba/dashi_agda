module DASHI.Physics.Closure.NSTriadKNThreeSoftOwnerHardFloorRound46Exact where

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
-- This is the conditional end-state of the Round-46 tax-kind audit.  If the
-- physical Com and kernel producers are eventually proved Young-soft (HH-good
-- already is) and boundary is zero-tax, then the only unavoidable viscosity
-- floor is
--
--   F = 2 C_* + 4/64.
--
-- From F<1 we choose the SAME constructive split
--
--   s = (1-F)/6
--
-- for HH-good, Com and kernel.  Their total soft tax is (1-F)/2, so the full
-- nine-owner eta total is (1+F)/2 < 1 and the remaining viscosity is exactly
-- (1-F)/2.  Thus no optimizer is required and, under the stated softness
-- hypotheses, the finite reserve gate reduces to F<1.
--
-- This file does NOT classify Com or kernel as soft.  It consumes such proofs
-- only if their genuine physical pre-absorption estimates justify them.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; _/_; 1/_; positive; nonNegative)
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

oneSixth : ℚ
oneSixth = Int.+ 1 / 6

oneSixthPositive : 0ℚ < oneSixth
oneSixthPositive = toWitness {a? = 0ℚ <? oneSixth} _

record ThreeSoftOwnerCore
    (environment : Owner.TaxEnvironment) : Set₁ where
  field
    hhGoodSoft : Soft.YoungSoftOwnerFamily environment Tax.HH-good
    comSoft : Soft.YoungSoftOwnerFamily environment Tax.Com
    kernelSoft : Soft.YoungSoftOwnerFamily environment Tax.kernel

    hhBadEstimate : Owner.AdmissibleOwnerEstimate environment
    hhBadOwner : Owner.owner hhBadEstimate ≡ Tax.HH-bad
    hhBadProfileCeiling : ℚ
    hhBadProfileCeilingNonnegative : 0ℚ ≤ hhBadProfileCeiling
    hhBadEtaExact :
      Owner.eta hhBadEstimate ≡ Sharp.two * hhBadProfileCeiling

    boundaryEstimate : Owner.AdmissibleOwnerEstimate environment
    boundaryOwner : Owner.owner boundaryEstimate ≡ Tax.boundary
    boundaryEtaZero : Owner.eta boundaryEstimate ≡ 0ℚ

open ThreeSoftOwnerCore public

irreducibleEtaFloor :
  ∀ {environment} → ThreeSoftOwnerCore environment → ℚ
irreducibleEtaFloor core =
  Sharp.two * hhBadProfileCeiling core
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth
  + Critical.oneSixtyFourth

irreducibleMargin :
  ∀ {environment} → ThreeSoftOwnerCore environment → ℚ
irreducibleMargin core = 1ℚ - irreducibleEtaFloor core

irreducibleMarginPositive :
  ∀ {environment}
    (core : ThreeSoftOwnerCore environment) →
  irreducibleEtaFloor core < 1ℚ →
  0ℚ < irreducibleMargin core
irreducibleMarginPositive core floorStrict = ℚP.-positiveˡ floorStrict

softSplitValue :
  ∀ {environment} → ThreeSoftOwnerCore environment → ℚ
softSplitValue core = oneSixth * irreducibleMargin core

softSplitValuePositive :
  ∀ {environment}
    (core : ThreeSoftOwnerCore environment) →
  irreducibleEtaFloor core < 1ℚ →
  0ℚ < softSplitValue core
softSplitValuePositive core floorStrict =
  let
    instance
      sixthPosI = positive oneSixthPositive
      marginPosI = positive (irreducibleMarginPositive core floorStrict)
      productPosI = ℚP.pos*pos⇒pos oneSixth (irreducibleMargin core)
  in
  ℚP.positive⁻¹ (softSplitValue core)

softSplit :
  ∀ {environment}
    (core : ThreeSoftOwnerCore environment) →
  irreducibleEtaFloor core < 1ℚ →
  Threshold.PositiveThreshold
softSplit core floorStrict =
  let
    value = softSplitValue core
    valuePositive = softSplitValuePositive core floorStrict
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

threeSoftRemainingOwners :
  ∀ {environment}
    (core : ThreeSoftOwnerCore environment)
    (floorStrict : irreducibleEtaFloor core < 1ℚ) →
  Five.FiveRemainingPhysicalOwners environment
threeSoftRemainingOwners core floorStrict =
  let split = softSplit core floorStrict
  in record
  { hhGoodEstimate = Soft.estimateAtSplit (hhGoodSoft core) split
  ; hhBadEstimate = hhBadEstimate core
  ; comEstimate = Soft.estimateAtSplit (comSoft core) split
  ; kernelEstimate = Soft.estimateAtSplit (kernelSoft core) split
  ; boundaryEstimate = boundaryEstimate core
  ; hhGoodOwner = Soft.ownerAtSplit (hhGoodSoft core) split
  ; hhBadOwner = hhBadOwner core
  ; comOwner = Soft.ownerAtSplit (comSoft core) split
  ; kernelOwner = Soft.ownerAtSplit (kernelSoft core) split
  ; boundaryOwner = boundaryOwner core
  }

threeSoftEtaTotalExact :
  ∀ {environment}
    (core : ThreeSoftOwnerCore environment)
    (floorStrict : irreducibleEtaFloor core < 1ℚ) →
  Five.fiveOwnerEtaTotal (threeSoftRemainingOwners core floorStrict)
  ≡ irreducibleEtaFloor core
    + Sharp.half * irreducibleMargin core
threeSoftEtaTotalExact core floorStrict
  rewrite Soft.etaAtSplit (hhGoodSoft core) (softSplit core floorStrict)
        | Soft.etaAtSplit (comSoft core) (softSplit core floorStrict)
        | Soft.etaAtSplit (kernelSoft core) (softSplit core floorStrict)
        | hhBadEtaExact core
        | boundaryEtaZero core =
  solve
    ( softSplitValue core
    ∷ hhBadProfileCeiling core
    ∷ Critical.oneSixtyFourth
    ∷ irreducibleMargin core
    ∷ [])

halfMarginLessThanMargin :
  ∀ {environment}
    (core : ThreeSoftOwnerCore environment)
    (floorStrict : irreducibleEtaFloor core < 1ℚ) →
  Sharp.half * irreducibleMargin core < irreducibleMargin core
halfMarginLessThanMargin core floorStrict =
  let
    halfLessThanOne : Sharp.half < 1ℚ
    halfLessThanOne = toWitness {a? = Sharp.half <? 1ℚ} _
    instance marginPosI = positive (irreducibleMarginPositive core floorStrict)
    scaled :
      Sharp.half * irreducibleMargin core
      < 1ℚ * irreducibleMargin core
    scaled = ℚP.*-monoˡ-<-pos (irreducibleMargin core) halfLessThanOne
  in
  subst
    (λ upper → Sharp.half * irreducibleMargin core < upper)
    (solve (irreducibleMargin core ∷ []))
    scaled

threeSoftTotalStrict :
  ∀ {environment}
    (core : ThreeSoftOwnerCore environment)
    (floorStrict : irreducibleEtaFloor core < 1ℚ) →
  Five.fiveOwnerEtaTotal (threeSoftRemainingOwners core floorStrict) < 1ℚ
threeSoftTotalStrict core floorStrict =
  let
    halfBelow = halfMarginLessThanMargin core floorStrict
    shifted :
      irreducibleEtaFloor core + Sharp.half * irreducibleMargin core
      < irreducibleEtaFloor core + irreducibleMargin core
    shifted = ℚP.+-mono-≤-< ℚP.≤-refl halfBelow

    rightMeaning :
      irreducibleEtaFloor core + irreducibleMargin core ≡ 1ℚ
    rightMeaning = solve (irreducibleEtaFloor core ∷ [])
  in
  subst₂ _<_
    (sym (threeSoftEtaTotalExact core floorStrict))
    rightMeaning
    shifted

threeSoftRemainingViscosityExact :
  ∀ {environment}
    (core : ThreeSoftOwnerCore environment)
    (floorStrict : irreducibleEtaFloor core < 1ℚ) →
  1ℚ - Five.fiveOwnerEtaTotal (threeSoftRemainingOwners core floorStrict)
  ≡ Sharp.half * irreducibleMargin core
threeSoftRemainingViscosityExact core floorStrict =
  subst
    (λ total →
      1ℚ - Five.fiveOwnerEtaTotal (threeSoftRemainingOwners core floorStrict)
      ≡ 1ℚ - total)
    (threeSoftEtaTotalExact core floorStrict)
    (solve (irreducibleEtaFloor core ∷ irreducibleMargin core ∷ []))

hhBadEtaNonnegative :
  ∀ {environment} (core : ThreeSoftOwnerCore environment) →
  0ℚ ≤ Owner.eta (hhBadEstimate core)
hhBadEtaNonnegative core =
  let instance
    twoNNI = nonNegative Scale.twoNonnegative
    ceilingNNI = nonNegative (hhBadProfileCeilingNonnegative core)
    productNNI =
      ℚP.nonNeg*nonNeg⇒nonNeg Sharp.two (hhBadProfileCeiling core)
    productNN = ℚP.nonNegative⁻¹ (Sharp.two * hhBadProfileCeiling core)
  in
  subst (0ℚ ≤_) (sym (hhBadEtaExact core)) productNN

threeSoftStrictReserveInput :
  ∀ {environment}
    (core : ThreeSoftOwnerCore environment)
    (floorStrict : irreducibleEtaFloor core < 1ℚ) →
  Five.FiveOwnerStrictReserveInput (threeSoftRemainingOwners core floorStrict)
threeSoftStrictReserveInput core floorStrict =
  let split = softSplit core floorStrict
      splitNN = Threshold.thresholdNonnegative split
      remainingPositive :
        0ℚ < 1ℚ - Five.fiveOwnerEtaTotal
          (threeSoftRemainingOwners core floorStrict)
      remainingPositive =
        subst
          (0ℚ <_)
          (sym (threeSoftRemainingViscosityExact core floorStrict))
          (let
             halfPositive : 0ℚ < Sharp.half
             halfPositive = toWitness {a? = 0ℚ <? Sharp.half} _
             instance
               halfPosI = positive halfPositive
               marginPosI = positive (irreducibleMarginPositive core floorStrict)
               productPosI = ℚP.pos*pos⇒pos Sharp.half (irreducibleMargin core)
           in ℚP.positive⁻¹ (Sharp.half * irreducibleMargin core))
  in record
  { hhGoodEtaNonnegative =
      subst (0ℚ ≤_) (sym (Soft.etaAtSplit (hhGoodSoft core) split)) splitNN
  ; hhBadEtaNonnegative = hhBadEtaNonnegative core
  ; comEtaNonnegative =
      subst (0ℚ ≤_) (sym (Soft.etaAtSplit (comSoft core) split)) splitNN
  ; kernelEtaNonnegative =
      subst (0ℚ ≤_) (sym (Soft.etaAtSplit (kernelSoft core) split)) splitNN
  ; boundaryEtaNonnegative =
      subst (0ℚ ≤_) (sym (boundaryEtaZero core)) ℚP.≤-refl
  ; fiveOwnerTotalStrict = threeSoftTotalStrict core floorStrict
  ; fiveOwnerRemainingPositive = remainingPositive
  }

strictNineOwnerBudgetFromIrreducibleFloorBelowOne :
  ∀ {environment}
    (core : ThreeSoftOwnerCore environment)
    (tailInput : Tail.PhysicalTailCriticalOwnerInput environment)
    (floorStrict : irreducibleEtaFloor core < 1ℚ) →
  Owner.StrictAdmissibleOwnerBudget
    (Owner.nineOwnerList
      (Five.physicalNineOwnerEstimateFamily
        (threeSoftRemainingOwners core floorStrict)
        tailInput))
strictNineOwnerBudgetFromIrreducibleFloorBelowOne core tailInput floorStrict =
  Five.strictPhysicalNineOwnerBudget
    (threeSoftRemainingOwners core floorStrict)
    tailInput
    (threeSoftStrictReserveInput core floorStrict)

threeSoftConditionalGateReducedToHHBadPlusOneSixteenth : Bool
threeSoftConditionalGateReducedToHHBadPlusOneSixteenth = true

threeSoftConditionalGateReducedToHHBadPlusOneSixteenthIsTrue :
  threeSoftConditionalGateReducedToHHBadPlusOneSixteenth ≡ true
threeSoftConditionalGateReducedToHHBadPlusOneSixteenthIsTrue = refl
