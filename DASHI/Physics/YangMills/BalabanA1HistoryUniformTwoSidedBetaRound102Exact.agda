{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA1HistoryUniformTwoSidedBetaRound102Exact where

------------------------------------------------------------------------
-- ROUND102 A CAPSTONE: HISTORY-UNIFORM FIVE-CHANNEL ABSOLUTE BOUND -> TWO-SIDED BETA
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; -_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Beta
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticBetaAdapterExact as Five
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticAbsoluteBetaRound102Exact as AbsFive
import DASHI.Physics.YangMills.BalabanA1ExplicitSmallCouplingQuarticAbsorptionRound101Exact as Absorb
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2

record HistoryUniformTwoSidedBetaData (History Cell : Set) : Set₁ where
  field
    interaction : History → AbsFive.FiveChannelQuarticAbsoluteBetaData Cell
    gamma : History → ℚ

    couplingNonnegative : ∀ history →
      0ℚ ≤ Five.coupling (AbsFive.lowerData (interaction history))
    gammaNonnegative : ∀ history → 0ℚ ≤ gamma history
    couplingBelowGamma : ∀ history →
      Five.coupling (AbsFive.lowerData (interaction history)) ≤ gamma history

    betaZ beta : History → ℚ
    betaExact : ∀ history →
      beta history ≡
        betaZ history + Five.betaInt (AbsFive.lowerData (interaction history))

    gaussianFloor gaussianCeiling : ℚ
    gaussianFloorPositive : 0ℚ < gaussianFloor
    gaussianLower : ∀ history → gaussianFloor ≤ betaZ history
    gaussianUpper : ∀ history → betaZ history ≤ gaussianCeiling

    uniformCoefficient : ℚ
    uniformCoefficientNonnegative : 0ℚ ≤ uniformCoefficient
    coefficientUniform : ∀ history →
      Five.coefficientTotal (AbsFive.lowerData (interaction history))
      ≤ uniformCoefficient

    historyGammaBelowCanonical : ∀ history →
      gamma history
      ≤ Absorb.gammaStar
          uniformCoefficient gaussianFloor
          uniformCoefficientNonnegative gaussianFloorPositive

open HistoryUniformTwoSidedBetaData public

canonicalGamma :
  ∀ {History Cell} → HistoryUniformTwoSidedBetaData History Cell → ℚ
canonicalGamma dataSet =
  Absorb.gammaStar
    (uniformCoefficient dataSet)
    (gaussianFloor dataSet)
    (uniformCoefficientNonnegative dataSet)
    (gaussianFloorPositive dataSet)

interactionDebtAtGamma :
  ∀ {History Cell} →
  HistoryUniformTwoSidedBetaData History Cell → History → ℚ
interactionDebtAtGamma dataSet history =
  Five.coefficientTotal (AbsFive.lowerData (interaction dataSet history))
    * Beta.power4 (gamma dataSet history)

interactionDebtBelowHalfFloor :
  ∀ {History Cell}
    (dataSet : HistoryUniformTwoSidedBetaData History Cell)
    history →
  interactionDebtAtGamma dataSet history
  ≤ Beta.half * gaussianFloor dataSet
interactionDebtBelowHalfFloor dataSet history =
  let
    data = AbsFive.lowerData (interaction dataSet history)
    g = gamma dataSet history
    canonical = canonicalGamma dataSet
    canonicalNN = Absorb.gammaStarNonnegative
      (uniformCoefficient dataSet) (gaussianFloor dataSet)
      (uniformCoefficientNonnegative dataSet) (gaussianFloorPositive dataSet)

    fourthBelow = Beta.power4Monotone
      g canonical
      (gammaNonnegative dataSet history)
      canonicalNN
      (historyGammaBelowCanonical dataSet history)

    fourthNN = FiniteL2.squareNonnegative (g * g)
    coefficientStep = Norm.scaleRight fourthNN (coefficientUniform dataSet history)
    powerStep = Norm.scaleNonnegative
      (uniformCoefficient dataSet)
      (uniformCoefficientNonnegative dataSet)
      fourthBelow
  in
  ℚP.≤-trans coefficientStep
    (ℚP.≤-trans powerStep
      (Absorb.explicitQuarticAbsorption
        (uniformCoefficient dataSet) (gaussianFloor dataSet)
        (uniformCoefficientNonnegative dataSet) (gaussianFloorPositive dataSet)))

interactionLowerAtGamma :
  ∀ {History Cell}
    (dataSet : HistoryUniformTwoSidedBetaData History Cell)
    history →
  - interactionDebtAtGamma dataSet history
  ≤ Five.betaInt (AbsFive.lowerData (interaction dataSet history))
interactionLowerAtGamma dataSet history =
  Beta.quarticUniformInteractionLower
    (Five.asFiniteInteractionAtomEnclosure
      (AbsFive.lowerData (interaction dataSet history)))
    (gamma dataSet history)
    (couplingNonnegative dataSet history)
    (gammaNonnegative dataSet history)
    (couplingBelowGamma dataSet history)
    (Five.coefficientTotalNN
      (AbsFive.lowerData (interaction dataSet history)))

interactionUpperAtGamma :
  ∀ {History Cell}
    (dataSet : HistoryUniformTwoSidedBetaData History Cell)
    history →
  Five.betaInt (AbsFive.lowerData (interaction dataSet history))
  ≤ interactionDebtAtGamma dataSet history
interactionUpperAtGamma dataSet history =
  let
    data = AbsFive.lowerData (interaction dataSet history)
    coefficient = Five.coefficientTotal data
    coupling = Five.coupling data
    gammaH = gamma dataSet history
    coefficientNN = Five.coefficientTotalNN data
    fourthBelow = Beta.power4Monotone
      coupling gammaH
      (couplingNonnegative dataSet history)
      (gammaNonnegative dataSet history)
      (couplingBelowGamma dataSet history)
    scaled = Norm.scaleNonnegative coefficient coefficientNN fourthBelow
  in
  ℚP.≤-trans (AbsFive.globalQuarticUpper (interaction dataSet history)) scaled

halfFloorBelowBeta :
  ∀ {History Cell}
    (dataSet : HistoryUniformTwoSidedBetaData History Cell)
    history →
  Beta.half * gaussianFloor dataSet ≤ beta dataSet history
halfFloorBelowBeta dataSet history =
  let
    debt = interactionDebtAtGamma dataSet history
    shifted = ℚP.+-mono-≤
      (gaussianLower dataSet history)
      (interactionLowerAtGamma dataSet history)

    halfBelowFloorMinusDebt :
      Beta.half * gaussianFloor dataSet
      ≤ gaussianFloor dataSet + (- debt)
    halfBelowFloorMinusDebt =
      let
        negated = ℚP.neg-mono-≤ (interactionDebtBelowHalfFloor dataSet history)
        added = ℚP.+-monoʳ-≤ (gaussianFloor dataSet) negated
      in
      subst
        (λ left → left ≤ gaussianFloor dataSet + (- debt))
        (ℚRing.solve-∀ (gaussianFloor dataSet))
        added
  in
  ℚP.≤-trans halfBelowFloorMinusDebt
    (subst
      (λ upper → gaussianFloor dataSet + (- debt) ≤ upper)
      (sym (betaExact dataSet history))
      shifted)

betaBelowGaussianCeilingPlusHalfFloor :
  ∀ {History Cell}
    (dataSet : HistoryUniformTwoSidedBetaData History Cell)
    history →
  beta dataSet history
  ≤ gaussianCeiling dataSet + Beta.half * gaussianFloor dataSet
betaBelowGaussianCeilingPlusHalfFloor dataSet history =
  let
    interactionUpper = ℚP.≤-trans
      (interactionUpperAtGamma dataSet history)
      (interactionDebtBelowHalfFloor dataSet history)
    summed = ℚP.+-mono-≤
      (gaussianUpper dataSet history)
      interactionUpper
  in
  subst
    (λ left → left ≤ gaussianCeiling dataSet + Beta.half * gaussianFloor dataSet)
    (sym (betaExact dataSet history))
    summed

historyUniformTwoSidedBetaRound102Level : ProofLevel
historyUniformTwoSidedBetaRound102Level = machineChecked

literalHistoryUniformTwoSidedCMP109BetaLevel : ProofLevel
literalHistoryUniformTwoSidedCMP109BetaLevel = conditional
