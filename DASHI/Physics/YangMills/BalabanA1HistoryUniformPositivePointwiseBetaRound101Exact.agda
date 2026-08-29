{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA1HistoryUniformPositivePointwiseBetaRound101Exact where

------------------------------------------------------------------------
-- ROUND101 A-ARITHMETIC CAPSTONE
--
-- BIDI target: the frozen Row-A compiler needs a pointwise positive lower bound
-- on the SAME current beta over every admissible generated history.
--
-- Forward producers already give:
--   * history-uniform Gaussian floor b;
--   * five-channel current interaction betaInt >= - C_h gamma_h^4;
--   * no second additive history debt (history is already an argument of beta).
--
-- If one finite C uniformly dominates every C_h, choose the constructive
--
--        gamma* = (1/2) b / (C+b).
--
-- and require every admitted history to have gamma_h <= gamma*.  Then this file
-- proves directly
--
--        b/2 <= beta(history).
--
-- Thus after same-object/source instantiation, pointwise positivity itself has
-- no remaining numerical search, fourth root, cumulative history debt or shell
-- summation theorem.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA1HistoryUniformRemainderAntiDoubleCountRound101Exact as Uniform
import DASHI.Physics.YangMills.BalabanA1ExplicitSmallCouplingQuarticAbsorptionRound101Exact as Absorb
import DASHI.Physics.YangMills.BalabanCMP109A1CrossPollinatedDebtProducersExact as Debt
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticBetaAdapterExact as Five
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Beta
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record UniformHistoryPositiveBetaData (History Cell : Set) : Set₁ where
  field
    split : Uniform.HistoryUniformCMP109BetaSplit History Cell

    uniformCoefficient : ℚ
    uniformCoefficientNonnegative : 0ℚ ≤ uniformCoefficient
    gaussianFloorPositive : 0ℚ < Uniform.gaussianFloor split

    coefficientUniform : ∀ history →
      Debt.fiveChannelInteractionCoefficient
        (Uniform.interaction split history)
      ≤ uniformCoefficient

    historyGammaBelowCanonical : ∀ history →
      Debt.gamma (Uniform.interaction split history)
      ≤ Absorb.gammaStar
          uniformCoefficient
          (Uniform.gaussianFloor split)
          uniformCoefficientNonnegative
          gaussianFloorPositive

open UniformHistoryPositiveBetaData public

canonicalGamma :
  ∀ {History Cell} → UniformHistoryPositiveBetaData History Cell → ℚ
canonicalGamma dataSet =
  Absorb.gammaStar
    (uniformCoefficient dataSet)
    (Uniform.gaussianFloor (split dataSet))
    (uniformCoefficientNonnegative dataSet)
    (gaussianFloorPositive dataSet)

historyDebtBelowCanonicalDebt :
  ∀ {History Cell}
    (dataSet : UniformHistoryPositiveBetaData History Cell)
    history →
  Debt.fiveChannelInteractionDebtAtGamma
      (Uniform.interaction (split dataSet) history)
  ≤ uniformCoefficient dataSet * Beta.power4 (canonicalGamma dataSet)
historyDebtBelowCanonicalDebt dataSet history =
  let
    producer = Uniform.interaction (split dataSet) history
    coefficient = Debt.fiveChannelInteractionCoefficient producer
    gamma = Debt.gamma producer

    coefficientNN = Five.coefficientTotalNN (Debt.dataSet producer)
    gammaNN = Debt.gammaNonnegative producer
    canonicalNN = Absorb.gammaStarNonnegative
      (uniformCoefficient dataSet)
      (Uniform.gaussianFloor (split dataSet))
      (uniformCoefficientNonnegative dataSet)
      (gaussianFloorPositive dataSet)

    fourthNN : 0ℚ ≤ Beta.power4 gamma
    fourthNN =
      let squareNN = DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2.squareNonnegative gamma
      in DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2.squareNonnegative (gamma * gamma)

    canonicalFourthNN : 0ℚ ≤ Beta.power4 (canonicalGamma dataSet)
    canonicalFourthNN =
      let squareNN = DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2.squareNonnegative (canonicalGamma dataSet)
      in DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2.squareNonnegative
          (canonicalGamma dataSet * canonicalGamma dataSet)

    fourthBelow = Beta.power4Monotone
      gamma (canonicalGamma dataSet)
      gammaNN canonicalNN (historyGammaBelowCanonical dataSet history)

    coefficientStep :
      coefficient * Beta.power4 gamma
      ≤ uniformCoefficient dataSet * Beta.power4 gamma
    coefficientStep = Norm.scaleRight
      fourthNN (coefficientUniform dataSet history)

    powerStep :
      uniformCoefficient dataSet * Beta.power4 gamma
      ≤ uniformCoefficient dataSet * Beta.power4 (canonicalGamma dataSet)
    powerStep = Norm.scaleNonnegative
      (uniformCoefficient dataSet)
      (uniformCoefficientNonnegative dataSet)
      fourthBelow
  in
  ℚP.≤-trans coefficientStep powerStep

historyDebtBelowHalfFloor :
  ∀ {History Cell}
    (dataSet : UniformHistoryPositiveBetaData History Cell)
    history →
  Debt.fiveChannelInteractionDebtAtGamma
      (Uniform.interaction (split dataSet) history)
  ≤ Beta.half * Uniform.gaussianFloor (split dataSet)
historyDebtBelowHalfFloor dataSet history =
  ℚP.≤-trans
    (historyDebtBelowCanonicalDebt dataSet history)
    (Absorb.explicitQuarticAbsorption
      (uniformCoefficient dataSet)
      (Uniform.gaussianFloor (split dataSet))
      (uniformCoefficientNonnegative dataSet)
      (gaussianFloorPositive dataSet))

halfFloorBelowFloorMinusDebt :
  ∀ floor debt → debt ≤ Beta.half * floor →
  Beta.half * floor ≤ floor - debt
halfFloorBelowFloorMinusDebt floor debt debtBelow =
  let
    negated = ℚP.neg-mono-≤ debtBelow
    shifted = ℚP.+-monoʳ-≤ floor negated
  in
  subst
    (λ left → left ≤ floor - debt)
    (ℚRing.solve-∀ floor)
    (subst
      (λ right → floor + (- (Beta.half * floor)) ≤ right)
      (ℚRing.solve-∀ floor debt)
      shifted)

historyPointwiseBetaPositiveMargin :
  ∀ {History Cell}
    (dataSet : UniformHistoryPositiveBetaData History Cell)
    history →
  Beta.half * Uniform.gaussianFloor (split dataSet)
  ≤ Uniform.beta (split dataSet) history
historyPointwiseBetaPositiveMargin dataSet history =
  let
    producer = Uniform.interaction (split dataSet) history
    debt = Debt.fiveChannelInteractionDebtAtGamma producer
    floor = Uniform.gaussianFloor (split dataSet)
  in
  ℚP.≤-trans
    (halfFloorBelowFloorMinusDebt floor debt
      (historyDebtBelowHalfFloor dataSet history))
    (Uniform.historyUniformCurrentRemainderLower (split dataSet) history)

historyUniformPositivePointwiseBetaRound101Level : ProofLevel
historyUniformPositivePointwiseBetaRound101Level = machineChecked

-- Remaining physical content is source instantiation: one uniform finite C over
-- the full admitted generated history and the literal Gaussian floor on the SAME
-- CMP109 mixed beta jet.  No additional history margin is part of this theorem.
literalHistoryUniformPositivePointwiseBetaLevel : ProofLevel
literalHistoryUniformPositivePointwiseBetaLevel = conditional
