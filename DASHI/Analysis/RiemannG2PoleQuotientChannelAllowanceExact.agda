module DASHI.Analysis.RiemannG2PoleQuotientChannelAllowanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact as Split
import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as Complement

------------------------------------------------------------------------
-- FINAL POLE-QUOTIENT CHANNEL ALLOWANCE COMPILER
--
-- Reuse the producer-friendly allowance pattern already present in the Riemann
-- near/far and finite-Schur lanes.  The downstream consumer chooses separate
-- channel allowances and proves their SUM lies strictly below the quantitative
-- cluster margin.  The off/Gamma producers only have to prove their actual
-- budgets lie below the assigned allowances.
--
-- No division, subtraction, positivity, midpoint, or "half the margin" theorem
-- is assumed.  This matches the deliberately weak final ordered-additive
-- carrier.
------------------------------------------------------------------------

record PoleQuotientChannelAllowance
    (surface : Split.OrderedAdditiveComplementSurface) : Set₁ where
  private
    S = Split.order surface
  field
    offBudget gammaBudget : Complement.Scalar S
    offAllowance gammaAllowance : Complement.Scalar S
    clusterMargin : Complement.Scalar S

    offBudgetBelowAllowance :
      Complement._≤_ S offBudget offAllowance

    gammaBudgetBelowAllowance :
      Complement._≤_ S gammaBudget gammaAllowance

    allowancesStrictBelowMargin :
      Complement._<_ S
        (Split.add surface offAllowance gammaAllowance)
        clusterMargin

open PoleQuotientChannelAllowance public

combinedBudgetsBelowCombinedAllowances :
  ∀ {surface} →
  (d : PoleQuotientChannelAllowance surface) →
  Complement._≤_ (Split.order surface)
    (Split.add surface (offBudget d) (gammaBudget d))
    (Split.add surface (offAllowance d) (gammaAllowance d))
combinedBudgetsBelowCombinedAllowances {surface} d =
  Split.addMonotone surface
    (offBudgetBelowAllowance d)
    (gammaBudgetBelowAllowance d)

combinedBudgetsStrictBelowMargin :
  ∀ {surface} →
  (d : PoleQuotientChannelAllowance surface) →
  Complement._<_ (Split.order surface)
    (Split.add surface (offBudget d) (gammaBudget d))
    (clusterMargin d)
combinedBudgetsStrictBelowMargin {surface} d =
  Complement.leLtTrans (Split.order surface)
    (combinedBudgetsBelowCombinedAllowances d)
    (allowancesStrictBelowMargin d)

------------------------------------------------------------------------
-- Compiler into the existing split-complement final consumer.
--
-- This keeps the analytic producers separate from the final strict-window
-- allocation.  Once a split record has all literal response/budget identities,
-- an allowance receipt can replace only its final strict-budget field.
------------------------------------------------------------------------

record SplitInputsExceptStrictBudget
    (surface : Split.OrderedAdditiveComplementSurface) : Set₁ where
  field
    clusterResponse : Complement.Scalar (Split.order surface)
    offOrdinateResponse : Complement.Scalar (Split.order surface)
    gammaResidual : Complement.Scalar (Split.order surface)

    offOrdinateBudget : Complement.Scalar (Split.order surface)
    gammaBudget : Complement.Scalar (Split.order surface)
    clusterMargin : Complement.Scalar (Split.order surface)

    clusterEqualsOffPlusGamma :
      clusterResponse ≡ Split.add surface offOrdinateResponse gammaResidual

    clusterMarginLower :
      Complement._≤_ (Split.order surface) clusterMargin clusterResponse

    offOrdinateUpper :
      Complement._≤_ (Split.order surface) offOrdinateResponse offOrdinateBudget

    gammaUpper :
      Complement._≤_ (Split.order surface) gammaResidual gammaBudget

open SplitInputsExceptStrictBudget public

allowanceToSplitComplementMargin :
  ∀ {surface} →
  (inputs : SplitInputsExceptStrictBudget surface) →
  (allowance : PoleQuotientChannelAllowance surface) →
  offBudget allowance ≡ offOrdinateBudget inputs →
  gammaBudget allowance ≡ gammaBudget inputs →
  clusterMargin allowance ≡ clusterMargin inputs →
  Split.SplitPoleQuotientComplementMargin surface
allowanceToSplitComplementMargin {surface} inputs allowance refl refl refl =
  Split.split-pole-quotient-complement-margin
    (clusterResponse inputs)
    (offOrdinateResponse inputs)
    (gammaResidual inputs)
    (offOrdinateBudget inputs)
    (gammaBudget inputs)
    (clusterMargin inputs)
    (clusterEqualsOffPlusGamma inputs)
    (clusterMarginLower inputs)
    (offOrdinateUpper inputs)
    (gammaUpper inputs)
    (combinedBudgetsStrictBelowMargin allowance)

allowanceContradiction :
  ∀ {surface} →
  (inputs : SplitInputsExceptStrictBudget surface) →
  (allowance : PoleQuotientChannelAllowance surface) →
  offBudget allowance ≡ offOrdinateBudget inputs →
  gammaBudget allowance ≡ gammaBudget inputs →
  clusterMargin allowance ≡ clusterMargin inputs →
  ⊥
allowanceContradiction {surface} inputs allowance hoff hgamma hmargin =
  Split.splitPoleQuotientComplementContradiction surface
    (allowanceToSplitComplementMargin
      inputs allowance hoff hgamma hmargin)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record PoleQuotientChannelAllowanceBoundary : Set where
  constructor pole-quotient-channel-allowance-boundary
  field
    consumerChoosesChannelAllowances : Bool
    consumerChoosesChannelAllowancesIsTrue :
      consumerChoosesChannelAllowances ≡ true

    producerMayChooseAdequacyPredicate : Bool
    producerMayChooseAdequacyPredicateIsFalse :
      producerMayChooseAdequacyPredicate ≡ false

    halfMarginDivisionRequired : Bool
    halfMarginDivisionRequiredIsFalse :
      halfMarginDivisionRequired ≡ false

    separateProducerBoundsCompileToStrictCombinedBudget : Bool
    separateProducerBoundsCompileToStrictCombinedBudgetIsTrue :
      separateProducerBoundsCompileToStrictCombinedBudget ≡ true

    finalContradictionCompilerReused : Bool
    finalContradictionCompilerReusedIsTrue :
      finalContradictionCompilerReused ≡ true

canonicalPoleQuotientChannelAllowanceBoundary :
  PoleQuotientChannelAllowanceBoundary
canonicalPoleQuotientChannelAllowanceBoundary =
  pole-quotient-channel-allowance-boundary
    true refl
    false refl
    false refl
    true refl
    true refl
