module DASHI.Analysis.RiemannAristotlePoleQuotientSplitComplementBudgetExact where

------------------------------------------------------------------------
-- SPLIT COMPLEMENT BUDGET
--
-- The admissible pole-quotient final lane retains exactly two live complement
-- channels at high ordinate:
--
--   offOrdinateZeros + GammaResidual.
--
-- This module compiles independent upper budgets for those channels into the
-- whole-complement budget consumed by the contradiction compiler.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotlePoleQuotientComplementMarginCompilerExact as C

record OrderedAdditiveComplementSurface : Set₁ where
  constructor ordered-additive-complement-surface
  field
    order : C.OrderedComplementSurface
    add : C.Scalar order → C.Scalar order → C.Scalar order
    addMonotone :
      ∀ {a a' b b'} →
      C._≤_ order a a' →
      C._≤_ order b b' →
      C._≤_ order (add a b) (add a' b')

open OrderedAdditiveComplementSurface public

record SplitPoleQuotientComplementMargin
  (S : OrderedAdditiveComplementSurface) : Set where
  constructor split-pole-quotient-complement-margin
  field
    clusterResponse : C.Scalar (order S)
    offOrdinateResponse : C.Scalar (order S)
    gammaResidual : C.Scalar (order S)

    offOrdinateBudget : C.Scalar (order S)
    gammaBudget : C.Scalar (order S)
    clusterMargin : C.Scalar (order S)

    clusterEqualsOffPlusGamma :
      clusterResponse ≡ add S offOrdinateResponse gammaResidual

    clusterMarginLower :
      C._≤_ (order S) clusterMargin clusterResponse

    offOrdinateUpper :
      C._≤_ (order S) offOrdinateResponse offOrdinateBudget

    gammaUpper :
      C._≤_ (order S) gammaResidual gammaBudget

    splitBudgetStrictBelowMargin :
      C._<_ (order S)
        (add S offOrdinateBudget gammaBudget)
        clusterMargin

open SplitPoleQuotientComplementMargin public

compiledWholeComplementMargin :
  (S : OrderedAdditiveComplementSurface) →
  SplitPoleQuotientComplementMargin S →
  C.PoleQuotientComplementMargin (order S)
compiledWholeComplementMargin S d =
  C.pole-quotient-complement-margin
    (clusterResponse d)
    (add S (offOrdinateResponse d) (gammaResidual d))
    (add S (offOrdinateBudget d) (gammaBudget d))
    (clusterMargin d)
    (clusterEqualsOffPlusGamma d)
    (clusterMarginLower d)
    (addMonotone S (offOrdinateUpper d) (gammaUpper d))
    (splitBudgetStrictBelowMargin d)

splitPoleQuotientComplementContradiction :
  (S : OrderedAdditiveComplementSurface) →
  SplitPoleQuotientComplementMargin S →
  ⊥
splitPoleQuotientComplementContradiction S d =
  C.poleQuotientComplementMarginContradiction
    (order S)
    (compiledWholeComplementMargin S d)
