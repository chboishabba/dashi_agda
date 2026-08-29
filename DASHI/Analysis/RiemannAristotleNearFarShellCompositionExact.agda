module DASHI.Analysis.RiemannAristotleNearFarShellCompositionExact where

------------------------------------------------------------------------
-- S2 COMPOSITION: ANALYTIC PRODUCERS -> WHOLE-CARRIER CONTRADICTION
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; _+_; _≤_; _<_)

import DASHI.Analysis.RiemannAristotleNearFarShellBudgetCompilerExact as Budget
import DASHI.Analysis.RiemannAristotleNearFarShellProducerSocketsExact as Socket

record NearFarAnalyticClosure : Set where
  constructor near-far-analytic-closure
  field
    near : Socket.FiniteSignedNearShellCore
    far : Socket.FarShellQuantitativeEnvelope
    compatible : Socket.CompatibleNearFarProducers near far

    offResidualSq clusterMargin : ℚ

    offSplitBound :
      offResidualSq
        ≤ Socket.signedNearContribution near
          + Socket.farContribution far

    combinedBudgetBelowClusterMargin :
      Socket.nearBudget near + Socket.farBudget far < clusterMargin

open NearFarAnalyticClosure public

compiledNearFarBudget :
  (d : NearFarAnalyticClosure) → Budget.NearFarShellBudget
compiledNearFarBudget d =
  record
    { cutoff = Socket.nearCutoff (near d)
    ; offResidualSq = offResidualSq d
    ; nearContribution = Socket.signedNearContribution (near d)
    ; farContribution = Socket.farContribution (far d)
    ; nearBudget = Socket.nearBudget (near d)
    ; farBudget = Socket.farBudget (far d)
    ; clusterMargin = clusterMargin d
    ; offSplitBound = offSplitBound d
    ; nearBound = Socket.signedAggregateBound (near d)
    ; farBound = Socket.farContributionBound (far d)
    ; combinedBudgetBelowClusterMargin = combinedBudgetBelowClusterMargin d
    }

analyticClosureStrictlyBelowClusterMargin :
  (d : NearFarAnalyticClosure) →
  offResidualSq d < clusterMargin d
analyticClosureStrictlyBelowClusterMargin d =
  Budget.offResidualStrictlyBelowClusterMargin (compiledNearFarBudget d)

analyticClosureContradictsExactSchur :
  (d : NearFarAnalyticClosure) →
  clusterMargin d ≡ offResidualSq d →
  ⊥
analyticClosureContradictsExactSchur d exactSchur =
  Budget.nearFarShellBudgetContradictsExactSchur
    (compiledNearFarBudget d)
    exactSchur

record NearFarCompositionBoundary : Set where
  constructor near-far-composition-boundary
  field
    compositionCompilerClosed : Bool
    compositionCompilerClosedIsTrue : compositionCompilerClosed ≡ true
    farAnalyticProducerClosed : Bool
    farAnalyticProducerClosedIsFalse : farAnalyticProducerClosed ≡ false
    nearSignedProducerClosed : Bool
    nearSignedProducerClosedIsFalse : nearSignedProducerClosed ≡ false
    strictCombinedMarginClosed : Bool
    strictCombinedMarginClosedIsFalse : strictCombinedMarginClosed ≡ false

canonicalNearFarCompositionBoundary : NearFarCompositionBoundary
canonicalNearFarCompositionBoundary =
  near-far-composition-boundary true refl false refl false refl false refl
