module DASHI.Analysis.RiemannAristotleFarTailCutoffSelectorExact where

------------------------------------------------------------------------
-- S2a CUTOFF SELECTION: SUMMABLE FAR TAIL -> AVAILABLE MARGIN
--
-- Forward input:
--   a quantitative far-tail budget law B_far(J) together with the genuine
--   tail property that every positive allowance can eventually be beaten.
--
-- Backward input:
--   a near-core budget and a cluster margin, together with an explicit positive
--   allowance epsilon satisfying
--
--       B_near + epsilon < M_cluster.
--
-- Meeting theorem:
--   choose J so that B_far(J) < epsilon.  Then automatically
--
--       B_near + B_far(J) < M_cluster.
--
-- This module does not assert that bare convergence supplies a numerical
-- modulus.  A concrete analytic owner must provide the `chooseCutoff` field.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Rational.Base using (ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP

record FarTailDecayLaw : Set where
  constructor far-tail-decay-law
  field
    farBudgetAt : Nat → ℚ

    -- Exact quantitative content required from the summable-tail producer.
    -- It may come from an explicit shell-tail formula or a constructive modulus.
    chooseCutoff :
      (allowance : ℚ) →
      (+ 0 / 1) < allowance →
      Σ Nat (λ J → farBudgetAt J < allowance)

open FarTailDecayLaw public

record RemainingMarginAllowance : Set where
  constructor remaining-margin-allowance
  field
    nearBudget clusterMargin allowance : ℚ
    allowancePositive : (+ 0 / 1) < allowance
    allowanceFitsRemainingMargin :
      nearBudget + allowance < clusterMargin

open RemainingMarginAllowance public

selectedCutoff :
  FarTailDecayLaw → RemainingMarginAllowance → Nat
selectedCutoff law margin =
  proj₁ (chooseCutoff law (allowance margin) (allowancePositive margin))

selectedFarBudgetBelowAllowance :
  (law : FarTailDecayLaw) →
  (margin : RemainingMarginAllowance) →
  farBudgetAt law (selectedCutoff law margin) < allowance margin
selectedFarBudgetBelowAllowance law margin =
  proj₂ (chooseCutoff law (allowance margin) (allowancePositive margin))

selectedCombinedBudgetBelowClusterMargin :
  (law : FarTailDecayLaw) →
  (margin : RemainingMarginAllowance) →
  nearBudget margin + farBudgetAt law (selectedCutoff law margin)
    < clusterMargin margin
selectedCombinedBudgetBelowClusterMargin law margin =
  ℚP.<-trans
    (ℚP.+-monoʳ-< (nearBudget margin)
      (selectedFarBudgetBelowAllowance law margin))
    (allowanceFitsRemainingMargin margin)

------------------------------------------------------------------------
-- Boundary: summability and an explicit cutoff modulus are different claims.
------------------------------------------------------------------------

record FarTailCutoffSelectorBoundary : Set where
  constructor far-tail-cutoff-selector-boundary
  field
    absoluteSummabilityKnownInLean : Bool
    absoluteSummabilityKnownInLeanIsTrue :
      absoluteSummabilityKnownInLean ≡ true

    genericCutoffSelectionCompilerClosed : Bool
    genericCutoffSelectionCompilerClosedIsTrue :
      genericCutoffSelectionCompilerClosed ≡ true

    explicitLeanTailModulusTransportedToAgda : Bool
    explicitLeanTailModulusTransportedToAgdaIsFalse :
      explicitLeanTailModulusTransportedToAgda ≡ false

    cutoffMayIgnoreNearBudgetAndClusterMargin : Bool
    cutoffMayIgnoreNearBudgetAndClusterMarginIsFalse :
      cutoffMayIgnoreNearBudgetAndClusterMargin ≡ false

canonicalFarTailCutoffSelectorBoundary : FarTailCutoffSelectorBoundary
canonicalFarTailCutoffSelectorBoundary =
  far-tail-cutoff-selector-boundary true refl true refl false refl false refl
