module DASHI.Analysis.RiemannAristotleWholeCarrierCancellationCompilerExact where

------------------------------------------------------------------------
-- CORRECT BIDI READING OF THE POST-SCHUR WHOLE-CARRIER SOCKET
--
-- In the literal projective balance, after the short-support prime channel is
-- zero and deterministic Gamma/pole vectors are eliminated exactly,
--
--   E D_cluster = E D_off.
--
-- Here `D_off` is the complement of `SameOrd t`; it does NOT contain the target
-- same-ordinate cluster.  Therefore a theorem proving
--
--   ||E D_off||^2 <= B_far < ||E D_cluster||^2
--
-- is not an invalid target: combined with the exact identity it is precisely
-- the desired contradiction.  What the no-go says is only that this strict
-- inequality cannot be manufactured by the elimination algebra itself.  It
-- must come from genuine signed cancellation analysis of the off-ordinate zero
-- carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP

record WholeCarrierCancellationMargin : Set where
  constructor whole-carrier-cancellation-margin
  field
    clusterResidualSq offResidualSq farBudget : ℚ
    exactSchurIdentity : clusterResidualSq ≡ offResidualSq
    analyticFarBound : offResidualSq ≤ farBudget
    farBudgetBelowClusterMargin : farBudget < clusterResidualSq

open WholeCarrierCancellationMargin public

wholeCarrierCancellationContradiction :
  (d : WholeCarrierCancellationMargin) → ⊥
wholeCarrierCancellationContradiction d =
  let
    cluster≤budget : clusterResidualSq d ≤ farBudget d
    cluster≤budget =
      subst (λ x → x ≤ farBudget d) (sym (exactSchurIdentity d)) (analyticFarBound d)
  in
  ℚP.<-irrefl refl
    (ℚP.<-≤-trans (farBudgetBelowClusterMargin d) cluster≤budget)
  where
    open import Relation.Binary.PropositionalEquality using (subst; sym)

record WholeCarrierCancellationBoundary : Set where
  constructor whole-carrier-cancellation-boundary
  field
    offCarrierContainsSameOrdinateTargetCluster : Bool
    offCarrierContainsSameOrdinateTargetClusterIsFalse :
      offCarrierContainsSameOrdinateTargetCluster ≡ false
    strictWholeOffCarrierBoundIsValidContradictionTarget : Bool
    strictWholeOffCarrierBoundIsValidContradictionTargetIsTrue :
      strictWholeOffCarrierBoundIsValidContradictionTarget ≡ true
    eliminationAlgebraAloneCanProduceStrictBound : Bool
    eliminationAlgebraAloneCanProduceStrictBoundIsFalse :
      eliminationAlgebraAloneCanProduceStrictBound ≡ false
    signedCancellationAnalysisRequired : Bool
    signedCancellationAnalysisRequiredIsTrue :
      signedCancellationAnalysisRequired ≡ true

canonicalWholeCarrierCancellationBoundary : WholeCarrierCancellationBoundary
canonicalWholeCarrierCancellationBoundary =
  whole-carrier-cancellation-boundary false refl true refl false refl true refl
