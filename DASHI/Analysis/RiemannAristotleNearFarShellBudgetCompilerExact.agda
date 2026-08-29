module DASHI.Analysis.RiemannAristotleNearFarShellBudgetCompilerExact where

------------------------------------------------------------------------
-- S2 BIDI COMPILER: FINITE SIGNED CORE + SUMMABLE FAR SHELLS
--
-- The newest Lean tranche proves absolute convergence of the reflection-paired
-- far zero carrier.  The remaining strict cancellation theorem should therefore
-- be allowed to split at an explicit shell cutoff J:
--
--   R_off <= R_near(J) + R_far(J)
--         <= B_near(J) + B_far(J)
--          < M_cluster.
--
-- This module owns only that order-theoretic composition.  It deliberately does
-- NOT manufacture either analytic bound.  In particular:
--
--   * B_far must come from the kernel-checked curvature / delta^-2 shell lane;
--   * B_near must come from finite signed/oscillatory analysis of the remaining
--     nearby shells;
--   * the strict sum-of-budgets margin is a genuine analytic input.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP

import DASHI.Analysis.RiemannAristotleWholeCarrierCancellationCompilerExact as Whole

record NearFarShellBudget : Set where
  constructor near-far-shell-budget
  field
    cutoff : Nat

    offResidualSq : ℚ
    nearContribution farContribution : ℚ
    nearBudget farBudget : ℚ
    clusterMargin : ℚ

    -- Domain owner: the literal post-Schur off carrier is bounded by the sum of
    -- the two cutoff pieces.  This can be equality or a norm/triangle estimate;
    -- the compiler does not force either representation.
    offSplitBound :
      offResidualSq ≤ nearContribution + farContribution

    nearBound : nearContribution ≤ nearBudget
    farBound : farContribution ≤ farBudget

    combinedBudgetBelowClusterMargin :
      nearBudget + farBudget < clusterMargin

open NearFarShellBudget public

piecesBelowCombinedBudget :
  (d : NearFarShellBudget) →
  nearContribution d + farContribution d
    ≤ nearBudget d + farBudget d
piecesBelowCombinedBudget d =
  ℚP.+-mono-≤ (nearBound d) (farBound d)

offResidualBelowCombinedBudget :
  (d : NearFarShellBudget) →
  offResidualSq d ≤ nearBudget d + farBudget d
offResidualBelowCombinedBudget d =
  ℚP.≤-trans (offSplitBound d) (piecesBelowCombinedBudget d)

offResidualStrictlyBelowClusterMargin :
  (d : NearFarShellBudget) →
  offResidualSq d < clusterMargin d
offResidualStrictlyBelowClusterMargin d =
  ℚP.≤-<-trans
    (offResidualBelowCombinedBudget d)
    (combinedBudgetBelowClusterMargin d)

------------------------------------------------------------------------
-- Direct bridge to the already-owned whole-carrier contradiction.
------------------------------------------------------------------------

nearFarBudgetToWholeCarrierMargin :
  (d : NearFarShellBudget) →
  clusterMargin d ≡ offResidualSq d →
  Whole.WholeCarrierCancellationMargin
nearFarBudgetToWholeCarrierMargin d exactSchur =
  record
    { clusterResidualSq = clusterMargin d
    ; offResidualSq = offResidualSq d
    ; farBudget = nearBudget d + farBudget d
    ; exactSchurIdentity = exactSchur
    ; analyticFarBound = offResidualBelowCombinedBudget d
    ; farBudgetBelowClusterMargin = combinedBudgetBelowClusterMargin d
    }

nearFarShellBudgetContradictsExactSchur :
  (d : NearFarShellBudget) →
  clusterMargin d ≡ offResidualSq d →
  ⊥
nearFarShellBudgetContradictsExactSchur d exactSchur =
  Whole.wholeCarrierCancellationContradiction
    (nearFarBudgetToWholeCarrierMargin d exactSchur)

------------------------------------------------------------------------
-- Source-shape boundary for the two pieces.
------------------------------------------------------------------------

record NearFarShellBudgetBoundary : Set where
  constructor near-far-shell-budget-boundary
  field
    explicitCutoffRequired : Bool
    explicitCutoffRequiredIsTrue : explicitCutoffRequired ≡ true

    farPieceMayUseAbsoluteSummability : Bool
    farPieceMayUseAbsoluteSummabilityIsTrue :
      farPieceMayUseAbsoluteSummability ≡ true

    nearPieceMustRemainSigned : Bool
    nearPieceMustRemainSignedIsTrue : nearPieceMustRemainSigned ≡ true

    compilerProvesEitherAnalyticBound : Bool
    compilerProvesEitherAnalyticBoundIsFalse :
      compilerProvesEitherAnalyticBound ≡ false

    convergenceAloneProvesStrictMargin : Bool
    convergenceAloneProvesStrictMarginIsFalse :
      convergenceAloneProvesStrictMargin ≡ false

canonicalNearFarShellBudgetBoundary : NearFarShellBudgetBoundary
canonicalNearFarShellBudgetBoundary =
  near-far-shell-budget-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
