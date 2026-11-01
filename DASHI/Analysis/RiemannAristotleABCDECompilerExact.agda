module DASHI.Analysis.RiemannAristotleABCDECompilerExact where

------------------------------------------------------------------------
-- BIDIRECTIONAL A--E CUTSET COMPILER
--
-- The finite selected-carrier geometry is already closed in the Lean owner.
-- This module closes the *logical* forward/backward compiler around the five
-- remaining research slots without fabricating the two analytic estimates.
--
--   A : literal post-elim2 carrier/balance identity
--   B : signed/clustered projected unselected-zero estimate
--   C : projected prime/Gamma payment
--   D : B_far < M_target
--   E : off-line witness contradiction -> existing RH predicate
--
-- The crucial separation is intentional: A/D/E are composition logic; B/C are
-- the genuine analytic producer sockets.  Any future claim of RH must inhabit
-- those literal producer sockets on the actual certified carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP

------------------------------------------------------------------------
-- D/E scalar margin compiler.
--
-- The literal A/B/C domain work is allowed to choose its own projected scalar
-- coordinate.  Once it proves
--
--   M <= target <= farResidual <= farBudget < M,
--
-- contradiction is purely ordered-field logic.
------------------------------------------------------------------------

record ABCDEMarginContradiction : Set where
  constructor abcde-margin-contradiction
  field
    targetSignal farResidual farBudget strictTargetMargin : ℚ
    targetMarginLower : strictTargetMargin ≤ targetSignal
    balanceForcesTargetBelowFarResidual : targetSignal ≤ farResidual
    farResidualBound : farResidual ≤ farBudget
    farBudgetBelowTargetMargin : farBudget < strictTargetMargin

open ABCDEMarginContradiction public

abcdeMarginImpossible : (d : ABCDEMarginContradiction) → ⊥
abcdeMarginImpossible d =
  let
    marginBelowResidual : strictTargetMargin d ≤ farResidual d
    marginBelowResidual =
      ℚP.≤-trans (targetMarginLower d)
        (balanceForcesTargetBelowFarResidual d)

    marginBelowBudget : strictTargetMargin d ≤ farBudget d
    marginBelowBudget =
      ℚP.≤-trans marginBelowResidual (farResidualBound d)

    marginBelowItself : strictTargetMargin d < strictTargetMargin d
    marginBelowItself =
      ℚP.≤-<-trans marginBelowBudget (farBudgetBelowTargetMargin d)
  in
  ℚP.<-irrefl refl marginBelowItself

------------------------------------------------------------------------
-- E: generic final bridge into the repository's existing, unweakened RH
-- statement.  The domain instance must provide the existing equivalence/bridge
-- from "no off-line zero" to that exact proposition; this compiler does not
-- invent a replacement RH definition.
------------------------------------------------------------------------

record RHCompletionInterface : Set₁ where
  field
    Zero : Set
    OffLine : Zero → Set
    RH : Set
    noOffLineImpliesRH : ((ρ : Zero) → ¬ (OffLine ρ)) → RH
    cutsetForOffLine : (ρ : Zero) → OffLine ρ → ABCDEMarginContradiction

open RHCompletionInterface public

rhFromCompletedABCDECutset : (d : RHCompletionInterface) → RH d
rhFromCompletedABCDECutset d =
  noOffLineImpliesRH d
    (λ ρ hρ → abcdeMarginImpossible (cutsetForOffLine d ρ hρ))

------------------------------------------------------------------------
-- Machine-readable frontier.  "Compiler closed" is not "analytic socket
-- closed".  These flags prevent a thin composition theorem from being confused
-- with a proof of B or C.
------------------------------------------------------------------------

record ABCDECutsetStatus : Set where
  constructor abcde-cutset-status
  field
    postElim2IdentityCompilerClosed : Bool
    postElim2IdentityCompilerClosedIsTrue : postElim2IdentityCompilerClosed ≡ true
    signedProjectedZeroTailEstimateClosed : Bool
    signedProjectedZeroTailEstimateClosedIsFalse :
      signedProjectedZeroTailEstimateClosed ≡ false
    projectedPrimeGammaPaymentClosed : Bool
    projectedPrimeGammaPaymentClosedIsFalse :
      projectedPrimeGammaPaymentClosed ≡ false
    farTailMarginCompilerClosed : Bool
    farTailMarginCompilerClosedIsTrue : farTailMarginCompilerClosed ≡ true
    finalNoOffLineToRHCompilerClosed : Bool
    finalNoOffLineToRHCompilerClosedIsTrue : finalNoOffLineToRHCompilerClosed ≡ true
    shortSupportCompatibleThreeTaperFamilyOwned : Bool
    shortSupportCompatibleThreeTaperFamilyOwnedIsFalse :
      shortSupportCompatibleThreeTaperFamilyOwned ≡ false
    equalHeightClusterRouteClosed : Bool
    equalHeightClusterRouteClosedIsFalse : equalHeightClusterRouteClosed ≡ false
    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false
    boundedReading : String

open ABCDECutsetStatus public

canonicalABCDECutsetStatus : ABCDECutsetStatus
canonicalABCDECutsetStatus =
  abcde-cutset-status
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "The A/D/E compiler is closed. The only genuinely analytic payment sockets are B (signed projected unselected-zero tail) and C (projected prime/Gamma payment, with short-support compatibility still unproved for the constructed three-window family). Equal-height clustering remains a separate domain gate. RH is not derived."
