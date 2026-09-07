module DASHI.Physics.Closure.NSTriadKNSignedNetworkBudgetCompilerRound511Exact where

------------------------------------------------------------------------
-- ROUND511 / SIGNED NETWORK BUDGET COMPILER
--
-- R106 already proves the exact whole-network normal form
--
--   nu * P = I + (-T) + F,
--
-- where P is the integrated signed critical production, I/T are the initial and
-- terminal normal-form boundaries, and F is the complete signed forcing sum.
--
-- This owner turns that identity into the smallest theorem-shaped compiler
-- suggested by the physical-intuition pass: if the two boundary contributions
-- and the SIGNED forcing sum are bounded, then the integrated production is
-- bounded.  No absolute value, positive part, or per-triad danger tax is added.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; -_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNSignedPhaseTimeNormalFormRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNWaleffeForcingRouteAuditRound108Exact as R108
import DASHI.Physics.Closure.NSTriadKNPhysicalMeaningSignedCancellationRound510Exact as R510

record SignedNetworkBudget (N : R106.CommonViscositySignedPhaseNetwork) : Set where
  constructor signed-network-budget
  field
    initialBudget terminalBudget forcingBudget : ℚ

    initialBoundaryPaid :
      R106.sumInitialNormalFormBoundary (R106.cells N) ≤ initialBudget

    negativeTerminalBoundaryPaid :
      - R106.sumTerminalNormalFormBoundary (R106.cells N) ≤ terminalBudget

    signedForcingPaid :
      R106.sumSignedNormalFormForcing (R106.cells N) ≤ forcingBudget

open SignedNetworkBudget public

signedNetworkBudgetPaysWeightedCriticalProduction :
  ∀ {N} (B : SignedNetworkBudget N) →
  R106.viscosity N * R106.sumIntegratedCriticalProduction (R106.cells N)
  ≤ initialBudget B + terminalBudget B + forcingBudget B
signedNetworkBudgetPaysWeightedCriticalProduction {N} B =
  let
    foldedBudget :
      R106.sumInitialNormalFormBoundary (R106.cells N)
        + (- R106.sumTerminalNormalFormBoundary (R106.cells N))
        + R106.sumSignedNormalFormForcing (R106.cells N)
      ≤ initialBudget B + terminalBudget B + forcingBudget B
    foldedBudget =
      ℚP.+-mono-≤
        (ℚP.+-mono-≤
          (initialBoundaryPaid B)
          (negativeTerminalBoundaryPaid B))
        (signedForcingPaid B)
  in
  subst
    (λ left →
      left ≤ initialBudget B + terminalBudget B + forcingBudget B)
    (sym (R106.finiteSignedNetworkTimeNormalForm N))
    foldedBudget

------------------------------------------------------------------------
-- Introspective interpretation.
--
-- This compiler does NOT pay the current physical remainder.  It proves exactly
-- what theorem must be supplied next: cutoff-uniform bounds on the physical
-- instances of the two normal-form boundaries and, crucially, the signed
-- external network forcing after the already-exact self-phase extraction.
------------------------------------------------------------------------

round511ExactSignedBudgetCompilerClosed : Bool
round511ExactSignedBudgetCompilerClosed = true

round511AbsoluteValueRequired : Bool
round511AbsoluteValueRequired = false

round511PositivePartRequired : Bool
round511PositivePartRequired = false

round511ExternalCrossTriadPhysicalPaymentClosed : Bool
round511ExternalCrossTriadPhysicalPaymentClosed =
  R108.round108PhysicalExternalCrossTriadForcingRemainderPaymentClosed

round511PreserveSignBeforeMajorizing : Bool
round511PreserveSignBeforeMajorizing =
  R510.round510PreserveSignBeforeMajorizing

round511ClayPromotion : Bool
round511ClayPromotion = false

round511ExactSignedBudgetCompilerClosedIsTrue :
  round511ExactSignedBudgetCompilerClosed ≡ true
round511ExactSignedBudgetCompilerClosedIsTrue = refl

round511ExternalCrossTriadPhysicalPaymentClosedIsFalse :
  round511ExternalCrossTriadPhysicalPaymentClosed ≡ false
round511ExternalCrossTriadPhysicalPaymentClosedIsFalse =
  R108.round108PhysicalExternalCrossTriadForcingRemainderPaymentClosedIsFalse

round511ClayPromotionIsFalse : round511ClayPromotion ≡ false
round511ClayPromotionIsFalse = refl
