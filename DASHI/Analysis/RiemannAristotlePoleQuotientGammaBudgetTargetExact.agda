module DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact where

------------------------------------------------------------------------
-- POLE-QUOTIENT GAMMA BUDGET TARGET
--
-- The post-#642 final lane deliberately retains the deterministic Gamma channel
-- instead of eliminating it by the second Schur step.  This file isolates the
-- exact forward theorem needed by the split-complement compiler.
--
-- IMPORTANT: this is not a generic "Gamma is small" statement.  A producer
-- must bind the literal Gamma response of the SAME universal pole-quotient taper
-- used by the target cluster and the signed off-ordinate carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record PoleQuotientGammaBudgetTarget : Set₁ where
  constructor pole-quotient-gamma-budget-target
  field
    Scalar : Set
    Taper : Set

    GammaResponse : Taper → Scalar
    GammaBudget : Taper → Scalar
    _≤_ : Scalar → Scalar → Set

    universalPoleQuotientTaper : Taper

    -- This is the actual missing deterministic estimate.
    gammaResponseUpper :
      GammaResponse universalPoleQuotientTaper
      ≤ GammaBudget universalPoleQuotientTaper

open PoleQuotientGammaBudgetTarget public

record PoleQuotientGammaBudgetBoundary : Set where
  constructor pole-quotient-gamma-budget-boundary
  field
    sameUniversalPoleQuotientTaperRequired : Bool
    sameUniversalPoleQuotientTaperRequiredIsTrue :
      sameUniversalPoleQuotientTaperRequired ≡ true

    rankTwoSchurGammaZeroAcceptedAsPoleQuotientGammaPayment : Bool
    rankTwoSchurGammaZeroAcceptedAsPoleQuotientGammaPaymentIsFalse :
      rankTwoSchurGammaZeroAcceptedAsPoleQuotientGammaPayment ≡ false

    genericArchimedeanBoundOwnerFoundInAgdaSearch : Bool
    genericArchimedeanBoundOwnerFoundInAgdaSearchIsFalse :
      genericArchimedeanBoundOwnerFoundInAgdaSearch ≡ false

    literalPoleQuotientGammaBudgetClosed : Bool
    literalPoleQuotientGammaBudgetClosedIsFalse :
      literalPoleQuotientGammaBudgetClosed ≡ false

    deterministicLeafIndependentOfZeroPhaseLeaf : Bool
    deterministicLeafIndependentOfZeroPhaseLeafIsTrue :
      deterministicLeafIndependentOfZeroPhaseLeaf ≡ true

    requiredTheorem : String

canonicalPoleQuotientGammaBudgetBoundary : PoleQuotientGammaBudgetBoundary
canonicalPoleQuotientGammaBudgetBoundary =
  pole-quotient-gamma-budget-boundary
    true refl
    false refl
    false refl
    false refl
    true refl
    "On the exact universal pole-quotient taper g_pole, construct an explicit Gamma budget B_Gamma(g_pole) and prove GammaResponse(g_pole) <= B_Gamma(g_pole), with constants compatible with offBudget + B_Gamma < M_cluster^pole."
