module DASHI.Analysis.RiemannQuarticFourthPrimitiveQuantitativeBudgetLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RH FOURTH-PRIMITIVE QUANTITATIVE FAIL-FAST
--
-- Current Lean owner:
--   Synthesis/RiemannQuarticFourthPrimitiveQuantitativeBudget.lean
--
-- The exact dimensionless finite terminal quantity is
--
--   T_n = -1/2 I_n + H6 - L6
--
--   I_n = integral_[eta0,Q_n] C'_W(q) * r^4 D(t-rq,t+rq) dq
--   H6  = r^6 horizontal remainder
--   L6  = r^6 literal-versus-paired local correction.
--
-- The target is T_n < r^6 M_W (eventually with positive slack).
--
-- If fourfold IBP gives |I_n| <= Kboundary/Q_n^2 + B*K5,
-- the exact sufficient threshold after the boundary limit is
--
--   B*K5 < 2*(r^6*M_W - H6 + L6).
--
-- This threshold is NOT guaranteed positive.  In particular, a trivial
-- absolute RvM estimate of size r^4 log t on a fixed normalized window
-- does not automatically fit an O(1) terminal budget.
--
-- A polynomial-growth estimate |P4(Q)| <= B(t)(1+Q^5) is similarly only
-- useful with a weighted C5 kernel norm and its full height-dependent
-- coefficient accounted for. Smoothness and integrability are not quartic
-- cancellation.
--
-- The signed alternative -1/2 I_n + H6-L6 < r^6 M_W is retained.
-- Failure of an absolute sufficient budget DOES NOT disprove this signed
-- inequality.
--
-- Attribution: new Lean code is source-landed only; this module records
-- interfaces, not an independent Agda proof of real analysis or RH.
------------------------------------------------------------------------

record QuantitativeFourthPrimitiveBoundary : Set where
  constructor quantitative-fourth-primitive-boundary
  field
    budgetLeanOwner : String
    absoluteBudgetCommit : String
    weightedKernelCompilerCommit : String

    exactTerminalProductBudgetSourceWritten : Bool
    admissibleCoefficientThresholdSourceWritten : Bool
    oversizedAbsoluteBudgetFailfastSourceWritten : Bool
    weightedPolynomialPrimitiveCompilerSourceWritten : Bool

    weightedKernelGlobalMassProducerSourceWritten : Bool
    unconditionalQuantitativePhysicalCapBoundPaid : Bool
    primitiveBoundFitsTerminalBudgetPaid : Bool
    signedFifthKernelPairingEstimatePaid : Bool
    fixedHighStrictEstimatePaid : Bool
    exactHeadKernelReceipt : Bool
    rhDerived : Bool

    absoluteProductCriterion : String
    polynomialCriterion : String
    unresolvedAnalyticTheorem : String

    productBudgetIsExplicit :
      exactTerminalProductBudgetSourceWritten ≡ true
    coefficientThresholdIsExplicit :
      admissibleCoefficientThresholdSourceWritten ≡ true
    unconditionalCapBoundStillOpen :
      unconditionalQuantitativePhysicalCapBoundPaid ≡ false
    terminalBudgetUnpaid :
      primitiveBoundFitsTerminalBudgetPaid ≡ false
    noFalseRHDeduction :
      rhDerived ≡ false

open QuantitativeFourthPrimitiveBoundary public

canonicalQuantitativeFourthPrimitiveBoundary :
  QuantitativeFourthPrimitiveBoundary
canonicalQuantitativeFourthPrimitiveBoundary =
  quantitative-fourth-primitive-boundary
    "Synthesis/RiemannQuarticFourthPrimitiveQuantitativeBudget.lean"
    "6fbeb8df7a35408817323ffa8127ff0b75b4e5ab"
    "7405a1152a3a9f5ee44f40032fd40396038f1649"

    true true true true

    false false false false false false false

    "B*K5 < 2*(r^6*terminalMargin-r^6*horizontal+r^6*localCorrection)"
    "|P4(Q)| <= B(t)*(1+Q^5), with B(t)*integral_[eta0,infinity] (1+q^5)*|C5(q)| dq strictly inside the SAME terminal budget"
    "Prove an unconditional selected-height quantitative physical quartic-cap N-mu bound satisfying the strict budget, or prove a one-sided bound on the signed fifth-kernel cap pairing jointly with horizontal/local terms."

    refl refl refl refl refl
