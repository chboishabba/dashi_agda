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
-- RH SIGNED-CAP LIMIT CORRECTION / CLASSICAL REMAINDER BRIDGE
--
-- Lean owners:
--   Synthesis/RiemannQuarticFourthPrimitiveQuantitativeBudget.lean
--   Synthesis/RiemannQuarticFourthPrimitiveClassicalRemainder.lean
--
-- A single finite-Q signed-cap success does NOT imply the limiting canonical
-- high cut.  The earlier compiler conclusion was too strong.  The corrected
-- theorem requires an EVENTUAL signed bound with fixed positive slack and
-- the proven exhaustion limit:
--
--   3390073  repair finite-vs-global conclusion
--   0775f89  eventual signed-cap -> limiting high cut
--
-- Exact unconditional classical-remainder identity for nonnegative endpoints:
--
--   S0(T) = Ncount 0 T - integral_0^T mu,
--   D(A,B) = S0(B) - S0(A)  (0 <= A <= B).
--
-- Hence the physical fourth cap, only when S <= t, is a weighted integral of
-- S0(t+s)-S0(t-s).  The finite-Q exhaustion also includes S > t:
--
--   D(t-s,t+s)
--     = D(t-s,0) + S0(t+s)  (t < s).
--
-- No reflection of negative-ordinate counts into positive S_n is assumed.
-- The *actual* signed C5 cap interior is now source-expressed as an iterated
-- integral against this full two-sided RvM remainder.
--
--   2c57316  positive-ordinate remainder bridge
--   a0b53c9  exact crossing-zero decomposition
--   704fab1  induced signed fifth-cap integral.
--
-- These are source-written bridge identities, not a theorem estimating S_n.
------------------------------------------------------------------------

------------------------------------------------------------------------

------------------------------------------------------------------------
-- DIRECT POSITIVE-DEFINITE TRACE TRANSPORT: SAME-OBJECT NO-GO
--
-- Lean owner:
--   Synthesis/RiemannQuarticSignedCosinePSDNoGo.lean
--
-- For the selected negative-origin witness:
--   C_W(0) = 0, yet integral_R C_W(q) dq < 0.
--
-- The 2-point PSD condition would require, for all a,b,q,
--   0 <= (a*a+b*b)*C_W(0) + 2*a*b*C_W(q).
-- Choosing (a,b)=(1,1) and (1,-1), with C_W(0)=0, forces
--   C_W(q)=0 at every q,
-- contradicting the negative total mass.
--
-- Thus C_W is NOT itself a PSD translation-invariant Toeplitz kernel.
-- The conjectured Heisenberg/Weil trace donor cannot simply identify the
-- selected cosine with a positive-definite kernel. Any future spectral
-- mechanism must act on a completed/signed expression and preserve the
-- horizontal contribution and actual zero-distribution correlation.
--
-- This does not rule out such a completed positivity mechanism and does
-- not prove the RH signed fifth-cap estimate.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- SAME-WITNESS EXPLICIT-FORMULA / OPERATOR AUDIT (2026-09-30)
--
-- Lean source:
--   Synthesis/RiemannMarkedArithmeticCompletedOperatorAudit.lean
--
-- On the selected compact physical detector at t >= 200, the literal
-- Zeta23 primeProjectiveDefect is identically ZERO, before and after the
-- cosh mark. Indeed any pointwise multiplier h(u) retains this blindness,
-- because it cannot enlarge support beyond log(2).
--
-- Source-written Lean owners:
--   quarticFourPhysicalDetector_pointwiseMultiplier_prime_eq_zero
--   selectedPointwiseMultipliers_prime_eq_zero
--   selectedPointwiseMultipliers_no_positive_prime
--
-- Thus positive auxiliary prime-angular jets are not a prime-sign donor
-- for the SAME four-window detector. At A=0, both actual marked prime
-- combination and pole combination are zero and the source arithmetic
-- response is precisely its Gamma combination.
--
-- A different, genuinely prime-sensitive detector must be nonzero at
-- some |u| >= log(2), which changes its support and requires re-establishing
-- the actual high-witness estimates. Pointwise weighting alone cannot.
--
-- The selected normalized cosine C_W(0)=0 but is nonzero when the source
-- origin is negative. A PSD 2x2 completion with C_W(q) in its
-- off-diagonal therefore requires two STRICTLY POSITIVE independently
-- sourced diagonal terms a,d and a*d >= C_W(q)^2 for EVERY q.
--
-- Source-written Lean owners:
--   selectedCosineCompletion_requires_positive_diagonals
--   selectedCosineCompletion_iff_diagonalPayment
--
-- The prior Agda RiemannWeilPairKernelFrobeniusExact already exposes
-- mixed-channel interference and explicitly does NOT prove positive
-- diagonal excess or the required analytic Phi-kernel identification.
-- Its finite-source identities cannot be promoted as this diagonal donor.
--
-- No same-witness operator trace formula, terminal strict estimate,
-- or new RH proof is claimed in this receipt.
------------------------------------------------------------------------

record QuantitativeFourthPrimitiveBoundary : Set where
  constructor quantitative-fourth-primitive-boundary
  field
    budgetLeanOwner : String
    absoluteBudgetCommit : String
    weightedKernelCompilerCommit : String
    absoluteScaleAuditCommit : String
    signedBudgetCommit : String
    weightedKernelProducerCommit : String
    targetHeightOverheadCommit : String
    signedFifthCapCompilerCommit : String

    exactTerminalProductBudgetSourceWritten : Bool
    admissibleCoefficientThresholdSourceWritten : Bool
    oversizedAbsoluteBudgetFailfastSourceWritten : Bool
    weightedPolynomialPrimitiveCompilerSourceWritten : Bool
    absoluteCesaroScaleComparisonSourceWritten : Bool

    weightedKernelGlobalMassProducerSourceWritten : Bool
    signedFiniteAbelBudgetIffSourceWritten : Bool
    nonpositiveBudgetBlocksAbsoluteSourceWritten : Bool
    targetHeightOverheadExactSourceWritten : Bool
    signedFifthCapLowerBoundCompilesTerminalSourceWritten : Bool
    unconditionalQuantitativePhysicalCapBoundPaid : Bool
    primitiveBoundFitsTerminalBudgetPaid : Bool
    signedFifthKernelPairingEstimatePaid : Bool
    fixedHighStrictEstimatePaid : Bool
    exactHeadKernelReceipt : Bool
    rhDerived : Bool

    absoluteScaleAudit : String
    absoluteProductCriterion : String
    polynomialCriterion : String
    unresolvedAnalyticTheorem : String

    weightedKernelGlobalMassSourceWrittenIsTrue :
      weightedKernelGlobalMassProducerSourceWritten ≡ true
    signedBudgetIffSourceWrittenIsTrue :
      signedFiniteAbelBudgetIffSourceWritten ≡ true
    overheadIdentitySourceWrittenIsTrue :
      targetHeightOverheadExactSourceWritten ≡ true
    fifthCapCompilerSourceWrittenIsTrue :
      signedFifthCapLowerBoundCompilesTerminalSourceWritten ≡ true
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
    "cc364b53d9533243e86da170a0f25c2805d4d1b2"
    "48886e27436a74ae2cfdb881738b80debc463bbe"
    "823ed3556e1abbe2f12c1d6d514d696306ccce27"
    "f6eefd3d5ac04a0237ec0e5d300932c64fe5ca47"
    "da19d9aeb906cb0c1f41be5b49d0b191e71599c9"

    true true true true true

    true true true true true false false false false false false



    "If |D(t-rq,t+rq)| <= E throughout [eta0,Q], then |P4(Q)| <= r^4*E*(Q-eta0)^4/24. This is an upper bound, not a lower bound on P4 or a proof that signed cancellation is impossible."
    "B*K5 < 2*(r^6*terminalMargin-r^6*horizontal+r^6*localCorrection)"
    "|P4(Q)| <= B(t)*(1+Q^5), with B(t)*integral_[eta0,infinity] (1+q^5)*|C5(q)| dq strictly inside the SAME terminal budget"
    "Decide the exact budget sign for the selected witness and prove a lower bound on the literal signed outer Abel integral exceeding minus that budget, or prove a physical quartic-cap upper bound whose product with the paid weighted kernel norm fits the positive absolute budget."

    refl refl refl refl refl refl refl refl refl
