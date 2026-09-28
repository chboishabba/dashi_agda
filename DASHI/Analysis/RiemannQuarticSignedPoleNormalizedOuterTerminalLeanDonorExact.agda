module DASHI.Analysis.RiemannQuarticSignedPoleNormalizedOuterTerminalLeanDonorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannQuarticSignedPoleFourierTerminalLeanDonorExact as Terminal

------------------------------------------------------------------------
-- RH NORMALIZED OUTER TERMINAL DONOR / CURRENT ANALYTIC WALL
--
-- Lean companion:
--
--   Synthesis/
--     RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal.lean
--
-- This donor records the latest exact collapse of the high-side scalar.
--
-- Let
--
--   r = t/16,
--   eta0 = canonical normalized local radius,
--   D_t(q) = N-mu discrepancy on [t-rq,t+rq].
--
-- The Lean source proves:
--
--   A4_W(q) = r^4 D_t(q)                    for q >= 0,
--
-- and, on every finite outer exhaustion,
--
--   normalizedOuterAbel_n
--     =
--   integral_{eta0}^{n/r} C'_W(q) r^4 D_t(q) dq
--     =
--   r^6 canonicalOuterPairedAbel_n.
--
-- Adding the exact horizontal correction and subtracting the fixed
-- literal-vs-paired local correction gives a dimensionless finite carrier
--
--   OuterTerminal_n
--     =
--   -1/2 integral_{eta0}^{n/r} C'_W(q) r^4 D_t(q) dq
--   + r^6 Horizontal_W
--   - r^6 LocalCorrection_W.
--
-- Lean proves
--
--   OuterTerminal_n -> r^6 H_W,
--
-- where H_W is the already-canonical signed high residual.
--
-- It further proves that the canonical strict high cut is equivalent to:
--
--   exists eps>0, eventually
--     OuterTerminal_n <= r^6 terminalMargin - eps.
--
-- Hence a future ordinary analytic proof can be stated entirely using finite
-- q-integrals and an eventual positive slack.  No improper integral, Fourier
-- inversion, local/far representation theorem, or hidden Gamma/mu split
-- remains downstream.
--
-- CURRENT WALL
--
-- The repository owns absolute logarithmic RvM discrepancy bounds and the
-- local V4 theorem, but no signed outer theorem strong enough for
--
--   integral C'_W(q) r^4 D_t(q) dq.
--
-- The absolute log bound is not a substitute: multiplication by r^4 exposes
-- precisely the four inverse powers that must come from cancellation/sign.
-- Likewise q^-2 decay of C'_W or the horizontal kernel alone cannot recover
-- the missing r^-4 gain at fixed normalized q.
------------------------------------------------------------------------

record NormalizedOuterTerminalReceipt : Set where
  constructor normalized-outer-terminal-receipt
  field
    repository : String
    branch : String
    leanPath : String

    localSlackCommit : String
    normalizedPairedAbelCommit : String
    normalizedOuterSymmetricCommit : String
    normalizedOuterLimitCommit : String
    finiteQCompilerCommit : String

open NormalizedOuterTerminalReceipt public

currentNormalizedOuterTerminalReceipt : NormalizedOuterTerminalReceipt
currentNormalizedOuterTerminalReceipt =
  normalized-outer-terminal-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-marked-cluster-target-reflection"
    "Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal.lean"

    "8fcf1674d4acea6101dfaaeb5d6a59c9a5c38ddb"
    "49c01c243264930a3fcd9193e08215aea94fe23d"
    "44a3c07d728980d8f9aa969f9f702aee1fbc8f45"
    "294893e374056df778dd518422d81d5a8f7ea8be"
    "ddca274218839269332b54c82489e6926e5ee52c"

record NormalizedOuterTerminalBoundary : Set where
  constructor normalized-outer-terminal-boundary
  field
    completedResidualPlusLocalSlackNormalFormSourceWritten : Bool
    localBudgetSlackNonnegativeSourceWritten : Bool

    normalizedPairedAbelFiniteScalingSourceWritten : Bool
    normalizedPairedAbelLimitSourceWritten : Bool

    antisymmetricDiscrepancyIsLiteralSymmetricWindowSourceWritten : Bool
    normalizedOuterAbelLiteralSymmetricFormSourceWritten : Bool
    normalizedOuterAbelQuarticScalingSourceWritten : Bool

    normalizedOuterHorizontalQuarticScalingSourceWritten : Bool
    normalizedOuterTerminalConvergesToCanonicalHighScalarSourceWritten : Bool
    finiteQPositiveSlackEquivalentToHighCutSourceWritten : Bool
    finiteQEstimateCompilesToHighContradictionSourceWritten : Bool

    outerSymmetricSignedDiscrepancyEstimatePaid : Bool
    existingAbsoluteRvMLogBoundPaysOuterEstimate : Bool
    qDecayAlonePaysMissingQuarticGain : Bool
    horizontalAndVerticalJointSignedEstimatePaid : Bool

    leanExactHeadKernelReceiptOwnedHere : Bool
    agdaReprovesRealAnalysisHere : Bool
    rhDerivedHere : Bool

    normalizedCarrierPaid :
      normalizedOuterTerminalConvergesToCanonicalHighScalarSourceWritten ≡ true
    finiteQCompilerPaid :
      finiteQEstimateCompilesToHighContradictionSourceWritten ≡ true

    signedOuterDiscrepancyStillOpen :
      outerSymmetricSignedDiscrepancyEstimatePaid ≡ false
    absoluteLogBoundRejectedAsPayment :
      existingAbsoluteRvMLogBoundPaysOuterEstimate ≡ false
    qDecayAloneRejectedAsPayment :
      qDecayAlonePaysMissingQuarticGain ≡ false
    jointOuterEstimateStillOpen :
      horizontalAndVerticalJointSignedEstimatePaid ≡ false

    leanKernelReceiptNotClaimed :
      leanExactHeadKernelReceiptOwnedHere ≡ false
    agdaDoesNotInventAnalyticProof :
      agdaReprovesRealAnalysisHere ≡ false
    rhStillNotDerived :
      rhDerivedHere ≡ false

    finiteQCarrier : String
    exactLimit : String
    currentOrdinaryMathematicsWall : String
    rejectedShortcut : String

open NormalizedOuterTerminalBoundary public

canonicalNormalizedOuterTerminalBoundary :
  NormalizedOuterTerminalBoundary
canonicalNormalizedOuterTerminalBoundary =
  normalized-outer-terminal-boundary
    true true
    true true
    true true true
    true true true true
    false false false false
    false false false

    refl refl
    refl refl refl refl
    refl refl refl

    "-1/2 * integral_[eta0,n/r] C'_W(q) * r^4 * D(t-r*q,t+r*q) dq + r^6*Horizontal_W - r^6*LocalCorrection_W"
    "OuterTerminal_n tends to r^6 * canonicalSignedHighResidual"
    "Prove an eventual strict upper bound with positive slack for the finite-Q carrier uniformly on the selected high witness. Equivalently, prove the required signed correlation of C'_W with the outer symmetric Riemann-von-Mangoldt discrepancy, jointly with the horizontal zero correction."
    "The existing absolute logarithmic discrepancy estimate and q^-2 kernel decay are individually too coarse: at fixed normalized q the r^4 discrepancy factor exposes the exact four inverse powers that only signed cancellation can supply."

------------------------------------------------------------------------
-- FOUR-PRIMITIVE CANDIDATE ROUTE
--
-- Lean commit:
--
--   ee2290221d5fc0be389dfd4cedfbfb8b02755075
--
-- The normalized outer discrepancy is
--
--   A4(q) = r^4 D(t-r*q,t+r*q),   r=t/16.
--
-- Lean now defines the fourth Cesaro primitive
--
--   P4_q(Q)
--     = integral_[eta0,Q] ((Q-q)^3/6) A4(q) dq
--
-- and the physical-halfwidth primitive
--
--   P4_s(Q)
--     = integral_[r*eta0,r*Q]
--         ((r*Q-s)^3/6) D(t-s,t+s) ds.
--
-- The affine change of variables proves exactly
--
--   P4_q(Q) = P4_s(Q).
--
-- Thus the apparent r^4 loss cancels exactly after four primitives.  This is
-- a real candidate mechanism for the four inverse powers required by the
-- quartic terminal scale.
--
-- No analytic bound on P4_s is claimed.
--
-- Attribution / circularity firewall:
--
-- Sharp pointwise bounds for the classical iterated argument functions S_n
-- found in the modern literature are stated under RH.  Such theorems may be
-- used only as diagnostics here; importing an RH-conditional S_n bound into
-- an RH proof would be circular.  Any donor paying the primitive route must
-- be unconditional (or independently proved without RH).
------------------------------------------------------------------------

record FourPrimitiveRouteBoundary : Set where
  constructor four-primitive-route-boundary
  field
    fourthNormalizedPrimitiveDefined : Bool
    fourthPhysicalPrimitiveDefined : Bool
    fourthPrimitiveScaleCancellationExact : Bool

    unconditionalPhysicalFourthPrimitiveBoundPaid : Bool
    fourfoldIntegrationByPartsCompilerPaid : Bool
    rhConditionalSnMayPayClayDebt : Bool

    scaleCancellationPaid :
      fourthPrimitiveScaleCancellationExact ≡ true
    physicalBoundStillOpen :
      unconditionalPhysicalFourthPrimitiveBoundPaid ≡ false
    ibpCompilerStillOpen :
      fourfoldIntegrationByPartsCompilerPaid ≡ false
    conditionalSnFirewall :
      rhConditionalSnMayPayClayDebt ≡ false

    exactScaleIdentity : String
    nextPrimitiveWall : String

open FourPrimitiveRouteBoundary public

canonicalFourPrimitiveRouteBoundary : FourPrimitiveRouteBoundary
canonicalFourPrimitiveRouteBoundary =
  four-primitive-route-boundary
    true true true
    false false false
    refl refl refl refl
    "integral_[eta0,Q] ((Q-q)^3/6) * r^4*D(t-r*q,t+r*q) dq = integral_[r*eta0,r*Q] ((r*Q-s)^3/6) * D(t-s,t+s) ds"
    "Prove an unconditional bound for the physical fourth discrepancy primitive, then weld a fourfold integration-by-parts compiler for the exact outer kernel."

finiteQRepresentationDebtIsPaid :
  NormalizedOuterTerminalBoundary.finiteQEstimateCompilesToHighContradictionSourceWritten
    canonicalNormalizedOuterTerminalBoundary ≡ true
finiteQRepresentationDebtIsPaid = refl

outerSignedCorrelationIsTheWall :
  NormalizedOuterTerminalBoundary.outerSymmetricSignedDiscrepancyEstimatePaid
    canonicalNormalizedOuterTerminalBoundary ≡ false
outerSignedCorrelationIsTheWall = refl
