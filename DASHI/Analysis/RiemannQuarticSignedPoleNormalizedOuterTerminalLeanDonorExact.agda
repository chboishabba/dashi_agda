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
    ibpCompilerPaid :
      fourfoldIntegrationByPartsCompilerPaid ≡ true
    conditionalSnFirewall :
      rhConditionalSnMayPayClayDebt ≡ false

    exactScaleIdentity : String
    nextPrimitiveWall : String

open FourPrimitiveRouteBoundary public

canonicalFourPrimitiveRouteBoundary : FourPrimitiveRouteBoundary
canonicalFourPrimitiveRouteBoundary =
  four-primitive-route-boundary
    true true true
    false true false
    refl refl refl refl
    "integral_[eta0,Q] ((Q-q)^3/6) * r^4*D(t-r*q,t+r*q) dq = integral_[r*eta0,r*Q] ((r*Q-s)^3/6) * D(t-s,t+s) ds"
    "Fourfold AC integration-by-parts is source-written.  The remaining analytic donor is an unconditional bound for the same physical fourth primitive / quartic-cap N-mu pairing, plus the routine outer-staircase interval-integrability and boundary-decay welds."

------------------------------------------------------------------------
-- FOUR-PRIMITIVE KERNEL / AC COMPILER UPDATE
--
-- The Lean branch has advanced the candidate route substantially:
--
-- * compact cosine derivatives through C^5 are source-written;
-- * C^5 is globally L1 by the same twofold oscillatory-decay architecture
--   used for the Fourier-mass weld;
-- * arbitrary finite-order smoothness is transported from ContDiffBump
--   through the actual selected signed projective profile;
-- * the fourfold IBP compiler has both a smooth and an absolutely-continuous
--   formulation;
-- * a canonical anchored P1/P2/P3/P4 ladder is constructed from interval
--   integrals;
-- * derivative identities for that ladder are only a.e., via Lebesgue
--   differentiation, so the zero staircase is never falsely differentiated
--   pointwise;
-- * the compiler is specialized to the literal outer symmetric discrepancy,
--   conditional only on its routine finite-window interval-integrability.
--
-- Main Lean commits:
--
--   9d9e223d17c196db868b57ce6e1e04d7f3b95655
--   5a44456fbc288090cd7e2be4424054979be8dccb
--   f264fb4f09b415d70c6e3a8c9004efcb581215d5
--   6dd771a1fc25797de6bf0c1e6c1f8688c905951c
--   b84b3550c6fbd8f63f3ea4ffbe744d0e0bc15fe2
--   f4268a8333abf8de1effe798bef94a7c9a6b1087
------------------------------------------------------------------------

record FourPrimitiveKernelCompilerBoundary : Set where
  constructor four-primitive-kernel-compiler-boundary
  field
    fifthCosineDerivativeSourceWritten : Bool
    fifthCosineDerivativeL1SourceWritten : Bool
    arbitraryOrderWitnessSmoothnessSourceWritten : Bool
    genericFourfoldIBPSourceWritten : Bool
    absolutelyContinuousFourfoldIBPSourceWritten : Bool
    anchoredPrimitiveLadderSourceWritten : Bool
    anchoredPrimitiveAEDerivativesSourceWritten : Bool
    outerDiscrepancyIBPSpecializationSourceWritten : Bool

    staircasePointwiseDifferentiabilityAssumed : Bool

    outerDiscrepancyFiniteIntervalIntegrabilityWeldPaid : Bool
    quarticCapFubiniIdentificationPaid : Bool
    unconditionalQuarticCapEstimatePaid : Bool
    boundaryDecayCompilerPaid : Bool

    kernelCompilerPaid :
      absolutelyContinuousFourfoldIBPSourceWritten ≡ true
    anchoredLadderPaid :
      anchoredPrimitiveLadderSourceWritten ≡ true
    staircaseFirewall :
      staircasePointwiseDifferentiabilityAssumed ≡ false

    finiteIntegrabilityAdapterStillOpen :
      outerDiscrepancyFiniteIntervalIntegrabilityWeldPaid ≡ false
    capIdentificationStillOpen :
      quarticCapFubiniIdentificationPaid ≡ false
    capEstimateStillOpen :
      unconditionalQuarticCapEstimatePaid ≡ false
    boundaryDecayStillOpen :
      boundaryDecayCompilerPaid ≡ false

    currentKernelIdentity : String
    nextCapIdentity : String

open FourPrimitiveKernelCompilerBoundary public

canonicalFourPrimitiveKernelCompilerBoundary :
  FourPrimitiveKernelCompilerBoundary
canonicalFourPrimitiveKernelCompilerBoundary =
  four-primitive-kernel-compiler-boundary
    true true true true true true true true
    false
    false false false false
    refl refl refl
    refl refl refl refl
    "integral C'_W*A4 = [C'P1]-[C''P2]+[C'''P3]-[C''''P4] + integral C'''''_W*P4, with the primitive ladder interpreted a.e./AC"
    "Identify the physical fourth primitive with the literal N-mu pairing against the quartic cap weight (S-max(s0,abs(y-t)))_+^4/24, then prove an unconditional bound on that same cap pairing."

------------------------------------------------------------------------
-- QUARTIC CAP SAME-OBJECT IDENTIFICATION
--
-- New Lean source:
--
--   Synthesis/RiemannZetaMuExactAbelAC.lean
--   Synthesis/RiemannQuarticSymmetricCapAC.lean
--
-- Commits:
--
--   e033f9f2a7be35cddd8cf68d20f877cb3858bfd7
--     exact N-mu Abel identity extended to absolutely-continuous tests
--
--   3b6cf8b83f10ed5145f7a94efaf43ae1111505b9
--     theorem-bearing AC quartic symmetric cap with odd cubic derivative
--
--   5c7c80971224c874e6589c7367b846452da70712
--     identify the AC cap N-mu pair with the physical fourth primitive
--
-- The physical fourth primitive is therefore not merely "like" an S_4
-- coordinate.  It is the literal same-object weighted pairing
--
--   zetaWindowMinusMuPair
--     (t-S) (t+S)
--     quarticSymmetricCapAC
--
-- where the cap derivative is
--
--   +(S-s)^3/6 on the left outer annulus,
--   0           on the already-paid inner window,
--   -(S-s)^3/6 on the right outer annulus.
--
-- Exact left/right Abel pairing collapses this to
--
--   integral_[s0,S] ((S-s)^3/6) D(t-s,t+s) ds.
--
-- No pointwise derivative is assigned at the inner kink.  The AC Abel
-- compiler uses the actual a.e. derivative.
------------------------------------------------------------------------

record QuarticCapPairBoundary : Set where
  constructor quartic-cap-pair-boundary
  field
    exactNMuAbelForACTestsSourceWritten : Bool
    acQuarticCapSourceWritten : Bool
    capOuterEndpointsZeroSourceWritten : Bool
    capDerivativeOddSourceWritten : Bool
    capPairEqualsPhysicalFourthPrimitiveSourceWritten : Bool

    unconditionalCapPairBoundPaid : Bool
    primeSideExplicitFormulaForThisCapPaid : Bool
    rhConditionalSnUsed : Bool

    capIdentificationPaid :
      capPairEqualsPhysicalFourthPrimitiveSourceWritten ≡ true
    capBoundStillOpen :
      unconditionalCapPairBoundPaid ≡ false
    primeSideShortcutNotClaimed :
      primeSideExplicitFormulaForThisCapPaid ≡ false
    noCircularSn :
      rhConditionalSnUsed ≡ false

    exactCapPairIdentity : String
    remainingCapWall : String

open QuarticCapPairBoundary public

canonicalQuarticCapPairBoundary : QuarticCapPairBoundary
canonicalQuarticCapPairBoundary =
  quartic-cap-pair-boundary
    true true true true true
    false false false
    refl refl refl refl
    "physicalFourthPrimitive(S) = zetaWindowMinusMuPair(t-S,t+S,quarticSymmetricCapAC) = integral_[s0,S] ((S-s)^3/6)*D(t-s,t+s) ds"
    "Prove an unconditional quantitative bound for this exact AC quartic-cap N-mu pairing, strong enough after the C^5 fourfold-IBP kernel weighting and explicit boundary terms to leave the terminal positive slack."

------------------------------------------------------------------------
-- FOUR-PRIMITIVE KERNEL LANE CLOSED TO ONE PRIMITIVE NORM
--
-- Latest Lean commits:
--
--   9a1fe1a64fd4927b22f76929ad84af0822a1dea4
--     isolate |P4| times finite C^5 L1 mass
--
--   3e082ffaafc6aa3c78a91363b9cb776209485761
--     discharge the finite C^5 L1 envelope by the global L1 norm
--
--   5284d3734c9a6ebc8e0dd6bf888eadef2b9365e9
--     close the fourfold kernel lane:
--
--       |OuterAbel_n|
--         <= K_boundary / Q_n^2
--            + B_P * ||C_W^(5)||_1.
--
-- The boundary constant is produced by Schwartz rapid decay under the weak
-- polynomial primitive envelope.  The fifth-derivative norm is produced
-- internally from global integrability.
--
-- Therefore the kernel/Fourier side contributes no remaining analytic
-- assumption beyond a uniform bound B_P for the anchored fourth primitive.
--
-- IMPORTANT same-object seam:
--
-- The repository separately owns
--
--   physicalFourthPrimitive
--     = quartic-cap N-mu pairing
--
-- and
--
--   normalized Cesaro fourth primitive
--     = physicalFourthPrimitive.
--
-- The fourfold IBP compiler, however, currently consumes
--
--   anchoredPrimitive4 A4 eta0.
--
-- The generic equality
--
--   anchoredPrimitive4 A4 eta0 Q
--     =
--   integral_[eta0,Q] ((Q-q)^3/6) A4(q) dq
--
-- has not yet been recorded as a theorem.  Until that weld is paid, a bound
-- on the physical cap primitive must not be silently reused as B_P.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ANCHORED / CESARO / PHYSICAL SAME-OBJECT WELD
--
-- Lean commits:
--
--   d38fd7382202cfd665486e20d22744dc4e5a9b46
--     anchoredPrimitive4 = cubic Cesaro convolution by AC integration by parts
--
--   dc2d2df02b8eb71473e4eb78c6a96280dca84aac
--     specialize to A4 and weld normalized/physical fourth primitives directly
--     into the fourfold IBP norm bound.
--
-- Therefore there is no longer a representation gap between the primitive
-- consumed by IBP and the literal physical quartic-cap N-mu carrier.
------------------------------------------------------------------------

record FourPrimitiveKernelClosureBoundary : Set where
  constructor four-primitive-kernel-closure-boundary
  field
    outerDiscrepancyFiniteIntervalIntegrabilityPaid : Bool
    quarticCapSameObjectIdentificationPaid : Bool
    upperIBPBoundaryDecayPaid : Bool
    fifthDerivativeGlobalL1Paid : Bool
    fifthInteriorPrimitiveTimesL1Paid : Bool
    outerAbelInvSqPlusPrimitiveNormPaid : Bool

    anchoredFourthEqualsCesaroFourthPaid : Bool
    physicalFourthFeedsAnchoredBoundSourceWritten : Bool
    unconditionalPhysicalCapBoundPaid : Bool

    kernelLaneClosed :
      outerAbelInvSqPlusPrimitiveNormPaid ≡ true
    anchoredCesaroWeldPaid :
      anchoredFourthEqualsCesaroFourthPaid ≡ true
    physicalToAnchoredWeldPaid :
      physicalFourthFeedsAnchoredBoundSourceWritten ≡ true
    physicalCapBoundStillOpen :
      unconditionalPhysicalCapBoundPaid ≡ false

    exactKernelEstimate : String
    exactSameObjectWeld : String
    nextAnalyticWall : String

open FourPrimitiveKernelClosureBoundary public

canonicalFourPrimitiveKernelClosureBoundary :
  FourPrimitiveKernelClosureBoundary
canonicalFourPrimitiveKernelClosureBoundary =
  four-primitive-kernel-closure-boundary
    true true true true true true
    true true false
    refl refl refl refl
    "|normalizedOuterPairedAbelAt n| <= K_boundary / Q_n^2 + B_P * fifthDerivativeGlobalL1Mass"
    "anchoredPrimitive4 A4 eta0 Q = normalizedFourthPrimitive(Q) = physicalFourthPrimitive(Q), and any physical uniform bound feeds the anchored IBP bound"
    "Prove an unconditional quantitative bound or sufficiently controlled growth estimate for the literal quartic-cap N-mu pairing; kernel decay, C^5 L1, and all same-object welds are paid."

finiteQRepresentationDebtIsPaid :
  NormalizedOuterTerminalBoundary.finiteQEstimateCompilesToHighContradictionSourceWritten
    canonicalNormalizedOuterTerminalBoundary ≡ true
finiteQRepresentationDebtIsPaid = refl

outerSignedCorrelationIsTheWall :
  NormalizedOuterTerminalBoundary.outerSymmetricSignedDiscrepancyEstimatePaid
    canonicalNormalizedOuterTerminalBoundary ≡ false
outerSignedCorrelationIsTheWall = refl
