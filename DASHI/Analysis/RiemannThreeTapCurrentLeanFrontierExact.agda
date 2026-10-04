module DASHI.Analysis.RiemannThreeTapCurrentLeanFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CURRENT LEAN THREE-TAP / PORTFOLIO MAX-CUT FRONTIER
--
-- Status/provenance mirror only.  Real analysis remains Lean-owned.
--
-- Lean repository:
--   chboishabba/dashi_lean4
-- Lean branch:
--   agent/rh-marked-cluster-target-reflection
-- Donor head at refresh:
--   442903ad4905845ebe5bcaa294bb7c02a77d97a4
--
-- Paid in Lean source:
--   * same-object uniform M0 envelope;
--   * explicit finite half-height O(log t / t) budget;
--   * actual transformed q^-2 pair decay;
--   * fixed canonical alpha strip |alpha| <= 1/25;
--   * exact complementary inverse-square zero-tail carrier;
--   * compiler from a uniform curvature bound to the actual far tail;
--   * explicit t-uniform pole-weight Lipschitz/equicontinuity estimate on the
--     fixed four-window support region;
--   * conditional compiler from uniform pole localization to one fixed-width
--     signed-pole core;
--   * exact compensation-floor identity;
--   * final Route-A adverse-vs-compensation balance compiler;
--   * finite mid-strip mesh/Lipschitz compiler;
--   * literal arbitrary-endpoint RvM zero-count upper bound;
--   * exact inverse-square finite-window <= N(A,B)/d^2 carrier weld;
--   * positive-height left/right shell bounds and unconditional all-real
--     unit-window inverse-square bounds using the same literal Ncount carrier;
--   * boundary-safe first right inverse-square source window
--       (3t/2 - 1, 2t]
--     with separation t/2 - 1, so the literal gamma=3t/2 boundary no longer
--     requires a separate fibre or a carrier change;
--   * dyadic half-height shell geometry and the exact numerical identity
--       sum_k ((log t + 1) + k) 2^-k / t = (2 log t + 4) / t;
--   * fail-closed compiler from one exact literal carrier-to-shell inequality
--     to ThreeTapInverseSquareTailBound, with a harmless factor-four loss;
--   * compile-time regression of that conditional compiler without naming an
--     unproved unconditional tail producer;
--   * correct-polarity V4/H4 lower fourth-angular compiler:
--       literalLocalCenteredFourthAngularAt_lower;
--   * same-object A2 upper-source compiler:
--       literalOffOrdExactAt_le_postSixthV4H4AbsorbBudgetAt;
--     therefore the old G3 orientation wall is source-written past and the
--     remaining A2 theorem is the strict scalar ABSORB comparison;
--   * Route-B exact scalar
--       signedFifthCorrelationGapAt
--       = Credit - Debt + OuterBudget - 3 eps,
--     plus a direct compiler from eventual gap >= 0 to SignedFifthInteriorTarget.
--
-- Fail-closed boundary:
--   the normalized four-window determinant bookkeeping / uniform curvature is
--   not claimed as kernel-paid, and the literal complementary zero carrier has
--   not yet been completely summed into the paid dyadic/unit windows.  The
--   right half-height endpoint defect itself is paid by the widened first right
--   window above.  The A2 polarity is paid but its exposed strict ABSORB scalar
--   inequality is not.  Route B still lacks eventual gap nonnegativity.  No
--   exact-head Lean Actions receipt exists for the donor head recorded here.
--
-- Current analytic portfolio:
--   A1: literal complementary-zero carrier summation
--       -> uniform witness width / oscillatory curvature
--       -> translated gamma+pole gain versus local slack;
--   A2: strict post-sixth V4/H4 ABSORB scalar inequality;
--   B : eventual signedFifthCorrelationGapAt >= 0.
------------------------------------------------------------------------

record ThreeTapCurrentLeanFrontier : Set where
  constructor three-tap-current-lean-frontier
  field
    repository : String
    branch : String
    donorHead : String

    uniformM0EnvelopeSourceWritten : Bool
    finiteLogOverTSourceWritten : Bool
    inverseSquarePairDecaySourceWritten : Bool
    fixedAlphaStripSourceWritten : Bool
    inverseSquareTailCarrierSourceWritten : Bool
    uniformCurvatureToFarCompilerSourceWritten : Bool
    uniformPoleWeightEquicontinuitySourceWritten : Bool
    uniformPoleLocalizationToFixedWidthCompilerSourceWritten : Bool
    compensationFloorIdentitySourceWritten : Bool
    routeAAsymptoticBalanceCompilerSourceWritten : Bool
    midStripFiniteMeshCompilerSourceWritten : Bool
    arbitraryEndpointLiteralZeroCountBoundSourceWritten : Bool
    inverseSquareLiteralWindowBridgeSourceWritten : Bool
    allRealUnitInverseSquareBoundSourceWritten : Bool

    uniformHighTPoleLocalizationPaid : Bool
    uniformOscillatoryCurvaturePaid : Bool
    inverseSquareRvMTailPaid : Bool
    gammaPoleGainVsSlackPaid : Bool
    routeBEventualGapPaid : Bool
    exactHeadLeanKernelReceipt : Bool
    rhDerivedHere : Bool

    uniformM0Paid : uniformM0EnvelopeSourceWritten ≡ true
    finiteAsymptoticPaid : finiteLogOverTSourceWritten ≡ true
    pairDecayPaid : inverseSquarePairDecaySourceWritten ≡ true
    alphaStripPaid : fixedAlphaStripSourceWritten ≡ true
    inverseSquareCarrierPaid : inverseSquareTailCarrierSourceWritten ≡ true
    curvatureCompilerPaid : uniformCurvatureToFarCompilerSourceWritten ≡ true
    poleWeightEquicontinuityPaid : uniformPoleWeightEquicontinuitySourceWritten ≡ true
    fixedWidthCompilerPaid : uniformPoleLocalizationToFixedWidthCompilerSourceWritten ≡ true
    compensationIdentityPaid : compensationFloorIdentitySourceWritten ≡ true
    routeABalanceCompilerPaid : routeAAsymptoticBalanceCompilerSourceWritten ≡ true
    meshCompilerPaid : midStripFiniteMeshCompilerSourceWritten ≡ true
    arbitraryEndpointLiteralCountPaid : arbitraryEndpointLiteralZeroCountBoundSourceWritten ≡ true
    inverseSquareWindowBridgePaid : inverseSquareLiteralWindowBridgeSourceWritten ≡ true
    allRealUnitInverseSquarePaid : allRealUnitInverseSquareBoundSourceWritten ≡ true

    poleLocalizationStillOpen : uniformHighTPoleLocalizationPaid ≡ false
    curvatureStillOpen : uniformOscillatoryCurvaturePaid ≡ false
    inverseSquareTailStillOpen : inverseSquareRvMTailPaid ≡ false
    compensationAsymptoticsStillOpen : gammaPoleGainVsSlackPaid ≡ false
    routeBStillOpen : routeBEventualGapPaid ≡ false
    kernelReceiptStillOpen : exactHeadLeanKernelReceipt ≡ false
    rhStillOpen : rhDerivedHere ≡ false

    exactRemainingWall : String
    leanOwnershipRule : String
    routeBRule : String

open ThreeTapCurrentLeanFrontier public

currentThreeTapCurrentLeanFrontier : ThreeTapCurrentLeanFrontier
currentThreeTapCurrentLeanFrontier =
  three-tap-current-lean-frontier
    "chboishabba/dashi_lean4"
    "agent/rh-marked-cluster-target-reflection"
    "442903ad4905845ebe5bcaa294bb7c02a77d97a4"

    true true true true true true true true true true true true true true

    false false false false false false false

    refl refl refl refl refl refl refl refl refl refl refl refl refl refl
    refl refl refl refl refl refl refl

    "A1: finish the literal complementary-zero carrier summation into the already-paid left/right source windows (the gamma=3t/2 boundary is now absorbed by the widened first right window), then fixed-width witness -> uniform oscillatory curvature, then translated gamma+pole gain versus local slack. A2: prove the strict post-sixth V4/H4 ABSORB scalar inequality; the old fourth-angular/G3 orientation wall is already paid. B: prove eventual signedFifthCorrelationGapAt >= 0. Mid-strip remains downstream of a genuine near-line PASS."
    "Lean owns the real-analysis surface. Agda mirrors source-written status and provenance only; do not manufacture the missing carrier summation, determinant/curvature, compensation-sign, A2 ABSORB scalar, Route-B eventual gap, or RH arguments here."
    "Keep the signed fifth-cap route independent: prove eventual nonnegativity of signedFifthCorrelationGapAt and feed the common canonical terminal consumer."

uniformPoleWeightEquicontinuityIsCurrent :
  ThreeTapCurrentLeanFrontier.uniformPoleWeightEquicontinuitySourceWritten
    currentThreeTapCurrentLeanFrontier ≡ true
uniformPoleWeightEquicontinuityIsCurrent = refl

allRealUnitInverseSquareIsCurrent :
  ThreeTapCurrentLeanFrontier.allRealUnitInverseSquareBoundSourceWritten
    currentThreeTapCurrentLeanFrontier ≡ true
allRealUnitInverseSquareIsCurrent = refl

uniformCurvatureIsStillOpen :
  ThreeTapCurrentLeanFrontier.uniformOscillatoryCurvaturePaid
    currentThreeTapCurrentLeanFrontier ≡ false
uniformCurvatureIsStillOpen = refl

inverseSquareTailIsStillOpen :
  ThreeTapCurrentLeanFrontier.inverseSquareRvMTailPaid
    currentThreeTapCurrentLeanFrontier ≡ false
inverseSquareTailIsStillOpen = refl

rhNotClaimedByAgdaStatusMirror :
  ThreeTapCurrentLeanFrontier.rhDerivedHere
    currentThreeTapCurrentLeanFrontier ≡ false
rhNotClaimedByAgdaStatusMirror = refl