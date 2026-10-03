module DASHI.Analysis.RiemannThreeTapCurrentLeanFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CURRENT LEAN THREE-TAP MAX-CUT FRONTIER
--
-- Status/provenance mirror only.  Real analysis remains Lean-owned.
--
-- Lean repository:
--   chboishabba/dashi_lean4
-- Lean branch:
--   agent/rh-marked-cluster-target-reflection
-- Donor head at refresh:
--   3d62a006ad3904e43f4e4f35a06cba90cce36be9
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
--   * dyadic half-height shell geometry and the exact numerical identity
--       sum_k ((log t + 1) + k) 2^-k / t = (2 log t + 4) / t;
--   * fail-closed compiler from one exact literal carrier-to-shell inequality
--     to ThreeTapInverseSquareTailBound, with a harmless factor-four loss;
--   * compile-time regression of that conditional compiler without naming an
--     unproved unconditional tail producer.
--
-- Fail-closed boundary:
--   the normalized four-window determinant bookkeeping / uniform curvature is
--   not claimed as kernel-paid, and the literal complementary zero carrier has
--   not yet been partitioned and compared to the paid dyadic shell majorant.
--   The regression is conditional on precisely that missing producer rather
--   than using an unresolved identifier.  No exact-head Lean Actions receipt
--   exists for the donor head recorded here.
--
-- Current analytic wall:
--   finite determinant transport / fixed-width witness
--     -> uniform oscillatory curvature
--     -> literal complementary-zero carrier partition into paid unit/dyadic
--        windows (all subsequent geometric/log series algebra is now paid)
--     -> translated gamma+pole gain versus local slack.
--
-- Route B remains the independent eventual signed-correlation gap theorem.
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
    "3d62a006ad3904e43f4e4f35a06cba90cce36be9"

    true true true true true true true true true true true true true true

    false false false false false false false

    refl refl refl refl refl refl refl refl refl refl refl refl refl refl
    refl refl refl refl refl refl refl

    "finite normalized four-window determinant transport from the paid uniform pole-weight modulus -> fixed-width witness -> uniform oscillatory curvature; independently, prove the one remaining literal complementary-zero carrier-to-dyadic-shell inequality ThreeTapInverseSquareShellPartitionBound (the numerical dyadic sum and its compiler to O(log t/t) are already source-written); then prove translated gamma+pole gain versus local slack; after a one-scale PASS, use the already-owned finite mid-strip mesh compiler"
    "Lean owns the real-analysis surface. Agda mirrors source-written status and provenance only; do not manufacture the missing determinant transport, curvature, carrier partition, compensation-sign, or RH arguments here."
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
