module DASHI.Analysis.RiemannThreeTapCurrentLeanFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CURRENT LEAN THREE-ROUTE MAX-CUT FRONTIER
--
-- Status/provenance mirror only.  Real analysis remains Lean-owned.
--
-- Lean repository:
--   chboishabba/dashi_lean4
-- Lean branch:
--   agent/rh-postmerge-maxcut-20261007
-- Donor head at refresh:
--   f4fcbd410949d0323d47b75f5103a46a2be79a6e
--
-- Post-merge A2 audit:
--   * compensationTargetThreshold is explicitly
--       4*combinedZeroHeightDefect + integral signedOrdinateTest*mu;
--     no abstract high-ordinate contradiction proposition is hidden there;
--   * positive local debt is exactly split into vertical/count/sixth/eighth
--     coordinates;
--   * selected dominant M6 allowance leaves strict positive headroom on every
--     strength-floor witness;
--   * the remaining scalar itself is still unpaid.
--
-- A1 paid/source-written in Lean:
--   * finite half-height O(log t/t) budget and exact q^-2 pair decay;
--   * literal complementary inverse-square tail carrier;
--   * arbitrary-endpoint and all-real inverse-square window bounds;
--   * exact dyadic numerical series and conditional carrier-to-tail compiler;
--   * right half-height boundary repaired by (3t/2-1,2t];
--   * exact complement chart split gamma<=t/2 or gamma>=3t/2.
-- A1 still open:
--   * countable assignment/summation of those charts into paid shells;
--   * fixed-width witness / compact-alpha uniform curvature;
--   * translated gamma+pole gain versus local slack.
--
-- Route B paid/source-written in Lean:
--   * exact G_n = Credit-Debt+OuterBudget-3eps;
--   * exact direct form G_n = physicalCapInterior+OuterBudget-3eps;
--   * direct eventual gap + boundary decay + outer convergence compiles to the
--     existing SignedFifthAnalyticInput.
-- Route B still open:
--   * eventual nonnegativity of the exact signed scalar;
--   * selected-witness upper-boundary decay;
--   * selected-witness outer-terminal convergence.
--
-- No exact-head Lean kernel receipt and no RH claim are made here.
------------------------------------------------------------------------

record ThreeTapCurrentLeanFrontier : Set where
  constructor three-tap-current-lean-frontier
  field
    repository : String
    branch : String
    donorHead : String

    a1FiniteAndDecaySourceWritten : Bool
    a1LiteralWindowMachinerySourceWritten : Bool
    a1BoundaryAndChartGeometrySourceWritten : Bool
    a1DyadicSeriesSourceWritten : Bool
    a1CarrierToTailCompilerSourceWritten : Bool

    a2CorrectPolaritySourceWritten : Bool
    a2TerminalM6CertificateSourceWritten : Bool
    a2DominantCoefficientPaid : Bool
    a2DebtMinusMuGainNormalFormSourceWritten : Bool
    a2CanonicalMuGainPositiveSourceWritten : Bool
    a2ThresholdProvenanceExplicit : Bool
    a2FourDebtDecompositionSourceWritten : Bool
    a2DominantHeadroomPositiveSourceWritten : Bool

    routeBExactGapSourceWritten : Bool
    routeBDirectCapGapSourceWritten : Bool
    routeBTerminalCompilerSourceWritten : Bool
    routeBFullAuxiliaryCompilerSourceWritten : Bool

    a1CarrierSummationPaid : Bool
    a1UniformCurvaturePaid : Bool
    a1CompensationPaid : Bool
    a2StrictScalarPaid : Bool
    routeBEventualGapPaid : Bool
    routeBBoundaryDecayPaid : Bool
    routeBOuterConvergencePaid : Bool
    exactHeadLeanKernelReceipt : Bool
    rhDerivedHere : Bool

    a1FiniteAndDecayPaid : a1FiniteAndDecaySourceWritten ≡ true
    a1LiteralWindowsPaid : a1LiteralWindowMachinerySourceWritten ≡ true
    a1BoundaryGeometryPaid : a1BoundaryAndChartGeometrySourceWritten ≡ true
    a1SeriesPaid : a1DyadicSeriesSourceWritten ≡ true
    a1ConditionalTailCompilerPaid : a1CarrierToTailCompilerSourceWritten ≡ true

    a2PolarityPaid : a2CorrectPolaritySourceWritten ≡ true
    a2M6Paid : a2TerminalM6CertificateSourceWritten ≡ true
    a2LeadingSignPaid : a2DominantCoefficientPaid ≡ true
    a2NormalFormPaid : a2DebtMinusMuGainNormalFormSourceWritten ≡ true
    a2MuGainPaid : a2CanonicalMuGainPositiveSourceWritten ≡ true
    a2ThresholdAuditPaid : a2ThresholdProvenanceExplicit ≡ true
    a2FourDebtSplitPaid : a2FourDebtDecompositionSourceWritten ≡ true
    a2HeadroomPaid : a2DominantHeadroomPositiveSourceWritten ≡ true

    routeBGapPaid : routeBExactGapSourceWritten ≡ true
    routeBDirectPaid : routeBDirectCapGapSourceWritten ≡ true
    routeBCompilerPaid : routeBTerminalCompilerSourceWritten ≡ true
    routeBHonestAuxCompilerPaid : routeBFullAuxiliaryCompilerSourceWritten ≡ true

    a1CarrierStillOpen : a1CarrierSummationPaid ≡ false
    a1CurvatureStillOpen : a1UniformCurvaturePaid ≡ false
    a1CompensationStillOpen : a1CompensationPaid ≡ false
    a2ScalarStillOpen : a2StrictScalarPaid ≡ false
    routeBSignStillOpen : routeBEventualGapPaid ≡ false
    routeBBoundaryStillOpen : routeBBoundaryDecayPaid ≡ false
    routeBOuterLimitStillOpen : routeBOuterConvergencePaid ≡ false
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
    "agent/rh-postmerge-maxcut-20261007"
    "f4fcbd410949d0323d47b75f5103a46a2be79a6e"

    true true true true true
    true true true true true true true true
    true true true true

    false false false false false false false false false

    refl refl refl refl refl
    refl refl refl refl refl refl refl refl
    refl refl refl refl
    refl refl refl refl refl refl refl refl refl

    "A2: prove or refute verticalDebt+countDebt+sixthDebt+eighthDebt+signed FarExact < explicit compensationTargetThreshold+positive smooth-mu gain. A1: finish countable chart-to-shell summation, then uniform curvature and compensation. B: pay boundary decay and outer convergence and prove eventual signedFifthCorrelationGapAt >= 0."
    "Lean owns all real analysis. Agda mirrors source-written provenance/status only and must not manufacture A1 shell summation, curvature, compensation, A2 strict scalar, Route-B sign/limits, kernel receipt, or RH."
    "Route B's eventual gap is the only genuinely signed inequality, but boundary decay and outer-terminal convergence remain independent selected-witness obligations until Lean discharges them."

a2DominantCoefficientIsPaid :
  ThreeTapCurrentLeanFrontier.a2DominantCoefficientPaid
    currentThreeTapCurrentLeanFrontier ≡ true
a2DominantCoefficientIsPaid = refl

a2ThresholdProvenanceIsExplicit :
  ThreeTapCurrentLeanFrontier.a2ThresholdProvenanceExplicit
    currentThreeTapCurrentLeanFrontier ≡ true
a2ThresholdProvenanceIsExplicit = refl

a2FourDebtSplitIsSourceWritten :
  ThreeTapCurrentLeanFrontier.a2FourDebtDecompositionSourceWritten
    currentThreeTapCurrentLeanFrontier ≡ true
a2FourDebtSplitIsSourceWritten = refl

a2DominantHeadroomIsPositiveSourceWritten :
  ThreeTapCurrentLeanFrontier.a2DominantHeadroomPositiveSourceWritten
    currentThreeTapCurrentLeanFrontier ≡ true
a2DominantHeadroomIsPositiveSourceWritten = refl

a1CarrierIsStillOpen :
  ThreeTapCurrentLeanFrontier.a1CarrierSummationPaid
    currentThreeTapCurrentLeanFrontier ≡ false
a1CarrierIsStillOpen = refl

a2ScalarIsStillOpen :
  ThreeTapCurrentLeanFrontier.a2StrictScalarPaid
    currentThreeTapCurrentLeanFrontier ≡ false
a2ScalarIsStillOpen = refl

routeBSignIsStillOpen :
  ThreeTapCurrentLeanFrontier.routeBEventualGapPaid
    currentThreeTapCurrentLeanFrontier ≡ false
routeBSignIsStillOpen = refl

routeBBoundaryDecayIsStillOpen :
  ThreeTapCurrentLeanFrontier.routeBBoundaryDecayPaid
    currentThreeTapCurrentLeanFrontier ≡ false
routeBBoundaryDecayIsStillOpen = refl

routeBOuterConvergenceIsStillOpen :
  ThreeTapCurrentLeanFrontier.routeBOuterConvergencePaid
    currentThreeTapCurrentLeanFrontier ≡ false
routeBOuterConvergenceIsStillOpen = refl

rhNotClaimedByAgdaStatusMirror :
  ThreeTapCurrentLeanFrontier.rhDerivedHere
    currentThreeTapCurrentLeanFrontier ≡ false
rhNotClaimedByAgdaStatusMirror = refl
