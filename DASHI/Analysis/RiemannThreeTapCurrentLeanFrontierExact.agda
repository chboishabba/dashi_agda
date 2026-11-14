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
--   d4db1536707e18cd0a7551e30f996edf29626a5a
--
-- Fail-closed accounting:
--   K = source/kernel theorem on the same proof graph;
--   U = unconditional analytic input instantiated on the literal carrier;
--   O = genuinely open scalar/limit producer;
--   C = circular/RH-equivalent/logically inert as an RH producer.
-- C contributes zero proof-distance reduction.
--
-- Post-merge A2 audit paid/source-written in Lean:
--   * compensationTargetThreshold is explicitly
--       4*combinedZeroHeightDefect + integral signedOrdinateTest*mu;
--   * positive local debt is exactly split into vertical/count/sixth/eighth;
--   * it is further reassociated into lower-order vertical+count versus the
--     leading-scale sixth+eighth pair;
--   * exact canonical-radius expansions show BOTH D6 and D8 contain a leading
--       expandedZeroCount / (t/16)^2
--     contribution after terminal normalization;
--   * selected dominant M6 allowance still leaves strict positive headroom;
--   * the exact leading local allowance is now exposed as
--       A6 + A8(W) < targetStrength,
--     with A6 the paid M6 allowance and
--       A8(W) = (3/1700)*eta0^2*fourthLipschitz(W);
--     equivalently A8(W) must fit inside the paid dominant headroom;
--   * FarExact is exactly FarBaseExact + FarHorizontalExact;
--   * FarBase has an unconditional inverse-square shell bound;
--   * FarHorizontal and combined FarExact have the same shell compiler once a
--     selected HorizontalFarCurvatureBound CH is supplied;
--   * fixed-q normalized compensation starts at r^-2 while the quartic target
--     is r^-6, so four extra powers must come from cancellation/sign rather than
--     remote Fourier decay.
-- A2 still open:
--   * selected-witness fourthLipschitz sharpening enough to pay A8, or a sharper
--     signed eighth treatment (the generic explicit G1 K bound is too coarse to
--     be promoted to this PASS merely because it is unconditional);
--   * selected horizontal far-curvature constant CH;
--   * explicit completed compensation lower bound;
--   * the resulting strict scalar PASS, or a formal eventual no-go.
--
-- A1 paid/source-written in Lean:
--   * finite half-height O(log t/t) budget and exact q^-2 pair decay;
--   * literal complementary inverse-square tail carrier;
--   * arbitrary-endpoint and all-real inverse-square window bounds;
--   * exact dyadic numerical series and conditional carrier-to-tail compiler;
--   * right half-height boundary repaired by (3t/2-1,2t];
--   * exact complement chart split gamma<=t/2 or gamma>=3t/2.
-- A1 still open:
--   * ThreeTapInverseSquareShellPartitionBound, i.e. actual countable
--     assignment/summation of those charts into the paid shell family;
--   * fixed-width witness / compact-alpha uniform curvature;
--   * translated gamma+pole gain versus local slack.
--
-- Route B paid/source-written in Lean:
--   * exact G_n = Credit-Debt+OuterBudget-3eps;
--   * exact direct form G_n = physicalCapInterior+OuterBudget-3eps;
--   * sufficiently-large natural cutoff ownership is automatic/Archimedean;
--   * signedFifthAnalyticInput_of_three_producers exposes exactly boundary
--     decay + eventual direct gap sign + outer convergence.
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
    a2LeadingScaleSplitSourceWritten : Bool
    a2CanonicalEnvelopeExpansionsSourceWritten : Bool
    a2FarBaseShellPaid : Bool
    a2FarHorizontalConditionalCompilerSourceWritten : Bool

    routeBExactGapSourceWritten : Bool
    routeBDirectCapGapSourceWritten : Bool
    routeBTerminalCompilerSourceWritten : Bool
    routeBFullAuxiliaryCompilerSourceWritten : Bool
    routeBCutoffOwnershipSourceWritten : Bool
    routeBThreeProducerCompilerSourceWritten : Bool

    a1CarrierSummationPaid : Bool
    a1UniformCurvaturePaid : Bool
    a1CompensationPaid : Bool
    a2LeadingConstantsPaid : Bool
    a2HorizontalFarCurvaturePaid : Bool
    a2CompensationPaid : Bool
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
    a2LeadingScaleAuditPaid : a2LeadingScaleSplitSourceWritten ≡ true
    a2EnvelopeExpansionAuditPaid : a2CanonicalEnvelopeExpansionsSourceWritten ≡ true
    a2FarBaseShellAuditPaid : a2FarBaseShellPaid ≡ true
    a2FarHorizontalCompilerAuditPaid : a2FarHorizontalConditionalCompilerSourceWritten ≡ true

    routeBGapPaid : routeBExactGapSourceWritten ≡ true
    routeBDirectPaid : routeBDirectCapGapSourceWritten ≡ true
    routeBCompilerPaid : routeBTerminalCompilerSourceWritten ≡ true
    routeBHonestAuxCompilerPaid : routeBFullAuxiliaryCompilerSourceWritten ≡ true
    routeBCutoffOwnershipPaid : routeBCutoffOwnershipSourceWritten ≡ true
    routeBThreeProducerCompilerPaid : routeBThreeProducerCompilerSourceWritten ≡ true

    a1CarrierStillOpen : a1CarrierSummationPaid ≡ false
    a1CurvatureStillOpen : a1UniformCurvaturePaid ≡ false
    a1CompensationStillOpen : a1CompensationPaid ≡ false
    a2LeadingConstantsStillOpen : a2LeadingConstantsPaid ≡ false
    a2HorizontalFarCurvatureStillOpen : a2HorizontalFarCurvaturePaid ≡ false
    a2CompensationStillOpen : a2CompensationPaid ≡ false
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
    "d4db1536707e18cd0a7551e30f996edf29626a5a"

    true true true true true
    true true true true true true true true true true true true
    true true true true true true

    false false false false false false false false false false false false

    refl refl refl refl refl
    refl refl refl refl refl refl refl refl refl refl refl refl
    refl refl refl refl refl refl
    refl refl refl refl refl refl refl refl refl refl refl refl

    "A2: fit the selected eighth allowance (3/1700)*eta0^2*fourthLipschitz inside the already-paid dominant M6 headroom, or sharpen the signed eighth treatment; then prove selected HorizontalFarCurvatureBound CH and completed same-object compensation before PASS/no-go. A1: prove ThreeTapInverseSquareShellPartitionBound, then uniform curvature and compensation. B: prove boundary decay, eventual signedFifthCorrelationGapAt >= 0, and outer-terminal convergence."
    "Lean owns all real analysis. Agda mirrors K/U/O/C provenance/status only and must not manufacture A1 shell summation, curvature, compensation, A2 selected-K/far-curvature/compensation/strict scalar, Route-B sign/limits, kernel receipt, or RH."
    "Route B now has exactly three analytic producers: boundary decay, eventual direct signed-gap nonnegativity, and outer-terminal convergence. Large-cutoff ownership is mechanical and no longer counts as an analytic premise."

a2DominantCoefficientIsPaid :
  ThreeTapCurrentLeanFrontier.a2DominantCoefficientPaid
    currentThreeTapCurrentLeanFrontier ≡ true
a2DominantCoefficientIsPaid = refl

a2ThresholdProvenanceIsExplicit :
  ThreeTapCurrentLeanFrontier.a2ThresholdProvenanceExplicit
    currentThreeTapCurrentLeanFrontier ≡ true
a2ThresholdProvenanceIsExplicit = refl

a2LeadingScaleSplitIsSourceWritten :
  ThreeTapCurrentLeanFrontier.a2LeadingScaleSplitSourceWritten
    currentThreeTapCurrentLeanFrontier ≡ true
a2LeadingScaleSplitIsSourceWritten = refl

a2EnvelopeExpansionsAreSourceWritten :
  ThreeTapCurrentLeanFrontier.a2CanonicalEnvelopeExpansionsSourceWritten
    currentThreeTapCurrentLeanFrontier ≡ true
a2EnvelopeExpansionsAreSourceWritten = refl

a2FarBaseShellIsPaid :
  ThreeTapCurrentLeanFrontier.a2FarBaseShellPaid
    currentThreeTapCurrentLeanFrontier ≡ true
a2FarBaseShellIsPaid = refl

a2FarHorizontalCompilerIsSourceWritten :
  ThreeTapCurrentLeanFrontier.a2FarHorizontalConditionalCompilerSourceWritten
    currentThreeTapCurrentLeanFrontier ≡ true
a2FarHorizontalCompilerIsSourceWritten = refl

routeBCutoffOwnershipIsSourceWritten :
  ThreeTapCurrentLeanFrontier.routeBCutoffOwnershipSourceWritten
    currentThreeTapCurrentLeanFrontier ≡ true
routeBCutoffOwnershipIsSourceWritten = refl

routeBThreeProducerCompilerIsSourceWritten :
  ThreeTapCurrentLeanFrontier.routeBThreeProducerCompilerSourceWritten
    currentThreeTapCurrentLeanFrontier ≡ true
routeBThreeProducerCompilerIsSourceWritten = refl

a1CarrierIsStillOpen :
  ThreeTapCurrentLeanFrontier.a1CarrierSummationPaid
    currentThreeTapCurrentLeanFrontier ≡ false
a1CarrierIsStillOpen = refl

a2LeadingConstantsAreStillOpen :
  ThreeTapCurrentLeanFrontier.a2LeadingConstantsPaid
    currentThreeTapCurrentLeanFrontier ≡ false
a2LeadingConstantsAreStillOpen = refl

a2HorizontalFarCurvatureIsStillOpen :
  ThreeTapCurrentLeanFrontier.a2HorizontalFarCurvaturePaid
    currentThreeTapCurrentLeanFrontier ≡ false
a2HorizontalFarCurvatureIsStillOpen = refl

a2CompensationIsStillOpen :
  ThreeTapCurrentLeanFrontier.a2CompensationPaid
    currentThreeTapCurrentLeanFrontier ≡ false
a2CompensationIsStillOpen = refl

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
