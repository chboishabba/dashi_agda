module DASHI.Physics.Closure.NSKatoHessianConfinementReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Corrected Kato/Hessian confinement diagnostic receipt.
--
-- This is a strict fail-closed receipt for the corrected sign convention at a
-- true λ2 minimum / vortex-core target: Hess(λ2) should be positive
-- semidefinite; positive ∂e1∂e2 λ2 is confinement evidence, not adverse
-- evidence.  The N=128 target record is purely symbolic/typed and is
-- empirical-only.  The receipt also keeps the diagonal identity, signed gap,
-- PSD minimum, gap-collapse, H5/H6, and Clay bridge blocker surfaces
-- explicit while remaining fail-closed.  The Kato-Morse program rows below
-- are corrected so CL2 is a trichotomy surface rather than a dichotomy
-- surface, CL1 remains open/fail-closed, CL1b remains open as a PDE-gap route,
-- CL1/CL1b now target ∂Ω_K / the boundary layer rather than interior Ω_K
-- localization, millerToH5 is closeable by standard interpolation but not yet
-- inhabited here,
-- and Calc E remains empirical-only.

data NSKatoHessianSign : Set where
  signNegative : NSKatoHessianSign
  signPositive : NSKatoHessianSign

data NSKatoHessianConfinementStatus : Set where
  failClosedShapeOnly : NSKatoHessianConfinementStatus

record NSKatoHessianEigenvalueProjection : Set where
  constructor mkNSKatoHessianEigenvalueProjection
  field
    eigenAxis : Nat
    eigenAxisLabel : String
    eigenvalue : String

record NSKatoHessianFullHessian3DProjection : Set where
  constructor mkNSKatoHessianFullHessian3DProjection
  field
    hessianCoreGeometryIsTriaxial : Bool
    hessianCoreGeometryIsTriaxialIsTrue :
      hessianCoreGeometryIsTriaxial ≡ true
    hessianCoreIsInfiniteTubeLike : Bool
    hessianCoreIsInfiniteTubeLikeIsFalse :
      hessianCoreIsInfiniteTubeLike ≡ false
    h33IsLarge : Bool
    h33IsLargeIsTrue :
      h33IsLarge ≡ true
    h33Eigenvalue : String
    h33EigenvalueIsCanonical :
      h33Eigenvalue ≡ "11754.22"
    fullHessianEigenvalues : List NSKatoHessianEigenvalueProjection

canonicalNSKatoHessianFullHessianEigenvalues :
  List NSKatoHessianEigenvalueProjection
canonicalNSKatoHessianFullHessianEigenvalues =
  mkNSKatoHessianEigenvalueProjection 1 "λ1" "1612.35"
  ∷ mkNSKatoHessianEigenvalueProjection 2 "λ2" "7131.77"
  ∷ mkNSKatoHessianEigenvalueProjection 3 "h33" "11754.22"
  ∷ []

canonicalNSKatoHessianFullHessian3DProjection :
  NSKatoHessianFullHessian3DProjection
canonicalNSKatoHessianFullHessian3DProjection =
  mkNSKatoHessianFullHessian3DProjection
    true
    refl
    false
    refl
    true
    refl
    "11754.22"
    refl
    canonicalNSKatoHessianFullHessianEigenvalues

data NSKatoHessianConfinementShape : Set where
  hessianPSDAtTrueLambda2Core : NSKatoHessianConfinementShape
  lambda2NegativeRegionShapeRecorded : NSKatoHessianConfinementShape
  katoDiagonalIdentityShapeRecorded : NSKatoHessianConfinementShape
  signedGapStructureShapeRecorded : NSKatoHessianConfinementShape
  positiveCrossDerivativeIsConfinementEvidence : NSKatoHessianConfinementShape
  negativeCrossDerivativeConfinementCorrectionRecorded : NSKatoHessianConfinementShape
  globalLocalMinimumAtTrueVortexCore : NSKatoHessianConfinementShape
  psdMinimumConfinementRecorded : NSKatoHessianConfinementShape
  gapCollapseImpliesHessianBlowUpRecorded : NSKatoHessianConfinementShape
  curvatureSobolevH5H6SplitRecorded : NSKatoHessianConfinementShape
  hessian3DCoreTriaxialRecorded : NSKatoHessianConfinementShape
  hessian3DFullEigenSpectrumRecorded : NSKatoHessianConfinementShape
  n128TwoPlaneHessianPositiveDefiniteRecorded : NSKatoHessianConfinementShape
  trueKatoStableFractionRecorded : NSKatoHessianConfinementShape
  kappaAbsGt1FractionRecorded : NSKatoHessianConfinementShape
  kappaSignedGt1FractionRecorded : NSKatoHessianConfinementShape
  pressureHessianAdverseOnPositiveLaneRecorded : NSKatoHessianConfinementShape
  pressureQcritRouteAdverseRecorded : NSKatoHessianConfinementShape
  katoTubeBoundaryTheoremCandidateOnlyRecorded : NSKatoHessianConfinementShape
  omegaTubeOmegaSheetSplitCorrectedRecorded : NSKatoHessianConfinementShape
  millerBridgeOpenTheoremCandidateOnlyRecorded : NSKatoHessianConfinementShape
  clayBridgeOpenTheoremCandidateOnlyRecorded : NSKatoHessianConfinementShape
  divergenceMachinePrecisionRecorded : NSKatoHessianConfinementShape
  calcEEmpiricalProjectionRecorded : NSKatoHessianConfinementShape
  calcEEmpiricalReceiptRecorded : NSKatoHessianConfinementShape
  cl1MathematicallyOpenRecorded : NSKatoHessianConfinementShape
  cl1FailClosedRecorded : NSKatoHessianConfinementShape
  cl1CorrectedBoundaryLayerRecorded : NSKatoHessianConfinementShape
  cl1CorrectedBoundaryConcentrationStepARecorded : NSKatoHessianConfinementShape
  cl1CorrectedBoundaryConcentrationStepBRecorded : NSKatoHessianConfinementShape
  cl1CorrectedBoundaryConcentrationStepCRecorded : NSKatoHessianConfinementShape
  boundaryH_BRecorded : NSKatoHessianConfinementShape
  boundaryHBKornLevelSetHypothesisRecorded : NSKatoHessianConfinementShape
  boundaryMinG12OnBoundaryKRecorded : NSKatoHessianConfinementShape
  boundaryRealRhoOnBoundaryKRecorded : NSKatoHessianConfinementShape
  boundaryBetti0OnBoundaryKRecorded : NSKatoHessianConfinementShape
  boundaryMinG12RhoBettiOptionalCalcRankingRecorded :
    NSKatoHessianConfinementShape
  millerToH5StandardInterpolationRecorded : NSKatoHessianConfinementShape
  millerToH5Lambda2PlusGradientGateRecorded :
    NSKatoHessianConfinementShape
  weakL3ToL3Recorded : NSKatoHessianConfinementShape
  H2ToW13Recorded : NSKatoHessianConfinementShape
  H1H5InterpolationExponentQuarterRecorded :
    NSKatoHessianConfinementShape
  cl1bPDEGapOpenRecorded : NSKatoHessianConfinementShape
  katoIdentityLeafReceiptRecorded : NSKatoHessianConfinementShape
  secondDerivExpandLeafRecorded : NSKatoHessianConfinementShape
  gd3StandardRowRecorded : NSKatoHessianConfinementShape
  gd3CorrectStandardRecorded : NSKatoHessianConfinementShape
  cl2TrichotomyRowRecorded : NSKatoHessianConfinementShape
  cl2DichotomyRejectedRecorded : NSKatoHessianConfinementShape

canonicalNSKatoHessianConfinementShape : List NSKatoHessianConfinementShape
canonicalNSKatoHessianConfinementShape =
  hessianPSDAtTrueLambda2Core
  ∷ lambda2NegativeRegionShapeRecorded
  ∷ katoDiagonalIdentityShapeRecorded
  ∷ signedGapStructureShapeRecorded
  ∷ positiveCrossDerivativeIsConfinementEvidence
  ∷ negativeCrossDerivativeConfinementCorrectionRecorded
  ∷ globalLocalMinimumAtTrueVortexCore
  ∷ psdMinimumConfinementRecorded
  ∷ gapCollapseImpliesHessianBlowUpRecorded
  ∷ curvatureSobolevH5H6SplitRecorded
  ∷ hessian3DCoreTriaxialRecorded
  ∷ hessian3DFullEigenSpectrumRecorded
  ∷ n128TwoPlaneHessianPositiveDefiniteRecorded
  ∷ trueKatoStableFractionRecorded
  ∷ kappaAbsGt1FractionRecorded
  ∷ kappaSignedGt1FractionRecorded
  ∷ pressureHessianAdverseOnPositiveLaneRecorded
  ∷ pressureQcritRouteAdverseRecorded
  ∷ katoTubeBoundaryTheoremCandidateOnlyRecorded
  ∷ omegaTubeOmegaSheetSplitCorrectedRecorded
  ∷ millerBridgeOpenTheoremCandidateOnlyRecorded
  ∷ clayBridgeOpenTheoremCandidateOnlyRecorded
  ∷ divergenceMachinePrecisionRecorded
  ∷ calcEEmpiricalProjectionRecorded
  ∷ calcEEmpiricalReceiptRecorded
  ∷ cl1MathematicallyOpenRecorded
  ∷ cl1FailClosedRecorded
  ∷ cl1CorrectedBoundaryLayerRecorded
  ∷ cl1CorrectedBoundaryConcentrationStepARecorded
  ∷ cl1CorrectedBoundaryConcentrationStepBRecorded
  ∷ cl1CorrectedBoundaryConcentrationStepCRecorded
  ∷ boundaryH_BRecorded
  ∷ boundaryHBKornLevelSetHypothesisRecorded
  ∷ boundaryMinG12OnBoundaryKRecorded
  ∷ boundaryRealRhoOnBoundaryKRecorded
  ∷ boundaryBetti0OnBoundaryKRecorded
  ∷ boundaryMinG12RhoBettiOptionalCalcRankingRecorded
  ∷ millerToH5StandardInterpolationRecorded
  ∷ millerToH5Lambda2PlusGradientGateRecorded
  ∷ weakL3ToL3Recorded
  ∷ H2ToW13Recorded
  ∷ H1H5InterpolationExponentQuarterRecorded
  ∷ cl1bPDEGapOpenRecorded
  ∷ katoIdentityLeafReceiptRecorded
  ∷ secondDerivExpandLeafRecorded
  ∷ gd3StandardRowRecorded
  ∷ gd3CorrectStandardRecorded
  ∷ cl2TrichotomyRowRecorded
  ∷ cl2DichotomyRejectedRecorded
  ∷ []

data NSKatoHessianConfinementBlocker : Set where
  millerBridgeOpenTheoremCandidateOnly :
    NSKatoHessianConfinementBlocker
  clayBridgeOpenTheoremCandidateOnly :
    NSKatoHessianConfinementBlocker
  noExternalDNSPromotion :
    NSKatoHessianConfinementBlocker
  noFullRegularityInhabitant :
    NSKatoHessianConfinementBlocker
  millerToH5NotInhabitedHere :
    NSKatoHessianConfinementBlocker
  cl1bPDEGapOpen :
    NSKatoHessianConfinementBlocker
  noClayPromotion :
    NSKatoHessianConfinementBlocker

canonicalNSKatoHessianConfinementBlockers : List NSKatoHessianConfinementBlocker
canonicalNSKatoHessianConfinementBlockers =
  millerBridgeOpenTheoremCandidateOnly
  ∷ clayBridgeOpenTheoremCandidateOnly
  ∷ noExternalDNSPromotion
  ∷ noFullRegularityInhabitant
  ∷ millerToH5NotInhabitedHere
  ∷ cl1bPDEGapOpen
  ∷ noClayPromotion
  ∷ []

data NSKatoHessianConfinementAnalyticalRequirement : Set where
  standardInterpolationToH5CloseableNotInhabitedHere :
    NSKatoHessianConfinementAnalyticalRequirement
  cl1bBoundaryLayerLocalizationOpenPDE :
    NSKatoHessianConfinementAnalyticalRequirement
  noNewCalcERunInThisReceipt :
    NSKatoHessianConfinementAnalyticalRequirement
  optionalCalcMinG12OnBoundaryLayer :
    NSKatoHessianConfinementAnalyticalRequirement
  optionalCalcRealRhoOnBoundaryK :
    NSKatoHessianConfinementAnalyticalRequirement
  optionalCalcBetti0 :
    NSKatoHessianConfinementAnalyticalRequirement

canonicalNSKatoHessianConfinementAnalyticalRequirements :
  List NSKatoHessianConfinementAnalyticalRequirement
canonicalNSKatoHessianConfinementAnalyticalRequirements =
  standardInterpolationToH5CloseableNotInhabitedHere
  ∷ cl1bBoundaryLayerLocalizationOpenPDE
  ∷ noNewCalcERunInThisReceipt
  ∷ optionalCalcMinG12OnBoundaryLayer
  ∷ optionalCalcRealRhoOnBoundaryK
  ∷ optionalCalcBetti0
  ∷ []

shapeHessianPSDText : String
shapeHessianPSDText =
  "At a true global/local λ2 minimum, mixed-direction Hessian for λ2 is recorded as positive semidefinite by calculus."

shapeLambda2NegativeRegionText : String
shapeLambda2NegativeRegionText =
  "λ2<0 region is recorded as the true Kato-sign region used in the N=128 aggregate receipt."

shapeCrossDerivativePositiveText : String
shapeCrossDerivativePositiveText =
  "At the true λ2 minimum/vortex core, cross-derivative sign support is recorded as positive; this is the confinement signal."

shapeSignCorrectionText : String
shapeSignCorrectionText =
  "The prior negative-cross-derivative-as-confinement convention is corrected: positive cross-derivative supports confinement at the true core minimum."

shapePressureHessianText : String
shapePressureHessianText =
  "Pressure-Hessian local cross term is recorded as positive and adverse to confinement-sign promotion."

shapeHessian3DGeometryText : String
shapeHessian3DGeometryText =
  "Core geometry is recorded as triaxial (not infinite-tube-like); h33 is large and 3D."

shapeFullHessianEigenvaluesText : String
shapeFullHessianEigenvaluesText =
  "Full 3D Hessian eigenvalues are recorded as [1612.35, 7131.77, 11754.22]."

shapeTwoPlaneHessianText : String
shapeTwoPlaneHessianText =
  "N=128 true-core 2-plane Hessian block is recorded empirically as positive definite; this is a consistency datum only, not a theorem."

shapeTrueKatoStableFractionText : String
shapeTrueKatoStableFractionText =
  "Aggregate N=128 true Kato stable fraction / cross-derivative-positive fraction is recorded at approximately 49.75%."

shapeKappaAbsGt1FractionText : String
shapeKappaAbsGt1FractionText =
  "Aggregate N=128 kappa_abs_gt_1 fraction is recorded at approximately 30.63%."

shapeKappaSignedGt1FractionText : String
shapeKappaSignedGt1FractionText =
  "Aggregate N=128 kappa_signed_gt_1 fraction is recorded at approximately 15.29%."

shapePressureQcritRouteAdverseText : String
shapePressureQcritRouteAdverseText =
  "Pressure/Qcrit route is recorded as adverse to confinement promotion and remains fail-closed."

shapeKatoTubeBoundaryCandidateText : String
shapeKatoTubeBoundaryCandidateText =
  "Kato tube boundary is recorded as theorem-candidate only, not a promoted theorem."

shapeOmegaTubeOmegaSheetSplitText : String
shapeOmegaTubeOmegaSheetSplitText =
  "Corrected Ωtube/Ωsheet split is recorded in the aggregate N=128 table; the split is empirical, typed, and not promoted."

shapeMillerBridgeOpenText : String
shapeMillerBridgeOpenText =
  "Miller bridge is recorded as open only as a theorem-candidate route; no promotion is claimed."

shapeMillerToH5StandardInterpolationText : String
shapeMillerToH5StandardInterpolationText =
  "millerToH5 is recorded as a closeable standard-interpolation projection row on the boundary-layer CL1 surface; the chain is lambda2+ <= ||grad u||_F / 2, weak-L3 <= L3, H2 -> W1,3, and H1/H5 interpolation with exponent 1/4, and the inhabitant is not yet provided here."

shapeMillerToH5Lambda2PlusGradientGateText : String
shapeMillerToH5Lambda2PlusGradientGateText =
  "millerToH5 records the lambda2+ <= ||grad u||_F / 2 gate as the first closeable standard package step."

shapeWeakL3ToL3Text : String
shapeWeakL3ToL3Text =
  "weak-L3 <= L3 is recorded as the standard embedding step in the closeable package."

shapeH2ToW13Text : String
shapeH2ToW13Text =
  "H2 -> W1,3 is recorded as the standard Sobolev step in the closeable package."

shapeH1H5InterpolationExponentText : String
shapeH1H5InterpolationExponentText =
  "H1/H5 interpolation exponent is recorded as 1/4."

shapeCL1CorrectedBoundaryConcentrationStepAText : String
shapeCL1CorrectedBoundaryConcentrationStepAText =
  "CL1 boundary-concentration Step A is corrected to the boundary layer and is restricted to ∂Ω_K localization; the step is recorded as open and fail-closed."

shapeCL1CorrectedBoundaryConcentrationStepBText : String
shapeCL1CorrectedBoundaryConcentrationStepBText =
  "CL1 boundary-concentration Step B is corrected to the boundary layer and is restricted to ∂Ω_K localization; the step is recorded as open and fail-closed."

shapeCL1CorrectedBoundaryConcentrationStepCText : String
shapeCL1CorrectedBoundaryConcentrationStepCText =
  "CL1 boundary-concentration Step C is corrected to the boundary layer and is restricted to ∂Ω_K localization; the step is recorded as open and fail-closed."

shapeCL1CorrectedBoundaryLayerText : String
shapeCL1CorrectedBoundaryLayerText =
  "CL1 is corrected to the boundary layer: the target is ∂Ω_K / boundary-layer localization, not interior Ω_K localization, and the row remains open and fail-closed."

shapeBoundaryHBText : String
shapeBoundaryHBText =
  "boundary H_B is recorded on the boundary-layer surface / ∂Ω_K only; no interior Ω_K claim is made."

shapeBoundaryHBKornLevelSetHypothesisText : String
shapeBoundaryHBKornLevelSetHypothesisText =
  "Calc 10 records the h_strain_dom / alpha_strain_sq BoundaryHB/KornLevelSet hypothesis as an empirical boundary row only: frame 10 component 2 at bands 5e-4, 2.5e-4, and 1e-4 has c_empirical_true in [0.04180143943317622, 0.048108231165891815], alpha_strain_sq in [0.49648633477014364, 0.49956437854373653], and alpha_omega_sq in [0.5004356214562633, 0.5035136652298564]; no Clay theorem authority and no proof of KornLevelSet are claimed."

shapeBoundaryMinG12OnBoundaryKText : String
shapeBoundaryMinG12OnBoundaryKText =
  "Diagnostic calc: minimum of g12 on ∂Ω_K."

shapeBoundaryRealRhoOnBoundaryKText : String
shapeBoundaryRealRhoOnBoundaryKText =
  "Diagnostic calc: real rho on ∂Ω_K."

shapeBoundaryBetti0OnBoundaryKText : String
shapeBoundaryBetti0OnBoundaryKText =
  "Diagnostic calc: Betti-0 on ∂Ω_K."

shapeBoundaryMinG12RhoBettiOptionalCalcRankingText : String
shapeBoundaryMinG12RhoBettiOptionalCalcRankingText =
  "Optional calc ranking is boundary-first and boundary-layer localized: min g12 on ∂Ω_K, real rho on ∂Ω_K, then Betti-0 count; Miller λ2+ is outside/at boundary, not interior."

shapeBoundaryConcentrationStepA_PerComponentText : String
shapeBoundaryConcentrationStepA_PerComponentText =
  "Revised per-component boundary diagnostic after Betti-0 fragmentation: boundaryConcentrationStepA_PerComponent is the checked surface; the frame-10 component diagnostic ran as empirical/non-promoting JSON at scripts/data/outputs/ns_boundary_component_frame10/ns_boundary_component_N128_frame10_20260618.json; min-g12 is threshold-adjacent to components 2 and 16531 rather than threshold-contained, min-rho is inside component 2, and the frame-10 layer-thickness diagnostic ran as empirical/non-promoting JSON at scripts/data/outputs/ns_boundary_component_frame10/ns_boundary_layer_thickness_N128_frame10_20260618.json with component 2 resolved at 162 boundary-layer samples and transition thickness mean 2.4566 cells / 0.12059 physical units while component 16531 has no |lambda2| <= 1e-3 layer samples; Calc 7 temporal persistence ran as scripts/data/outputs/ns_boundary_carrier_timeseries_N128_20260618.json and records carrier 1 on frames 0-6, carrier 2 on frames 7-8 and 10-12, singleton carrier 11028 on frame 9, and singleton/no-layer warnings for 16531 and 3906; global BoundaryConnected is replaced by a component-carrying hypothesis."

shapeCL1bPDEGapText : String
shapeCL1bPDEGapText =
  "CL1b is recorded as an open PDE-gap boundary-layer route near ∂Ω_K and remains fail-closed/uninhabited in this receipt."

shapeDivergenceText : String
shapeDivergenceText =
  "Machine-precision divergence consistency is recorded as fail-closed empirical state."

shapeCalcEEmpiricalProjectionText : String
shapeCalcEEmpiricalProjectionText =
  "Calc E is recorded as empirical, non-promoting evidence: the 2026-06-18 boundary preflight calc was run on dashiCFD N128 frames and remains empirical/non-promoting; CL1 remains open and fail-closed; optional calcs are ranked as min g12 on ∂Ω_K, real rho on ∂Ω_K, then Betti-0 count; the closeable standard package is recorded separately as lambda2+ <= ||grad u||_F / 2, weak-L3 <= L3, H2 -> W1,3, and H1/H5 interpolation exponent 1/4; Miller λ2+ is outside/at boundary; rho_min stays positive with global minimum 0.23098019784845852 and Scenario D unsupported in dataset; boundary H_B numerically supported only; Calc 6 adds frame-10 component-2 Korn proxy ratio c_empirical_proxy = 8.688873662021036 at scripts/data/outputs/ns_boundary_component_frame10/ns_boundary_korn_ratio_N128_frame10_component2_20260618.json using denominator grad_lambda2_squared_proxy; Calc 8 adds the true velocity_hessian_norm_squared denominator at scripts/data/outputs/ns_boundary_component_frame10/ns_boundary_korn_ratio_true_N128_frame10_component2_20260618.json with c_empirical_true = 0.04974806822750822 and denominator_proxy_to_true_ratio = 0.0057254910317037335; Calc 9 extends the true denominator to the carrier timeseries at scripts/data/outputs/ns_boundary_component_frame10/ns_boundary_true_korn_timeseries_N128_20260618.json with c_empirical_true_min = 0.0026738091511738582, c_empirical_true_mean = 0.04374066464321035, c_empirical_true_max = 0.052591467297035434, and denominator_proxy_to_true_ratio_mean = 0.0053820601514769605; Calc 10 adds scripts/data/outputs/ns_boundary_component_frame10/ns_boundary_band_sweep_N128_frame10_component2_20260618.json with c_empirical_true in [0.04180143943317622, 0.048108231165891815], alpha_strain_sq in [0.49648633477014364, 0.49956437854373653], and alpha_omega_sq in [0.5004356214562633, 0.5035136652298564]; all are empirical and not analytic KornLevelSet proofs."

shapeCalcEEmpiricalReceiptText : String
shapeCalcEEmpiricalReceiptText =
  "Calc E stays empirical and non-promoting on this receipt surface; the 2026-06-18 boundary preflight calc was run on dashiCFD N128 frames and remains empirical/non-promoting; CL1 remains open and fail-closed; Calcs 1-10 are now recorded for this archive, including Calc 6 Korn proxy ratio, Calc 7 carrier persistence, Calc 8 true velocity-Hessian Korn denominator for frame-10 component 2, Calc 9 true velocity-Hessian Korn denominator over the carrier timeseries, and Calc 10 h_strain_dom / alpha_strain_sq BoundaryHB/KornLevelSet hypothesis with the frame-10 component-2 band sweep; the closeable standard package is carried as lambda2+ <= ||grad u||_F / 2, weak-L3 <= L3, H2 -> W1,3, and H1/H5 interpolation exponent 1/4; but no Clay theorem or BoundaryHB/KornLevelSet promotion is claimed."

shapeCL1OpenFailClosedText : String
shapeCL1OpenFailClosedText =
  "CL1 remains mathematically open and fail-closed; no theorem promotion is claimed."

shapeKatoIdentityLeafReceiptText : String
shapeKatoIdentityLeafReceiptText =
  "KatoIdentity leaf receipt records the checked secondDeriv-expand surface, the GD3 standard row, the GD3-SobolevBound-Correct projection, and CL2 trichotomy row without optional calc results; the latest GD3 payload names M, hM_pos, hM, δ0, δ1, hδ_pos, hδ, hδ1_pos, hδ1, δmin, C_emb, g23, C_k, hess_le_Ak_plus_Bk, Ak_le_D3u, sobolev_H5_C3, Bk/g12, Ck/g23, and the final GD3-SobolevBound-Correct bound C_emb*M + 2*C_emb^2*M^2/δ0 + 2*C_emb^2*M^2/δ1 are carried on this same leaf surface, with an optional compressed form using δmin noted but not promoted."

shapeSecondDerivExpandText : String
shapeSecondDerivExpandText =
  "secondDeriv-expand is the checked leaf surface name and is recorded only as a surface marker."

shapeGD3StandardRowText : String
shapeGD3StandardRowText =
  "GD3 is recorded as standard on the KatoIdentity leaf receipt, with no promotion beyond the typed row."

shapeGD3SobolevBoundCorrectRowName : String
shapeGD3SobolevBoundCorrectRowName =
  "GD3-SobolevBound-Correct"

shapeGD3SobolevBoundCorrectText : String
shapeGD3SobolevBoundCorrectText =
  "GD3-SobolevBound-Correct is an exact checked projection row on the KatoIdentity leaf: the latest payload keeps M, hM_pos, hM, δ0, δ1, hδ_pos, hδ, hδ1_pos, hδ1, δmin, C_emb, g23, and C_k as exact names; hess_le_Ak_plus_Bk, Ak_le_D3u, and sobolev_H5_C3 are exact shapes; B_k/g12 and C_k/g23 are carried as the two-gap Kato bounds; the final two-gap upper bound is recorded as C_emb*M + 2*C_emb^2*M^2/δ0 + 2*C_emb^2*M^2/δ1; and the optional compressed form C_emb*M + 4*C_emb^2*M^2/δmin is noted without any promotion claim."

canonicalGD3SobolevBoundCorrectProjectionRows : List String
canonicalGD3SobolevBoundCorrectProjectionRows =
  "M"
  ∷ "g23"
  ∷ "C_k"
  ∷ "δ0"
  ∷ "δ1"
  ∷ "δmin"
  ∷ "H5 <= M"
  ∷ "C_embed"
  ∷ "B_k/g12"
  ∷ "C_k/g23"
  ∷ "B_k quadratic in H5"
  ∷ "hM_pos"
  ∷ "hM"
  ∷ "hδ_pos"
  ∷ "hδ"
  ∷ "hδ1_pos"
  ∷ "hδ1"
  ∷ "C_emb"
  ∷ "hess_le_Ak_plus_Bk"
  ∷ "Ak_le_D3u"
  ∷ "sobolev_H5_C3"
  ∷ "Bk quadratic bound"
  ∷ "final GD3-SobolevBound-Correct bound"
  ∷ "optional compressed δmin formula"
  ∷ []

shapeCL2TrichotomyRowText : String
shapeCL2TrichotomyRowText =
  "CL2 is recorded as trichotomy on the KatoIdentity leaf receipt, not as a dichotomy."

shapeCL2BranchCText : String
shapeCL2BranchCText =
  "CL2 branch C is explicitly checked on this ledger and remains open only as a non-promoting trichotomy branch."

shapeCL2DichotomyRejectedText : String
shapeCL2DichotomyRejectedText =
  "CL2 dichotomy semantics are rejected on this leaf receipt surface."

shapeMillerToH5CloseableText : String
shapeMillerToH5CloseableText =
  "millerToH5 is recorded as a closeable standard-interpolation surface and stays uninhabited here; the package names lambda2+ <= ||grad u||_F / 2, weak-L3 <= L3, H2 -> W1,3, and H1/H5 interpolation exponent 1/4."

shapeGD3CorrectStandardText : String
shapeGD3CorrectStandardText =
  "GD3-correct is recorded as a standard closeable row on the KatoIdentity leaf surface, with no promotion beyond the typed receipt."

canonicalNSKatoIdentityLeafRows : List String
canonicalNSKatoIdentityLeafRows =
  "KatoIdentity"
  ∷ "secondDeriv-expand"
  ∷ "GD3"
  ∷ shapeGD3SobolevBoundCorrectRowName
  ∷ "CL2"
  ∷ "CL2 branch C"
  ∷ []

record NSKatoIdentityLeafReceipt : Set where
  constructor mkNSKatoIdentityLeafReceipt
  field
    leafName : String
    leafNameIsCanonical :
      leafName ≡ "KatoIdentity"
    checkedRows : List String
    checkedRowsIsCanonical :
      checkedRows ≡ canonicalNSKatoIdentityLeafRows
    katoIdentityLeafReceiptText : String
    katoIdentityLeafReceiptTextIsCanonical :
      katoIdentityLeafReceiptText ≡ shapeKatoIdentityLeafReceiptText
    secondDerivExpandRowName : String
    secondDerivExpandRowNameIsCanonical :
      secondDerivExpandRowName ≡ "secondDeriv-expand"
    secondDerivExpandRecorded : Bool
    secondDerivExpandRecordedIsTrue :
      secondDerivExpandRecorded ≡ true
    secondDerivExpandText : String
    secondDerivExpandTextIsCanonical :
      secondDerivExpandText ≡ shapeSecondDerivExpandText
    gd3RowName : String
    gd3RowNameIsCanonical :
      gd3RowName ≡ "GD3"
    gd3StandardReceiptRecorded : Bool
    gd3StandardReceiptRecordedIsTrue :
      gd3StandardReceiptRecorded ≡ true
    gd3StandardText : String
    gd3StandardTextIsCanonical :
      gd3StandardText ≡ shapeGD3StandardRowText
    gd3SobolevBoundCorrectRowName : String
    gd3SobolevBoundCorrectRowNameIsCanonical :
      gd3SobolevBoundCorrectRowName ≡
      shapeGD3SobolevBoundCorrectRowName
    gd3SobolevBoundCorrectRowRecorded : Bool
    gd3SobolevBoundCorrectRowRecordedIsTrue :
      gd3SobolevBoundCorrectRowRecorded ≡ true
    gd3SobolevBoundCorrectText : String
    gd3SobolevBoundCorrectTextIsCanonical :
      gd3SobolevBoundCorrectText ≡ shapeGD3SobolevBoundCorrectText
    gd3SobolevBoundCorrectProjectionRows : List String
    gd3SobolevBoundCorrectProjectionRowsIsCanonical :
      gd3SobolevBoundCorrectProjectionRows ≡
      canonicalGD3SobolevBoundCorrectProjectionRows
    cl2RowName : String
    cl2RowNameIsCanonical :
      cl2RowName ≡ "CL2"
    cl2TrichotomyReceiptRecorded : Bool
    cl2TrichotomyReceiptRecordedIsTrue :
      cl2TrichotomyReceiptRecorded ≡ true
    cl2BranchCRecorded : Bool
    cl2BranchCRecordedIsTrue :
      cl2BranchCRecorded ≡ true
    cl2BranchCText : String
    cl2BranchCTextIsCanonical :
      cl2BranchCText ≡ shapeCL2BranchCText
    cl2DichotomyReceiptRecorded : Bool
    cl2DichotomyReceiptRecordedIsFalse :
      cl2DichotomyReceiptRecorded ≡ false
    cl2TrichotomyText : String
    cl2TrichotomyTextIsCanonical :
      cl2TrichotomyText ≡ shapeCL2TrichotomyRowText
    cl2DichotomyRejectedText : String
    cl2DichotomyRejectedTextIsCanonical :
      cl2DichotomyRejectedText ≡ shapeCL2DichotomyRejectedText
    optionalCalcResultsRecorded : Bool
    optionalCalcResultsRecordedIsFalse :
      optionalCalcResultsRecorded ≡ false

canonicalNSKatoIdentityLeafReceipt : NSKatoIdentityLeafReceipt
canonicalNSKatoIdentityLeafReceipt =
  mkNSKatoIdentityLeafReceipt
    "KatoIdentity"
    refl
    canonicalNSKatoIdentityLeafRows
    refl
    shapeKatoIdentityLeafReceiptText
    refl
    "secondDeriv-expand"
    refl
    true
    refl
    shapeSecondDerivExpandText
    refl
    "GD3"
    refl
    true
    refl
    shapeGD3StandardRowText
    refl
    shapeGD3SobolevBoundCorrectRowName
    refl
    true
    refl
    shapeGD3SobolevBoundCorrectText
    refl
    canonicalGD3SobolevBoundCorrectProjectionRows
    refl
    "CL2"
    refl
    true
    refl
    true
    refl
    shapeCL2BranchCText
    refl
    false
    refl
    shapeCL2TrichotomyRowText
    refl
    shapeCL2DichotomyRejectedText
    refl
    false
    refl

record NSKatoCalcEEmpiricalProjection : Set where
  constructor mkNSKatoCalcEEmpiricalProjection
  field
    projectionText : String
    projectionTextIsCanonical :
      projectionText ≡ shapeCalcEEmpiricalProjectionText
    rhoApproxText : String
    rhoApproxTextIsCanonical :
      rhoApproxText ≡ "rho approx 8.02 at TG N=128 t≈9"
    scenarioDUnsupportedText : String
    scenarioDUnsupportedTextIsCanonical :
      scenarioDUnsupportedText ≡ "Scenario D unsupported in dataset"
    hBNumericallySupportedOnlyText : String
    hBNumericallySupportedOnlyTextIsCanonical :
      hBNumericallySupportedOnlyText ≡ "boundary H_B numerically supported only"
    calc10BoundaryHBKornLevelSetHypothesisText : String
    calc10BoundaryHBKornLevelSetHypothesisTextIsCanonical :
      calc10BoundaryHBKornLevelSetHypothesisText ≡
      shapeBoundaryHBKornLevelSetHypothesisText
    boundaryMinG12OnBoundaryKText : String
    boundaryMinG12OnBoundaryKTextIsCanonical :
      boundaryMinG12OnBoundaryKText ≡ shapeBoundaryMinG12OnBoundaryKText
    boundaryRealRhoOnBoundaryKText : String
    boundaryRealRhoOnBoundaryKTextIsCanonical :
      boundaryRealRhoOnBoundaryKText ≡ shapeBoundaryRealRhoOnBoundaryKText
    boundaryBetti0OnBoundaryKText : String
    boundaryBetti0OnBoundaryKTextIsCanonical :
      boundaryBetti0OnBoundaryKText ≡ shapeBoundaryBetti0OnBoundaryKText
    boundaryMinG12RhoBettiOptionalCalcRankingText : String
    boundaryMinG12RhoBettiOptionalCalcRankingTextIsCanonical :
      boundaryMinG12RhoBettiOptionalCalcRankingText ≡
      shapeBoundaryMinG12RhoBettiOptionalCalcRankingText
    millerToH5Lambda2PlusGradientGateText : String
    millerToH5Lambda2PlusGradientGateTextIsCanonical :
      millerToH5Lambda2PlusGradientGateText ≡
      shapeMillerToH5Lambda2PlusGradientGateText
    weakL3ToL3Text : String
    weakL3ToL3TextIsCanonical :
      weakL3ToL3Text ≡ shapeWeakL3ToL3Text
    H2ToW13Text : String
    H2ToW13TextIsCanonical :
      H2ToW13Text ≡ shapeH2ToW13Text
    H1H5InterpolationExponentText : String
    H1H5InterpolationExponentTextIsCanonical :
      H1H5InterpolationExponentText ≡
      shapeH1H5InterpolationExponentText
    empiricalOnly : Bool
    empiricalOnlyIsTrue :
      empiricalOnly ≡ true
    nonPromoting : Bool
    nonPromotingIsTrue :
      nonPromoting ≡ true

canonicalNSKatoCalcEEmpiricalProjection :
  NSKatoCalcEEmpiricalProjection
canonicalNSKatoCalcEEmpiricalProjection =
  mkNSKatoCalcEEmpiricalProjection
    shapeCalcEEmpiricalProjectionText
    refl
    "rho approx 8.02 at TG N=128 t≈9"
    refl
    "Scenario D unsupported in dataset"
    refl
    "boundary H_B numerically supported only"
    refl
    shapeBoundaryHBKornLevelSetHypothesisText
    refl
    shapeBoundaryMinG12OnBoundaryKText
    refl
    shapeBoundaryRealRhoOnBoundaryKText
    refl
    shapeBoundaryBetti0OnBoundaryKText
    refl
    shapeBoundaryMinG12RhoBettiOptionalCalcRankingText
    refl
    shapeMillerToH5Lambda2PlusGradientGateText
    refl
    shapeWeakL3ToL3Text
    refl
    shapeH2ToW13Text
    refl
    shapeH1H5InterpolationExponentText
    refl
    true
    refl
    true
    refl

record NSKatoCalcEEmpiricalReceipt : Set where
  constructor mkNSKatoCalcEEmpiricalReceipt
  field
    projection :
      NSKatoCalcEEmpiricalProjection
    projectionIsCanonical :
      projection ≡ canonicalNSKatoCalcEEmpiricalProjection
    calcEEmpiricalReceiptText : String
    calcEEmpiricalReceiptTextIsCanonical :
      calcEEmpiricalReceiptText ≡ shapeCalcEEmpiricalReceiptText
    cl1CorrectedBoundaryLayerText : String
    cl1CorrectedBoundaryLayerTextIsCanonical :
      cl1CorrectedBoundaryLayerText ≡ shapeCL1CorrectedBoundaryLayerText
    cl1BoundaryConcentrationStepAText : String
    cl1BoundaryConcentrationStepATextIsCanonical :
      cl1BoundaryConcentrationStepAText ≡
      shapeCL1CorrectedBoundaryConcentrationStepAText
    cl1BoundaryConcentrationStepBText : String
    cl1BoundaryConcentrationStepBTextIsCanonical :
      cl1BoundaryConcentrationStepBText ≡
      shapeCL1CorrectedBoundaryConcentrationStepBText
    cl1BoundaryConcentrationStepCText : String
    cl1BoundaryConcentrationStepCTextIsCanonical :
      cl1BoundaryConcentrationStepCText ≡
      shapeCL1CorrectedBoundaryConcentrationStepCText
    boundaryHBText : String
    boundaryHBTextIsCanonical :
      boundaryHBText ≡ shapeBoundaryHBText
    boundaryHBKornLevelSetHypothesisText : String
    boundaryHBKornLevelSetHypothesisTextIsCanonical :
      boundaryHBKornLevelSetHypothesisText ≡
      shapeBoundaryHBKornLevelSetHypothesisText
    boundaryMinG12RhoBettiOptionalCalcRankingText : String
    boundaryMinG12RhoBettiOptionalCalcRankingTextIsCanonical :
      boundaryMinG12RhoBettiOptionalCalcRankingText ≡
      shapeBoundaryMinG12RhoBettiOptionalCalcRankingText
    boundaryConcentrationStepA_PerComponentText : String
    boundaryConcentrationStepA_PerComponentTextIsCanonical :
      boundaryConcentrationStepA_PerComponentText ≡
      shapeBoundaryConcentrationStepA_PerComponentText
    millerToH5StandardInterpolationText : String
    millerToH5StandardInterpolationTextIsCanonical :
      millerToH5StandardInterpolationText ≡
      shapeMillerToH5StandardInterpolationText
    millerToH5Lambda2PlusGradientGateText : String
    millerToH5Lambda2PlusGradientGateTextIsCanonical :
      millerToH5Lambda2PlusGradientGateText ≡
      shapeMillerToH5Lambda2PlusGradientGateText
    weakL3ToL3Text : String
    weakL3ToL3TextIsCanonical :
      weakL3ToL3Text ≡ shapeWeakL3ToL3Text
    H2ToW13Text : String
    H2ToW13TextIsCanonical :
      H2ToW13Text ≡ shapeH2ToW13Text
    H1H5InterpolationExponentText : String
    H1H5InterpolationExponentTextIsCanonical :
      H1H5InterpolationExponentText ≡
      shapeH1H5InterpolationExponentText
    millerToH5CloseableText : String
    millerToH5CloseableTextIsCanonical :
      millerToH5CloseableText ≡ shapeMillerToH5CloseableText
    gd3CorrectStandardText : String
    gd3CorrectStandardTextIsCanonical :
      gd3CorrectStandardText ≡ shapeGD3CorrectStandardText
    cl1OpenFailClosedText : String
    cl1OpenFailClosedTextIsCanonical :
      cl1OpenFailClosedText ≡ shapeCL1OpenFailClosedText
    cl1MathematicallyOpen : Bool
    cl1MathematicallyOpenIsTrue :
      cl1MathematicallyOpen ≡ true
    cl1FailClosed : Bool
    cl1FailClosedIsTrue :
      cl1FailClosed ≡ true
    calcEPromoted : Bool
    calcEPromotedIsFalse :
      calcEPromoted ≡ false

canonicalNSKatoCalcEEmpiricalReceipt :
  NSKatoCalcEEmpiricalReceipt
canonicalNSKatoCalcEEmpiricalReceipt =
  mkNSKatoCalcEEmpiricalReceipt
    canonicalNSKatoCalcEEmpiricalProjection
    refl
    shapeCalcEEmpiricalReceiptText
    refl
    shapeCL1CorrectedBoundaryLayerText
    refl
    shapeCL1CorrectedBoundaryConcentrationStepAText
    refl
    shapeCL1CorrectedBoundaryConcentrationStepBText
    refl
    shapeCL1CorrectedBoundaryConcentrationStepCText
    refl
    shapeBoundaryHBText
    refl
    shapeBoundaryHBKornLevelSetHypothesisText
    refl
    shapeBoundaryMinG12RhoBettiOptionalCalcRankingText
    refl
    shapeBoundaryConcentrationStepA_PerComponentText
    refl
    shapeMillerToH5StandardInterpolationText
    refl
    shapeMillerToH5Lambda2PlusGradientGateText
    refl
    shapeWeakL3ToL3Text
    refl
    shapeH2ToW13Text
    refl
    shapeH1H5InterpolationExponentText
    refl
    shapeMillerToH5CloseableText
    refl
    shapeGD3CorrectStandardText
    refl
    shapeCL1OpenFailClosedText
    refl
    true
    refl
    true
    refl
    false
    refl

record NSKatoHessianAggregateStats : Set where
  constructor mkNSKatoHessianAggregateStats
  field
    aggregateN : Nat
    aggregateNIs128 : aggregateN ≡ 128
    lambda2NegativeRegionRecorded : Bool
    lambda2NegativeRegionRecordedIsTrue : lambda2NegativeRegionRecorded ≡ true
    trueKatoStableFractionText : String
    trueKatoStableFractionTextIsCanonical :
      trueKatoStableFractionText ≡ shapeTrueKatoStableFractionText
    kappaAbsGt1FractionText : String
    kappaAbsGt1FractionTextIsCanonical :
      kappaAbsGt1FractionText ≡ shapeKappaAbsGt1FractionText
    kappaSignedGt1FractionText : String
    kappaSignedGt1FractionTextIsCanonical :
      kappaSignedGt1FractionText ≡ shapeKappaSignedGt1FractionText
    pressureQcritRouteAdverse : Bool
    pressureQcritRouteAdverseIsTrue : pressureQcritRouteAdverse ≡ true
    pressureQcritRouteAdverseText : String
    pressureQcritRouteAdverseTextIsCanonical :
      pressureQcritRouteAdverseText ≡ shapePressureQcritRouteAdverseText
    katoTubeBoundaryTheoremCandidateOnly : Bool
    katoTubeBoundaryTheoremCandidateOnlyIsTrue :
      katoTubeBoundaryTheoremCandidateOnly ≡ true
    katoTubeBoundaryTheoremCandidateOnlyText : String
    katoTubeBoundaryTheoremCandidateOnlyTextIsCanonical :
      katoTubeBoundaryTheoremCandidateOnlyText ≡ shapeKatoTubeBoundaryCandidateText
    omegaTubeOmegaSheetSplitText : String
    omegaTubeOmegaSheetSplitTextIsCanonical :
      omegaTubeOmegaSheetSplitText ≡ shapeOmegaTubeOmegaSheetSplitText
    millerBridgeOpen : Bool
    millerBridgeOpenIsTrue : millerBridgeOpen ≡ true
    millerBridgeOpenText : String
    millerBridgeOpenTextIsCanonical :
      millerBridgeOpenText ≡ shapeMillerBridgeOpenText
    aggregateRouteIsFailClosed : Bool
    aggregateRouteIsFailClosedIsTrue : aggregateRouteIsFailClosed ≡ true

canonicalNSKatoHessianAggregateStats : NSKatoHessianAggregateStats
canonicalNSKatoHessianAggregateStats =
  mkNSKatoHessianAggregateStats
    128
    refl
    true
    refl
    shapeTrueKatoStableFractionText
    refl
    shapeKappaAbsGt1FractionText
    refl
    shapeKappaSignedGt1FractionText
    refl
    true
    refl
    shapePressureQcritRouteAdverseText
    refl
    true
    refl
    shapeKatoTubeBoundaryCandidateText
    refl
    shapeOmegaTubeOmegaSheetSplitText
    refl
    true
    refl
    shapeMillerBridgeOpenText
    refl
    true
    refl

record NSKatoHessianConfinementORCSLPGF : Set where
  constructor mkNSKatoHessianConfinementORCSLPGF
  field
    O : String
    OIsCanonical : O ≡
      "O: Record the corrected λ2 Hessian/vortex-core confinement receipt with explicit diagonal identity, KatoIdentity leaf, secondDeriv-expand, boundary-layer CL1/CL1b surfaces at ∂Ω_K, signed-gap, PSD minimum, curvature, Clay bridge blocker surfaces, and the Calc E note that the 2026-06-18 boundary preflight calc was run on dashiCFD N128 frames and remains empirical/non-promoting."
    R : String
    RIsCanonical : R ≡
      "R: Record Hess(λ2) PSD-at-minimum, the diagonal identity witness, the KatoIdentity leaf rows, the signed gap split, the conditional gap-collapse-to-Hessian-blow-up route, the H5/H6 curvature distinction, full 3D Hessian geometry, aggregate N=128 stats, explicit fail-closed gate rows, millerToH5 closeable-by-standard-interpolation (not yet inhabited), CL1-bounded Steps A/B/C corrected to ∂Ω_K boundary-layer localization and CL1b boundary-layer PDE-gap localization at ∂Ω_K, and the Calc E diagnostic-rank order: min g12 on ∂Ω_K, real rho on ∂Ω_K, then Betti-0."
    C : String
    CIsCanonical : C ≡
      "C: The receipt stores typed canonical target/value shapes, explicit receipt surfaces, the KatoIdentity leaf row checks, empirical N=128 aggregate metadata, and Calc E/CL1/CL1b fail-closed evidence only; CL1 and CL1b target ∂Ω_K / the boundary layer, no interior Ω_K localization is claimed, and the 2026-06-18 boundary preflight calc was run on dashiCFD N128 frames and remains empirical/non-promoting."
    S : String
    SIsCanonical : S ≡
      "S: Hessian PSD at core, the diagonal identity witness, the KatoIdentity leaf checked rows, the signed gap split, the PSD minimum surface, the gap-collapse/Hessian-blow-up route, the H5/H6 curvature split, triaxial full-3D core correction (large h33), positive cross-derivative confinement evidence, corrected Ωtube/Ωsheet split, millerToH5 as closeable-by-standard-interpolation (not yet inhabited), CL1 boundary-concentration Steps A/B/C as boundary-layer open surfaces at ∂Ω_K, CL1b as an open boundary-layer PDE route near ∂Ω_K, Calc E empirical projection/receipt evidence, CL1/CL1b open bookkeeping, the 2026-06-18 N128 boundary-preflight empirical note, and the ranked optional calcs: min g12 on ∂Ω_K, real rho on ∂Ω_K, then Betti-0 are recorded."
    L : String
    LIsCanonical : L ≡
      "L: Corrected sign convention at true λ2 minimum -> record the diagonal/gap/PSD/curvature/KatoIdentity leaf/Clay bridge surfaces plus Calc E empirical evidence -> keep CL1 open, redirect CL1/CL1b to the boundary layer at ∂Ω_K, note that the 2026-06-18 boundary preflight calc was run on dashiCFD N128 frames and remains empirical/non-promoting, and keep all promotions fail-closed."
    P : String
    PIsCanonical : P ≡
      "P: Do not promote any confinement theorem, external-DNS bridge, global regularity claim, full regularity theorem, Clay claim, Clay bridge claim, KatoIdentity leaf row, Calc E evidence, CL1/CL1b open bookkeeping, CL1b boundary-layer PDE gap, or the optional boundary calc ranking from this receipt."
    G : String
    GIsCanonical : G ≡
      "G: Governance guard: Miller bridge open only as theorem-candidate, Clay bridge open only as blocker, millerToH5 remains closeable-by-standard-interpolation but uninhabited here, CL1 boundary-concentration Steps A/B/C remain open fail-closed boundary-layer surfaces at ∂Ω_K, CL1b remains an open boundary-layer PDE route near ∂Ω_K, KatoIdentity leaf rows stay checked only, Calc E remains empirical and non-promoting, CL1 stays mathematically open and fail-closed, the 2026-06-18 boundary preflight calc was run on dashiCFD N128 frames and remains empirical/non-promoting, the optional calc ranking is min g12 on ∂Ω_K, real rho on ∂Ω_K, then Betti-0, and the boundary DNS calc path is split: producer `ns_boundary_derived_tensor_archive.py` materializes lambda2/g12/B_k/pressure_hessian_norm/beta from velocity/pressure input, consumer `ns_boundary_preflight_diagnostic.py` remains fail-closed, with the 2026-06-18 N128 frame summary recorded as empirical/non-promoting and no theorem promotion, and no external-DNS promotion path, no full/global regularity inhabitant, and no Clay promotion."
    F : String
    FIsCanonical : F ≡
      "F: Fail-closed due to explicit gate rows, the corrected sign convention, the open Clay bridge blocker, the KatoIdentity leaf checks, the open CL1/CL1b bookkeeping, and the note that the 2026-06-18 boundary preflight calc was run on dashiCFD N128 frames and remains empirical/non-promoting; proof obligations remain external to this row, CL1/CL1b stay boundary-layer only at ∂Ω_K, CL1 boundary-concentration Steps A/B/C remain fail-closed, and the optional calcs stay ranked as min g12 on ∂Ω_K, real rho on ∂Ω_K, then Betti-0."

data NSKatoHessianConfinementPromotion : Set where

nSKatoHessianNoPromotion : NSKatoHessianConfinementPromotion → ⊥
nSKatoHessianNoPromotion ()

n128TargetCoordinates : List Nat
n128TargetCoordinates =
  35 ∷ 36 ∷ 99 ∷ []

record NSKatoHessianConfinementN128Target : Set where
  constructor mkNSKatoHessianConfinementN128Target
  field
    targetName : String
    targetCoordinates : List Nat
    targetCoordinatesIsCanonical : targetCoordinates ≡ n128TargetCoordinates
    lambda2SignAtTarget : NSKatoHessianSign
    lambda2SignAtTargetIsCanonical : lambda2SignAtTarget ≡ signNegative
    crossDerivativeSignAtTarget : NSKatoHessianSign
    crossDerivativeSignAtTargetIsCanonical : crossDerivativeSignAtTarget ≡ signPositive
    pressureHessianSignAtTarget : NSKatoHessianSign
    pressureHessianSignAtTargetIsCanonical : pressureHessianSignAtTarget ≡ signPositive
    pressureHessianIsAdverseToConfinement :
      Bool
    pressureHessianIsAdverseToConfinementIsTrue :
      pressureHessianIsAdverseToConfinement ≡ true
    divergenceMachinePrecision :
      String
    divergenceMachinePrecisionIsCanonical :
      divergenceMachinePrecision ≡ "machine_precision"
    routeIsConfinementEvidence :
      Bool
    routeIsConfinementEvidenceIsTrue :
      routeIsConfinementEvidence ≡ true

canonicalN128Target :
  NSKatoHessianConfinementN128Target
canonicalN128Target =
  mkNSKatoHessianConfinementN128Target
    "xV"
    n128TargetCoordinates
    refl
    signNegative
    refl
    signPositive
    refl
    signPositive
    refl
    true
    refl
    "machine_precision"
    refl
    true
    refl

shapeDiagonalIdentityText : String
shapeDiagonalIdentityText =
  "The concrete 3x3 carrier is recorded as the diagonal identity witness on this receipt surface."

shapeSignedGapStructureText : String
shapeSignedGapStructureText =
  "The signed gap ledger keeps the Kato-side gap and confinement-side cross-derivative sign distinct; the signs are not collapsed."

shapePSDMinimumConfinementText : String
shapePSDMinimumConfinementText =
  "At the true λ2 minimum, the Hessian is recorded as positive semidefinite and the confinement surface is minimum-side only."

shapeGapCollapseHessianBlowUpText : String
shapeGapCollapseHessianBlowUpText =
  "Gap collapse is recorded only as a conditional route toward Hessian blow-up; no promotion is claimed here."

shapeCurvatureSobolevSplitText : String
shapeCurvatureSobolevSplitText =
  "Curvature-to-Sobolev bookkeeping separates H5 as the curvature bound for Hess λ2 L∞ from H6 as the Taylor confinement remainder; GD3 records H5 bounded by M and gap lower bound δ0 for that split."

shapeClayBridgeBlockerText : String
shapeClayBridgeBlockerText =
  "Clay bridge remains a typed blocker: no bridge promotion, no Clay promotion, and no terminal claim follow."

record NSKatoDiagonalIdentitySurface : Set where
  constructor mkNSKatoDiagonalIdentitySurface
  field
    diagonalIdentityText : String
    diagonalIdentityTextIsCanonical :
      diagonalIdentityText ≡ shapeDiagonalIdentityText
    diagonalIdentityRecorded : Bool
    diagonalIdentityRecordedIsTrue :
      diagonalIdentityRecorded ≡ true

record NSKatoSignedGapStructureSurface : Set where
  constructor mkNSKatoSignedGapStructureSurface
  field
    katoSideGapRecorded : Bool
    katoSideGapRecordedIsTrue :
      katoSideGapRecorded ≡ true
    confinementSideCrossDerivativeRecorded : Bool
    confinementSideCrossDerivativeRecordedIsTrue :
      confinementSideCrossDerivativeRecorded ≡ true
    signedGapText : String
    signedGapTextIsCanonical :
      signedGapText ≡ shapeSignedGapStructureText

record NSKatoPSDMinimumConfinementSurface : Set where
  constructor mkNSKatoPSDMinimumConfinementSurface
  field
    hessianPSDAtMinimum : Bool
    hessianPSDAtMinimumIsTrue :
      hessianPSDAtMinimum ≡ true
    confinementAtMinimumRecorded : Bool
    confinementAtMinimumRecordedIsTrue :
      confinementAtMinimumRecorded ≡ true
    psdMinimumConfinementText : String
    psdMinimumConfinementTextIsCanonical :
      psdMinimumConfinementText ≡ shapePSDMinimumConfinementText

record NSKatoGapCollapseHessianBlowUpSurface : Set where
  constructor mkNSKatoGapCollapseHessianBlowUpSurface
  field
    gapCollapseRecorded : Bool
    gapCollapseRecordedIsTrue :
      gapCollapseRecorded ≡ true
    gapCollapseImpliesHessianBlowUpSurfaceRecorded : Bool
    gapCollapseImpliesHessianBlowUpSurfaceRecordedIsTrue :
      gapCollapseImpliesHessianBlowUpSurfaceRecorded ≡ true
    gapCollapseImpliesHessianBlowUpPromoted : Bool
    gapCollapseImpliesHessianBlowUpPromotedIsFalse :
      gapCollapseImpliesHessianBlowUpPromoted ≡ false
    gapCollapseHessianBlowUpText : String
    gapCollapseHessianBlowUpTextIsCanonical :
      gapCollapseHessianBlowUpText ≡ shapeGapCollapseHessianBlowUpText

record NSKatoCurvatureSobolevSurface : Set where
  constructor mkNSKatoCurvatureSobolevSurface
  field
    h5ForHessianLInfinity : Bool
    h5ForHessianLInfinityIsTrue :
      h5ForHessianLInfinity ≡ true
    h6ForConfinementRemainder : Bool
    h6ForConfinementRemainderIsTrue :
      h6ForConfinementRemainder ≡ true
    curvatureSobolevText : String
    curvatureSobolevTextIsCanonical :
      curvatureSobolevText ≡ shapeCurvatureSobolevSplitText

record NSKatoClayBridgeBlockerSurface : Set where
  constructor mkNSKatoClayBridgeBlockerSurface
  field
    clayBridgeOpenCandidateOnly : Bool
    clayBridgeOpenCandidateOnlyIsTrue :
      clayBridgeOpenCandidateOnly ≡ true
    clayBridgePromoted : Bool
    clayBridgePromotedIsFalse :
      clayBridgePromoted ≡ false
    clayBridgeBlockerText : String
    clayBridgeBlockerTextIsCanonical :
      clayBridgeBlockerText ≡ shapeClayBridgeBlockerText

record NSKatoHessianConfinementReceipt : Set where
  field
    status :
      NSKatoHessianConfinementStatus
    statusIsFailClosed :
      status ≡ failClosedShapeOnly
    shapeLedger :
      List NSKatoHessianConfinementShape
    shapeLedgerIsCanonical :
      shapeLedger ≡ canonicalNSKatoHessianConfinementShape
    diagonalIdentitySurface :
      NSKatoDiagonalIdentitySurface
    diagonalIdentitySurfaceIsCanonical :
      diagonalIdentitySurface ≡
      mkNSKatoDiagonalIdentitySurface
        shapeDiagonalIdentityText
        refl
        true
        refl
    signedGapStructureSurface :
      NSKatoSignedGapStructureSurface
    signedGapStructureSurfaceIsCanonical :
      signedGapStructureSurface ≡
      mkNSKatoSignedGapStructureSurface
        true
        refl
        true
        refl
        shapeSignedGapStructureText
        refl
    psdMinimumConfinementSurface :
      NSKatoPSDMinimumConfinementSurface
    psdMinimumConfinementSurfaceIsCanonical :
      psdMinimumConfinementSurface ≡
      mkNSKatoPSDMinimumConfinementSurface
        true
        refl
        true
        refl
        shapePSDMinimumConfinementText
        refl
    gapCollapseHessianBlowUpSurface :
      NSKatoGapCollapseHessianBlowUpSurface
    gapCollapseHessianBlowUpSurfaceIsCanonical :
      gapCollapseHessianBlowUpSurface ≡
      mkNSKatoGapCollapseHessianBlowUpSurface
        true
        refl
        true
        refl
        false
        refl
        shapeGapCollapseHessianBlowUpText
        refl
    curvatureSobolevSurface :
      NSKatoCurvatureSobolevSurface
    curvatureSobolevSurfaceIsCanonical :
      curvatureSobolevSurface ≡
      mkNSKatoCurvatureSobolevSurface
        true
        refl
        true
        refl
        shapeCurvatureSobolevSplitText
        refl
    clayBridgeBlockerSurface :
      NSKatoClayBridgeBlockerSurface
    clayBridgeBlockerSurfaceIsCanonical :
      clayBridgeBlockerSurface ≡
      mkNSKatoClayBridgeBlockerSurface
        true
        refl
        false
        refl
        shapeClayBridgeBlockerText
        refl
    katoIdentityLeafReceipt :
      NSKatoIdentityLeafReceipt
    katoIdentityLeafReceiptIsCanonical :
      katoIdentityLeafReceipt ≡ canonicalNSKatoIdentityLeafReceipt
    hessianPSDRecorded :
      Bool
    hessianPSDRecordedIsTrue :
      hessianPSDRecorded ≡ true
    hessianPSDTextRecorded :
      String
    hessianPSDTextRecordedIsCanonical :
      hessianPSDTextRecorded ≡ shapeHessianPSDText
    hessian3DGeometryTextRecorded :
      String
    hessian3DGeometryTextRecordedIsCanonical :
      hessian3DGeometryTextRecorded ≡ shapeHessian3DGeometryText
    fullHessianEigenvaluesTextRecorded :
      String
    fullHessianEigenvaluesTextRecordedIsCanonical :
      fullHessianEigenvaluesTextRecorded ≡ shapeFullHessianEigenvaluesText
    lambda2NegativeRegionRecorded :
      Bool
    lambda2NegativeRegionRecordedIsTrue :
      lambda2NegativeRegionRecorded ≡ true
    lambda2NegativeRegionTextRecorded :
      String
    lambda2NegativeRegionTextRecordedIsCanonical :
      lambda2NegativeRegionTextRecorded ≡ shapeLambda2NegativeRegionText
    crossDerivativePositiveRecorded :
      Bool
    crossDerivativePositiveRecordedIsTrue :
      crossDerivativePositiveRecorded ≡ true
    crossDerivativePositiveTextRecorded :
      String
    crossDerivativePositiveTextRecordedIsCanonical :
      crossDerivativePositiveTextRecorded ≡ shapeCrossDerivativePositiveText
    signCorrectionRecorded :
      Bool
    signCorrectionRecordedIsTrue :
      signCorrectionRecorded ≡ true
    signCorrectionTextRecorded :
      String
    signCorrectionTextRecordedIsCanonical :
      signCorrectionTextRecorded ≡ shapeSignCorrectionText
    pressureHessianAdverseTextRecorded :
      String
    pressureHessianAdverseTextRecordedIsCanonical :
      pressureHessianAdverseTextRecorded ≡ shapePressureHessianText
    twoPlaneHessianPositiveDefiniteTextRecorded :
      String
    twoPlaneHessianPositiveDefiniteTextRecordedIsCanonical :
      twoPlaneHessianPositiveDefiniteTextRecorded ≡ shapeTwoPlaneHessianText
    fullHessian3DProjectionRecorded :
      NSKatoHessianFullHessian3DProjection
    fullHessian3DProjectionRecordedIsCanonical :
      fullHessian3DProjectionRecorded ≡ canonicalNSKatoHessianFullHessian3DProjection
    aggregateStats :
      NSKatoHessianAggregateStats
    aggregateStatsIsCanonical :
      aggregateStats ≡ canonicalNSKatoHessianAggregateStats
    divergenceTextRecorded :
      String
    divergenceTextRecordedIsCanonical :
      divergenceTextRecorded ≡ shapeDivergenceText
    calcEEmpiricalReceipt :
      NSKatoCalcEEmpiricalReceipt
    calcEEmpiricalReceiptIsCanonical :
      calcEEmpiricalReceipt ≡ canonicalNSKatoCalcEEmpiricalReceipt
    cl1MathematicallyOpen :
      Bool
    cl1MathematicallyOpenIsTrue :
      cl1MathematicallyOpen ≡ true
    cl1FailClosed :
      Bool
    cl1FailClosedIsTrue :
      cl1FailClosed ≡ true
    divergenceRouteRecorded :
      Bool
    divergenceRouteRecordedIsTrue :
      divergenceRouteRecorded ≡ true
    blockers :
      List NSKatoHessianConfinementBlocker
    blockersAreCanonical :
      blockers ≡ canonicalNSKatoHessianConfinementBlockers
    analyticalRequirements :
      List NSKatoHessianConfinementAnalyticalRequirement
    analyticalRequirementsAreCanonical :
      analyticalRequirements ≡
      canonicalNSKatoHessianConfinementAnalyticalRequirements
    target :
      NSKatoHessianConfinementN128Target
    targetIsCanonical :
      target ≡ canonicalN128Target
    millerBridgePromoted :
      Bool
    millerBridgePromotedIsFalse :
      millerBridgePromoted ≡ false
    externalDNSPromoted :
      Bool
    externalDNSPromotedIsFalse :
      externalDNSPromoted ≡ false
    fullRegularityPromoted :
      Bool
    fullRegularityPromotedIsFalse :
      fullRegularityPromoted ≡ false
    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false
    confinementClaimPromoted :
      Bool
    confinementClaimPromotedIsFalse :
      confinementClaimPromoted ≡ false
    orcslpgf :
      NSKatoHessianConfinementORCSLPGF

open NSKatoHessianConfinementORCSLPGF public
open NSKatoHessianEigenvalueProjection public
open NSKatoHessianFullHessian3DProjection public

canonicalNSKatoHessianConfinementORCSLPGF :
  NSKatoHessianConfinementORCSLPGF
canonicalNSKatoHessianConfinementORCSLPGF =
  mkNSKatoHessianConfinementORCSLPGF
    "O: Record the corrected λ2 Hessian/vortex-core confinement receipt with explicit diagonal identity, KatoIdentity leaf, secondDeriv-expand, boundary-layer CL1/CL1b surfaces at ∂Ω_K, signed-gap, PSD minimum, curvature, Clay bridge blocker surfaces, and the Calc E note that the 2026-06-18 boundary preflight calc was run on dashiCFD N128 frames and remains empirical/non-promoting."
    refl
    "R: Record Hess(λ2) PSD-at-minimum, the diagonal identity witness, the KatoIdentity leaf rows, the signed gap split, the conditional gap-collapse-to-Hessian-blow-up route, the H5/H6 curvature distinction, full 3D Hessian geometry, aggregate N=128 stats, explicit fail-closed gate rows, millerToH5 closeable-by-standard-interpolation (not yet inhabited), CL1-bounded Steps A/B/C corrected to ∂Ω_K boundary-layer localization and CL1b boundary-layer PDE-gap localization at ∂Ω_K, and the Calc E diagnostic-rank order: min g12 on ∂Ω_K, real rho on ∂Ω_K, then Betti-0."
    refl
    "C: The receipt stores typed canonical target/value shapes, explicit receipt surfaces, the KatoIdentity leaf row checks, empirical N=128 aggregate metadata, and Calc E/CL1/CL1b fail-closed evidence only; CL1 and CL1b target ∂Ω_K / the boundary layer, no interior Ω_K localization is claimed, and the 2026-06-18 boundary preflight calc was run on dashiCFD N128 frames and remains empirical/non-promoting."
    refl
    "S: Hessian PSD at core, the diagonal identity witness, the KatoIdentity leaf checked rows, the signed gap split, the PSD minimum surface, the gap-collapse/Hessian-blow-up route, the H5/H6 curvature split, triaxial full-3D core correction (large h33), positive cross-derivative confinement evidence, corrected Ωtube/Ωsheet split, millerToH5 as closeable-by-standard-interpolation (not yet inhabited), CL1 boundary-concentration Steps A/B/C as boundary-layer open surfaces at ∂Ω_K, CL1b as an open boundary-layer PDE route near ∂Ω_K, Calc E empirical projection/receipt evidence, CL1/CL1b open bookkeeping, the 2026-06-18 N128 boundary-preflight empirical note, and the ranked optional calcs: min g12 on ∂Ω_K, real rho on ∂Ω_K, then Betti-0 are recorded."
    refl
    "L: Corrected sign convention at true λ2 minimum -> record the diagonal/gap/PSD/curvature/KatoIdentity leaf/Clay bridge surfaces plus Calc E empirical evidence -> keep CL1 open, redirect CL1/CL1b to the boundary layer at ∂Ω_K, note that the 2026-06-18 boundary preflight calc was run on dashiCFD N128 frames and remains empirical/non-promoting, and keep all promotions fail-closed."
    refl
    "P: Do not promote any confinement theorem, external-DNS bridge, global regularity claim, full regularity theorem, Clay claim, Clay bridge claim, KatoIdentity leaf row, Calc E evidence, CL1/CL1b open bookkeeping, CL1b boundary-layer PDE gap, or the optional boundary calc ranking from this receipt."
    refl
    "G: Governance guard: Miller bridge open only as theorem-candidate, Clay bridge open only as blocker, millerToH5 remains closeable-by-standard-interpolation but uninhabited here, CL1 boundary-concentration Steps A/B/C remain open fail-closed boundary-layer surfaces at ∂Ω_K, CL1b remains an open boundary-layer PDE route near ∂Ω_K, KatoIdentity leaf rows stay checked only, Calc E remains empirical and non-promoting, CL1 stays mathematically open and fail-closed, the 2026-06-18 boundary preflight calc was run on dashiCFD N128 frames and remains empirical/non-promoting, the optional calc ranking is min g12 on ∂Ω_K, real rho on ∂Ω_K, then Betti-0, and the boundary DNS calc path is split: producer `ns_boundary_derived_tensor_archive.py` materializes lambda2/g12/B_k/pressure_hessian_norm/beta from velocity/pressure input, consumer `ns_boundary_preflight_diagnostic.py` remains fail-closed, with the 2026-06-18 N128 frame summary recorded as empirical/non-promoting and no theorem promotion, and no external-DNS promotion path, no full/global regularity inhabitant, and no Clay promotion."
    refl
    "F: Fail-closed due to explicit gate rows, the corrected sign convention, the open Clay bridge blocker, the KatoIdentity leaf checks, the open CL1/CL1b bookkeeping, and the note that the 2026-06-18 boundary preflight calc was run on dashiCFD N128 frames and remains empirical/non-promoting; proof obligations remain external to this row, CL1/CL1b stay boundary-layer only at ∂Ω_K, CL1 boundary-concentration Steps A/B/C remain fail-closed, and the optional calcs stay ranked as min g12 on ∂Ω_K, real rho on ∂Ω_K, then Betti-0."
    refl

canonicalNSKatoHessianConfinementReceipt : NSKatoHessianConfinementReceipt
canonicalNSKatoHessianConfinementReceipt =
  record
    { status = failClosedShapeOnly
    ; statusIsFailClosed = refl
    ; shapeLedger = canonicalNSKatoHessianConfinementShape
    ; shapeLedgerIsCanonical = refl
    ; diagonalIdentitySurface =
        mkNSKatoDiagonalIdentitySurface
          shapeDiagonalIdentityText
          refl
          true
          refl
    ; diagonalIdentitySurfaceIsCanonical = refl
    ; signedGapStructureSurface =
        mkNSKatoSignedGapStructureSurface
          true
          refl
          true
          refl
          shapeSignedGapStructureText
          refl
    ; signedGapStructureSurfaceIsCanonical = refl
    ; psdMinimumConfinementSurface =
        mkNSKatoPSDMinimumConfinementSurface
          true
          refl
          true
          refl
          shapePSDMinimumConfinementText
          refl
    ; psdMinimumConfinementSurfaceIsCanonical = refl
    ; gapCollapseHessianBlowUpSurface =
        mkNSKatoGapCollapseHessianBlowUpSurface
          true
          refl
          true
          refl
          false
          refl
          shapeGapCollapseHessianBlowUpText
          refl
    ; gapCollapseHessianBlowUpSurfaceIsCanonical = refl
    ; curvatureSobolevSurface =
        mkNSKatoCurvatureSobolevSurface
          true
          refl
          true
          refl
          shapeCurvatureSobolevSplitText
          refl
    ; curvatureSobolevSurfaceIsCanonical = refl
    ; clayBridgeBlockerSurface =
        mkNSKatoClayBridgeBlockerSurface
          true
          refl
          false
          refl
          shapeClayBridgeBlockerText
          refl
    ; clayBridgeBlockerSurfaceIsCanonical = refl
    ; katoIdentityLeafReceipt = canonicalNSKatoIdentityLeafReceipt
    ; katoIdentityLeafReceiptIsCanonical = refl
    ; hessianPSDRecorded = true
    ; hessianPSDRecordedIsTrue = refl
    ; hessianPSDTextRecorded = shapeHessianPSDText
    ; hessianPSDTextRecordedIsCanonical = refl
    ; hessian3DGeometryTextRecorded = shapeHessian3DGeometryText
    ; hessian3DGeometryTextRecordedIsCanonical = refl
    ; fullHessianEigenvaluesTextRecorded = shapeFullHessianEigenvaluesText
    ; fullHessianEigenvaluesTextRecordedIsCanonical = refl
    ; lambda2NegativeRegionRecorded = true
    ; lambda2NegativeRegionRecordedIsTrue = refl
    ; lambda2NegativeRegionTextRecorded = shapeLambda2NegativeRegionText
    ; lambda2NegativeRegionTextRecordedIsCanonical = refl
    ; crossDerivativePositiveRecorded = true
    ; crossDerivativePositiveRecordedIsTrue = refl
    ; crossDerivativePositiveTextRecorded = shapeCrossDerivativePositiveText
    ; crossDerivativePositiveTextRecordedIsCanonical = refl
    ; signCorrectionRecorded = true
    ; signCorrectionRecordedIsTrue = refl
    ; signCorrectionTextRecorded = shapeSignCorrectionText
    ; signCorrectionTextRecordedIsCanonical = refl
    ; pressureHessianAdverseTextRecorded = shapePressureHessianText
    ; pressureHessianAdverseTextRecordedIsCanonical = refl
    ; twoPlaneHessianPositiveDefiniteTextRecorded = shapeTwoPlaneHessianText
    ; twoPlaneHessianPositiveDefiniteTextRecordedIsCanonical = refl
    ; fullHessian3DProjectionRecorded = canonicalNSKatoHessianFullHessian3DProjection
    ; fullHessian3DProjectionRecordedIsCanonical = refl
    ; aggregateStats = canonicalNSKatoHessianAggregateStats
    ; aggregateStatsIsCanonical = refl
    ; divergenceTextRecorded = shapeDivergenceText
    ; divergenceTextRecordedIsCanonical = refl
    ; calcEEmpiricalReceipt = canonicalNSKatoCalcEEmpiricalReceipt
    ; calcEEmpiricalReceiptIsCanonical = refl
    ; cl1MathematicallyOpen = true
    ; cl1MathematicallyOpenIsTrue = refl
    ; cl1FailClosed = true
    ; cl1FailClosedIsTrue = refl
    ; divergenceRouteRecorded = true
    ; divergenceRouteRecordedIsTrue = refl
    ; blockers = canonicalNSKatoHessianConfinementBlockers
    ; blockersAreCanonical = refl
    ; analyticalRequirements =
      canonicalNSKatoHessianConfinementAnalyticalRequirements
    ; analyticalRequirementsAreCanonical = refl
    ; target = canonicalN128Target
    ; targetIsCanonical = refl
    ; millerBridgePromoted = false
    ; millerBridgePromotedIsFalse = refl
    ; externalDNSPromoted = false
    ; externalDNSPromotedIsFalse = refl
    ; fullRegularityPromoted = false
    ; fullRegularityPromotedIsFalse = refl
    ; clayPromoted = false
    ; clayPromotedIsFalse = refl
    ; confinementClaimPromoted = false
    ; confinementClaimPromotedIsFalse = refl
    ; orcslpgf = canonicalNSKatoHessianConfinementORCSLPGF
    }

open NSKatoHessianConfinementReceipt public

------------------------------------------------------------------------
-- Kato-Morse theorem-by-theorem receipt surface (program prompt alignment).

data KatoMorseProofStatus : Set where
  provableClassical : KatoMorseProofStatus
  standardRecorded : KatoMorseProofStatus
  trichotomyRecorded : KatoMorseProofStatus
  openBlocker : KatoMorseProofStatus

data KatoMorseTheorem : Set where
  MK1 : KatoMorseTheorem
  MK2 : KatoMorseTheorem
  MK3 : KatoMorseTheorem
  GD1 : KatoMorseTheorem
  GD2 : KatoMorseTheorem
  GD3 : KatoMorseTheorem
  CL2 : KatoMorseTheorem
  theoremCConditional : KatoMorseTheorem

katoMorseTheoremName : KatoMorseTheorem → String
katoMorseTheoremName MK1 = "MK1"
katoMorseTheoremName MK2 = "MK2"
katoMorseTheoremName MK3 = "MK3"
katoMorseTheoremName GD1 = "GD1"
katoMorseTheoremName GD2 = "GD2"
katoMorseTheoremName GD3 = "GD3"
katoMorseTheoremName CL2 = "CL2"
katoMorseTheoremName theoremCConditional = "Theorem C (conditional)"

katoMorseProofStatusName : KatoMorseProofStatus → String
katoMorseProofStatusName provableClassical = "provable classical"
katoMorseProofStatusName standardRecorded = "standard"
katoMorseProofStatusName trichotomyRecorded = "trichotomy"
katoMorseProofStatusName openBlocker = "open blocker"

record KatoMorseProgramVariables : Set where
  constructor mkKatoMorseProgramVariables
  field
    betaOfT : String
    OmegaBeta : String
    OmegaK : String
    g12 : String
    g23 : String
    psi12 : String
    B : String
    B_k : String
    C_k : String
    c0 : String
    c1 : String
    M : String
    delta0 : String
    δ1 : String
    δmin : String
    C_embed : String
    hM_pos : String
    hM : String
    hδ_pos : String
    hδ : String
    hδ1_pos : String
    hδ1 : String
    C_emb : String
    hess_le_Ak_plus_Bk : String
    Ak_le_D3u : String
    sobolev_H5_C3 : String
    BkQuadraticBound : String
    finalGD3SobolevBoundCorrectFormula : String
    H5 : String
    H6 : String
    h5VsH6Split : String
    h5Boundedness : String
    BkQuadraticHonesty : String
    cl2BranchC : String
    secondDerivExpand : String
    cl2Trichotomy : String

canonicalKatoMorseProgramVariables : KatoMorseProgramVariables
canonicalKatoMorseProgramVariables =
    mkKatoMorseProgramVariables
    "beta(t)=theta*lambda2min(t)"
    "OmegaBeta"
    "OmegaK"
    "g12"
    "g23"
    "B/g12"
    "B"
    "B_k"
    "C_k"
    "c0"
    "c1"
    "M"
    "δ0"
    "δ1"
    "δmin"
    "C_embed"
    "hM_pos"
    "hM"
    "hδ_pos"
    "hδ"
    "hδ1_pos"
    "hδ1"
    "C_emb"
    "hess_le_Ak_plus_Bk"
    "Ak_le_D3u"
    "sobolev_H5_C3"
    "Bk quadratic bound"
    "final GD3-SobolevBound-Correct bound: C_emb*M + 2*C_emb^2*M^2/δ0 + 2*C_emb^2*M^2/δ1 is the recorded two-gap upper bound with C_k carried through the g23 branch; optional compressed form uses δmin"
    "H5"
    "H6"
    "H5 curvature bound vs H6 Taylor remainder split; H1/H5 interpolation exponent is 1/4 in the closeable standard package"
    "H5 bounded by M"
    "Bk quadratic in H5 with C_emb"
    "CL2 branch C"
    "secondDeriv-expand"
    "CL2 trichotomy"

mk1Statement : String
mk1Statement =
  "MK1: geometric kernel preparation at beta(t)=theta*lambda2min(t), OmegaBeta, OmegaK, g12, and g23 is recorded as provable classical on the current exact receipt variables."

mk2Statement : String
mk2Statement =
  "MK2: local Morse kernel counting with B_k and C_k is recorded as provable classical on the current exact receipt variables."

mk3Statement : String
mk3Statement =
  "MK3: minimum-split/shape coupling remains conditional and is carried as a pending theorem-program target."

gd1Statement : String
gd1Statement =
  "GD1: gap-defect estimate is recorded with psi12=B/g12 as an open route on the existing Kato-Morse variables."

gd2Statement : String
gd2Statement =
  "GD2: standard receipt row on the current Kato-Morse variables; the CL2 trichotomy is carried on its own row and remains fail-closed."

gd3Statement : String
gd3Statement =
  "GD3-SobolevBound-Correct: the checked GD3 row is standard on the KatoIdentity leaf and records the exact payload names M, hM_pos, hM, δ0, δ1, hδ_pos, hδ, hδ1_pos, hδ1, δmin, C_emb, g23, C_k, hess_le_Ak_plus_Bk, Ak_le_D3u, sobolev_H5_C3, B_k/g12, C_k/g23, and the final two-gap upper bound C_emb*M + 2*C_emb^2*M^2/δ0 + 2*C_emb^2*M^2/δ1, with optional compressed form C_emb*M + 4*C_emb^2*M^2/δmin. The row still carries the curvature-to-Sobolev split with secondDeriv-expand and H6 as the Taylor remainder, and no calcs/proxy claims are introduced."

cl2TrichotomyStatement : String
cl2TrichotomyStatement =
  "CL2: gap-or-coupling is recorded as trichotomy, not dichotomy, on the KatoIdentity leaf receipt and the current Kato-Morse variables. Branch C is explicitly checked as the live branch in this pass; no promotion beyond the typed receipt surface is introduced."

theoremCConditionalStatement : String
theoremCConditionalStatement =
  "Theorem C (conditional): the final blow-up implication remains open until the exact curvature-to-Sobolev step through H6 is closed."

katoMorseTheoremStatement : KatoMorseTheorem → String
katoMorseTheoremStatement MK1 = mk1Statement
katoMorseTheoremStatement MK2 = mk2Statement
katoMorseTheoremStatement MK3 = mk3Statement
katoMorseTheoremStatement GD1 = gd1Statement
katoMorseTheoremStatement GD2 = gd2Statement
katoMorseTheoremStatement GD3 = gd3Statement
katoMorseTheoremStatement CL2 = cl2TrichotomyStatement
katoMorseTheoremStatement theoremCConditional = theoremCConditionalStatement

katoMorseTheoremExactBlocker : KatoMorseTheorem → String
katoMorseTheoremExactBlocker MK1 =
  "MK1 exact blocker: none; this row is already provable classical on the current receipt variables."
katoMorseTheoremExactBlocker MK2 =
  "MK2 exact blocker: none; this row is already provable classical on the current receipt variables."
katoMorseTheoremExactBlocker MK3 =
  "MK3 exact blocker: conditional theorem target only."
katoMorseTheoremExactBlocker GD1 =
  "GD1 exact blocker: open route only; psi12=B/g12 remains unclosed."
katoMorseTheoremExactBlocker GD2 =
  "GD2 exact blocker: none; this row is already standard on the current receipt variables."
katoMorseTheoremExactBlocker GD3 =
  "GD3 exact blocker: none; this row is already standard on the current receipt variables, with GD3-SobolevBound-Correct projections checking the exact payload names M, hM_pos, hM, δ0, δ1, hδ_pos, hδ, hδ1_pos, hδ1, δmin, C_emb, g23, C_k, hess_le_Ak_plus_Bk, Ak_le_D3u, sobolev_H5_C3, B_k/g12, C_k/g23, and the final two-gap upper bound C_emb*M + 2*C_emb^2*M^2/δ0 + 2*C_emb^2*M^2/δ1; optional compressed form C_emb*M + 4*C_emb^2*M^2/δmin is recorded but not promoted."
katoMorseTheoremExactBlocker CL2 =
  "CL2 exact blocker: trichotomy is recorded (branch C is checked), not a dichotomy; the surface remains fail-closed."
katoMorseTheoremExactBlocker theoremCConditional =
  "Theorem C exact blocker: the curvature-to-Sobolev H6 transfer remains open."

record KatoMorseProgramTheoremRow : Set where
  constructor mkKatoMorseProgramTheoremRow
  field
    theorem : KatoMorseTheorem
    theoremName : String
    theoremNameIsCanonical : theoremName ≡ katoMorseTheoremName theorem
    status : KatoMorseProofStatus
    statusText : String
    statusTextIsCanonical : statusText ≡ katoMorseProofStatusName status
    statement : String
    statementIsCanonical : statement ≡ katoMorseTheoremStatement theorem
    exactBlocker : String
    exactBlockerIsCanonical : exactBlocker ≡
      katoMorseTheoremExactBlocker theorem
    variables : KatoMorseProgramVariables
    variablesAreCanonical : variables ≡ canonicalKatoMorseProgramVariables

canonicalKatoMorseProgramRows : List KatoMorseProgramTheoremRow
canonicalKatoMorseProgramRows =
  mkKatoMorseProgramTheoremRow
    MK1
    (katoMorseTheoremName MK1)
    refl
    provableClassical
    (katoMorseProofStatusName provableClassical)
    refl
    mk1Statement
    refl
    (katoMorseTheoremExactBlocker MK1)
    refl
    canonicalKatoMorseProgramVariables
    refl
    ∷
  mkKatoMorseProgramTheoremRow
    MK2
    (katoMorseTheoremName MK2)
    refl
    provableClassical
    (katoMorseProofStatusName provableClassical)
    refl
    mk2Statement
    refl
    (katoMorseTheoremExactBlocker MK2)
    refl
    canonicalKatoMorseProgramVariables
    refl
    ∷
  mkKatoMorseProgramTheoremRow
    MK3
    (katoMorseTheoremName MK3)
    refl
    openBlocker
    (katoMorseProofStatusName openBlocker)
    refl
    mk3Statement
    refl
    (katoMorseTheoremExactBlocker MK3)
    refl
    canonicalKatoMorseProgramVariables
    refl
    ∷
  mkKatoMorseProgramTheoremRow
    GD1
    (katoMorseTheoremName GD1)
    refl
    openBlocker
    (katoMorseProofStatusName openBlocker)
    refl
    gd1Statement
    refl
    (katoMorseTheoremExactBlocker GD1)
    refl
    canonicalKatoMorseProgramVariables
    refl
    ∷
  mkKatoMorseProgramTheoremRow
    GD2
    (katoMorseTheoremName GD2)
    refl
    standardRecorded
    (katoMorseProofStatusName standardRecorded)
    refl
    gd2Statement
    refl
    (katoMorseTheoremExactBlocker GD2)
    refl
    canonicalKatoMorseProgramVariables
    refl
    ∷
  mkKatoMorseProgramTheoremRow
    GD3
    (katoMorseTheoremName GD3)
    refl
    standardRecorded
    (katoMorseProofStatusName standardRecorded)
    refl
    gd3Statement
    refl
    (katoMorseTheoremExactBlocker GD3)
    refl
    canonicalKatoMorseProgramVariables
    refl
    ∷
  mkKatoMorseProgramTheoremRow
    CL2
    (katoMorseTheoremName CL2)
    refl
    trichotomyRecorded
    (katoMorseProofStatusName trichotomyRecorded)
    refl
    cl2TrichotomyStatement
    refl
    (katoMorseTheoremExactBlocker CL2)
    refl
    canonicalKatoMorseProgramVariables
    refl
    ∷
  mkKatoMorseProgramTheoremRow
    theoremCConditional
    (katoMorseTheoremName theoremCConditional)
    refl
    openBlocker
    (katoMorseProofStatusName openBlocker)
    refl
    theoremCConditionalStatement
    refl
    (katoMorseTheoremExactBlocker theoremCConditional)
    refl
    canonicalKatoMorseProgramVariables
    refl
    ∷ []

data KatoMorseProgramBlocker : Set where
  noProofOfTheoremCConditional : KatoMorseProgramBlocker
  noAcceptedCurvatureToSobolevTransfer : KatoMorseProgramBlocker
  noH5RequirementForHessianLInfinity : KatoMorseProgramBlocker
  noClayPromotion : KatoMorseProgramBlocker

canonicalKatoMorseProgramBlockers : List KatoMorseProgramBlocker
canonicalKatoMorseProgramBlockers =
  noProofOfTheoremCConditional
  ∷ noAcceptedCurvatureToSobolevTransfer
  ∷ noH5RequirementForHessianLInfinity
  ∷ noClayPromotion
  ∷ []

record KatoMorseProgramORCSLPGF : Set where
  constructor mkKatoMorseProgramORCSLPGF
  field
    O : String
    OIsCanonical : O ≡
      "O: Record Kato-Morse theorem-by-theorem rows with explicit statuses and exact variable/shapes names."
    R : String
    RIsCanonical : R ≡
      "R: The prompt-aligned rows are MK1 and MK2 as provable classical, GD2 and GD3 as standard, CL2 as trichotomy (with branch C as the checked branch), and MK3, GD1, and conditional Theorem C as open."
    C : String
    CIsCanonical : C ≡
      "C: Kato-Morse status fields are explicit as provable classical/standard/trichotomy/open blocker, with secondDeriv-expand kept as a checked leaf surface only, and the closeable standard package is kept separate from any theorem claim."
    S : String
    SIsCanonical : S ≡
      "S: beta(t)=theta*lambda2min(t), OmegaBeta, OmegaK, g12, g23, psi12=B/g12, B, B_k, C_k, c0, c1, M, δ0, δ1, δmin, hM_pos, hM, hδ_pos, hδ, hδ1_pos, hδ1, C_embed, C_emb, hess_le_Ak_plus_Bk, Ak_le_D3u, sobolev_H5_C3, B_k/g12, C_k/g23, Bk quadratic bound, final GD3-SobolevBound-Correct bound C_emb*M + 2*C_emb^2*M^2/δ0 + 2*C_emb^2*M^2/δ1, optional compressed δmin formula, H5, H6, H5 bounded by M and H5/H6 split, Bk-quadratic-in-H5 honesty note, CL2 branch C, H1/H5 interpolation exponent 1/4, and secondDeriv-expand are recorded as exact program variables and shapes."
    L : String
    LIsCanonical : L ≡
      "L: theorem-by-theorem row surface orders the claims as provable classical, standard, trichotomy, then open blocker, with MK1/MK2 classical, GD2/GD3 standard, CL2 trichotomy (branch C checked) rather than dichotomy, and MK3/GD1/Theorem C open."
    P : String
    PIsCanonical : P ≡
      "P: no Clay promotion is performed from this program surface."
    G : String
    GIsCanonical : G ≡
      "G: all pending route rows remain fail-closed; only typed record data is carried, CL2 stays a trichotomy row with branch C checked rather than dichotomy, secondDeriv-expand is a checked leaf surface, and no Clay promotion is allowed."
    F : String
    FIsCanonical : F ≡
      "F: status is explicit; MK1 and MK2 are provable classical, GD2 and GD3 are standard with GD3-SobolevBound-Correct checks, CL2 is trichotomy rather than dichotomy with branch C checked, CL1 remains open and fail-closed elsewhere in the receipt, MK3, GD1, and theorem C remain open, and no Clay promotion is allowed."

record KatoMorseProgramSurface : Set where
  constructor mkKatoMorseProgramSurface
  field
    theoremRows : List KatoMorseProgramTheoremRow
    theoremRowsAreCanonical : theoremRows ≡ canonicalKatoMorseProgramRows
    variableBundle : KatoMorseProgramVariables
    variableBundleIsCanonical : variableBundle ≡ canonicalKatoMorseProgramVariables
    curvatureToSobolevRow : String
    curvatureToSobolevRowIsCanonical : curvatureToSobolevRow ≡
      "The H5 versus H6 split is explicit: H5 carries the curvature bound for Hess λ2 L∞, and H6 carries the Taylor confinement remainder; the closeable standard package records lambda2+ <= ||grad u||_F / 2, weak-L3 <= L3, H2 -> W1,3, and H1/H5 interpolation exponent 1/4; GD3-SobolevBound-Correct enforces the two-gap upper-bound shape with g23, C_k, δ1, hδ1_pos, hδ1, δmin, the final bound C_emb*M + 2*C_emb^2*M^2/δ0 + 2*C_emb^2*M^2/δ1, and the optional compressed form C_emb*M + 4*C_emb^2*M^2/δmin."
    programBlockers : List KatoMorseProgramBlocker
    programBlockersAreCanonical : programBlockers ≡ canonicalKatoMorseProgramBlockers
    clayPromoted : Bool
    clayPromotedIsFalse : clayPromoted ≡ false
    theoremCOpen : Bool
    theoremCOpenIsTrue : theoremCOpen ≡ true
    programRecord : KatoMorseProgramORCSLPGF

canonicalKatoMorseProgramORCSLPGF : KatoMorseProgramORCSLPGF
canonicalKatoMorseProgramORCSLPGF =
  mkKatoMorseProgramORCSLPGF
    "O: Record Kato-Morse theorem-by-theorem rows with explicit statuses and exact variable/shapes names."
    refl
    "R: The prompt-aligned rows are MK1 and MK2 as provable classical, GD2 and GD3 as standard, CL2 as trichotomy (with branch C as the checked branch), and MK3, GD1, and conditional Theorem C as open."
    refl
    "C: Kato-Morse status fields are explicit as provable classical/standard/trichotomy/open blocker, with secondDeriv-expand kept as a checked leaf surface only, and the closeable standard package is kept separate from any theorem claim."
    refl
    "S: beta(t)=theta*lambda2min(t), OmegaBeta, OmegaK, g12, g23, psi12=B/g12, B, B_k, C_k, c0, c1, M, δ0, δ1, δmin, hM_pos, hM, hδ_pos, hδ, hδ1_pos, hδ1, C_embed, C_emb, hess_le_Ak_plus_Bk, Ak_le_D3u, sobolev_H5_C3, B_k/g12, C_k/g23, Bk quadratic bound, final GD3-SobolevBound-Correct bound C_emb*M + 2*C_emb^2*M^2/δ0 + 2*C_emb^2*M^2/δ1, optional compressed δmin formula, H5, H6, H5 bounded by M and H5/H6 split, Bk-quadratic-in-H5 honesty note, CL2 branch C, H1/H5 interpolation exponent 1/4, and secondDeriv-expand are recorded as exact program variables and shapes."
    refl
    "L: theorem-by-theorem row surface orders the claims as provable classical, standard, trichotomy, then open blocker, with MK1/MK2 classical, GD2/GD3 standard, CL2 trichotomy (branch C checked) rather than dichotomy, and MK3/GD1/Theorem C open."
    refl
    "P: no Clay promotion is performed from this program surface."
    refl
    "G: all pending route rows remain fail-closed; only typed record data is carried, CL2 stays a trichotomy row with branch C checked rather than dichotomy, secondDeriv-expand is a checked leaf surface, and no Clay promotion is allowed."
    refl
    "F: status is explicit; MK1 and MK2 are provable classical, GD2 and GD3 are standard with GD3-SobolevBound-Correct checks, CL2 is trichotomy rather than dichotomy with branch C checked, CL1 remains open and fail-closed elsewhere in the receipt, MK3, GD1, and theorem C remain open, and no Clay promotion is allowed."
    refl

canonicalKatoMorseProgramSurface : KatoMorseProgramSurface
canonicalKatoMorseProgramSurface =
  mkKatoMorseProgramSurface
    canonicalKatoMorseProgramRows
    refl
    canonicalKatoMorseProgramVariables
    refl
    "The H5 versus H6 split is explicit: H5 carries the curvature bound for Hess λ2 L∞, and H6 carries the Taylor confinement remainder; the closeable standard package records lambda2+ <= ||grad u||_F / 2, weak-L3 <= L3, H2 -> W1,3, and H1/H5 interpolation exponent 1/4; GD3-SobolevBound-Correct enforces the two-gap upper-bound shape with g23, C_k, δ1, hδ1_pos, hδ1, δmin, the final bound C_emb*M + 2*C_emb^2*M^2/δ0 + 2*C_emb^2*M^2/δ1, and the optional compressed form C_emb*M + 4*C_emb^2*M^2/δmin."
    refl
    canonicalKatoMorseProgramBlockers
    refl
    false
    refl
    true
    refl
    canonicalKatoMorseProgramORCSLPGF
