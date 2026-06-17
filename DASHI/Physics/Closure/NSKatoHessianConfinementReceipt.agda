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
-- surface, CL1 remains open/fail-closed, and Calc E remains empirical-only.

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
  katoIdentityLeafReceiptRecorded : NSKatoHessianConfinementShape
  secondDerivExpandLeafRecorded : NSKatoHessianConfinementShape
  gd3StandardRowRecorded : NSKatoHessianConfinementShape
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
  ∷ katoIdentityLeafReceiptRecorded
  ∷ secondDerivExpandLeafRecorded
  ∷ gd3StandardRowRecorded
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
  noClayPromotion :
    NSKatoHessianConfinementBlocker

canonicalNSKatoHessianConfinementBlockers : List NSKatoHessianConfinementBlocker
canonicalNSKatoHessianConfinementBlockers =
  millerBridgeOpenTheoremCandidateOnly
  ∷ clayBridgeOpenTheoremCandidateOnly
  ∷ noExternalDNSPromotion
  ∷ noFullRegularityInhabitant
  ∷ noClayPromotion
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

shapeDivergenceText : String
shapeDivergenceText =
  "Machine-precision divergence consistency is recorded as fail-closed empirical state."

shapeCalcEEmpiricalProjectionText : String
shapeCalcEEmpiricalProjectionText =
  "Calc E is recorded as empirical, non-promoting evidence: no new NS calc was run or required; CL1 remains open and fail-closed; optional calcs are ranked as real min g12 on Omega_K, real rho on boundary from tensors, then Betti-0 count; rho approx 8.02 at TG N=128 t≈9; Scenario D unsupported in dataset; H_B numerically supported only."

shapeCalcEEmpiricalReceiptText : String
shapeCalcEEmpiricalReceiptText =
  "Calc E stays empirical and non-promoting on this receipt surface; no new NS calc was run or required; CL1 remains open and fail-closed; optional calcs are ranked as real min g12 on Omega_K, real rho on boundary from tensors, then Betti-0 count."

shapeCL1OpenFailClosedText : String
shapeCL1OpenFailClosedText =
  "CL1 remains mathematically open and fail-closed; no theorem promotion is claimed."

shapeKatoIdentityLeafReceiptText : String
shapeKatoIdentityLeafReceiptText =
  "KatoIdentity leaf receipt records the checked secondDeriv-expand surface, the GD3 standard row, the GD3-SobolevBound-Correct projection, and CL2 trichotomy row without optional calc results; the latest GD3 payload names M, hM_pos, hM, δ0, hδ_pos, hδ, C_emb, hess_le_Ak_plus_Bk, Ak_le_D3u, sobolev_H5_C3, Bk quadratic bound, and the final GD3-SobolevBound-Correct formula are carried on this same leaf surface."

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
  "GD3-SobolevBound-Correct is a checked projection row: the latest payload keeps M, hM_pos, hM, δ0, hδ_pos, hδ, and C_emb as exact names; hess_le_Ak_plus_Bk, Ak_le_D3u, and sobolev_H5_C3 are exact shapes; B_k is carried only through the recorded quadratic bound; and the final GD3-SobolevBound-Correct formula is recorded as a named surface without any promotion claim."

canonicalGD3SobolevBoundCorrectProjectionRows : List String
canonicalGD3SobolevBoundCorrectProjectionRows =
  "M"
  ∷ "δ0"
  ∷ "H5 <= M"
  ∷ "C_embed"
  ∷ "B_k quadratic in H5"
  ∷ "hM_pos"
  ∷ "hM"
  ∷ "hδ_pos"
  ∷ "hδ"
  ∷ "C_emb"
  ∷ "hess_le_Ak_plus_Bk"
  ∷ "Ak_le_D3u"
  ∷ "sobolev_H5_C3"
  ∷ "Bk quadratic bound"
  ∷ "final GD3-SobolevBound-Correct formula"
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
      hBNumericallySupportedOnlyText ≡ "H_B numerically supported only"
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
    "H_B numerically supported only"
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
      "O: Record the corrected λ2 Hessian/vortex-core confinement receipt with explicit diagonal identity, KatoIdentity leaf, secondDeriv-expand, signed-gap, PSD minimum, curvature, Clay bridge blocker surfaces, and the Calc E note that no new NS calc was run or required."
    R : String
    RIsCanonical : R ≡
      "R: Record Hess(λ2) PSD-at-minimum, the diagonal identity witness, the KatoIdentity leaf rows, the signed gap split, the conditional gap-collapse-to-Hessian-blow-up route, the H5/H6 curvature distinction, full 3D Hessian geometry, aggregate N=128 stats, explicit fail-closed gate rows, and the Calc E rank order real min g12 on Omega_K, real rho on boundary from tensors, then Betti-0 count."
    C : String
    CIsCanonical : C ≡
      "C: The receipt stores typed canonical target/value shapes, explicit receipt surfaces, the KatoIdentity leaf row checks, empirical N=128 aggregate metadata, and Calc E/CL1 fail-closed evidence only; CL1 remains open and no new NS calc was required."
    S : String
    SIsCanonical : S ≡
      "S: Hessian PSD at core, the diagonal identity witness, the KatoIdentity leaf checked rows, the signed gap split, the PSD minimum surface, the gap-collapse/Hessian-blow-up route, the H5/H6 curvature split, triaxial full-3D core correction (large h33), positive cross-derivative confinement evidence, corrected Ωtube/Ωsheet split, Calc E empirical projection/receipt evidence, CL1 open bookkeeping, the no-new-NS-calc note, and the ranked optional calcs real min g12 on Omega_K, real rho on boundary from tensors, then Betti-0 count are recorded."
    L : String
    LIsCanonical : L ≡
      "L: Corrected sign convention at true λ2 minimum -> record the diagonal/gap/PSD/curvature/KatoIdentity leaf/Clay bridge surfaces plus Calc E empirical evidence -> keep CL1 open, note that no new NS calc was run or required, and keep all promotions fail-closed."
    P : String
    PIsCanonical : P ≡
      "P: Do not promote any confinement theorem, external-DNS bridge, global regularity claim, full regularity theorem, Clay claim, Clay bridge claim, KatoIdentity leaf row, Calc E evidence, CL1 open bookkeeping, or the optional calc ranking from this receipt."
    G : String
    GIsCanonical : G ≡
      "G: Governance guard: Miller bridge open only as theorem-candidate, Clay bridge open only as blocker, KatoIdentity leaf rows stay checked only, Calc E remains empirical and non-promoting, CL1 stays mathematically open and fail-closed, no new NS calc was required, the optional calc ranking is real min g12 on Omega_K, real rho on boundary from tensors, then Betti-0 count, and there is no external-DNS promotion path, no full/global regularity inhabitant, and no Clay promotion."
    F : String
    FIsCanonical : F ≡
      "F: Fail-closed due to explicit gate rows, the corrected sign convention, the open Clay bridge blocker, the KatoIdentity leaf checks, the open CL1 bookkeeping, and the note that no new NS calc was run or required; proof obligations remain external to this row, and the optional calcs stay ranked as real min g12 on Omega_K, real rho on boundary from tensors, then Betti-0 count."

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
    "O: Record the corrected λ2 Hessian/vortex-core confinement receipt with explicit diagonal identity, KatoIdentity leaf, secondDeriv-expand, signed-gap, PSD minimum, curvature, Clay bridge blocker surfaces, and the Calc E note that no new NS calc was run or required."
    refl
    "R: Record Hess(λ2) PSD-at-minimum, the diagonal identity witness, the KatoIdentity leaf rows, the signed gap split, the conditional gap-collapse-to-Hessian-blow-up route, the H5/H6 curvature distinction, full 3D Hessian geometry, aggregate N=128 stats, explicit fail-closed gate rows, and the Calc E rank order real min g12 on Omega_K, real rho on boundary from tensors, then Betti-0 count."
    refl
    "C: The receipt stores typed canonical target/value shapes, explicit receipt surfaces, the KatoIdentity leaf row checks, empirical N=128 aggregate metadata, and Calc E/CL1 fail-closed evidence only; CL1 remains open and no new NS calc was required."
    refl
    "S: Hessian PSD at core, the diagonal identity witness, the KatoIdentity leaf checked rows, the signed gap split, the PSD minimum surface, the gap-collapse/Hessian-blow-up route, the H5/H6 curvature split, triaxial full-3D core correction (large h33), positive cross-derivative confinement evidence, corrected Ωtube/Ωsheet split, Calc E empirical projection/receipt evidence, CL1 open bookkeeping, the no-new-NS-calc note, and the ranked optional calcs real min g12 on Omega_K, real rho on boundary from tensors, then Betti-0 count are recorded."
    refl
    "L: Corrected sign convention at true λ2 minimum -> record the diagonal/gap/PSD/curvature/KatoIdentity leaf/Clay bridge surfaces plus Calc E empirical evidence -> keep CL1 open, note that no new NS calc was run or required, and keep all promotions fail-closed."
    refl
    "P: Do not promote any confinement theorem, external-DNS bridge, global regularity claim, full regularity theorem, Clay claim, Clay bridge claim, KatoIdentity leaf row, Calc E evidence, CL1 open bookkeeping, or the optional calc ranking from this receipt."
    refl
    "G: Governance guard: Miller bridge open only as theorem-candidate, Clay bridge open only as blocker, KatoIdentity leaf rows stay checked only, Calc E remains empirical and non-promoting, CL1 stays mathematically open and fail-closed, no new NS calc was required, the optional calc ranking is real min g12 on Omega_K, real rho on boundary from tensors, then Betti-0 count, and there is no external-DNS promotion path, no full/global regularity inhabitant, and no Clay promotion."
    refl
    "F: Fail-closed due to explicit gate rows, the corrected sign convention, the open Clay bridge blocker, the KatoIdentity leaf checks, the open CL1 bookkeeping, and the note that no new NS calc was run or required; proof obligations remain external to this row, and the optional calcs stay ranked as real min g12 on Omega_K, real rho on boundary from tensors, then Betti-0 count."
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
    C_embed : String
    hM_pos : String
    hM : String
    hδ_pos : String
    hδ : String
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
    "C_embed"
    "hM_pos"
    "hM"
    "hδ_pos"
    "hδ"
    "C_emb"
    "hess_le_Ak_plus_Bk"
    "Ak_le_D3u"
    "sobolev_H5_C3"
    "Bk quadratic bound"
    "final GD3-SobolevBound-Correct formula: hess_le_Ak_plus_Bk, Ak_le_D3u, sobolev_H5_C3, and Bk quadratic bound are the recorded closure shapes with M, hM_pos, hM, δ0, hδ_pos, hδ, and C_emb as the named payload slots"
    "H5"
    "H6"
    "H5 curvature bound vs H6 Taylor remainder split"
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
  "GD3-SobolevBound-Correct: the checked GD3 row is standard on the KatoIdentity leaf and records the exact payload names M, hM_pos, hM, δ0, hδ_pos, hδ, C_emb, hess_le_Ak_plus_Bk, Ak_le_D3u, sobolev_H5_C3, Bk quadratic bound, and the final GD3-SobolevBound-Correct formula, while carrying the curvature-to-Sobolev split with secondDeriv-expand and H6 as the Taylor remainder. B_k remains only a recorded quadratic bound and no calcs/proxy claims are introduced."

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
  "GD3 exact blocker: none; this row is already standard on the current receipt variables, with GD3-SobolevBound-Correct projections checking the exact payload names M, hM_pos, hM, δ0, hδ_pos, hδ, C_emb, hess_le_Ak_plus_Bk, Ak_le_D3u, sobolev_H5_C3, Bk quadratic bound, and the final GD3-SobolevBound-Correct formula."
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
      "C: Kato-Morse status fields are explicit as provable classical/standard/trichotomy/open blocker, with secondDeriv-expand kept as a checked leaf surface only."
    S : String
    SIsCanonical : S ≡
      "S: beta(t)=theta*lambda2min(t), OmegaBeta, OmegaK, g12, g23, psi12=B/g12, B, B_k, C_k, c0, c1, M, hM_pos, hM, δ0, hδ_pos, hδ, C_embed, C_emb, hess_le_Ak_plus_Bk, Ak_le_D3u, sobolev_H5_C3, Bk quadratic bound, final GD3-SobolevBound-Correct formula, H5, H6, H5 bounded by M and H5/H6 split, Bk-quadratic-in-H5 honesty note, CL2 branch C, and secondDeriv-expand are recorded as exact program variables and shapes."
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
      "The H5 versus H6 split is explicit: H5 carries the curvature bound for Hess λ2 L∞, and H6 carries the Taylor confinement remainder; GD3-SobolevBound-Correct enforces the exact payload names M, hM_pos, hM, δ0, hδ_pos, hδ, C_emb, hess_le_Ak_plus_Bk, Ak_le_D3u, sobolev_H5_C3, Bk quadratic bound, and the final GD3-SobolevBound-Correct formula."
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
    "C: Kato-Morse status fields are explicit as provable classical/standard/trichotomy/open blocker, with secondDeriv-expand kept as a checked leaf surface only."
    refl
    "S: beta(t)=theta*lambda2min(t), OmegaBeta, OmegaK, g12, g23, psi12=B/g12, B, B_k, C_k, c0, c1, M, hM_pos, hM, δ0, hδ_pos, hδ, C_embed, C_emb, hess_le_Ak_plus_Bk, Ak_le_D3u, sobolev_H5_C3, Bk quadratic bound, final GD3-SobolevBound-Correct formula, H5, H6, H5 bounded by M and H5/H6 split, Bk-quadratic-in-H5 honesty note, CL2 branch C, and secondDeriv-expand are recorded as exact program variables and shapes."
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
    "The H5 versus H6 split is explicit: H5 carries the curvature bound for Hess λ2 L∞, and H6 carries the Taylor confinement remainder; GD3-SobolevBound-Correct enforces the exact payload names M, hM_pos, hM, δ0, hδ_pos, hδ, C_emb, hess_le_Ak_plus_Bk, Ak_le_D3u, sobolev_H5_C3, Bk quadratic bound, and the final GD3-SobolevBound-Correct formula."
    refl
    canonicalKatoMorseProgramBlockers
    refl
    false
    refl
    true
    refl
    canonicalKatoMorseProgramORCSLPGF
