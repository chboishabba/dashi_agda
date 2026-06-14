#!/usr/bin/env python3
"""Generate the Paper 1 NS / Paper 3 YM / Paper 8 Unification theorem-variable manifest."""

from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT_DIR = REPO_ROOT / "Docs" / "papers" / "generated"
BASE_NAME = "core_papers_theorem_var_manifest"
COMPAT_BASE_NAMES = ("paper1_paper3_theorem_var_manifest",)
PLACEHOLDER_AGDA_FILES = frozenset(
    {
        "DASHI/Physics/Closure/MissingMathMasterFrontierReceipt.agda",
    }
)


@dataclass(frozen=True)
class ManifestRow:
    paper: str
    lemma: str
    agda_file: str
    exact_var: str
    expected_status: str
    authority: str
    section: str
    governance_note: str


ROWS: tuple[ManifestRow, ...] = (
    ManifestRow(
        "Paper1 NS",
        "Fixed-K LP identity/sign spine",
        "DASHI/Physics/Closure/NSPaper1ClayTargetReceipt.agda",
        "lpIdentityFixedKSignsLocked",
        "recorded",
        "repo-native Agda receipt",
        "Paper 1 Section 2",
        "Fixed cutoff bookkeeping only; no moving-cutoff theorem or Clay promotion.",
    ),
    ManifestRow(
        "Paper1 NS",
        "Theta seam definition after fixed-K profile",
        "DASHI/Physics/Closure/NSPaper1ClayTargetReceipt.agda",
        "thetaFluxOverDissDefinedAfterFixedKProfile",
        "recorded",
        "repo-native Agda receipt",
        "Paper 1 Sections 1-2",
        "Theta is a seam/profile variable, not a theorem-level monotonicity claim.",
    ),
    ManifestRow(
        "Paper1 NS",
        "Theta less than one implies tail decay",
        "DASHI/Physics/Closure/NSPaper1ClayTargetReceipt.agda",
        "thetaImpliesTailDecayConditionally",
        "conditional",
        "repo-native Agda receipt",
        "Paper 1 Section 2",
        "Conditional reduction only; real NS data must still supply the estimate.",
    ),
    ManifestRow(
        "Paper1 NS",
        "Danger-shell maximum principle",
        "DASHI/Physics/Closure/NSPaper1ClayTargetReceipt.agda",
        "dangerShellMaximumPrincipleOpen",
        "open",
        "repo-native Agda receipt",
        "Paper 1 Sections 3-6",
        "Hard open point; cannot be consumed as smoothness or Clay NS.",
    ),
    ManifestRow(
        "Paper1 NS",
        "H-minus-half nonlinear defect bound",
        "DASHI/Physics/Closure/NSPaper1ClayTargetReceipt.agda",
        "hMinusHalfNonlinearDefectBoundWithoutCircularity",
        "open",
        "repo-native Agda receipt",
        "Paper 1 Sections 3-6",
        "Promotion requires accepted constants and non-circular norm control.",
    ),
    ManifestRow(
        "Paper1 NS",
        "Comparison theorem target",
        "DASHI/Physics/Closure/NSPaper1ClayTargetReceipt.agda",
        "comparisonTheoremThetaControlsH118ByInterpolation",
        "target-only",
        "repo-native Agda receipt",
        "Paper 1 theorem-resolution checklist",
        "Explicit target, not accepted theorem input and not Clay closure.",
    ),
    ManifestRow(
        "Paper1 NS",
        "Tail-flux theta profile computability",
        "DASHI/Physics/Closure/NSTailFluxAbsorptionMarginReceipt.agda",
        "thetaProfileComputableAfterFixedKFluxDissProfile",
        "recorded",
        "repo-native Agda receipt",
        "Paper 1 Sections 1-2",
        "Profile is computed after fixed-K data; danger-shell argmax is separate.",
    ),
    ManifestRow(
        "Paper1 NS",
        "Theta analytic estimate",
        "DASHI/Physics/Closure/NSTailFluxAbsorptionMarginReceipt.agda",
        "thetaLessThanOneAnalyticEstimateProvedHere",
        "false",
        "repo-native Agda receipt",
        "Paper 1 Section 2",
        "Clay promotion row false; analytic theta<1 estimate is not proved here.",
    ),
    ManifestRow(
        "Paper1 NS",
        "Theta-to-theorem promotion",
        "DASHI/Physics/Closure/EV5ThetaMarginUpgradeReceipt.agda",
        "thetaPromotedToTheorem",
        "false",
        "repo-native Agda receipt",
        "Paper 1 theta/EV5 note",
        "Clay promotion row false; theta evidence remains diagnostic.",
    ),
    ManifestRow(
        "Paper1 NS",
        "Clay Navier-Stokes promotion guard",
        "DASHI/Physics/Closure/ClayNSCurrentStateReceipt.agda",
        "clayNSCurrentStateKeepsClayFalse",
        "false",
        "repo-native Agda receipt",
        "Paper 1 governance boundary",
        "Clay promotion row false by current-state guard.",
    ),
    ManifestRow(
        "Paper1 NS",
        "Paper-facing NS theorem interface",
        "DASHI/Papers/NavierStokes/TheoremInterface.agda",
        "canonicalNSPaperTheoremStatus",
        "interface",
        "repo-native Agda wrapper over exact A6/A7/A8/A9/final receipts",
        "Paper 1 formal-status appendix",
        "Normalized paper interface; does not promote Clay or terminal claims.",
    ),
    ManifestRow(
        "Paper1 NS",
        "Missing-math master: NS A1/A3 Abel stationarity",
        "DASHI/Physics/Closure/NSSereginESSTheoremIntakeReceipt.agda",
        "candidateAbelRateNotDerived",
        "open",
        "repo-native Seregin/ESS intake and Abel-rate boundary",
        "Paper 1 A1/A3 missing-math master frontier",
        "Abel stationarity remains open; governance blocks Clay and terminal promotion.",
    ),
    ManifestRow(
        "Paper1 NS",
        "Missing-math master: NS A4 support transfer",
        "DASHI/Physics/Closure/NSA4CoareaStripPreimageCalculationBoundary.agda",
        "A4LeiRenTianFourierOutputCouplingProved",
        "false",
        "repo-native A4 coarea/output-support boundary",
        "Paper 1 A4 missing-math master frontier",
        "Support transfer remains false as a theorem consumer; governance blocks Clay and terminal promotion.",
    ),
    ManifestRow(
        "Paper1 NS",
        "Missing-math master: NS A5 kappa-bias",
        "DASHI/Physics/Closure/NSA6A4BiasToLeakageClosureCompositeBoundary.agda",
        "a5BiasVanishingTheoremProved",
        "false",
        "repo-native A4/A5/A6 bias-to-leakage boundary",
        "Paper 1 A5 missing-math master frontier",
        "A5 kappa-bias vanishing stays false as a theorem burden; governance blocks Clay and terminal promotion.",
    ),
    ManifestRow(
        "Paper1 NS",
        "Missing-math master: NS A6 pointwise-to-Abel",
        "DASHI/Physics/Closure/NSPointwiseToAbelCompositeA6Boundary.agda",
        "compositeA6BoundaryDoesNotProveNSClay",
        "downstream-locked",
        "repo-native A6 pointwise-to-Abel composite boundary",
        "Paper 1 A6 missing-math master frontier",
        "A6 is downstream-locked behind residual monotonicity/A7 and cannot promote Clay or terminal claims.",
    ),
    ManifestRow(
        "Paper1 NS",
        "Seregin/ESS A3 theorem-intake boundary",
        "DASHI/Physics/Closure/NSPaper1ClayTargetReceipt.agda",
        "publishableClaimText",
        "authority-intake-boundary",
        "external Seregin/ESS compactness intake; candidate Abel rate remains a target",
        "Paper 1 A1-A3 and Appendix B",
        "Records the Seregin/ESS ancient-solution intake as support only; A3 constants and Clay promotion remain unpromoted.",
    ),
    ManifestRow(
        "Paper1 NS",
        "A9 CKN/BKM closure interface anchor",
        "DASHI/Papers/NavierStokes/TheoremInterface.agda",
        "a9CKNBKMClosureProved",
        "true",
        "NSA9CKNBKMClosureBoundary imported equality",
        "Paper 1 formal-status appendix",
        "Receipt-level A9 anchor only; final Clay promotion remains false.",
    ),
    ManifestRow(
        "Paper1 NS",
        "NS terminal Clay guard in interface",
        "DASHI/Papers/NavierStokes/TheoremInterface.agda",
        "nsPaperInterfaceTerminalFalse",
        "false",
        "NSFinalStateReceipt imported equality",
        "Paper 1 governance boundary",
        "Explicitly prevents paper-facing interface from reading as Clay promotion.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Paper 3 carrier-to-continuum claim chain",
        "DASHI/Physics/Closure/YMPaper3ClayTargetReceipt.agda",
        "canonicalYMPaper3ClaimChain",
        "recorded",
        "repo-native Agda receipt",
        "Paper 3 Sections 1-5",
        "Records actualActivity -> KP -> Balaban -> area law -> open continuum gaps.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Actual polymer activity",
        "DASHI/Physics/Closure/YMPaper3ClayTargetReceipt.agda",
        "actualActivityStep",
        "recorded",
        "repo-native Agda receipt",
        "Paper 3 KP/Balaban setup",
        "Carrier-scale activity step only; not continuum Yang-Mills.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Gate 3 bridge",
        "DASHI/Physics/Closure/YMPaper3ClayTargetReceipt.agda",
        "gate3BridgeStepOpen",
        "open",
        "repo-native Agda receipt",
        "Paper 3 Section 5",
        "Open bridge; cannot be promoted to Clay authority.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Continuum mass-gap step",
        "DASHI/Physics/Closure/YMPaper3ClayTargetReceipt.agda",
        "continuumMassGapStepOpen",
        "open",
        "repo-native Agda receipt",
        "Paper 3 Sections 5-7",
        "Open continuum step; finite carrier margins are not the Clay mass gap.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Mosco bridge gap",
        "DASHI/Physics/Closure/YMPaper3ClayTargetReceipt.agda",
        "moscoBridgeOpen",
        "open",
        "repo-native Agda receipt",
        "Paper 3 Section 5",
        "Mosco structure alone does not prove no spectral pollution.",
    ),
    ManifestRow(
        "Paper3 YM",
        "No-spectral-pollution gap",
        "DASHI/Physics/Closure/YMPaper3ClayTargetReceipt.agda",
        "noSpectralPollutionOpen",
        "open",
        "repo-native Agda receipt",
        "Paper 3 Section 5.3",
        "Requires H3a/H3b-strength transfer before promotion.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Mass-shell bridge gap",
        "DASHI/Physics/Closure/YMPaper3ClayTargetReceipt.agda",
        "massShellBridgeOpen",
        "open",
        "repo-native Agda receipt",
        "Paper 3 Section 7",
        "Physical mass-shell identification remains a boundary obligation.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Continuum mass gap proved field",
        "DASHI/Physics/Closure/YMPaper3ClayTargetReceipt.agda",
        "continuumMassGapProved",
        "false",
        "repo-native Agda receipt",
        "Paper 3 governance boundary",
        "Clay promotion row false; continuum mass gap is not proved here.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Clay YM mass-gap promotion field",
        "DASHI/Physics/Closure/YMPaper3ClayTargetReceipt.agda",
        "clayYMMassGapPromoted",
        "false",
        "repo-native Agda receipt",
        "Paper 3 governance boundary",
        "Clay promotion row false by target receipt.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Balaban RG / H3a frontier",
        "DASHI/Physics/Closure/Paper3YMDependencyGraphReceipt.agda",
        "ym6Statement",
        "open-frontier",
        "repo-native Agda receipt plus cited-authority intake",
        "Paper 3 Section 5.1",
        "H3a remains the Balaban-centered hard bridge unless accepted as authority intake.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Balaban Option A theorem-intake boundary",
        "DASHI/Physics/Closure/Paper3YMDependencyGraphReceipt.agda",
        "ym6Statement",
        "authority-intake-boundary",
        "external Balaban RG/polymer theorem intake for H3a",
        "Paper 3 Section 5.1",
        "Records Option A as a cited-authority intake surface only; no local Balaban theorem, mass gap, Clay, or terminal promotion follows.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Option B B1 Casimir suppression boundary",
        "DASHI/Physics/Closure/OptionBNativePolymerFiveLemmaBoundaryReceipt.agda",
        "B1CasimirSuppressionSU2SU3Constants",
        "diagnostic",
        "repo-native Option-B gate constructor",
        "Paper 3 Section 5.1 companion-paper boundary",
        "B1 records finite SU2/SU3 Casimir constants only; it is not a Clay authority and cannot promote Clay YM.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Option B B2 polymer localization boundary",
        "DASHI/Physics/Closure/OptionBNativePolymerFiveLemmaBoundaryReceipt.agda",
        "B2PolymerLocalization",
        "diagnostic",
        "repo-native Option-B gate constructor",
        "Paper 3 Section 5.1 companion-paper boundary",
        "B2 records finite carrier localization only; it supplies no continuum support theorem and cannot promote Clay YM.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Option B B3 Kotecky-Preiss activity bound",
        "DASHI/Physics/Closure/OptionBNativePolymerFiveLemmaBoundaryReceipt.agda",
        "B3DASHIBalabanActivityBoundAndKPCondition",
        "false",
        "repo-native Option-B gate constructor",
        "Paper 3 Section 5.1 companion-paper boundary",
        "B3 keeps the KP activity condition false; the deferred activity bound cannot be consumed as Clay YM promotion.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Option B B4 trace-norm consequence boundary",
        "DASHI/Physics/Closure/OptionBNativePolymerFiveLemmaBoundaryReceipt.agda",
        "B4TraceNormConvergenceFromSummability",
        "diagnostic",
        "repo-native Option-B gate constructor",
        "Paper 3 Section 5.1 companion-paper boundary",
        "B4 records summability/Cauchy diagnostics only; it does not construct the operator limit or promote Clay YM.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Option B B5 intermediate-beta RG induction boundary",
        "DASHI/Physics/Closure/OptionBNativePolymerFiveLemmaBoundaryReceipt.agda",
        "B5IntermediateBetaRGInductionWarning",
        "false",
        "repo-native Option-B gate constructor",
        "Paper 3 Section 5.1 companion-paper boundary",
        "B5 keeps the intermediate-beta RG induction candidate unpromoted; continuum, mass-gap, and Clay YM promotion remain blocked.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Balaban RG theorem proved field",
        "DASHI/Physics/Closure/Paper3YMDependencyGraphReceipt.agda",
        "balabanRGTheoremProved",
        "false",
        "repo-native Agda receipt",
        "Paper 3 Section 5.1",
        "Clay promotion row false; no local full Balaban theorem is claimed.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Yang-Mills mass-gap promotion field",
        "DASHI/Physics/Closure/Paper3YMDependencyGraphReceipt.agda",
        "yangMillsMassGapPromoted",
        "false",
        "repo-native Agda receipt",
        "Paper 3 governance boundary",
        "Clay promotion row false; mass-gap promotion is blocked.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Clay Yang-Mills promotion boundary",
        "DASHI/Physics/Closure/YMClayPromotionBoundary.agda",
        "clayYangMillsPromoted",
        "false",
        "repo-native Agda receipt",
        "Paper 3 governance boundary",
        "Clay promotion row false by explicit boundary.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Paper-facing YM theorem interface",
        "DASHI/Papers/YangMills/TheoremInterface.agda",
        "canonicalYangMillsPaperTheoremInterface",
        "interface",
        "repo-native Agda wrapper over self-adjointness, Bochner, Gate3, and final receipts",
        "Paper 3 formal-status appendix",
        "Normalized paper interface; separates local finite anchors from OS/continuum/Clay guards.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Local Bochner-Weitzenbock domination interface anchor",
        "DASHI/Papers/YangMills/TheoremInterface.agda",
        "paperInterfaceLocalDominationTrue",
        "true",
        "YMBochnerWeitzenbockHamiltonianDominationBoundary imported equality",
        "Paper 3 formal-status appendix",
        "Local finite domination is recorded true; OS/continuum/Clay consumers remain separately guarded.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Gate3 no-spectral-pollution transfer interface anchor",
        "DASHI/Papers/YangMills/TheoremInterface.agda",
        "paperInterfacePAWOTGTransferTrue",
        "true",
        "Gate3PAWOTGUniformSeparationTargetReceipt imported equality",
        "Paper 3 formal-status appendix",
        "Transfer anchor true while Gate3 and Clay promotion remain false.",
    ),
    ManifestRow(
        "Paper3 YM",
        "YM terminal Clay guard in interface",
        "DASHI/Papers/YangMills/TheoremInterface.agda",
        "paperInterfaceClayTerminalFalse",
        "false",
        "YMFinalStateReceipt/interface guard",
        "Paper 3 governance boundary",
        "Explicitly prevents paper-facing interface from reading as Clay promotion.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Missing-math master: YM finite domination",
        "DASHI/Physics/Closure/YMBochnerWeitzenbockHamiltonianDominationBoundary.agda",
        "noClayPromotionFromYMBochnerWeitzenbockBoundary",
        "downstream-locked",
        "repo-native finite Bochner-Weitzenbock domination boundary",
        "Paper 3 finite-domination missing-math master frontier",
        "Finite domination is locked below OS/continuum transfer; governance blocks Clay and terminal promotion.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Missing-math master: YM H3a",
        "DASHI/Physics/Closure/YMH3aContinuumIntakeReceipt.agda",
        "ymH3aContinuumIntakeKeepsClayFalse",
        "authority-intake",
        "repo-native H3a continuum intake boundary",
        "Paper 3 H3a missing-math master frontier",
        "H3a is authority intake only; governance blocks Clay and terminal promotion.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Missing-math master: YM H3b",
        "DASHI/Physics/Closure/YMH3bVacuumProjectorNoSpectralPollutionBoundaryReceipt.agda",
        "ymH3bBoundaryPromotionImpossibleHere",
        "open",
        "repo-native H3b vacuum-projector boundary",
        "Paper 3 H3b missing-math master frontier",
        "H3b remains an open boundary before no-spectral-pollution consumers; governance blocks Clay and terminal promotion.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Missing-math master: YM no spectral pollution",
        "DASHI/Physics/Closure/YMNoSpectralPollutionToOSWightmanSocketCompositeLightweightBoundary.agda",
        "YMNoSpectralPollutionToOSWightmanSocketCompositeProved",
        "false",
        "repo-native no-spectral-pollution to OS/Wightman socket",
        "Paper 3 no-spectral-pollution missing-math master frontier",
        "No spectral pollution remains false as a promoted theorem; governance blocks Clay and terminal promotion.",
    ),
    ManifestRow(
        "Paper3 YM",
        "Missing-math master: YM RP/OS/Wightman",
        "DASHI/Physics/Closure/YMThermodynamicOSWightmanOperatorBoundaryReceipt.agda",
        "YMThermodynamicOSWightmanOperatorBoundaryClosesNothing",
        "downstream-locked",
        "repo-native thermodynamic OS/Wightman operator boundary",
        "Paper 3 RP/OS/Wightman missing-math master frontier",
        "RP/OS/Wightman consumers are downstream-locked and close no Clay theorem; governance blocks terminal promotion.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Paper 8 core thesis receipt",
        "DASHI/Physics/Closure/Paper8CoreThesisReceipt.agda",
        "canonicalPaper8CoreThesisReceipt",
        "recorded",
        "repo-native Agda receipt",
        "Paper 8 core thesis",
        "Records fail-closed receipt architecture and diagnostics without terminal physics unification.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Paper 8 terminal promotion guard",
        "DASHI/Physics/Closure/Paper8CoreThesisReceipt.agda",
        "paper8CoreThesisKeepsTerminalFalse",
        "false",
        "repo-native Agda receipt",
        "Paper 8 governance boundary",
        "Full unification, Clay YM, and Clay NS promotion remain false.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Millennium tower schema",
        "DASHI/Physics/Closure/MillenniumTowerSchemaReceipt.agda",
        "canonicalMillenniumTowerSchemaReceipt",
        "recorded",
        "repo-native Agda receipt",
        "Paper 8 Section 7",
        "Shared T0-T4 schema records YM/NS instances; T3/T4 obligations remain fail-closed.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Millennium tower Clay promotion guard",
        "DASHI/Physics/Closure/MillenniumTowerSchemaReceipt.agda",
        "millenniumTowerSchemaKeepsClayFalse",
        "false",
        "repo-native Agda receipt",
        "Paper 8 Section 7 governance boundary",
        "Schema typechecking does not promote Clay, full unification, or terminal claims.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Millennium tower YM instance",
        "DASHI/Physics/Closure/MillenniumTowerYangMillsInstanceReceipt.agda",
        "canonicalMillenniumTowerYangMillsInstanceReceipt",
        "recorded",
        "repo-native Agda receipt",
        "Paper 8 YM Millennium lane",
        "Finite carrier gap and field-equation surfaces are recorded; continuum/Clay YM remains blocked.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Millennium tower YM no-promotion guard",
        "DASHI/Physics/Closure/MillenniumTowerYangMillsInstanceReceipt.agda",
        "millenniumTowerYangMillsNoClayPromotion",
        "false",
        "repo-native Agda receipt",
        "Paper 8 YM Millennium lane boundary",
        "Keeps the YM instance from changing Paper 3 or Clay YM semantics.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Millennium tower NS instance",
        "DASHI/Physics/Closure/MillenniumTowerNavierStokesInstanceReceipt.agda",
        "canonicalMillenniumTowerNavierStokesInstanceReceipt",
        "recorded",
        "repo-native Agda receipt",
        "Paper 8 NS Millennium lane",
        "Finite NS regularity tower data are recorded; continuum BKM/Clay NS remains blocked.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Millennium tower NS no-promotion guard",
        "DASHI/Physics/Closure/MillenniumTowerNavierStokesInstanceReceipt.agda",
        "millenniumTowerNavierStokesNoClayPromotion",
        "false",
        "repo-native Agda receipt",
        "Paper 8 NS Millennium lane boundary",
        "Keeps the NS instance from changing Paper 1 or Clay NS semantics.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Millennium schema blocker map",
        "DASHI/Physics/Closure/MillenniumSchemaBlockerMapReceipt.agda",
        "canonicalMillenniumSchemaBlockerMapReceipt",
        "recorded",
        "repo-native Agda receipt",
        "Paper 8 blocker map",
        "Records YM active blocker plus NS/unification candidate-package posture without promotion.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Millennium schema terminal guard",
        "DASHI/Physics/Closure/MillenniumSchemaBlockerMapReceipt.agda",
        "millenniumSchemaBlockerMapKeepsTerminalFalse",
        "false",
        "repo-native Agda receipt",
        "Paper 8 blocker map boundary",
        "Blocker map is structural only and makes no Yang-Mills, Navier-Stokes, unification, or terminal promotion.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "U-1a-H scale-invariant cross-term hypothesis",
        "DASHI/Physics/Closure/UnificationScaleInvariantCrossTermHypothesisBoundary.agda",
        "scaleInvariantCrossTermHypothesisRecorded",
        "recorded",
        "repo-native Agda receipt",
        "Paper 8 UCT.1/U-1a-H frontier",
        "Records the cross-term hypothesis boundary; decomposition and downstream consumers remain open.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "U-1a-H decomposition blocker",
        "DASHI/Physics/Closure/UnificationScaleInvariantCrossTermHypothesisBoundary.agda",
        "scaleInvariantCrossTermDecompositionProved",
        "false",
        "repo-native Agda receipt",
        "Paper 8 UCT.1/U-1a-H frontier",
        "First live theorem burden stays false; two-homogeneity alone is not accepted.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Missing-math master: UCT.1 residual PDE",
        "DASHI/Physics/Closure/UnificationCrossTermNullityTheoremBoundary.agda",
        "uct1ResidualPDESpecificationRecorded",
        "open",
        "repo-native UCT exact-intake theorem boundary",
        "Paper 8 UCT.1 missing-math master frontier",
        "UCT.1 residual PDE remains an open intake burden; governance blocks Clay and terminal promotion.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Missing-math master: UCT.2 operator class",
        "DASHI/Physics/Closure/UnificationCrossTermNullityTheoremBoundary.agda",
        "uct2EllipticityOrParabolicityClassRecorded",
        "open",
        "repo-native UCT exact-intake theorem boundary",
        "Paper 8 UCT.2 missing-math master frontier",
        "UCT.2 elliptic/parabolic class remains an open intake burden; governance blocks Clay and terminal promotion.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Missing-math master: UCT.3 Carleman intake",
        "DASHI/Physics/Closure/UnificationCrossTermNullityTheoremBoundary.agda",
        "uct3CarlemanUniqueContinuationRecorded",
        "authority-intake",
        "repo-native UCT exact-intake theorem boundary",
        "Paper 8 UCT.3 missing-math master frontier",
        "UCT.3 is authority intake only and does not discharge UCT.4; governance blocks Clay and terminal promotion.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Missing-math master: UCT.4 cross-term nullity",
        "DASHI/Physics/Closure/UnificationCrossTermNullityTheoremBoundary.agda",
        "uct4ActualTheoremTargetRecorded",
        "open",
        "repo-native UCT exact theorem-target boundary",
        "Paper 8 UCT.4 missing-math master frontier",
        "UCT.4 cross-term nullity remains open; governance blocks Clay and terminal promotion.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Missing-math master: UCT.5 modulo-null linearity",
        "DASHI/Physics/Closure/UnificationCrossTermNullityTheoremBoundary.agda",
        "moduloNullLinearityConsumer",
        "downstream-locked",
        "repo-native UCT downstream consumer boundary",
        "Paper 8 UCT.5 missing-math master frontier",
        "UCT.5 is locked downstream of UCT.4 and cannot promote Clay or terminal claims.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Missing-math master: UCT.6 four-point cancellation",
        "DASHI/Physics/Closure/UnificationCrossTermNullityTheoremBoundary.agda",
        "fourPointConsumer",
        "downstream-locked",
        "repo-native UCT downstream consumer boundary",
        "Paper 8 UCT.6 missing-math master frontier",
        "UCT.6 is locked downstream of UCT.5 and cannot promote Clay or terminal claims.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Missing-math master: UCT.7 parallelogram",
        "DASHI/Physics/Closure/UnificationCrossTermNullityTheoremBoundary.agda",
        "parallelogramConsumer",
        "downstream-locked",
        "repo-native UCT downstream consumer boundary",
        "Paper 8 UCT.7 missing-math master frontier",
        "UCT.7 is locked downstream of UCT.6 and cannot promote Clay or terminal claims.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Missing-math master: UCT.8 Jordan-von Neumann",
        "DASHI/Physics/Closure/UnificationCrossTermNullityTheoremBoundary.agda",
        "jordanVonNeumannAdapterConsumer",
        "downstream-locked",
        "repo-native UCT downstream consumer boundary",
        "Paper 8 UCT.8 missing-math master frontier",
        "UCT.8 is locked downstream of UCT.7 and cannot promote Clay or terminal claims.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Cross-term nullity discriminant",
        "DASHI/Physics/Closure/UnificationCrossTermNullityDiscriminantBoundary.agda",
        "UnificationCrossTermNullityDiscriminantRecorded",
        "recorded",
        "repo-native Agda receipt",
        "Paper 8 UCT.4 frontier",
        "Records the discriminant boundary feeding UCT.4-UCT.8 consumers without discharging it.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Cross-term nullity discriminant proof guard",
        "DASHI/Physics/Closure/UnificationCrossTermNullityDiscriminantBoundary.agda",
        "UnificationCrossTermNullityDiscriminantProved",
        "false",
        "repo-native Agda receipt",
        "Paper 8 UCT.4 frontier",
        "Residual nullity remains a fail-closed blocker before downstream promotion.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Null-class subspace completeness",
        "DASHI/Physics/Closure/UnificationNullClassSubspaceCompleteBoundary.agda",
        "UnificationNullClassSubspaceCompleteRecorded",
        "recorded",
        "repo-native Agda receipt",
        "Paper 8 modulo-null consumer chain",
        "Records null-class subspace completeness as a consumer boundary, not a terminal theorem.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Parallelogram law from bilinear boundary",
        "DASHI/Physics/Closure/UnificationParallelogramFromBilinearBoundary.agda",
        "UnificationParallelogramFromBilinearRecorded",
        "recorded",
        "repo-native Agda receipt",
        "Paper 8 UCT.6 frontier",
        "Records the bilinear-to-parallelogram route while keeping the theorem burden explicit.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Jordan-von Neumann socket",
        "DASHI/Physics/Closure/UnificationParallelogramToJordanVonNeumannSocketCompositeLightweightBoundary.agda",
        "UnificationParallelogramToJordanVonNeumannSocketCompositeRecorded",
        "recorded",
        "repo-native Agda receipt",
        "Paper 8 UCT.7 frontier",
        "Downstream socket is recorded; it does not replace the missing parallelogram/Jordan-von Neumann proof.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Unification authority review packet",
        "DASHI/Physics/Closure/UnificationAuthorityReviewPacketBoundary.agda",
        "UnificationAuthorityReviewPacketRecorded",
        "recorded",
        "repo-native Agda receipt",
        "Paper 8 authority boundary",
        "Authority packet is recorded but not ready and does not enable terminal promotion.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Unification authority review no-promotion guard",
        "DASHI/Physics/Closure/UnificationAuthorityReviewPacketBoundary.agda",
        "TerminalPromotionFromUnificationAuthorityReviewPacket",
        "false",
        "repo-native Agda receipt",
        "Paper 8 authority boundary",
        "Explicit terminal promotion guard for the review packet.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Paper-facing Unification theorem interface",
        "DASHI/Papers/Unification/TheoremInterface.agda",
        "canonicalUnificationPaperTheoremInterface",
        "interface",
        "repo-native Agda wrapper over UCT receipts and consumer authority boundaries",
        "Paper 8 formal-status appendix",
        "Normalized paper interface; terminal unification promotion remains false.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "DCHoTT adapter index",
        "DASHI/DCHoTT/UnificationCandidate.agda",
        "canonicalDCHoTTUnificationCandidateAdapter",
        "adapter",
        "repo-native DCHoTT interpretation adapter",
        "Paper 8 adapter appendix",
        "DCHoTT adapter records interpretation coverage without full repo port or terminal promotion.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "DCHoTT adapter terminal guard",
        "DASHI/DCHoTT/UnificationCandidate.agda",
        "dchottUnificationCandidateTerminalFalse",
        "false",
        "repo-native DCHoTT interpretation adapter",
        "Paper 8 adapter appendix",
        "Terminal unification remains false through the DCHoTT-facing adapter.",
    ),
    ManifestRow(
        "Paper8 Unification",
        "Cubical adapter incompatibility surface",
        "DASHI/Cubical/UnificationCandidate.agda",
        "unificationCubicalAdapterIncompatibility",
        "adapter-boundary",
        "repo-native Cubical compatibility boundary",
        "Paper 8 adapter appendix",
        "Records why a Cubical wrapper is not constructed; no Cubical path or terminal promotion is fabricated.",
    ),
)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    parser.add_argument(
        "--canonical-only",
        action="store_true",
        help="write only the canonical core_papers manifest files, skipping compatibility aliases",
    )
    return parser.parse_args(argv)


def token_exists(text: str, token: str) -> bool:
    return re.search(rf"(?<![A-Za-z0-9_']){re.escape(token)}(?![A-Za-z0-9_'])", text) is not None


def validate_rows(rows: tuple[ManifestRow, ...], repo_root: Path) -> list[str]:
    errors: list[str] = []
    text_cache: dict[str, str] = {}
    for row in rows:
        path = repo_root / row.agda_file
        if not path.exists():
            if row.agda_file in PLACEHOLDER_AGDA_FILES:
                continue
            errors.append(f"missing Agda file: {row.agda_file}")
            continue
        if row.agda_file not in text_cache:
            text_cache[row.agda_file] = path.read_text(encoding="utf-8")
        if not token_exists(text_cache[row.agda_file], row.exact_var):
            errors.append(f"missing exact var {row.exact_var!r} in {row.agda_file}")
    return errors


def render_markdown(rows: tuple[ManifestRow, ...]) -> str:
    headers = [
        "paper",
        "lemma",
        "Agda file",
        "exact var",
        "expected status",
        "authority",
        "section",
        "governance note",
    ]
    lines = [
        "# Paper 1 / Paper 3 / Paper 8 theorem-variable manifest",
        "",
        "Generated deterministically by `scripts/generate_paper_proof_manifest.py`.",
        "Clay, full-unification, and terminal promotion rows are kept false; open rows stay open or target-only.",
        "",
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        values = [
            row.paper,
            row.lemma,
            f"`{row.agda_file}`",
            f"`{row.exact_var}`",
            row.expected_status,
            row.authority,
            row.section,
            row.governance_note,
        ]
        lines.append("| " + " | ".join(value.replace("|", "\\|") for value in values) + " |")
    return "\n".join(lines) + "\n"


def write_manifest_set(
    rows: tuple[ManifestRow, ...],
    out_dir: Path,
    base_name: str,
    *,
    compatibility_alias: bool = False,
) -> list[Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    json_path = out_dir / f"{base_name}.json"
    tsv_path = out_dir / f"{base_name}.tsv"
    md_path = out_dir / f"{base_name}.md"

    payload = {
        "generator": "scripts/generate_paper_proof_manifest.py",
        "basename": base_name,
        "compatibility_alias": compatibility_alias,
        "row_count": len(rows),
        "columns": list(ManifestRow.__dataclass_fields__.keys()),
        "rows": [asdict(row) for row in rows],
    }
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    with tsv_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(ManifestRow.__dataclass_fields__.keys()), delimiter="\t")
        writer.writeheader()
        for row in rows:
            writer.writerow(asdict(row))

    md_path.write_text(render_markdown(rows), encoding="utf-8")
    return [json_path, tsv_path, md_path]


def write_outputs(
    rows: tuple[ManifestRow, ...],
    out_dir: Path,
    *,
    include_compatibility_aliases: bool = True,
) -> list[Path]:
    paths = write_manifest_set(rows, out_dir, BASE_NAME)
    if not include_compatibility_aliases:
        return paths
    for compat_base_name in COMPAT_BASE_NAMES:
        paths.extend(
            write_manifest_set(
                rows,
                out_dir,
                compat_base_name,
                compatibility_alias=True,
            )
        )
    return paths


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir

    errors = validate_rows(ROWS, repo_root)
    if errors:
        for error in errors:
            print(f"generate_paper_proof_manifest: {error}", file=sys.stderr)
        return 1

    paths = write_outputs(
        ROWS,
        out_dir,
        include_compatibility_aliases=not args.canonical_only,
    )
    print(f"wrote {len(ROWS)} rows")
    for path in paths:
        rel = path.relative_to(repo_root) if path.is_relative_to(repo_root) else path
        print(rel.as_posix())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
