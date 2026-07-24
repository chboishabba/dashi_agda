#!/usr/bin/env python3
"""Fail-closed audit for exact finite-cell and quantitative YM certificates."""

from __future__ import annotations

from pathlib import Path
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
YM = ROOT / "DASHI/Physics/YangMills"

FILES = {
    YM / "BalabanBoolean4BlockPoincareExact.agda": [
        "walshSpectralIdentityRaw",
        "walshRemainderNonnegative",
        "boolean4BlockPoincare",
        "fourComponentBoolean4BlockPoincare",
        "finiteDisjointBoolean4BlockPoincare",
        "arbitraryPhysicalRGBlockPoincareLevel = conditional",
    ],
    YM / "BalabanBoolean4PhysicalBlockLiftExact.agda": [
        "translatedBlockPoincare",
        "translatedHaloPoincare",
        "translatedReferenceHodgePoincare",
        "physicalTranslatedBlockPoincare",
        "physicalReferenceHodgePoincare",
        "arbitraryFixedSideTensorizedBlockLevel = conditional",
        "physicalHaloOverlapCountingLevel = conditional",
    ],
    YM / "BalabanPath3PoincareExact.agda": [
        "path3SpectralIdentityRaw",
        "pathRemainderNonnegative",
        "path3Poincare",
        "fourPath3Poincare",
        "finiteDisjointPath3Poincare",
        "path3FourDimensionalTensorizationLevel = conditional",
    ],
    YM / "BalabanRationalLDLCertificate.agda": [
        "termValueNonnegative",
        "sumTermValuesNonnegative",
        "RationalLDLCertificate",
        "ldlCertificatePoincare",
        "arbitraryLengthLDLCertificateConsumerLevel = machineChecked",
    ],
    YM / "BalabanPath4GeneratedLDLCertificate.agda": [
        "path4LDLDecompositionRaw",
        "path4LDLCertificate",
        "path4Poincare",
        "path4GeneratedLDLReconstructionLevel = computed",
        "path4GeneratedLDLConsumptionLevel = machineChecked",
    ],
    YM / "BalabanFourDimensionalLDLTensorization.agda": [
        "familyLDLPoincare",
        "FourDimensionalTensorizationData",
        "fourDimensionalTensorizedPoincare",
        "fourDimensionalLDLTensorizationLevel = machineChecked",
        "physicalFourDimensionalFibreDecompositionLevel = conditional",
    ],
    YM / "BalabanFourDimensionalHaloOverlapExact.agda": [
        "lengthAllCyclicIndices",
        "haloOffsetEnumerationLength",
        "literalFourDimensionalHaloOverlap",
        "regularTranslatedHaloOverlapCountLevel = machineChecked",
        "physicalBlockOriginOffsetBijectionLevel = conditional",
    ],
    YM / "BalabanBoolean4PatchExtensionsExact.agda": [
        "restrictFaceAfterExtend",
        "faceNormIdentity",
        "faceEnergyIdentity",
        "facePoincare",
        "restrictCornerAfterExtend",
        "cornerNormIdentity",
        "cornerEnergyIdentity",
        "cornerPoincare",
        "physicalWeightedPatchResidualLevel = conditional",
    ],
    YM / "BalabanBoolean4PatchLaplacianIntertwining.agda": [
        "cubeLaplacian",
        "faceLaplacianIntertwining",
        "cornerLaplacianIntertwining",
        "boolean4BoundaryReferenceResidualZeroLevel = machineChecked",
        "boolean4CornerReferenceResidualZeroLevel = machineChecked",
        "physicalBackgroundPatchResidualLevel = conditional",
    ],
    YM / "BalabanSU2AdjointTransportExact.agda": [
        "adjointRotationNormExact",
        "adjointDisplacementWithUnitDefectExact",
        "unitDefectVanishes",
        "adjointDisplacementOnUnitQuaternion",
        "su2AdjointSmallRadiusOperatorBoundLevel = conditional",
    ],
    YM / "BalabanSU2AdjointOrderedReduction.agda": [
        "unitMainPlusDotSquareExact",
        "unitAdjointMainUpper",
        "unitQuaternionAdjointDisplacementUpper",
        "su2AdjointOrderedSquareReductionLevel = machineChecked",
        "su2ImaginaryPartRadiusInputLevel = conditional",
        "su2SquaredNormToOperatorNormInputLevel = conditional",
    ],
    YM / "BalabanSU2TransportTelescopingExact.agda": [
        "rotationAddX",
        "rotateSub",
        "transportStepExact",
        "transportRemainderExact",
        "su2TransportPathNormBoundLevel = conditional",
    ],
    YM / "BalabanSU2TransportPathNormBound.agda": [
        "transportRemainderNormBound",
        "transportDisplacementNormBound",
        "pathBudgetEqualsLengthScale",
        "transportPathLengthNormBound",
        "su2OneLinkSmallRadiusBoundLevel = conditional",
    ],
    YM / "BalabanDyadicQuantitativeRegionExact.agda": [
        "hessianCandidateComputation",
        "hessianCandidateBudget",
        "patchCandidateComputation",
        "nonlinearCandidateComputation",
        "candidateQuantitativeRegion",
        "physicalHessianCoefficientDerivationLevel = conditional",
        "physicalPatchCoefficientDerivationLevel = conditional",
        "physicalSevenNonlinearCoefficientDerivationLevel = conditional",
    ],
    YM / "BalabanWilsonRGCoefficientCombinatoricsExact.agda": [
        "curvatureCandidateFromIncidence",
        "derivedFiveComponentMatchesCandidate",
        "LiteralWilsonRGOperatorCoefficientMatch",
        "wilsonRGIncidenceArithmeticLevel = computed",
        "literalWilsonRGOperatorEstimateLevel = conditional",
    ],
    YM / "BalabanCollarPatchResidualBudgetExact.agda": [
        "rawNumeratorNormalization",
        "rawDenominatorNormalization",
        "collarPatchCandidateComputation",
        "collarPatchCandidateStrict",
        "collarPatchCandidateCertificate",
        "physicalCutoffCommutatorSchurLevel = conditional",
        "physicalBackgroundPatchMismatchLevel = conditional",
        "physicalInterfaceScaleMismatchLevel = conditional",
        "physicalNestedFarTailLevel = conditional",
    ],
    YM / "BalabanDyadicTerminalScaleExact.agda": [
        "terminalDyadicSpacingIsUnit",
        "normalizedDyadicTerminalScaleBounded",
        "normalizedDyadicTerminalSpacingLevel = machineChecked",
        "physicalRunningCouplingToDyadicScheduleLevel = conditional",
        "dimensionalTransmutationScaleMatchingLevel = conjectural",
    ],
    YM / "BalabanTerminalScalePhysicalClustering.agda": [
        "terminalScalePolymerGapProducesUniformPhysicalClustering",
        "terminalScaleToOSCorrelationDecayData",
        "terminalPhysicalClusteringAssemblyLevel = machineChecked",
        "terminalPolymerClusteringInputLevel = conditional",
        "terminalPhysicalScaleComparisonInputLevel = conditional",
    ],
    YM / "BalabanTerminalKPPhysicalScaleAssembly.agda": [
        "terminalPolymerClusteringFromStepV",
        "terminalScalePhysicalClusteringData",
        "terminalKPProducesUniformPhysicalClustering",
        "terminalKPPhysicalScaleAssemblyLevel = machineChecked",
        "stepVClusterEstimateCarrierMatchingLevel = conditional",
        "boundedTerminalPhysicalScaleInputLevel = conditional",
    ],
}

SCRIPTS = {
    ROOT / "scripts/search_ym_quantitative_region.py": [
        "Fraction",
        "physical_coefficients_proved",
        "HESSIAN_DEFAULTS",
        "NONLINEAR_DEFAULTS",
    ],
    ROOT / "scripts/generate_path_poincare_sos.py": [
        "Fraction",
        "mean_zero_basis",
        "path_laplacian",
        "ldl",
        "generate_agda_module",
        "agda_emitter_available",
        "agda_consumed",
    ],
}

FORBIDDEN = (
    "postulate",
    "{!!}",
    "{-# TERMINATING #-}",
    "= _",
)


def fail(message: str) -> None:
    print(f"Exact quantitative YM audit failed: {message}", file=sys.stderr)
    raise SystemExit(1)


def audit_text(path: Path, required: list[str], forbid_proof_escapes: bool) -> None:
    if not path.is_file():
        fail(f"missing {path.relative_to(ROOT)}")
    text = path.read_text(encoding="utf-8")
    if forbid_proof_escapes:
        for token in FORBIDDEN:
            if token in text:
                fail(f"forbidden token {token!r} in {path.relative_to(ROOT)}")
    for item in required:
        if item not in text:
            fail(f"missing {item!r} in {path.relative_to(ROOT)}")


def run_json_script(path: Path, *arguments: str) -> dict[str, object]:
    completed = subprocess.run(
        [sys.executable, str(path), *arguments],
        cwd=ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    try:
        return json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        fail(f"non-JSON output from {path.relative_to(ROOT)}: {error}")


def audit_generated_agda() -> None:
    with tempfile.TemporaryDirectory() as directory:
        output = Path(directory) / "GeneratedPath5LDLCertificate.agda"
        result = run_json_script(
            ROOT / "scripts/generate_path_poincare_sos.py",
            "5",
            "--agda-output",
            str(output),
            "--agda-module",
            "DASHI.Physics.YangMills.GeneratedPath5LDLCertificate",
        )
        if result.get("verified_exactly") is not True:
            fail("path-five LDL certificate did not verify exactly")
        if result.get("agda_emitter_available") is not True:
            fail("arbitrary-length Agda emitter was not reported available")
        generated = output.read_text(encoding="utf-8")
        for token in (
            "pathLDLDecompositionRaw = ℚRing.solve-∀",
            "pathLDLCertificate : RationalLDLCertificate PathCoordinates",
            "pathPoincare = ldlCertificatePoincare pathLDLCertificate",
            "generatedPathLDLConsumptionLevel = machineChecked",
        ):
            if token not in generated:
                fail(f"generated Agda certificate missing {token!r}")
        for token in FORBIDDEN:
            if token in generated:
                fail(f"generated Agda certificate contains {token!r}")


def main() -> None:
    for path, required in FILES.items():
        audit_text(path, required, forbid_proof_escapes=True)
    for path, required in SCRIPTS.items():
        audit_text(path, required, forbid_proof_escapes=False)

    region = run_json_script(
        ROOT / "scripts/search_ym_quantitative_region.py",
        "--max-exponent",
        "16",
    )
    if region.get("status") != "found":
        fail("default exact quantitative search found no region")
    if region.get("exponent") != 8:
        fail(f"unexpected first dyadic exponent: {region.get('exponent')!r}")
    if region.get("physical_coefficients_proved") is not False:
        fail("candidate coefficients must remain explicitly unproved")

    path3 = run_json_script(
        ROOT / "scripts/generate_path_poincare_sos.py",
        "3",
    )
    if path3.get("verified_exactly") is not True:
        fail("path-three LDL certificate did not verify exactly")
    if path3.get("agda_consumed") is not False:
        fail("generated data must not self-promote without Agda checking")

    audit_generated_agda()
    print("Exact finite-cell and quantitative YM certificates are fail-closed.")


if __name__ == "__main__":
    main()
