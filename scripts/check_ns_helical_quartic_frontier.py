#!/usr/bin/env python3
"""Fail closed on the helical, coherence, and Stage-3 analytic tranche."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

FILES = [
    "DASHI/Physics/Closure/NSTriadKNPeriodicHelicalFourierInfrastructure.agda",
    "DASHI/Physics/Closure/NSTriadKNHelicityPerturbedOperatorQuadratic.agda",
    "DASHI/Physics/Closure/NSTriadKNGlobalHelicityH3DiscriminantCounterexample.agda",
    "DASHI/Physics/Closure/NSTriadKNLocalizedHelicityCommutatorProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNAdaptiveLinearHelicalProbeProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNHelicalDiscriminantMarginProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNLocalizedHelicityExactReconnaissance.agda",
    "DASHI/Physics/Closure/NSTriadKNFixedSymbolBalancedFamilyReconnaissance.agda",
    "DASHI/Physics/Closure/NSTriadKNTriadPhaseCoherenceFallback.agda",
    "DASHI/Physics/Closure/NSTriadKNOffDiagonalReflectionMatrixCandidate.agda",
    "DASHI/Physics/Closure/NSTriadKNMatrixCoherenceExactReconnaissance.agda",
    "DASHI/Physics/Closure/NSTriadKNConstantinFeffermanDirectionCoherenceProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNTriadDirectionAlignmentProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNPermanaAlignmentRateAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNObjectiveVortexCriteriaScopeAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNHelicalCandidateDecisionFork.agda",
    "DASHI/Physics/Closure/NSTriadKNKiriukhinOrbitRowSumAdapter.agda",
    "DASHI/Physics/Closure/NSTriadKNKiriukhinSymmetricStretchingCompanionAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNOrbitToDyadicShellBridge.agda",
    "DASHI/Physics/Closure/NSTriadKNFiniteHelicityRowLifting.agda",
    "DASHI/Physics/Closure/NSTriadKNWeightedSchurDualityProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNGrafakosTorresThreeFunctionSchurProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNGrafakosTorresExactTransposeSymbols.agda",
    "DASHI/Physics/Closure/NSTriadKNTaoFrozenLegParaproductProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNBernsteinDirectionAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNFrozenLegDerivativeLerayLedger.agda",
    "DASHI/Physics/Closure/NSTriadKNShellExponentLedgerProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNHighHighToLowCancellationProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNThreeWeightAffineCertificateProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNMultilinearSchurParaproductProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNTriadicDyadicExponentSystem.agda",
    "DASHI/Physics/Closure/NSTriadKNKiriukhinWeightedSchurFiniteReconnaissance.agda",
    "DASHI/Physics/Closure/NSTriadKNStage3KiriukhinWeightedSchurProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3AlgebraLaws.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3RelocationInstantiation.agda",
    "DASHI/Physics/Closure/NSTriadKNLiteralVectorAdjointCandidates.agda",
    "DASHI/Physics/Closure/NSTriadKNCherevanResonantParaproductAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNSymmetrisedFirstAdjointNullAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNFirstAdjointSobolevTailLedger.agda",
    "DASHI/Physics/Closure/NSTriadKNRepositoryDyadicSeparationAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNThreeNumericShellLedgerStatus.agda",
    "DASHI/Physics/Closure/NSTriadKNStage3AdjointTailIntegration.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticLyapunovStage3AdjointTailBridge.agda",
    "DASHI/Physics/Closure/NSTriadKNCherevanCompanionScalingAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNCannoneTrilinearAntisymmetryAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3HermitianAlgebraProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNLerayAlgebraProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3HermitianNondegeneracy.agda",
    "DASHI/Physics/Closure/NSTriadKNVectorAdjointUniquenessProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNCheskidovEguchiCountingTransferAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNFirstAdjointShellConvolutionProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNKatoPonceFirstAdjointFallback.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3HermitianScalingLaws.agda",
    "DASHI/Physics/Closure/NSTriadKNOneLowShellExponentArchetypes.agda",
    "DASHI/Physics/Closure/NSTriadKNFiniteOverlapConstantProgram.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3HermitianAdditiveLaws.agda",
    "DASHI/Physics/Closure/NSTriadKNLeraySelfAdjointness.agda",
    "DASHI/Physics/Closure/NSTriadKNLiteralVectorAdjointPairingTheorems.agda",
    "DASHI/Physics/Closure/NSTriadKNOrderedEuclideanL2Carrier.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3EuclideanSelfPairing.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3TransverseDifference.agda",
    "DASHI/Physics/Closure/NSTriadKNRestrictedTransverseUniqueness.agda",
    "DASHI/Physics/Closure/NSTriadKNComplex3RestrictedUniquenessInputs.agda",
    "DASHI/Physics/Closure/NSTriadKNLerayContractionFromPythagoras.agda",
    "DASHI/Physics/Closure/NSTriadKNExactDyadicShellGeometry.agda",
    "DASHI/Physics/Closure/NSTriadKNSeparatedComponentLedger.agda",
    "DASHI/Physics/Closure/NSTriadKNSeparatedComponentEndpointProfiles.agda",
    "DASHI/Physics/Closure/NSTriadKNFiniteOverlapCanonicalConstants.agda",
    "DASHI/Physics/Closure/NSTriadKNHardDyadicShellOwner.agda",
    "DASHI/Physics/Closure/NSTriadKNFirstAdjointCutoffUniformAssembly.agda",
    "DASHI/Physics/Closure/NSTriadKNGrafakosOhDiagonalConvolutionAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNDAnconaCommutatorFallbackAudit.agda",
    "DASHI/Physics/Closure/NSTriadKNComponentAffineConstraintLedger.agda",
    "DASHI/Physics/Closure/NSTriadKNGrafakosTorresComponentAssembly.agda",
    "DASHI/Physics/Closure/NSTriadKNFinalCutoffUniformDualBoundAssembly.agda",
    "DASHI/Physics/Closure/NSTriadKNStage3OrderedL2AnalyticIntegration.agda",
    "DASHI/Physics/Closure/NSTriadKNQuarticLyapunovStage3OrderedL2Bridge.agda",
]

# The general DASHI balanced/unbalanced ternary and Base369 developments are
# intentionally untouched.  The Stage-3 status-only adapters introduced on
# this branch are preserved in history but are not part of this proof-critical
# checker or dependency path.

PROVENANCE_MARKERS = (
    "-- PROVENANCE",
    "-- Title:",
    "-- Venue/year:",
    "-- Relationship:",
)
DOI_MARKERS = ("-- DOI:", "-- Journal DOI:", "-- arXiv/DataCite DOI:")
FORBIDDEN = ("{!!}", "?}", "{-# TERMINATING #-}", "{-# NON_TERMINATING #-}")
POSTULATE = re.compile(r"(?m)^\s*postulate(?:\s|$)")


def run_verifier(root: Path, relative: str, label: str) -> str | None:
    verifier = root / relative
    if not verifier.is_file():
        return f"missing {label}"
    result = subprocess.run(
        [sys.executable, str(verifier)],
        cwd=root,
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode:
        return f"{label} failed: " + (result.stderr.strip() or result.stdout.strip())
    return None


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    failures: list[str] = []

    for relative in FILES:
        path = root / relative
        if not path.is_file():
            failures.append(f"missing: {relative}")
            continue
        text = path.read_text(encoding="utf-8")
        if POSTULATE.search(text):
            failures.append(f"{relative}: forbidden postulate declaration")
        for marker in FORBIDDEN:
            if marker in text:
                failures.append(f"{relative}: forbidden marker {marker!r}")
        for opening, closing in (("(", ")"), ("{", "}")):
            if text.count(opening) != text.count(closing):
                failures.append(f"{relative}: unbalanced {opening}{closing} delimiters")
        for marker in PROVENANCE_MARKERS:
            if marker not in text:
                failures.append(f"{relative}: missing provenance marker {marker!r}")
        if "-- Authors:" not in text and "-- Author:" not in text:
            failures.append(f"{relative}: missing provenance author")
        if not any(marker in text for marker in DOI_MARKERS):
            failures.append(f"{relative}: missing DOI status")

    verifiers = (
        ("scripts/ns_quartic_helicity_perturbed_counterexample.py", "global-helicity exact verifier"),
        ("scripts/ns_quartic_localized_helicity_reconnaissance.py", "localized-helicity verifier"),
        ("scripts/ns_quartic_localized_helicity_extended_family.py", "extended localized-helicity verifier"),
        ("scripts/ns_quartic_matrix_coherence_reconnaissance.py", "matrix-coherence verifier"),
        ("scripts/ns_quartic_direction_coherence_audit.py", "direction-coherence verifier"),
        ("scripts/ns_kiriukhin_weighted_schur_reconnaissance.py", "weighted-Schur verifier"),
        ("scripts/ns_grafakos_torres_exponent_reconnaissance.py", "Grafakos--Torres exponent verifier"),
        ("scripts/ns_kiriukhin_symmetric_companion_audit.py", "symmetric companion verifier"),
        ("scripts/ns_tao_frozen_leg_paraproduct_audit.py", "frozen-leg verifier"),
        ("scripts/ns_exact_transpose_high_high_audit.py", "transpose/high-high verifier"),
        ("scripts/ns_symmetrised_first_adjoint_audit.py", "symmetrised first-adjoint verifier"),
        ("scripts/ns_stage3_tail_threshold_affine_audit.py", "tail/threshold verifier"),
        ("scripts/ns_stage3_classical_antisymmetry_audit.py", "classical antisymmetry verifier"),
        ("scripts/ns_stage3_hermitian_convolution_audit.py", "Hermitian/convolution verifier"),
        ("scripts/ns_stage3_shell_certificate_audit.py", "shell-certificate verifier"),
        ("scripts/ns_stage3_vector_adjoint_pairing_audit.py", "vector-adjoint verifier"),
        ("scripts/ns_stage3_ordered_l2_shell_audit.py", "ordered-l2/hard-shell verifier"),
    )
    for relative, label in verifiers:
        failure = run_verifier(root, relative, label)
        if failure is not None:
            failures.append(failure)

    if failures:
        print("\n".join(failures))
        return 1
    print(
        f"checked {len(FILES)} proof-critical Agda files and {len(verifiers)} "
        "exact verifiers: no holes, postulates, termination escapes, missing "
        "provenance, or verifier failures"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
