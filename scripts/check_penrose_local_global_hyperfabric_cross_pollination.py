#!/usr/bin/env python3
"""Focused static contract for Penrose local/global hyperfabric cross-pollination.

This checker requires a thin Interop bridge over already-owned Penrose,
LocalFibre, NDim/Pareto, and graph-colouring surfaces. It does not certify any
of those domain theorems, does not create source authority, and does not turn
proof-architecture correspondence into theorem/domain identity.
"""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Interop/PenroseLocalGlobalHyperfabricCrossPollinationExact.agda"
REGRESSION = ROOT / "DASHI/Interop/PenroseLocalGlobalHyperfabricCrossPollinationRegression.agda"


def require(path: Path, needles: list[str]) -> None:
    if not path.exists():
        raise SystemExit(f"missing required file: {path.relative_to(ROOT)}")
    text = path.read_text(encoding="utf-8")
    missing = [needle for needle in needles if needle not in text]
    if missing:
        raise SystemExit(f"{path.relative_to(ROOT)} missing required surfaces: {missing}")


require(OWNER, [
    "DASHI.Reasoning.LocalFibreHyperfabricExact",
    "DASHI.Core.NDimParetoHyperfabricExact",
    "DASHI.Combinatorics.GraphColouringRecolourPantsSnowballExact",
    "DASHI.Physics.Gravity.PenroseGlobalHorismosContradictionExact",
    "DASHI.Physics.Gravity.PenroseGlobalCausalityAuthorityExact",
    "LocalGlobalRole",
    "localWitness",
    "boundaryRestriction",
    "compatibilityCondition",
    "globalCompatibleObject",
    "projectionReduction",
    "globalObstruction",
    "reductioConclusion",
    "PenroseLocalGlobalAdapter",
    "canonicalPenroseLocalGlobalAdapter",
    "GraphColouringLocalGlobalAdapter",
    "canonicalGraphColouringLocalGlobalAdapter",
    "LocalFibreLocalGlobalAdapter",
    "canonicalLocalFibreLocalGlobalAdapter",
    "NDimProjectionAdapter",
    "canonicalNDimProjectionAdapter",
    "ConstructiveGluingObstructionDuality",
    "canonicalConstructiveGluingObstructionDuality",
    "localValidityDoesNotImplyGlobalValidity",
    "projectionValidityDoesNotImplySourceSufficiency",
    "boundedLocalCarrierDoesNotImplyGlobalCompactnessOrClosure",
    "sharedProofArchitectureDoesNotIdentifyDomainTheorems",
    "penroseProjectionIsNotParetoAxisProjection",
    "horismosIsNotHyperfabricGlobalSection",
    "graphSeamCompatibilityIsNotLorentzianCompatibility",
    "sameObjectReductioRequiresSameObjectIdentity",
    "crossPollinationAddsNoNewSourceAuthority",
    "crossPollinationIsRetrospectiveNotHistoricalInfluence",
    "CrossPollinationParentLineage",
    "snowballAcquisitionMayProceedOutOfDependencyOrder",
    "snowballPaymentMaySkipUnpaidParentDependency",
    "crossDomainAnalogyCreatesSourceAuthority",
    "DownstreamCrossPollinationCandidate",
    "rsaNDimCandidate",
    "flyMaleCNSCandidate",
    "navierStokesCandidate",
    "sensibLawCandidate",
    "downstreamCandidateMapIsImplementation",
])

require(REGRESSION, [
    "localValidityFirewallRegression",
    "projectionSufficiencyFirewallRegression",
    "boundedLocalCarrierFirewallRegression",
    "sharedArchitectureFirewallRegression",
    "penroseProjectionIdentityFirewallRegression",
    "horismosGlobalSectionIdentityFirewallRegression",
    "graphLorentzianCompatibilityFirewallRegression",
    "sameObjectIdentityRegression",
    "noNewSourceAuthorityRegression",
    "retrospectiveNotHistoricalRegression",
    "snowballPaymentCannotSkipParentRegression",
    "analogyDoesNotCreateAuthorityRegression",
    "downstreamCandidateMapIsNotImplementationRegression",
])

print("Penrose local/global hyperfabric cross-pollination static contract: OK")
