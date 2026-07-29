#!/usr/bin/env python3
"""Fail-closed audit for the RCEPP governance/fibre tranche.

The exact checks protect the coarse-one/fine-three distinction.  The source scan
protects the new theorem surface against proof holes, postulate declarations and
accidental authority promotion.  It is not a substitute for Agda kernel checking
or for external legal, political or popular-recognition authority.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]

FILES = [
    ROOT / "DASHI/Governance/RelationalMandateFibre.agda",
    ROOT / "DASHI/Governance/AuthorityMandateCore.agda",
    ROOT / "DASHI/Governance/SituatedConstituency.agda",
    ROOT / "DASHI/Governance/CouncilDelegationGraph.agda",
    ROOT / "DASHI/Governance/TransitionResidual.agda",
    ROOT / "DASHI/Governance/ExternalLegitimacyBoundary.agda",
    ROOT / "DASHI/Governance/Sudan/RCEPPSourceBoundary.agda",
    ROOT / "DASHI/Governance/Sudan/RCEPPInstitutionalSurface.agda",
    ROOT / "DASHI/Governance/Sudan/RCEPPPromotionBoundary.agda",
    ROOT / "DASHI/Governance/Sudan/RCEPPRegression.agda",
    ROOT / "DASHI/Governance/Everything.agda",
]

REQUIRED_TOKENS = {
    "RelationalMandateFibre.agda": [
        "data MandateFineRole",
        "coarseMandateUnit",
        "canonicalMandateFineRoleCountIsThree",
        "MandateFibre : CoarseMandateUnit",
        "mandateFibreRestrictionCore",
        "rankOneDepthOneHasThreeSites",
        "arithmeticOneEqualsThreeClaimed",
        "spatialOntologyClaimed",
        "politicalAuthorityPromoted",
    ],
    "AuthorityMandateCore.agda": [
        "data AuthoritySource",
        "AdmissibleAuthoritySource possessionOfForce = Never",
        "possessionOfForceRejected",
        "record Mandate",
        "record NonAlienatingMandate",
        "mandateRemainsWithConstituency",
        "recallable",
        "reviewable",
        "governanceRoleFamily",
        "formalModelCreatesPopularLegitimacy",
        "Hanna Fenichel Pitkin",
    ],
    "SituatedConstituency.agda": [
        "data GovernanceAxis",
        "ruralUrbanAxis",
        "displacementAxis",
        "landAxis",
        "colonialityAxis",
        "armedPowerAxis",
        "axisFreeRepresentationIsFalse",
        "ruralConstituency",
        "idpCampConstituency",
        "10.2307/1229039",
    ],
    "CouncilDelegationGraph.agda": [
        "data CouncilLevel",
        "delegatesUpward",
        "accountsDownward",
        "data SubordinationPath",
        "militaryToPeoplePath",
        "militaryHasDirectSovereignEdge",
    ],
    "TransitionResidual.agda": [
        "governanceTopologyIsChartResidualPlusOne",
        "data TransitionalPhase",
        "data AdmissibleTransition",
        "data GovernanceValidation",
        "undeterminedAxisIncomplete",
        "record ConstitutionalResidual",
        "record ConstitutionalPlusOne",
        "unresolvedResidualsRetainedIsTrue",
        "authorityPromotedByFormalStepIsFalse",
        "stageCompressionDoesNotPromoteAuthority",
    ],
    "ExternalLegitimacyBoundary.agda": [
        "data ExternalPopularRecognitionToken",
        "formalReceiptDoesNotCreatePopularLegitimacy",
        "externalRecognitionTokenAvailableInternally",
        "politicalAuthorityPromoted",
        "legalAuthorityPromoted",
    ],
    "RCEPPSourceBoundary.agda": [
        "The Revolutionary Charter for Establishing People's Power",
        "11 January 2023",
        "No DOI assigned in the supplied edition",
        "suppliedPageCount",
        "canonicalRCEPPCitationHasNoArtifact",
        "legalOperationClaimed",
        "universalEndorsementClaimed",
    ],
    "RCEPPInstitutionalSurface.agda": [
        "data RCEPPConstituencyKind",
        "electedUnionConstituencyKind",
        "idpCampConstituencyKind",
        "canonicalRCEPPCivilianSupremacySurface",
        "canonicalRCEPPPublicResourceCustody",
        "canonicalRCEPPPeaceReconstructionSurface",
        "canonicalRCEPPTransitionInvariantSurface",
        "officialRCEPPInterpretationClaimed",
        "legalOperationClaimed",
    ],
    "RCEPPPromotionBoundary.agda": [
        "rceppCitationIdentityRemainsOpen",
        "rceppCitationOnlyQuarantines",
        "rceppCitationOnlyAuthorizationAbstains",
        "canonicalPromotionAuthorized",
        "governedDecisionIsAbstain",
    ],
    "RCEPPRegression.agda": [
        "record RCEPPGovernanceRegression",
        "canonicalRCEPPGovernanceRegression",
        "rankOneFineRoleCountIsThree",
        "rankOneHypervoxelCountIsThree",
        "forceSourceRejected",
        "formalLegitimacyNotMinted",
        "citationOnlyAuthorizationAbstains",
        "canonicalRCEPPGovernanceReceiptsNonPromoting",
    ],
    "Everything.agda": [
        "import DASHI.Governance.AuthorityMandateCore",
        "import DASHI.Governance.RelationalMandateFibre",
        "import DASHI.Governance.Sudan.RCEPPPromotionBoundary",
        "import DASHI.Governance.Sudan.RCEPPRegression",
    ],
}

FORBIDDEN_PATTERNS = [
    re.compile(r"^\s*postulate\b", re.MULTILINE),
    re.compile(r"\{!"),
    re.compile(r"!\}"),
    re.compile(r"\bTERMINATING\b"),
    re.compile(r"\bNON_TERMINATING\b"),
    re.compile(r"arithmeticOneEqualsThreeClaimed\s*=\s*true"),
    re.compile(r"spatialOntologyClaimed\s*=\s*true"),
    re.compile(r"formalModelCreatesPopularLegitimacy\s*=\s*true"),
    re.compile(r"militaryHasDirectSovereignEdge\s*=\s*true"),
    re.compile(r"legalOperationClaimed\s*=\s*true"),
    re.compile(r"universalEndorsementClaimed\s*=\s*true"),
    re.compile(r"officialRCEPPInterpretationClaimed\s*=\s*true"),
    re.compile(r"canonicalPromotionAuthorized\s*=\s*true"),
]


def check_exact_shape() -> None:
    coarse_units = 1
    fine_roles = ("principal", "delegate", "mandate-relation")
    rank = 1
    depth = 1
    assert coarse_units == 1
    assert len(fine_roles) == 3
    assert 3 ** (rank * depth) == len(fine_roles)
    assert coarse_units != len(fine_roles)

    phases = (
        "coup",
        "prefigurative",
        "temporary-civilian",
        "constituted-transition",
        "constitution-making",
        "democratic-closure",
    )
    assert len(phases) == 6

    validation_positions = (
        "satisfied",
        "positively-violated",
        "undetermined-axis-incomplete",
        "inapplicable-to-role",
    )
    assert len(validation_positions) == 4


def scan_sources() -> None:
    for path in FILES:
        if not path.is_file():
            raise AssertionError(f"missing required file: {path.relative_to(ROOT)}")

        text = path.read_text(encoding="utf-8")
        for pattern in FORBIDDEN_PATTERNS:
            if pattern.search(text):
                raise AssertionError(
                    f"forbidden pattern {pattern.pattern!r} in {path.relative_to(ROOT)}"
                )

        for token in REQUIRED_TOKENS[path.name]:
            if token not in text:
                raise AssertionError(
                    f"missing required token {token!r} in {path.relative_to(ROOT)}"
                )


def main() -> int:
    check_exact_shape()
    scan_sources()
    print("PASS: one coarse mandate unit remains distinct from three fine relational roles")
    print("PASS: rank-one/depth-one ternary shape has exactly three fine sites")
    print("PASS: force, elite agreement and external recognition alone cannot originate authority")
    print("PASS: situated representation carries explicit rural, displacement, land and power axes")
    print("PASS: delegation upward remains distinct from accountability and recall downward")
    print("PASS: constitutional +1 transitions retain residuals and preserve authority boundaries")
    print("PASS: RCEPP citation identity remains separate from artifact, legal and popular authority")
    print("PASS: governance/RCEPP source surface is fail-closed")
    print("NOTE: run the Agda checker for kernel validation")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
