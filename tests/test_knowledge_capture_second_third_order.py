#!/usr/bin/env python3
"""Independent finite-regression witness for the governance cut model.

This is a lightweight Python mirror of *named finite instances* in Agda,
NOT an Agda kernel certificate or proof of a real deployed federation.
Run: python -m unittest tests/test_knowledge_capture_second_third_order.py
Source originality: DASHI repo extension. Stafford Beer and Stigler are
conceptual precedents, not authors of this executable implementation.
"""
from __future__ import annotations

import itertools
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[1]
SOURCE = ROOT / "DASHI/Governance/KnowledgeCaptureSecondThirdOrder20261101Exact.agda"
BASE = ROOT / "DASHI/Governance/KnowledgeProcessingSovereignCaptureExact.agda"
SELECTION = ROOT / "DASHI/Governance/KnowledgeCaptureSelectionFeedback20261101Exact.agda"
ATLAS = ROOT / "DASHI/Governance/KnowledgeProcessingCaptureSourceAtlas20261101Exact.agda"
ROLLUP = ROOT / "DASHI/Governance/Everything.agda"

ROUTES = ("cloudOne", "cloudTwo", "privateLocal", "federatedPeer")
CONTROLS = {
    "sharedPlatform": frozenset(("cloudOne", "cloudTwo")),
    "localOperator": frozenset(("privateLocal",)),
    "peerOperator": frozenset(("federatedPeer",)),
}
SAFETY_DECLARATION = {
    "proportionalAndPlural": "declaredProtectiveSafety",
    "fixedGateAndCaptive": "declaredProtectiveSafety",
}
SECOND_ORDER_ACCESS = {
    "proportionalAndPlural": "independentVerificationSurvives",
    "fixedGateAndCaptive": "openWeightExitContracts",
}
THIRD_ORDER_POWER = {
    "proportionalAndPlural": "contestableStandards",
    "fixedGateAndCaptive": "closedStandardsFeedback",
}
PATHS = {
    "plural": (
        "protectivePolicyIntervention",
        "nondiscriminatoryIndependentReview",
        "pluralKnowledgeInfrastructure",
        "contestablePublicOversight",
    ),
    "concentrated": (
        "protectivePolicyIntervention",
        "restrictiveCommonCertification",
        "lossOfIndependentKnowledgeExit",
        "entrenchedPrivateStandardsPower",
    ),
}
FINANCE = (
    "lenderStress",
    "correlatedSupplierExposure",
    "interventionPoliticalIncentive",
)


def blocked_by(coalition: frozenset[str]) -> frozenset[str]:
    blocked: set[str] = set()
    for actor in coalition:
        blocked.update(CONTROLS[actor])
    return frozenset(blocked)


def blockers() -> tuple[frozenset[str], ...]:
    keys = tuple(CONTROLS)
    candidates = [
        frozenset(group)
        for size in range(1, len(keys) + 1)
        for group in itertools.combinations(keys, size)
        if blocked_by(frozenset(group)) == frozenset(ROUTES)
    ]
    return tuple(
        group
        for group in candidates
        if not any(other < group for other in candidates)
    )


class KnowledgeCaptureSecondThirdOrderTests(unittest.TestCase):
    def test_all_single_actors_have_a_feasible_escape(self):
        for actor in CONTROLS:
            with self.subTest(actor=actor):
                self.assertTrue(set(ROUTES) - set(blocked_by(frozenset((actor,)))))

    def test_every_two_actor_coalition_preserves_a_route(self):
        for actors in itertools.combinations(CONTROLS, 2):
            with self.subTest(actors=actors):
                self.assertTrue(set(ROUTES) - set(blocked_by(frozenset(actors))))

    def test_unique_minimal_blocking_coalition_has_three_actors(self):
        self.assertEqual(blockers(), (frozenset(CONTROLS),))
        self.assertEqual(blocked_by(frozenset(CONTROLS)), frozenset(ROUTES))

    def test_same_public_safety_purpose_does_not_fix_indirect_outcome(self):
        plural, captive = SAFETY_DECLARATION
        self.assertEqual(SAFETY_DECLARATION[plural], SAFETY_DECLARATION[captive])
        self.assertNotEqual(SECOND_ORDER_ACCESS[plural], SECOND_ORDER_ACCESS[captive])
        self.assertNotEqual(THIRD_ORDER_POWER[plural], THIRD_ORDER_POWER[captive])

    def test_third_order_path_is_conditional_and_has_three_edges(self):
        for label, path in PATHS.items():
            with self.subTest(label=label):
                self.assertEqual(len(path) - 1, 3)
                self.assertEqual(path[0], "protectivePolicyIntervention")
        self.assertNotEqual(PATHS["plural"][-1], PATHS["concentrated"][-1])

    def test_financial_stress_path_stops_before_public_rescue(self):
        self.assertEqual(len(FINANCE) - 1, 2)
        self.assertEqual(FINANCE[-1], "interventionPoliticalIncentive")
        self.assertNotIn("actualGovernmentStepIn", FINANCE)
        self.assertNotIn("actualExclusiveKnowledgeAuthority", FINANCE)

    def test_agda_source_has_reused_owners_and_exact_witnesses(self):
        contents = SOURCE.read_text()
        for token in (
            "import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID",
            "import DASHI.Philosophy.PowerAndGrammar as Power",
            "import DASHI.Core.IntersectionalNonFactorability as INF",
            "import DASHI.Economics.AIFinancingReflexivityExact as Finance",
            "declarationCannotDetermineSecondOrderAccess",
            "declarationCannotDetermineThirdOrderPower",
            "stressCanReachInterventionIncentive",
            "allThreeCoalitionCanBlockEveryOption",
            "noHypotheticalPerformedStepIn",
            "noHypotheticalExclusiveAuthority",
        ):
            with self.subTest(token=token):
                self.assertIn(token, contents)
        self.assertNotIn("postulate ", contents)
        self.assertIn("canonicalNoSingleActorCut", BASE.read_text())
        self.assertIn("conditionalFeedback", SELECTION.read_text())

    def test_primary_receipts_and_aggregate_import(self):
        atlas = ATLAS.read_text()
        for token in (
            "rbaOct2026FinancialStability",
            "rbaOct2026FinancialAssessment",
            "anthropicCurrentPublicS1",
            "0001628280-26-067168",
            "thielOriginal2009",
            "heritagePolicy2025Defense",
            "humanityPlusBlackDraft",
        ):
            self.assertIn(token, atlas)
        self.assertIn(
            "import DASHI.Governance.KnowledgeCaptureSecondThirdOrder20261101Exact",
            ROLLUP.read_text(),
        )


if __name__ == "__main__":
    unittest.main()
