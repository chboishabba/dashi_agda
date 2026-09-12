#!/usr/bin/env bash
set -euo pipefail

# Focused source-attribution/static contract. This is not Agda/kernel CI.

grep -q 'liTorrPRB1992APS' DASHI/Physics/ExoticGravity/LiTorrPRB1992AttributedSourceExact.agda
grep -q '10.1103/PhysRevB.46.5489' DASHI/Physics/ExoticGravity/LiTorrPRB1992AttributedSourceExact.agda
grep -q 'apsLandingPaysExactEquationLocator = false' DASHI/Physics/ExoticGravity/LiTorrPRB1992AttributedSourceExact.agda
grep -q 'apsTheoryPaysExperimentalAntigravity = false' DASHI/Physics/ExoticGravity/LiTorrPRB1992AttributedSourceExact.agda

grep -q 'attachedDiscoveryLinksA' DASHI/Culture/MissingDeceasedInvestigativeDiscoveryLinksAExact.agda
grep -q 'link.aps.org/doi/10.1103/PhysRevB.46.5489' DASHI/Culture/MissingDeceasedInvestigativeDiscoveryLinksAExact.agda
grep -q 'attachedDiscoveryLinksB' DASHI/Culture/MissingDeceasedInvestigativeDiscoveryLinksBExact.agda
grep -q 'attachedDiscoveryLinksC' DASHI/Culture/MissingDeceasedInvestigativeDiscoveryLinksCExact.agda
grep -q 'SP23012p.pdf' DASHI/Culture/MissingDeceasedInvestigativeDiscoveryLinksCExact.agda

grep -q 'investigativeSourceAtlas' DASHI/Culture/MissingDeceasedInvestigativeAttributedSourceAtlasExact.agda
grep -q 'newMexicoClusterIsSourceBacked = true' DASHI/Culture/MissingDeceasedSouthwestGeographyDiscriminatorExact.agda
grep -q 'whiteSandsEventAnchorIsUnpaid = true' DASHI/Culture/MissingDeceasedSouthwestGeographyDiscriminatorExact.agda
grep -q 'lanlKirtlandWhiteSandsTriangleIsPaid = false' DASHI/Culture/MissingDeceasedSouthwestGeographyDiscriminatorExact.agda
grep -q 'secondaryReportDoesNotBecomePrimaryEventFact = true' DASHI/Culture/MissingDeceasedReportedAnomalyAttributionLedgerExact.agda

grep -q 'surp2023Maiwald' DASHI/Culture/MaiwaldSURPActionSpectroscopyManifestationSuccessionExact.agda
grep -q 'surp2024Nemchick' DASHI/Culture/MaiwaldSURPActionSpectroscopyManifestationSuccessionExact.agda
grep -q 'surp2025Nemchick' DASHI/Culture/MaiwaldSURPActionSpectroscopyManifestationSuccessionExact.agda
grep -q 'projectContinuityPaysRawDataCustody = false' DASHI/Culture/MaiwaldSURPActionSpectroscopyManifestationSuccessionExact.agda

grep -q 'LiTorrPRB1992AttributedSourceExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda
grep -q 'MissingDeceasedInvestigativeDiscoveryLinksAExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda
grep -q 'MissingDeceasedInvestigativeDiscoveryLinksBExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda
grep -q 'MissingDeceasedInvestigativeDiscoveryLinksCExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda

echo 'missing/deceased attribution-link static check: ok'
