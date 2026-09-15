#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Culture/MissingDeceasedTwentyScientistRound47ForeignSourceStrataExact.agda"

test -f "$owner"
grep -q 'ForeignSourceRole' "$owner"
grep -q 'chinaDomesticPrimaryLike' "$owner"
grep -q 'hongKongIndependentReporting' "$owner"
grep -q 'nonUSCrossNationalComparison' "$owner"
grep -q 'foreignReportingCannotPayH2' "$owner"
grep -q 'foreignReportingCannotPayH3' "$owner"
grep -q 'clusterNarrativeCannotOverrideObjectEvidence' "$owner"
grep -q 'round47H2PaidCount = 0' "$owner"
grep -q 'round47H3PaidCount = 0' "$owner"
