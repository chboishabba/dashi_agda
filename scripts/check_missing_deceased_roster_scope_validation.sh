#!/usr/bin/env bash
set -euo pipefail

grep -q 'data RosterScope' DASHI/Culture/MissingDeceasedRosterScopeReconciliationExact.agda
grep -q 'houseApril2026Core' DASHI/Culture/MissingDeceasedRosterScopeReconciliationExact.agda
grep -q 'expandedUAPNarrative' DASHI/Culture/MissingDeceasedRosterScopeReconciliationExact.agda
grep -q 'ningLiPredatesHouseSequenceStart' DASHI/Culture/MissingDeceasedRosterScopeReconciliationExact.agda
grep -q 'nickPopeDoesNotEnterScientificDenominator' DASHI/Culture/MissingDeceasedRosterScopeReconciliationExact.agda
grep -q 'scopeSpecificDenominatorRequired' DASHI/Culture/MissingDeceasedRosterScopeReconciliationExact.agda

grep -q 'MissingDeceasedRosterScopeReconciliationExact' DASHI/Culture/MissingDeceasedScientificWorkEverything.agda

echo 'missing/deceased roster scope static check: ok'
