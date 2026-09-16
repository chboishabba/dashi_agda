#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound69HCBNamedManagementSurfaceExact.agda"

[ -f "$OWNER" ]
grep -q "afrlNamedHCBProgramManager" "$OWNER"
grep -q "aerojetNamedHBTDProgramManager" "$OWNER"
grep -q "bernsteinNamedManagerPaid" "$OWNER"
grep -q "burnettNamedManagerPaid" "$OWNER"
grep -q "mccaslandNamedHCBProgramManagerPaid" "$OWNER"
grep -q "commanderDoesNotEqualNamedProgrammeManager" "$OWNER"
grep -q "namedManagerSurfaceDoesNotProveExclusiveManagement" "$OWNER"
grep -q "round69H2PaidCount" "$OWNER"
grep -q "round69H3PaidCount" "$OWNER"
