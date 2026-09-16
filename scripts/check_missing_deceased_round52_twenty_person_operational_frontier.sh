#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Culture/MissingDeceasedTwentyScientistRound52TwentyPersonOperationalFrontierExact.agda"

[ -f "$OWNER" ]
grep -q "OperationalClass" "$OWNER"
grep -q "paidFact" "$OWNER"
grep -q "liveDisputedProposition" "$OWNER"
grep -q "promotionCriticalResidual" "$OWNER"
grep -q "TwentyPersonOperationalRow" "$OWNER"
grep -q "round52RetainedCount" "$OWNER"
grep -q "round52PaidFactCount" "$OWNER"
grep -q "round52PromotionCriticalCount" "$OWNER"
grep -q "allTwentyCarryVisibleResidual" "$OWNER"
grep -q "consumerProjectionCannotPromoteBaseClass" "$OWNER"
grep -q "round52H2PaidCount" "$OWNER"
grep -q "round52H3PaidCount" "$OWNER"
