#!/usr/bin/env bash
set -euo pipefail

TARGET="DASHI/Culture/MissingDeceasedTwentyScientistRound40CohortFrontierRefreshExact.agda"
AGG="DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$TARGET"
grep -q "record CohortFrontierRefresh" "$TARGET"
grep -q "round40FrontierCount = 20" "$TARGET"
grep -q "round40H2PaidCount = 0" "$TARGET"
grep -q "round40H3PaidCount = 0" "$TARGET"
grep -q "chavezIdentityPaid = true" "$TARGET"
grep -q "leblancExactTeamSurfacePaid = true" "$TARGET"
grep -q "maiwaldExactProjectTeamPaid = true" "$TARGET"
grep -q "hicksExactCampaignTeamPaid = true" "$TARGET"
grep -q "nunoExactViriatoProjectPaid = true" "$TARGET"
grep -q "grillmairExactStreamProjectPaid = true" "$TARGET"
grep -q "fangExactPublicationTeamPaid = true" "$TARGET"
grep -q "zhangXiaoxinExactFengyunPaperPaid = true" "$TARGET"
grep -q "crossPersonH2RequiresRetainedPersonOnSameExactObject = true" "$TARGET"
grep -q "strongerSinglePersonObjectDoesNotPayH2 = true" "$TARGET"
grep -q "searchAttentionDoesNotUpgradeEvidence = true" "$TARGET"
grep -q "MissingDeceasedTwentyScientistRound40CohortFrontierRefreshExact" "$AGG"
