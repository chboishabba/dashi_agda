#!/usr/bin/env bash
set -euo pipefail

branch="${1:-agent/missing-deceased-round23-promotion-roadmap}"
repo="chboishabba/dashi_agda"
path="DASHI/Culture/MissingDeceasedTwentyScientistRound44OfficialInquiryCohortExact.agda"

if gh api "repos/$repo/contents/$path?ref=$branch" >/dev/null 2>&1; then
  echo "round44 production owner present"
  exit 0
else
  echo "round44 production owner missing"
  exit 1
fi
