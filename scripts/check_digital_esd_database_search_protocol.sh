#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OWNER=DASHI/Education/DigitalESDDatabaseSearchProtocolExact.agda
REGRESSION=DASHI/Education/DigitalESDDatabaseSearchProtocolRegression.agda
APPENDIX=docs/digital-esd-search-protocol-v1.md

for file in "$OWNER" "$REGRESSION" "$APPENDIX"; do
  [[ -f "$file" ]] || { echo "required database-search protocol source is missing: $file" >&2; exit 1; }
done

for file in "$OWNER" "$REGRESSION"; do
  if grep -nE '\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '^protocolVersion : String' "$OWNER"
grep -q 'digital-esd-search-v1-2026-09-16' "$OWNER"
grep -q '^digitalEducationBlock :' "$OWNER"
grep -q '^esdBlock :' "$OWNER"
grep -q '^transformationBlock :' "$OWNER"
grep -q '^reflexiveSustainabilityBlock :' "$OWNER"
grep -q '^participantGovernanceBlock :' "$OWNER"
grep -q '^longitudinalDurabilityBlock :' "$OWNER"
grep -q '^openInfrastructureBlock :' "$OWNER"
grep -q '^canonicalPlannedQueries :' "$OWNER"
grep -q '^plannedQueryCount : Nat' "$OWNER"
grep -q '^canonicalDatabaseTranslationPlans :' "$OWNER"
grep -q '^plannedQueryDoesNotCreateExecutionReceipt :' "$OWNER"
grep -q '^platformNeutralQueryDoesNotEqualDatabaseSpecificSyntax :' "$OWNER"
grep -q '^canonicalSearchProtocolBoundary :' "$OWNER"

grep -q '^queryCountRegression :' "$REGRESSION"
grep -q '^protocolVersionRegression :' "$REGRESSION"
grep -q '^translationsRemainUnexecutedRegression :' "$REGRESSION"
grep -q '^plannedQueryDoesNotCreateExecutionReceiptRegression :' "$REGRESSION"
grep -q '^platformNeutralDoesNotEqualDatabaseSyntaxRegression :' "$REGRESSION"

grep -q 'Protocol version.*digital-esd-search-v1-2026-09-16' "$APPENDIX"
grep -q '^## Concept blocks$' "$APPENDIX"
grep -q '^## Planned query families$' "$APPENDIX"
grep -q '^## Translation and execution rule$' "$APPENDIX"
grep -q 'A planned query is not an execution receipt' "$APPENDIX"

if command -v nix >/dev/null 2>&1 && [[ -x scripts/run_agda29_parallel_check.sh ]]; then
  scripts/run_agda29_parallel_check.sh "$REGRESSION"
elif command -v agda >/dev/null 2>&1; then
  agda -i . "$REGRESSION"
elif [[ "${1:-}" == "--source-only" ]]; then
  echo "digital ESD database-search protocol source audit passed; Agda kernel receipt unobserved (--source-only explicitly selected)"
else
  echo "Agda kernel check unavailable: agda executable not found" >&2
  exit 2
fi
