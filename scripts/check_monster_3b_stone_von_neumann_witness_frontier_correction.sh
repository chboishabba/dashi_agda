#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Moonshine/Monster3BFiniteStoneVonNeumannWitnessFrontierCorrectionExact.agda"

required=(
  "module DASHI.Moonshine.Monster3BFiniteStoneVonNeumannWitnessFrontierCorrectionExact"
  "correctedLeafState"
  "extractNonzeroCoordinateFromNonzeroVector = Frontier.closed"
  "proveSchrodingerIrreducible = Frontier.closed"
  "proveFixedCentralCharacterUniqueness = Frontier.open"
  "identifyCertifiedMonster729Constituent = Frontier.blocked"
  "import DASHI.Wikimedia.IbrahimMonster3BMathlibCharacterDeterminationInteropExact as CharacterInterop"
  "standardCharacterDeterminationTheoremPaid"
  "chosenCharacterRouteAvoidsAlgebraicClosure"
  "leanEqualCharacterSimpleIsoReceiptPaid"
  "dashiCharacterDeterminationTransportPaid"
  "CharacterInterop.currentMathlibCharacterDeterminationInteropFrontier"
  "highestImpactStructuralLeafAfterWitness"
  "A005052"
  "oeisHasFrontierAuthority"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing Stone-von Neumann witness-frontier correction surface: $needle" >&2
    exit 1
  fi
done

if grep -Fq "over an algebraically closed characteristic-zero field" "$OWNER"; then
  echo "superseded algebraically-closed-field prerequisite remains in Stone-von Neumann frontier" >&2
  exit 1
fi

echo "monster 3B Stone-von Neumann witness-frontier correction check: ok"
