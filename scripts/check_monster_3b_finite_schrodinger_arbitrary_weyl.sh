#!/usr/bin/env bash
set -euo pipefail
ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Moonshine/Monster3BFiniteSchrodingerArbitraryWeylExact.agda"
[[ -f "$OWNER" ]] || { echo "missing owner: $OWNER" >&2; exit 1; }
required=(
  "translationByVectorComposition"
  "dotTranslateByVector"
  "dotTranslationCancellation"
  "arbitraryTranslation"
  "arbitraryModulation"
  "arbitraryTranslationComposition"
  "arbitraryModulationComposition"
  "arbitraryWeylRelation"
  "heisenbergActionFactorsThroughWeyl"
  "arbitraryWeylPaid"
  "fullHeisenbergActionLawPaid"
  "generatorWeylDoesNotCreateArbitraryWeyl"
  "A005052"
  "oeisHasWeylAuthority"
)
for needle in "${required[@]}"; do
  grep -Fq "$needle" "$OWNER" || { echo "missing arbitrary Weyl surface: $needle" >&2; exit 1; }
done
echo "monster 3B finite Schrodinger arbitrary Weyl check: ok"
