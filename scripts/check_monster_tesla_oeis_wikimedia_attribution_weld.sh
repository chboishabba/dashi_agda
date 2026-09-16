#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonsterTeslaOEISWikimediaAttributionWeldExact.agda"
PARENT="$ROOT/scripts/check_monster_3b_multiplicity_basis_linear_wrongtype.sh"

[[ -f "$OWNER" ]] || { echo "missing owner: $OWNER" >&2; exit 1; }
[[ -f "$PARENT" ]] || { echo "missing parent tranche: $PARENT" >&2; exit 1; }

required=(
  "AttributedSourceCore"
  "SnowballExternalIdentityAvailabilityExact"
  "WikipediaAllPairsPrunedMergeSnowballExact"
  "Q9036"
  "Q392440"
  "https://en.wikipedia.org/wiki/Nikola_Tesla"
  "Monstrous_moonshine&oldid=1355357732"
  "US382281A"
  "A007246"
  "A007244"
  "A007255"
  "tesla369QuotePrimarySourcePaid"
  "externalIdentityCreatesAuthority"
  "wikipediaNavigationCreatesTheoremAuthority"
  "teslaPatentCreatesMonsterTheorem"
  "oeisIdentifiersCreateLiteralAction"
  "record TypedAttributionEdge"
  "teslaPolyphaseEngineeringEdge"
  "moonshineOEISManifestationEdge"
  "replicabilityPowerFamilyEdge"
  "teslaRefinementNullModelEdge"
  "directTeslaToMonsterTheoremEdgePaid"
  "canonicalMonsterTeslaAttributionFrontier"
)

for needle in "${required[@]}"; do
  grep -Fq "$needle" "$OWNER" || { echo "missing Monster/Tesla attribution marker: $needle" >&2; exit 1; }
done

grep -Fq 'check_monster_tesla_oeis_wikimedia_attribution_weld.sh' "$PARENT" || {
  echo "parent Monster tranche does not chain Tesla/OEIS/Wikimedia attribution weld" >&2
  exit 1
}

echo "monster Tesla OEIS Wikimedia attribution weld check: ok"
