#!/usr/bin/env bash
set -euo pipefail
ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonster3BOEISSameIntegerRoleCollisionExact.agda"
UNIFIED="$ROOT/DASHI/Wikimedia/IbrahimMonster3BOEIS369UnifiedCrossPollinationExact.agda"
[[ -f "$OWNER" ]] || { echo "missing owner: $OWNER" >&2; exit 1; }
[[ -f "$UNIFIED" ]] || { echo "missing unified owner: $UNIFIED" >&2; exit 1; }
required=(
  "record OEISRoleCoordinate"
  "A000244"
  "A005052"
  "A001379"
  "A014708"
  "A058678"
  "A199014"
  "A309510"
  "17496"
  "196883"
  "196884"
  "sameIntegerMonsterContextDoesNotIdentifyObject"
  "mcKayThompson42d17496DoesNotIdentifyRestriction17496"
  "oeisPaysNumericalCoordinateOnly"
  "sameIntegerCollisionCounterexamplePaid"
)
for needle in "${required[@]}"; do
  grep -Fq "$needle" "$OWNER" || { echo "missing OEIS same-integer collision marker: $needle" >&2; exit 1; }
done
grep -Fq "IbrahimMonster3BOEISSameIntegerRoleCollisionExact" "$UNIFIED" || {
  echo "unified OEIS owner does not import same-integer collision boundary" >&2; exit 1;
}
echo "monster 3B OEIS same-integer role collision check: ok"
