#!/usr/bin/env bash
set -euo pipefail

# Materialize the PINNED original Kozyrev PR1404 referee and physical ledger
# from Git objects, not a scraped website, browser or invented duplicate.
# Does not change working tree, does not invoke nix, no network unless --fetch.
PR1404_HEAD=337aabb00ed54bc1a4c28ada48364cb4dc54d46e
OUT="${KOZYREV_PR1404_DIR:-/tmp/dashi-kozyrev-pr1404-337aabb}"
FETCH=0
while [[ "$#" -gt 0 ]]; do
  case "$1" in
    --fetch) FETCH=1; shift ;;
    --output-dir)
      [[ "$#" -gt 1 ]] || { echo "missing --output-dir argument" >&2; exit 2; }
      OUT="$2"; shift 2 ;;
    *) echo "Unknown argument: $1" >&2; exit 2 ;;
  esac
done

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if ! git cat-file -e "${PR1404_HEAD}^{commit}" 2>/dev/null; then
  if [[ "$FETCH" -ne 1 ]]; then
    echo "Original PR #1404 commit not locally available; rerun with --fetch" >&2
    exit 3
  fi
  git fetch --no-tags origin "refs/pull/1404/head"
fi

git cat-file -e "${PR1404_HEAD}^{commit}" || {
  echo "Refusing different Kozyrev source commit" >&2; exit 4;
}

mkdir -p "$OUT"
for name in kozyrev_first_forward_intersection_referee.py kozyrev_optical_event_ledger.py; do
  git show "${PR1404_HEAD}:scripts/${name}" > "${OUT}/${name}"
done

SOURCE_ROOT="$OUT" python - <<'PY'
import hashlib
import os
from pathlib import Path
p=Path(os.environ["SOURCE_ROOT"])
owners={
"kozyrev_first_forward_intersection_referee.py":"30c6f3021f32769d153aa9afb17cc6a38d55b90d",
"kozyrev_optical_event_ledger.py":"6f89d38c6509ccbc332d066829cbddf620844b64",
}
for name, expected in owners.items():
    value=(p/name).read_bytes()
    actual=hashlib.sha1(b"blob "+str(len(value)).encode()+b"\x00"+value).hexdigest()
    if actual!=expected:
        raise SystemExit(f"PR1404 canonical blob mismatch: {name}: {actual}")
print("PR1404 exact original source blobs verified")
PY

python scripts/gielis_kozyrev_pr1404_bridge.py --legacy-dir "$OUT" \
    --require-legacy --segments 384 --rays 48 --thickness 0
python scripts/gielis_kozyrev_pr1404_bridge.py --legacy-dir "$OUT" \
    --require-legacy --segments 384 --rays 48 --thickness 0.156

echo "PR1404 source-pinned normal-offset parity passed."
echo "Original HTML stroked-SDF collision and event replay remain separate G13c."
