#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "$0")/.." && pwd)"
script="$repo_root/scripts/j369_field_transition_atlas.py"
test_script="$repo_root/scripts/test_j369_field_transition_atlas.py"
committed="$repo_root/scripts/data/outputs/j369_field_transition_atlas_20261007"
certificate="$repo_root/DASHI/Moonshine/Generated/OggSSPFiniteFieldBracketGenerated.agda"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
python3 "$test_script"
python3 "$script" --outdir "$tmp" >/dev/null
for name in fieldBracketTable.csv fieldCandidates.csv atlasManifest.json; do
  diff -u "$committed/$name" "$tmp/$name"
done
diff -u "$certificate" "$tmp/OggSSPFiniteFieldBracketGenerated.agda"
# Large CSV/SVG plots are regenerated on demand; unit tests assert they exist.
echo "j369 field/transition atlas: verified generated certificates and plot generation"
