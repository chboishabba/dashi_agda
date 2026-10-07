#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "$0")/.." && pwd)"
script="$repo_root/scripts/j369_field_transition_atlas.py"
test_script="$repo_root/scripts/test_j369_field_transition_atlas.py"
recognition_script="$repo_root/scripts/j369_kernel_field_recognition.py"
recognition_test="$repo_root/scripts/test_j369_kernel_field_recognition.py"
maxcut_receipt_script="$repo_root/scripts/j369_maxcut_runtime_receipt.py"
committed="$repo_root/scripts/data/outputs/j369_field_transition_atlas_20261007"
certificate="$repo_root/DASHI/Moonshine/Generated/OggSSPFiniteFieldBracketGenerated.agda"
maxcut_certificate="$repo_root/DASHI/Moonshine/Generated/OggSSPMaxCutRuntimeGenerated.agda"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
python3 "$test_script"
python3 "$recognition_test"
python3 "$script" --outdir "$tmp" >/dev/null
python3 "$recognition_script" --output "$tmp/kernelFieldRecognition.json"
python3 "$maxcut_receipt_script" --output "$tmp/OggSSPMaxCutRuntimeGenerated.agda"
for name in fieldBracketTable.csv fieldCandidates.csv atlasManifest.json kernelFieldRecognition.json; do
  diff -u "$committed/$name" "$tmp/$name"
done
diff -u "$certificate" "$tmp/OggSSPFiniteFieldBracketGenerated.agda"
diff -u "$maxcut_certificate" "$tmp/OggSSPMaxCutRuntimeGenerated.agda"
# Large CSV/SVG plots are regenerated on demand; unit tests assert they exist.
echo "j369 field/transition atlas: verified numeric atlas + structural max-cut certificates"
