#!/usr/bin/env bash
# Pin worker to DASHI's existing flake.lock; never execute Arch's system Lean.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if ! command -v nix >/dev/null 2>&1; then
  echo "nix is required for the Lean world worker" >&2
  exit 127
fi
LEAN_STORE="$(nix build --no-link --print-out-paths "${ROOT}#lean-world-bin" --no-update-lock-file)"
if [[ "$LEAN_STORE" != /nix/store/* || ! -x "$LEAN_STORE/bin/lean" ]]; then
  echo "failed to resolve a Nix-store Lean binary" >&2
  exit 126
fi
# Force the exact resolved binary even if PATH also contains a system lean.
# Python is supplied from the same DASHI Nix environment.
exec nix develop "${ROOT}#lean-world" --no-update-lock-file --command \
  python3 "${ROOT}/scripts/lean_ephemeral_nix_worker.py" \
  --lean "$LEAN_STORE/bin/lean" "$@"
