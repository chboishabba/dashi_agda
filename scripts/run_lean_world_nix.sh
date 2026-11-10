#!/usr/bin/env bash
# Reuse DASHI's existing Nix flake and lock, without changing Agda's pin.
# Lean version is checked against the source repository's lean-toolchain.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if ! command -v nix >/dev/null 2>&1; then
  echo "nix is required for the Lean world worker" >&2
  exit 127
fi
# Keep invocation under the existing locked flake. Unlike the Agda wrapper,
# do not synchronize complete repository source trees or modify its caches.
exec nix develop "${ROOT}#lean-world" --no-update-lock-file --command \
  python3 "${ROOT}/scripts/lean_ephemeral_nix_worker.py" "$@"
