#!/usr/bin/env bash
# Run from an isolated #1495 worktree in the Nix-resolved Lean 4.28 shell.
# Requires Nix-provided Rust/Cargo. No .NET, CI, Docker or permanent tool checkout.
set -euo pipefail
out="${1:-/tmp/dashi-lean-semantic-original}"
python3 -m unittest discover -s tests -p 'test_lean_world_native_v3_projection.py' -v
python3 -m unittest discover -s tests -p 'test_lean_world_native_v3_projection_observation.py' -v
python3 -m unittest discover -s tests -p 'test_lean_world_external_checker.py' -v
python3 -m unittest discover -s tests -p 'test_lean_world_rust_nanoda.py' -v
python3 -m unittest discover -s tests -p 'test_lean_world_native_check_observation.py' -v
python3 -m unittest discover -s tests -p 'test_lean_world_builder_contract.py' -v
python3 -m unittest discover -s tests -p 'test_lean_world_handoff_integration.py' -v
python3 scripts/run_lean_world_real_semantic_acceptance.py --output-dir "$out"
echo "Semantic source/checker gate finished; use printed receipt path for #1484 isolated PG/retrieval gate."
