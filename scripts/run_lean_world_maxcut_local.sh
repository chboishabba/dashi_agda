#!/usr/bin/env bash
# No CI / no Docker. Run locally under the existing pinned DASHI flake:
#   nix develop .#lean-world --command bash scripts/run_lean_world_maxcut_local.sh all
#   nix develop .#lean-world --command bash scripts/run_lean_world_maxcut_local.sh offline
#   ... postgres | lean | corpus pinned_manifest.json
set -euo pipefail
phase="${1:-all}"

run_offline() {
  python3 -m unittest discover -s tests -p 'test_lean_remote_*.py' -v
  python3 -m unittest discover -s tests -p 'test_lean_world_source_world.py' -v
  python3 -m unittest discover -s tests -p 'test_lean_ephemeral_elaboration.py' -v
  python3 -m unittest discover -s tests -p 'test_lean_world_canonical_dag.py' -v
  python3 -m unittest discover -s tests -p 'test_lean_world_semantic_candidate_pg.py' -v
  python3 scripts/bench_lean_world_acquisition.py --mode offline --files 100 1000
}
run_postgres() {
  bash scripts/run_lean_world_pg_ephemeral.sh
}
run_lean() {
  python3 tests/smoke_lean_ephemeral_real.py
}
run_corpus() {
  manifest="${2:?usage: $0 corpus path/to/pinned_manifest.json}"
  python3 scripts/bench_lean_world_corpus.py --manifest "$manifest"
}
case "$phase" in
  offline) run_offline ;;
  postgres) run_postgres ;;
  lean) run_lean ;;
  corpus) run_corpus "$@" ;;
  all) run_offline; run_postgres; run_lean ;;
  *) echo "unknown phase: $phase" >&2; exit 2 ;;
esac
