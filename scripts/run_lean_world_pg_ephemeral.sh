#!/usr/bin/env bash
# Explicit no-CI/no-Docker PostgreSQL 15+ migration gate using pinned Nix shell.
# Invoke: nix develop .#lean-world --command bash scripts/run_lean_world_pg_ephemeral.sh
set -euo pipefail

for command_name in initdb pg_ctl createdb psql python3; do
  command -v "$command_name" >/dev/null || {
    echo "POSTGRES_MIGRATION_NOT_VALIDATED: missing $command_name" >&2
    exit 2
  }
done

tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/dashi-lean-pg.XXXXXX")"
pg_dir="$tmp_root/cluster"
log="$tmp_root/postgres.log"
started=0
cleanup() {
  rc=$?
  if [ "$started" -eq 1 ]; then
    pg_ctl -D "$pg_dir" -m immediate stop >/dev/null 2>&1 || true
  fi
  if [ "$rc" -ne 0 ]; then
    echo "POSTGRES_MIGRATION_INCOMPLETE: postgres last diagnostics:" >&2
    if [ -f "$log" ]; then tail -n 60 "$log" >&2; fi
  fi
  rm -rf "$tmp_root"
  exit "$rc"
}
trap cleanup EXIT

# local-only trust authentication is restricted to this randomly named socket
# directory (mode 0700), not a network interface.
chmod 700 "$tmp_root"
initdb -D "$pg_dir" --auth-local=trust --auth-host=reject   --no-instructions >/dev/null
port="$(python3 - <<'PY'
import socket
with socket.socket() as s:
    s.bind(('127.0.0.1', 0))
    print(s.getsockname()[1])
PY
)"
pg_ctl -D "$pg_dir" -l "$log" \
  -o "-c listen_addresses='' -k $tmp_root -p $port" start >/dev/null
started=1

export PGHOST="$tmp_root"
export PGPORT="$port"
export PGDATABASE="lean_world_migration_test"
export PGUSER="$(id -un)"
createdb "$PGDATABASE"
python3 -m unittest discover -s tests \
  -p 'test_lean_world_postgres_migration.py' -v
python3 -m unittest discover -s tests \
  -p 'test_lean_world_postgres_candidate.py' -v
python3 -m unittest discover -s tests \
  -p 'test_lean_world_source_stream_pg.py' -v
python3 -m unittest discover -s tests \
  -p 'test_lean_world_cross_repo_joins.py' -v
python3 -m unittest discover -s tests \
  -p 'test_lean_world_compiled_join_store_pg.py' -v
echo "POSTGRES_MIGRATION_VALIDATED: actual isolated PostgreSQL server, real SQL and data-integrity tests"
