#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(CDPATH= cd -- "$script_dir/.." && pwd)"
log_dir="$repo_root/logs"
audit_script="$script_dir/audit_stale_consumer_flips.py"

python3 "$audit_script" --repo-root "$repo_root" --log-dir "$log_dir"
