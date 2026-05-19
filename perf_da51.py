#!/usr/bin/env python3
"""Collect perf traces from Agda proofs, emit DA51 CBOR shards with fingerprints."""
import argparse
import glob
import hashlib
import json
import os
import subprocess

AGDA = "/nix/store/c4s2d92ggrrb4nh2myyzskh3snbvqnfb-agdaWithPackages-2.8.0/bin/agda"
COUNTERS = ["cycles", "instructions", "cache-misses", "branch-misses"]
DA51_TAG = 0xDA51  # 55889


def _load_template_fragments(template_dir):
    """Load file-name -> fractran payload map from existing shard files."""
    import cbor2

    # Temporary bridge for generator/schema mismatch:
    # shipped shards currently carry `fractran`, while legacy generation
    # in this script emits only counters. When template_dir is provided, we
    # copy that existing `fractran` payload by file name so downstream tooling
    # can regenerate without changing canonical shard semantics.
    template_payloads = {}
    if not template_dir:
        return template_payloads
    for cbor_path in sorted(glob.glob(os.path.join(template_dir, "*.cbor"))):
        try:
            with open(cbor_path, "rb") as fh:
                decoded = cbor2.loads(fh.read())
            payload = decoded.value if isinstance(decoded, cbor2.CBORTag) else decoded
            file_name = payload.get("file")
            if not file_name:
                file_name = os.path.basename(cbor_path).replace(".cbor", ".agda")
            if "fractran" in payload and file_name:
                template_payloads[str(file_name)] = payload["fractran"]
        except (FileNotFoundError, cbor2.CBORDecodeError, TypeError, AttributeError):
            # Ignore malformed/unreadable shards during template hydration so
            # bulk regeneration can continue in best-effort mode.
            continue
    return template_payloads


def perf_stat(agda_file):
    """Run perf stat -j on agda, return summed counters (atom+core)."""
    r = subprocess.run(
        ["perf", "stat", "-j", "-e", ",".join(COUNTERS), "--", AGDA, agda_file],
        capture_output=True, text=True, timeout=120
    )
    totals = {c: 0 for c in COUNTERS}
    for line in (r.stdout + r.stderr).splitlines():
        try:
            obj = json.loads(line)
            for c in COUNTERS:
                if c in obj.get("event", ""):
                    totals[c] += int(float(obj["counter-value"]))
        except (json.JSONDecodeError, KeyError, ValueError):
            pass
    return totals


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()


def da51_shard(agda_file, counters, src_hash, fractran=None):
    """Build a DA51 CBOR shard payload."""
    import cbor2

    # The shipped contract is larger than this emitter for now; `fractran`
    # is intentionally optional and opt-in via the compatibility flag.
    payload = {
        "file": os.path.basename(agda_file),
        "sha256": src_hash,
        "counters": counters,
        "trace_sha256": hashlib.sha256(json.dumps(counters, sort_keys=True).encode()).hexdigest(),
    }
    if fractran is not None:
        payload["fractran"] = fractran
    return cbor2.dumps(cbor2.CBORTag(DA51_TAG, payload))


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Emit DA51 shards in the checked-in format. By default this preserves\n"
            "the legacy shard schema (no fractran payload). Use --fractran-template\n"
            "to project full fractran payloads from an existing shard directory."
        )
    )
    parser.add_argument(
        "--fractran-template",
        default="",
        help=(
            "Directory containing existing DA51 .cbor shards with full fractran payloads.\n"
            "If provided, generated shards inherit the matching payload per file."
        ),
    )
    parser.add_argument(
        "--strict-template",
        action="store_true",
        help=(
            "Fail fast if a file does not have a matching fractran template entry.\n"
            "Only valid when --fractran-template is also provided."
        ),
    )
    return parser


def main():
    parser = build_parser()
    args = parser.parse_args()

    template_fragments = _load_template_fragments(args.fractran_template)
    agda_dir = os.path.dirname(os.path.abspath(__file__))
    out_dir = os.path.join(agda_dir, "da51_shards")
    os.makedirs(out_dir, exist_ok=True)

    files = sorted(glob.glob(os.path.join(agda_dir, "*.agda")))
    results = []
    for f in files:
        name = os.path.basename(f)
        print(f"  {name} ...", end=" ", flush=True)
        try:
            counters = perf_stat(f)
            src_hash = sha256_file(f)
            # Match by file name for deterministic payload overlay.
            fractran = template_fragments.get(name)
            if args.strict_template and args.fractran_template and fractran is None:
                raise RuntimeError(f"missing fractran template entry for {name}")
            shard = da51_shard(f, counters, src_hash, fractran)
            shard_path = os.path.join(out_dir, name.replace(".agda", ".cbor"))
            with open(shard_path, "wb") as out:
                out.write(shard)
            counters["file"] = name
            counters["src_sha256"] = src_hash
            results.append(counters)
            print(f"cycles={counters['cycles']:,} instr={counters['instructions']:,} "
                  f"cache={counters['cache-misses']:,} branch={counters['branch-misses']:,}")
        except Exception as e:
            print(f"FAIL: {e}")

    summary_path = os.path.join(out_dir, "summary.json")
    with open(summary_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\n{len(results)} shards → {out_dir}/")
    print(f"summary → {summary_path}")


if __name__ == "__main__":
    main()
