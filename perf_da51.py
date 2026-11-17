#!/usr/bin/env python3
"""Collect perf traces from Agda proofs, emit DA51 CBOR shards with fingerprints."""
import subprocess, json, hashlib, struct, sys, os, glob

AGDA = "/nix/store/c4s2d92ggrrb4nh2myyzskh3snbvqnfb-agdaWithPackages-2.8.0/bin/agda"
COUNTERS = ["cycles", "instructions", "cache-misses", "branch-misses"]
DA51_TAG = 0xDA51  # 55889

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

def da51_shard(agda_file, counters, src_hash):
    """Build DA51 CBOR shard: {tag: 0xDA51, file, sha256, counters}."""
    import cbor2
    payload = {
        "file": os.path.basename(agda_file),
        "sha256": src_hash,
        "counters": counters,
        "trace_sha256": hashlib.sha256(json.dumps(counters, sort_keys=True).encode()).hexdigest(),
    }
    return cbor2.dumps(cbor2.CBORTag(DA51_TAG, payload))

def main():
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
            shard = da51_shard(f, counters, src_hash)
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

    # Summary JSON
    summary_path = os.path.join(out_dir, "summary.json")
    with open(summary_path, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\n{len(results)} shards → {out_dir}/")
    print(f"summary → {summary_path}")

if __name__ == "__main__":
    main()
