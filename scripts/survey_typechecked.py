#!/usr/bin/env python3
"""Survey which Agda modules have been typechecked (have .agdai interfaces) and which have not.

Evidence sources:
  - Track A legacy: _build/2.6.4.3/agda/<path>.agdai  (Agda 2.6.4.3 interfaces)
  - Track B:        ~/.cache/dashi-agda29/dashi-shadow/<path>.agdai  (Agda 2.9 interfaces)

An .agdai file exists only after Agda successfully typechecks a module, so its
presence is the repo's own record of "typechecked at some point". Staleness is
flagged when the source file is newer than the newest interface file.
"""

from __future__ import annotations

import argparse
import os
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BUILD_AGDAI = ROOT / "_build" / "2.6.4.3" / "agda"
HOME_DIR = Path(os.environ.get("HOME", "/home/c"))
SHADOWS = sorted(
    p
    for p in HOME_DIR.glob(".cache/dashi-*/dashi-shadow")
    if p.is_dir()
)
SHADOW = SHADOWS[0] if SHADOWS else HOME_DIR / ".cache" / "dashi-agda29" / "dashi-shadow"

SKIP_DIRS = {
    "_build",
    "build",
    ".git",
    ".cache",
    "agda-toolchain",
    "cubical",
    "vendor",
    "monster",
    "MAlonzo",
    "__pycache__",
    "node_modules",
    "outputs",
    "result",
    "tmp",
    "temp-DOWNLOADED",
}


def source_files(root: Path) -> list[Path]:
    out = []
    for dirpath, dirnames, filenames in os.walk(root):
        rel = Path(dirpath).relative_to(root)
        if any(part in SKIP_DIRS for part in rel.parts):
            dirnames[:] = []
            continue
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
        for fn in filenames:
            if fn.endswith(".agda") and not fn.startswith("."):
                out.append(Path(dirpath) / fn)
    return out


def rel_to_interface(src: Path) -> Path:
    return Path(str(src)[:-5] + ".agdai")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--limit", type=int, default=0, help="cap on rows printed per dir")
    ap.add_argument("--only-unchecked", action="store_true", help="list unchecked modules only")
    ap.add_argument("--json", action="store_true", help="emit machine-readable summary")
    args = ap.parse_args()

    srcs = source_files(ROOT)
    build_ok = BUILD_AGDAI.is_dir()
    shadow_ok = SHADOW.is_dir()

    def has_build(rel: str) -> bool:
        if not build_ok:
            return False
        return (BUILD_AGDAI / rel[:-5]).with_suffix(".agdai").is_file()

    def has_shadow(rel: str) -> bool:
        return any((s / rel).with_suffix(".agdai").is_file() for s in SHADOWS)

    rows = []
    for src in srcs:
        rel = src.relative_to(ROOT).as_posix()
        b = has_build(rel)
        s = has_shadow(rel)
        src_mtime = src.stat().st_mtime
        mtimes: list[float] = []
        if s:
            for shadow in SHADOWS:
                p = (shadow / rel).with_suffix(".agdai")
                if p.is_file():
                    mtimes.append(p.stat().st_mtime)
        if b:
            mtimes.append((BUILD_AGDAI / rel).with_suffix(".agdai").stat().st_mtime)
        iface_mtime = max(mtimes) if mtimes else 0.0
        stale = (b or s) and src_mtime > iface_mtime
        rows.append((rel, b, s, stale))

    total = len(rows)
    ever = sum(1 for _, b, s, _ in rows if b or s)
    checked_build = sum(1 for _, b, _, _ in rows if b)
    checked_shadow = sum(1 for _, _, s, _ in rows if s)
    stale_count = sum(1 for _, _, _, st in rows if st)

    by_dir: dict[str, list] = defaultdict(list)
    for row in rows:
        top = row[0].split("/", 1)[0]
        by_dir[top].append(row)

    if args.json:
        import json
        dirs = []
        for top in sorted(by_dir):
            r = by_dir[top]
            dirs.append({
                "dir": top,
                "total": len(r),
                "checked_build": sum(1 for _, b, _, _ in r if b),
                "checked_shadow": sum(1 for _, _, s, _ in r if s),
                "ever": sum(1 for _, b, s, _ in r if b or s),
                "stale": sum(1 for _, _, _, st in r if st),
                "unchecked": sum(1 for _, b, s, _ in r if not (b or s)),
            })
        print(json.dumps({
            "root": str(ROOT),
            "build_iface_dir": str(BUILD_AGDAI) if build_ok else "missing",
            "shadow_iface_dir": str(SHADOW) if shadow_ok else "missing",
            "total": total,
            "ever_typechecked": ever,
            "checked_build_2643": checked_build,
            "checked_shadow_29": checked_shadow,
            "stale": stale_count,
            "unchecked": total - ever,
            "dirs": dirs,
        }, indent=2, sort_keys=True))
        return 0

    print(f"root             : {ROOT}")
    print(f"Agda 2.6.4.3 iface: {BUILD_AGDAI}  ({'present' if build_ok else 'MISSING'})")
    print(f"Agda 2.9 iface    : {SHADOW}  ({'present' if shadow_ok else 'MISSING'})")
    print()
    print(f"total source modules     : {total}")
    print(f"ever typechecked (either) : {ever}  ({100.0 * ever / total:.1f}%)")
    print(f"  Agda 2.6.4.3 interface  : {checked_build}")
    print(f"  Agda 2.9 interface      : {checked_shadow}")
    print(f"stale (source newer than iface): {stale_count}")
    print(f"never typechecked         : {total - ever}")
    print()
    print(f"{'dir':<28} {'total':>7} {'2.6.4.3':>8} {'2.9':>6} {'ever':>6} {'stale':>6} {'unchecked':>10}")
    for top in sorted(by_dir):
        r = by_dir[top]
        n = len(r)
        b = sum(1 for _, x, _, _ in r if x)
        s = sum(1 for _, _, x, _ in r if x)
        ev = sum(1 for _, x, y, _ in r if x or y)
        st = sum(1 for _, _, _, x in r if x)
        print(f"{top:<28} {n:>7} {b:>8} {s:>6} {ev:>6} {st:>6} {n - ev:>10}")

    print()
    print("== DASHI subdirectory breakdown ==")
    print(f"{'dir':<44} {'total':>7} {'2.6.4.3':>8} {'2.9':>6} {'ever':>6} {'stale':>6} {'unchecked':>10}")
    dash = by_dir["DASHI"]
    dash_by: dict[str, list] = defaultdict(list)
    for row in dash:
        parts = row[0].split("/")
        key = parts[1] if len(parts) > 1 else "<root>"
        dash_by[key].append(row)
    for key in sorted(dash_by):
        r = dash_by[key]
        n = len(r)
        b = sum(1 for _, x, _, _ in r if x)
        s = sum(1 for _, _, x, _ in r if x)
        ev = sum(1 for _, x, y, _ in r if x or y)
        st = sum(1 for _, _, _, x in r if x)
        print(f"DASHI/{key:<40} {n:>7} {b:>8} {s:>6} {ev:>6} {st:>6} {n - ev:>10}")

    if args.only_unchecked:
        print()
        print("== never typechecked modules ==")
        for rel, b, s, _ in rows:
            if not (b or s):
                print(rel)

    return 0


if __name__ == "__main__":
    sys.exit(main())
