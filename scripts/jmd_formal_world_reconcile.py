#!/usr/bin/env python3
"""Deterministic JMD formal-world reconciliation using DASHI's existing repository DB.

No LLM, no new index database, no theorem inference from Github/QID/OEIS.
Source: .dashi/repository.sqlite3 repo_symbols / repo_symbol_signatures / repo_refs.
Only an *executed* Lean kernel check may create a successful proof receipt.
External Lean checkouts are NEVER cloned, fetched, modified or published.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import shutil
import sqlite3
import subprocess
import tempfile
from pathlib import Path

WORDS = re.compile(r"[A-Za-z][A-Za-z0-9_']*")
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")
MODULE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")
QID = re.compile(r"(?<![A-Za-z0-9])Q[1-9][0-9]*(?![0-9])")
OEIS = re.compile(r"(?<![A-Za-z0-9])A[0-9]{6}(?![0-9])")
STOP = frozenset("theorem lemma example exact agda lean dashi core module math import where source original proof type results".split())
SCHEMA = 1


def digest(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def words(s: str) -> set[str]:
    return {x.lower() for x in WORDS.findall(s) if len(x) > 2 and x.lower() not in STOP}


def records(path: Path):
    if not path.exists():
        raise FileNotFoundError(path)
    with path.open(encoding="utf-8") as f:
        for n, line in enumerate(f, 1):
            if line.strip():
                try:
                    row = json.loads(line)
                except json.JSONDecodeError as exc:
                    raise ValueError(f"{path}:{n}: {exc}") from exc
                if not isinstance(row, dict):
                    raise ValueError(f"{path}:{n}: expected JSON object")
                yield row


def read_ids(path: Path) -> set[int]:
    with path.open(newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        if not reader.fieldnames or "github_id" not in reader.fieldnames:
            raise ValueError("Manifest missing github_id")
        found = set()
        for row in reader:
            value = int(row["github_id"])
            if value <= 0 or value in found:
                raise ValueError("Duplicate or invalid GitHub repository ID")
            found.add(value)
    return found


def init(conn: sqlite3.Connection) -> None:
    """Extend the EXISTING DASHI DB; no shadow schema for source declarations."""
    names = {r[0] for r in conn.execute("SELECT name FROM sqlite_master WHERE type='table'")}
    if not {"repo_symbols", "repo_symbol_signatures", "repo_refs"} <= names:
        raise ValueError("Run dashi-repo index first; canonical Agda source tables are absent")
    conn.executescript("""
    CREATE TABLE IF NOT EXISTS jmd_world_sources (
      source_key TEXT PRIMARY KEY, repository_id INTEGER, repository TEXT NOT NULL,
      source_commit TEXT NOT NULL, module TEXT NOT NULL, declaration TEXT NOT NULL,
      formal_type TEXT NOT NULL, input_kind TEXT NOT NULL,
      statement_hash TEXT NOT NULL, authority TEXT NOT NULL
        CHECK(authority IN ('agda-index','lean-source-unverified'))
    );
    CREATE TABLE IF NOT EXISTS jmd_world_goals (
      goal_id TEXT PRIMARY KEY, module TEXT NOT NULL,
      proposition TEXT NOT NULL, fingerprint TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS jmd_world_external_coordinates (
      source_key TEXT NOT NULL REFERENCES jmd_world_sources(source_key) ON DELETE CASCADE,
      coordinate TEXT NOT NULL, provenance TEXT NOT NULL,
      PRIMARY KEY(source_key,coordinate,provenance)
    );
    CREATE TABLE IF NOT EXISTS jmd_world_candidates (
      goal_id TEXT NOT NULL REFERENCES jmd_world_goals(goal_id) ON DELETE CASCADE,
      source_key TEXT NOT NULL REFERENCES jmd_world_sources(source_key) ON DELETE CASCADE,
      method TEXT NOT NULL, score INTEGER NOT NULL,
      authority TEXT NOT NULL CHECK(authority='candidate-only'),
      PRIMARY KEY(goal_id,source_key,method)
    );
    CREATE TABLE IF NOT EXISTS jmd_world_attempts (
      attempt_id TEXT PRIMARY KEY, goal_id TEXT NOT NULL,
      source_key TEXT NOT NULL, goal_fingerprint TEXT NOT NULL,
      statement_hash TEXT NOT NULL, checker TEXT NOT NULL,
      checker_revision TEXT NOT NULL, return_code INTEGER NOT NULL,
      checked_module TEXT NOT NULL, stdout_excerpt TEXT NOT NULL,
      proof_accepted INTEGER NOT NULL CHECK(proof_accepted IN (0,1)),
      source_revision TEXT NOT NULL, trust_boundary TEXT NOT NULL
        CHECK(trust_boundary='local-pinned-Lean-checker')
    );
    CREATE TABLE IF NOT EXISTS jmd_world_affected (
      changed_symbol TEXT NOT NULL, affected_symbol TEXT NOT NULL,
      PRIMARY KEY(changed_symbol,affected_symbol)
    );
    """)
    conn.execute("PRAGMA foreign_keys=ON")


def source_key(repo: str, commit: str, decl: str) -> str:
    return digest("\x1f".join([repo, commit, decl]))


def import_external(conn, path: Path, global_ids: set[int]) -> int:
    count = 0
    for r in records(path):
        for f in ("repository_id", "repository", "commit", "module", "declaration", "type"):
            if f not in r:
                raise ValueError(f"Missing {f} from external declaration")
        rid = int(r["repository_id"])
        if rid not in global_ids:
            raise ValueError(f"External repository ID not in admitted global corpus: {rid}")
        for field in ("module", "declaration"):
            if not MODULE.fullmatch(str(r[field])):
                raise ValueError(f"Invalid {field}: {r[field]}")
        commit = str(r["commit"])
        if not re.fullmatch(r"[0-9a-f]{40}", commit):
            raise ValueError("External source must have a pinned full Git commit")
        typ = str(r["type"]).strip()
        if not typ:
            raise ValueError("Empty source theorem type")
        key = source_key(str(r["repository"]), commit, str(r["declaration"]))
        conn.execute("""INSERT INTO jmd_world_sources
        VALUES (?,?,?,?,?,?,?,?,?,?)
        ON CONFLICT(source_key) DO UPDATE SET
          formal_type=excluded.formal_type, statement_hash=excluded.statement_hash,
          authority=excluded.authority
        """, (key, rid, r["repository"], commit, r["module"],
              r["declaration"], typ, "lean", digest(typ), "lean-source-unverified"))
        count += 1
    return count


def import_agda(conn, *, revision: str, max_rows: int = 0) -> int:
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("Agda revision must be full 40-digit git SHA")
    sql = """SELECT s.symbol_id,s.module,ss.signature,ss.signature_sha256
             FROM repo_symbols s JOIN repo_symbol_signatures ss
             ON ss.symbol_id=s.symbol_id WHERE s.language='agda'
             AND ss.signature <> '' ORDER BY s.symbol_id"""
    if max_rows:
        sql += " LIMIT " + str(max_rows)
    rows = conn.execute(sql).fetchall()
    for name, module, typ, fp in rows:
        key = source_key("chboishabba/dashi_agda", revision, name)
        conn.execute("""INSERT INTO jmd_world_sources VALUES(?,?,?,?,?,?,?,?,?,?)
        ON CONFLICT(source_key) DO UPDATE SET formal_type=excluded.formal_type,
        statement_hash=excluded.statement_hash""",
        (key, None, "chboishabba/dashi_agda", revision, module or "",
         name, typ, "agda", fp or digest(typ), "agda-index"))
    return len(rows)


def import_coordinates(conn, path: Path | None):
    if path is None:
        return 0
    n = 0
    for r in records(path):
        key, external, provenance = (str(r[k]) for k in ("source_key", "external_id", "provenance"))
        if not (QID.fullmatch(external) or OEIS.fullmatch(external)):
            raise ValueError(f"Not a valid exact QID/OEIS coordinate: {external}")
        if not provenance:
            raise ValueError("Unattributed external identity")
        if not conn.execute("SELECT 1 FROM jmd_world_sources WHERE source_key=?", (key,)).fetchone():
            raise ValueError(f"Unknown formal source for coordinate {key}")
        conn.execute("INSERT OR IGNORE INTO jmd_world_external_coordinates VALUES(?,?,?)",
                     (key, external, provenance))
        n += 1
    return n


def upsert_goals(conn, path: Path) -> tuple[int, set[str]]:
    changed = set()
    seen = set()
    for r in records(path):
        name, module, prop = (str(r[k]) for k in ("goal_id", "module", "proposition"))
        if not name or name in seen or not MODULE.fullmatch(module) or not prop.strip():
            raise ValueError("Invalid or duplicate goal")
        seen.add(name)
        fingerprint = digest(module + "\x1f" + prop)
        old = conn.execute("SELECT fingerprint FROM jmd_world_goals WHERE goal_id=?", (name,)).fetchone()
        if old is None or old[0] != fingerprint:
            changed.add(name)
            conn.execute("DELETE FROM jmd_world_candidates WHERE goal_id=?", (name,))
            # An old successful attempt is historical, but not current payment.
        conn.execute("""INSERT INTO jmd_world_goals VALUES(?,?,?,?)
        ON CONFLICT(goal_id) DO UPDATE SET module=excluded.module,
        proposition=excluded.proposition,fingerprint=excluded.fingerprint""",
        (name, module, prop, fingerprint))
    return len(seen), changed


def candidates(conn, *, limit: int = 8) -> int:
    """Deterministic *candidate-only* routing, not theorem matching."""
    sources = conn.execute("""SELECT source_key,declaration,formal_type
                              FROM jmd_world_sources ORDER BY source_key""").fetchall()
    coords = {}
    for key, coord in conn.execute("SELECT source_key,coordinate FROM jmd_world_external_coordinates"):
        coords.setdefault(key, set()).add(coord)
    inserted = 0
    for goal_id, proposition in conn.execute("SELECT goal_id,proposition FROM jmd_world_goals ORDER BY goal_id"):
        tokens, goal_ids = words(proposition), set(QID.findall(proposition)) | set(OEIS.findall(proposition))
        ranking = []
        for key, decl, typ in sources:
            overlap = tokens & words(decl + " " + typ)
            related_ids = goal_ids & coords.get(key, set())
            if not overlap and not related_ids:
                continue
            methods = []
            if overlap:
                methods.append("lexical")
            if related_ids:
                methods.append("external-coordinate")
            score = len(overlap) + 2 * len(related_ids)
            ranking.append((-score, key, "+".join(methods)))
        ranking.sort()
        conn.execute("DELETE FROM jmd_world_candidates WHERE goal_id=?", (goal_id,))
        for score, key, method in ranking[:limit]:
            conn.execute("INSERT INTO jmd_world_candidates VALUES(?,?,?,?,?)",
                         (goal_id, key, method, -score, "candidate-only"))
            inserted += 1
    return inserted


def check_lean(conn, *, root: Path, limit: int = 4, timeout: int = 120) -> dict:
    """Generate a Lean exact-reuse probe and RUN the actual local Lean checker.

    A pass proves only the *goal proposition* from a donor term in its own
    environment. It is not a Lean->Agda transport or a claim about the target
    theorem's original namespace unless the supplied goal matches that type.
    """
    root = root.resolve()
    if not (root / "lakefile.toml").exists() and not (root / "lakefile.lean").exists():
        raise ValueError("Explicit Lean checkout with lakefile required")
    if not (root / ".git").exists():
        raise ValueError("Refuse to treat an unpinned/non-git checkout as a source environment")
    if not shutil.which("lake"):
        raise RuntimeError("Lean Lake missing; no proof promotion")
    revision = subprocess.run(["git","rev-parse","HEAD"],cwd=root,
                              capture_output=True,text=True,check=True).stdout.strip()
    if not re.fullmatch("[0-9a-f]{40}",revision):
        raise ValueError("Unpinned Lean checkout")
    accepted = failed = 0
    sql = """SELECT c.goal_id,c.source_key,g.module,g.proposition,g.fingerprint,
             s.module,s.declaration,s.statement_hash,s.source_commit,s.input_kind
             FROM jmd_world_candidates c
             JOIN jmd_world_goals g ON c.goal_id=g.goal_id
             JOIN jmd_world_sources s ON c.source_key=s.source_key
             WHERE s.input_kind='lean' AND s.repository=?
               AND s.source_commit=?
             ORDER BY c.goal_id,c.score DESC,c.source_key LIMIT ?"""
    repo_name = None
    remote = subprocess.run(["git","remote","get-url","origin"],cwd=root,capture_output=True,text=True)
    if remote.returncode == 0:
        value = remote.stdout.strip().removesuffix(".git")
        if value.startswith("git@github.com:"):
            repo_name=value[len("git@github.com:"):]
        elif value.startswith("https://github.com/"):
            repo_name=value[len("https://github.com/"):]
    if not repo_name:
        raise ValueError("Checkout origin must be GitHub and match imported source")
    rows = conn.execute(sql,(repo_name,revision,limit)).fetchall()
    for goal,key,gmod,prop,fp,smod,decl,source_fp,commit,kind in rows:
        if not MODULE.fullmatch(gmod) or not MODULE.fullmatch(smod) or not IDENT.fullmatch(decl):
            continue
        # Goal proposition is provided by a source declaration consumer.
        # Its exact elaboration is checked by Lean, not by Python.
        probe = f"import {gmod}\nimport {smod}\nexample : {prop} := by\n  exact {decl}\n"
        with tempfile.NamedTemporaryFile(mode="w",suffix=".lean",dir=root,
                                         prefix="JMDProbe_",delete=False) as f:
            f.write(probe)
            name = Path(f.name)
        try:
            run = subprocess.run(["lake","env","lean",name.name],cwd=root,
                                 text=True,capture_output=True,timeout=timeout,check=False)
            ok = run.returncode == 0
            msg = (run.stdout + "\n" + run.stderr)[:1500]
        except subprocess.TimeoutExpired:
            ok,msg=False,"CHECKER_TIMEOUT"
        finally:
            name.unlink(missing_ok=True)
        attempt = digest("\x1f".join([goal,key,fp,source_fp,commit,revision]))
        conn.execute("""INSERT INTO jmd_world_attempts VALUES(?,?,?,?,?,?,?,?,?,?,?,?)
        ON CONFLICT(attempt_id) DO UPDATE SET
        return_code=excluded.return_code,stdout_excerpt=excluded.stdout_excerpt,
        proof_accepted=excluded.proof_accepted""",
        (attempt,goal,key,fp,source_fp,"lake env lean",revision,
         0 if ok else 1, gmod, msg, int(ok), commit,"local-pinned-Lean-checker"))
        accepted += int(ok)
        failed += int(not ok)
    return {"attempts":len(rows),"kernel_accepted":accepted,"not_accepted":failed,
            "limited_scope":"Lean-local exact reuse only; not cross-prover semantics"}


def changed_closure(conn, changed: set[str]) -> int:
    """Use the existing dependency relation. Record impact, never refute proof."""
    if not changed:
        return 0
    n = 0
    for source in sorted(changed):
        conn.execute("DELETE FROM jmd_world_affected WHERE changed_symbol=?", (source,))
        # repo_refs points from dependent -> dependency.
        query = """WITH RECURSIVE affected(symbol) AS (
           SELECT ? UNION SELECT r.from_symbol FROM repo_refs r
           JOIN affected a ON r.to_symbol=a.symbol
        ) SELECT symbol FROM affected"""
        for (target,) in conn.execute(query,(source,)):
            conn.execute("INSERT OR IGNORE INTO jmd_world_affected VALUES(?,?)",(source,target))
            n += 1
    return n


def report(conn) -> dict:
    result = {"schema":"jmd-formal-world-v1","llm_required":False,
              "external_publication":False,"proof_authority":"Lean/Agda kernels only"}
    for key, sql in {
        "sources":"SELECT count(*) FROM jmd_world_sources",
        "goals":"SELECT count(*) FROM jmd_world_goals",
        "candidate_edges":"SELECT count(*) FROM jmd_world_candidates",
        "external_coordinates":"SELECT count(*) FROM jmd_world_external_coordinates",
        "executed_kernel_passes":"SELECT count(*) FROM jmd_world_attempts a JOIN jmd_world_goals g ON g.goal_id=a.goal_id JOIN jmd_world_sources s ON s.source_key=a.source_key WHERE a.proof_accepted=1 AND a.goal_fingerprint=g.fingerprint AND a.statement_hash=s.statement_hash AND a.source_revision=s.source_commit",
        "affected_nodes":"SELECT count(*) FROM jmd_world_affected"
    }.items():
        result[key] = conn.execute(sql).fetchone()[0]
    result["cross_prover_proofs_asserted"] = 0
    result["unverified_candidates_promoted"] = 0
    return result


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--database",type=Path,default=Path(".dashi/repository.sqlite3"))
    p.add_argument("--global-csv",type=Path,required=True)
    p.add_argument("--external-declarations",type=Path)
    p.add_argument("--goals",type=Path,required=True)
    p.add_argument("--external-coordinates",type=Path)
    p.add_argument("--agda-revision",help="Pinned Agda repository HEAD (40 hex)")
    p.add_argument("--max-agda-rows",type=int,default=0)
    p.add_argument("--max-candidates",type=int,default=8)
    p.add_argument("--verify-lean-root",type=Path,help="Opt-in local kernel run; no network fetch")
    p.add_argument("--max-probes",type=int,default=4)
    args=p.parse_args(argv)
    if not args.database.is_file():
        p.error("Missing canonical DB; run dashi-repo index first")
    if args.max_candidates<1 or args.max_probes<0 or args.max_agda_rows<0:
        p.error("Limits must be non-negative; candidates at least one")
    admitted=read_ids(args.global_csv)
    conn=sqlite3.connect(args.database)
    try:
        init(conn)
        with conn:
            if args.agda_revision:
                import_agda(conn,revision=args.agda_revision,max_rows=args.max_agda_rows)
            if args.external_declarations:
                import_external(conn,args.external_declarations,admitted)
            import_coordinates(conn,args.external_coordinates)
            _,changed=upsert_goals(conn,args.goals)
            candidates(conn,limit=args.max_candidates)
            changed_closure(conn,changed)
        probe=None
        if args.verify_lean_root:
            with conn:
                probe=check_lean(conn,root=args.verify_lean_root,limit=args.max_probes)
        status=report(conn)
        status["admitted_global_repository_count"]=len(admitted)
        status["checker_run"]=probe
        print(json.dumps(status,indent=2,sort_keys=True))
    finally:
        conn.close()

if __name__=="__main__":
    main()
