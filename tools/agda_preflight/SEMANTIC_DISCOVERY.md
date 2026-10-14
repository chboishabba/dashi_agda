# Semantic discovery

`dashi-agda` now joins the existing repo-wide `.repo-index/index.sqlite3` inventory with preflight's persistent source/interface cache.

Authority split:

- **repo-index**: whole-repository symbol identity, source spans, refs, requirements, explicit status, file coverage;
- **preflight**: incremental interfaces, shallow signature fingerprints, structural similarity, dependency/affected state;
- **Agda**: final type/proof authority.

Normal symbol search demotes numbered `RoundNNN` modules. Historical matches remain available with `--include-history` and remain visible in discovery receipts.

## Bootstrap/update repo-index

```bash
python scripts/repo_index.py build --root .
# later
python scripts/repo_index.py update --root .
```

## Commands

```bash
dashi-agda symbol FactorsThrough --json
dashi-agda symbol FactorsThrough --include-history --json
dashi-agda related DASHI.Core.SomeModule.FactorsThrough --json
dashi-agda object DASHI.Core.SomeModule.FactorsThrough --json
dashi-agda discover "finite spectral projector" --json
dashi-agda lineage --prefix DASHI.Physics.Closure.NSTriadKN --json
```

`related` and `discover` lazily derive a shallow type-signature overlay from fresh repo-index source spans and persist it in preflight's SQLite DB. Exact `symbol` lookup does not require that enrichment pass.

## Absence protocol

`discover` is fail-closed. `absence_claim_permitted=true` is possible only when:

1. no live, historical, equivalent, or materially similar indexed candidate was found; and
2. repo-index coverage is complete and fresh for its configured repository surface.

If repo-index is missing/stale/incomplete, the result is `absence_status=search_incomplete`, never a categorical non-existence result.

## Round lineage

`lineage` groups module names containing `Round<digits>` into families, compares consecutive rounds, and reports added/removed/unchanged/signature-changed declarations plus `novelty_ratio` and `snapshot_noise_ratio`. This tranche is read-only: it identifies collapse candidates but does not rewrite theorem history.

Structural equivalence and similarity are discovery evidence only; they do not establish Agda definitional equality or proof validity.
