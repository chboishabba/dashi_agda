## Start Here

This repo is a formal-and-bridge workspace around the DASHI program.

> **Source attribution is repository style, not optional decoration.** When a
> module, theorem surface, empirical claim, calibration, bridge, dataset use,
> standard, or external construction comes from an identifiable source, attach
> recoverable provenance wherever available. Prefer a stable DOI or comparable
> identifier; otherwise use a canonical link, author/title/venue, theorem or
> section locator, repository commit, dataset ID/version, or the best accurate
> attribution available. **No DOI does not mean no citation.** Do not fabricate
> missing metadata.

For source-derived Agda, provenance should normally be visible near the module
header and should be typed into a source/registry/attribution surface when the
source identity matters downstream. Keep source claims separate from DASHI
reconstruction, cross-source inference, synthetic witnesses/new theorems, and
promotion/adjudication claims.

See **[`Docs/SourceAttributionPolicy.md`](Docs/SourceAttributionPolicy.md)** for
the normative repository policy and preferred identifier order.

### Repository orientation and current status

For a generated, source-derived table of contents of the `DASHI/` module
tree—lane sizes, aggregate entrypoints, and dependency hubs—start with
**[`Docs/ProjectMap.md`](Docs/ProjectMap.md)**. Regenerate it with
`python scripts/build_project_map.py` after structural changes.

The previous full README, including the detailed current lane/status orientation,
is preserved verbatim at
**[`Docs/RepositoryLongformREADME.md`](Docs/RepositoryLongformREADME.md)**.
Serious readers should continue there after reading the source-attribution rule
above.

The proof-search/observation development method is documented in
**[`Docs/IntrospectiveProofLoop.md`](Docs/IntrospectiveProofLoop.md)**, including
the plain-language visual walkthrough and the rule that visualization remains a
diagnostic aid rather than evidence or proof.

Repository automation follows a resource-conscious, newest-run-wins policy;
see [`.github/WORKFLOW_PHILOSOPHY.md`](.github/WORKFLOW_PHILOSOPHY.md) before
adding or broadening a GitHub Actions workflow.

### Checking Agda modules locally

Use the parallel-check wrapper, not `agda` directly:

```bash
scripts/run_agda29_parallel_check.sh DASHI/Path/To/Target.agda
```

With no target it checks `DASHI/Everything.agda`. Useful knobs:

```bash
AGDA_JOBS=4 scripts/run_agda29_parallel_check.sh DASHI/Path/To/Target.agda
DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh DASHI/Path/To/Target.agda
DASHI_AGDA29_CLEAN=1 scripts/run_agda29_parallel_check.sh DASHI/Everything.agda
```

The wrapper resolves the Agda 2.9 binary from the sibling
`/home/c/Documents/code/agda` flake, rsyncs a source-only shadow of this repo
(plus the stdlib `experimental` checkout) under
`${XDG_CACHE_HOME:-$HOME/.cache}/dashi-agda29`, and reuses `.agdai` interfaces
across runs. `DASHI_NO_TMUX=1` runs in the current shell instead of a detached
tmux session. Full mechanics, cache controls, and the Track A (authoritative
flake) vs Track B (fast parallel feedback) distinction are documented in
[`Docs/AgentOperationalNotes.md`](Docs/AgentOperationalNotes.md).

The high-level claim classes remain:

- `proved`: canonical Agda theorem spine and specifically discharged closure claims;
- `bridge`: connections from formal surfaces to interpretations without claiming full derivation;
- `packaging`: summaries that assemble existing lanes without strengthening them;
- `empirical`: data/measurement-facing surfaces that remain explicitly bounded;
- `speculative`: roadmap or intuition surfaces that are not current repo claims.
