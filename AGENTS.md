# Agent Notes

## Agda And Nix

This repository has its own local `flake.nix` and `flake.lock`. Treat them as
the reproducibility authority for Dashi artifacts and baked references. Do not
update or rewrite the Dashi flake/lock just to get a newer Agda, unless the user
explicitly asks for that migration.

There are two Agda tracks. Keep them separate:

- **Track A, authoritative:** use the Dashi flake/pinned toolchain for final
  `DASHI/Everything.agda` promotion checks. This track preserves baked refs and
  reproducibility, even if it is slower.
- **Track B, draft worker:** use the neighboring Agda checkout at
  `/home/c/Documents/code/agda`, which builds Agda 2.9.0 and supports native
  parallel import checking via `-j[N]` / `--parallel[=N]`. Track B is fast
  feedback only and must not block promotion by itself.

The preferred wrapper for this workflow is:

```bash
scripts/run_agda29_parallel_check.sh
scripts/run_agda29_parallel_check.sh DASHI/Core/FormalStructureLawCore.agda
AGDA_JOBS=4 scripts/run_agda29_parallel_check.sh DASHI/Everything.agda
```

Workers and subagents that are explicitly allowed to run Agda should use that
wrapper, not `agda` directly and not the old `run_agda29_shadow_check` name.
For normal focused checks, this is the command to hand to agents:

```bash
scripts/run_agda29_parallel_check.sh DASHI/Path/To/Target.agda
```

For Python harnesses or sandboxed callers that cannot invoke `nix build`
inside the wrapper, pre-resolve the binary once and pass it through:

The pre-existing operational, Agda/Nix, proof-lane, audit, and promotion notes
remain normative and are preserved verbatim in
[`Docs/AgentOperationalNotes.md`](Docs/AgentOperationalNotes.md). **Agents must
read that file before making repository changes.** This root file is the
front-door style contract; the linked operational notes are part of the same
agent instructions.


## Native proof-symbol snowball for active SAT/ETH max-cut

For the OpenAI SAT/ETH integration, **discover before writing a new proof**.
The authoritative [39 exact remaining lemma/certificate register](docs/superpowers/plans/2026-10-31-openai-math-exact-lemma-maxcut-ledger.md),
[175 prioritized symbol-search terms](docs/superpowers/plans/2026-10-31-local-symbol-snowball-terms.json),
and [workstation-agent workflow](docs/superpowers/plans/2026-10-31-local-symbol-snowball-agent.md)
are maintained on the existing Agda #1212 integration branch.
Run `scripts/run_openai_math_symbol_snowball.py` against the native
`dashi-repo` semantic index and, optionally, the sibling Lean repository.
Do **not** implement a competing symbol database, redefine the original
circuit evaluator or unique-gate proof, or treat a similar name/number/DA51
or QID as a kernel-verified same-object theorem.

The Agda Golden proofs and Lean downstream remain distinct authorities.
The original source-written P1/P2 and staged Lean P3/P4 require exact-head
compiler acceptance and a verified real executable source-to-machine
translation with time and **every-prefix** space costs.
No CI is required for this research workflow; executable Python checks
do not establish Lean or Agda kernel acceptance. Preserve the existing
attribution and operational policies above, including ESD import-only
and original Ibrahim Monster 3B proof ownership.
