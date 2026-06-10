# DASHI Root Index

Declared surface level: `router`.

This file is the compact root-level map for finding the current live surfaces
without treating every root file as equally authoritative.

## Live Entry Points

- `README.md`: repo orientation and current high-level status.
- `architecture.md`: canonical architecture and diagram entrypoint.
- `Docs/LiveSurfaceIndex.md`: shortest live corpus and support router.
- `Docs/RepoGuide.md`: detailed repository guide.
- `Docs/PhysicsGuide.md`: physics-facing guide.
- `Docs/AgdaValidationTargets.md`: focused validation policy.
- `status.md`: current live state.
- `TODO.md`: current live blockers.
- `CHANGELOG.md`: release and claim-state history.

## Current Publication Stack

The current publishable programme is organized as:

- Paper 1: `Docs/Paper1NavierStokesClayDraft.md`
- Paper 3: `Docs/Paper3YangMillsClayDraft.md`
- Paper 8: `Docs/Paper8UnificationDraft.md`
- shared support: `Docs/SupportCompendium.md`,
  `Docs/PaperCommonCitationLedger.md`, and
  `Docs/PaperCommonNotationGlossary.md`

Legacy papers and section drafts remain provenance or source-feeding surfaces.
They are not equal-priority live manuscripts.

The cleanup must preserve the fail-closed publication boundary: no cleanup move
promotes Clay, continuum YM, NS regularity, Gate 3, or exact Standard Model
claims.

## Formal Entrypoints

- Aggregate check: `DASHI/Everything.agda`.
- Primary formal tree: `DASHI/`.
- Main current pressure point: `DASHI/Physics/Closure/`.
- Canonical theorem-spine map: `Docs/CanonicalProofSpine.md`.
- Current cleanup roadmap: `Docs/RepoStructureCleanupRoadmap.md`.
- Live paper corpus router: `Docs/LiveSurfaceIndex.md`.

## Generated And Archive Policy

Generated snapshots, old validation logs, downloaded scratch payloads, and
historical status blocks should not stay as root navigation surfaces.

Ignored local generated build surfaces such as `MAlonzo/`, `_build/`, and
`artifacts/` may exist on disk and should not be treated as source. `MAlonzo/`
is used by generated-Haskell workflows, so clean it only when the corresponding
Agda Haskell output can be rebuilt.

Planned archive buckets:

- `Docs/archive/generated/YYYY-MM/`
- `Docs/archive/validation/YYYY-MM/`
- `Docs/archive/status/YYYY-MM/`
- `Docs/archive/todo/YYYY-MM/`
- `Docs/archive/old-roadmaps/YYYY-MM/`

Generated future equivalents should be ignored or untracked only after the
historical copy/index step is complete.

Search-noise reduction:

- the repo-local `.rgignore` excludes submodules, build outputs, archives,
  working folders, and large authority/evidence surfaces from default `rg`
  searches
- use `rg -uu` when you intentionally want the full repo

## Submodule And External Boundaries

Do not reorganize these during ordinary repo cleanup:

- `DCHoTT-Agda/`: external Agda dependency.
- `cubical/`: external Agda dependency.
- `Monster-LILA/`: meta-introspector/JMD-adjacent submodule.
- `monster/`: meta-introspector/JMD-adjacent submodule.
- sibling repos such as `../dashiCFD`, `../dashiRTX`, `../dashifine`,
  `../DASHIg`, and `../dashi_lean4`.

References to sibling outputs should remain explicit; cleanup in this repo is
not permission to mutate sibling repos.

## Validation Commands

Focused checks should use the lane-specific targets in
`Docs/AgdaValidationTargets.md`.

Final aggregate check:

```sh
timeout 300s agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Everything.agda
```

Basic hygiene check:

```sh
git diff --check
```

Python-script surface check when `scripts/` or `tests/` move:

```sh
python -m pytest tests
```

## Cleanup Rule

The safe ordering is:

```text
classify -> archive/index -> compact live state -> add aggregate modules -> move Agda files only if still needed
```

Physical Agda moves require import maps, compatibility wrappers, targeted
validation, and aggregate validation.
