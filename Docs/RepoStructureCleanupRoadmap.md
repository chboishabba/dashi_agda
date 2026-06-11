# Repo Structure Cleanup Roadmap

Declared surface level: `roadmap`.

This roadmap records the cleanup plan for reducing repo navigation and
validation drag without losing provenance, breaking Agda imports, or crossing
external/JMD/submodule ownership boundaries.

The governing policy for future passes is now `Docs/ProofFirstRepoPolicy.md`.
This roadmap should be read as an execution plan for that proof-first rule.

## Current Observations

The repo has become hard to navigate because several different artifact classes
now live in the same surfaces:

- theorem/source modules
- receipt and governance modules
- generated snapshots and validation logs
- historical planning state
- external authority packets
- submodules and sibling-repo evidence

Measured pressure as of `2026-06-10`:

- `Docs/` top-level files: `372`
- `DASHI/Physics/Closure` `.agda` files: `2139`
- `DASHI/Physics/Closure` files with `Receipt` in the name: `882`

That means the current problem is not just "too many files." It is that the
same directories are simultaneously serving as live entrypoints, historical
provenance stores, scratch pads, and executable governance surfaces.

The largest pressure point is `DASHI/Physics/Closure`: it is mostly flat and
contains more than a thousand direct Agda files, including hundreds of
receipt-like modules. `DASHI/Everything.agda` imports the whole surface, so any
physical module move must be staged carefully.

The root also contains tracked generated or scratch-like artifacts such as
`all_code*.txt`, old `status.paper7-wave*.root-validation.log` files,
`TEST_ADD_FILE.tmp`, and tracked files under `temp-DOWNLOADED/`.

## Ownership Boundaries

Do not move or edit these as part of repo cleanup unless a separate task
explicitly assigns that work:

- `DCHoTT-Agda/`: external Agda dependency
- `cubical/`: external Agda dependency
- `Monster-LILA/`: meta-introspector/JMD-adjacent submodule
- `monster/`: meta-introspector/JMD-adjacent submodule
- sibling repos such as `../dashiCFD`, `../dashiRTX`, `../dashifine`,
  `../DASHIg`, and `../dashi_lean4`

For this repo, cleanup means organizing `dashi_agda` while preserving explicit
references to sibling outputs. It does not mean moving or normalizing sibling
repos.

## Target Shape

The intended state is:

- small root with only live entrypoints and build/config surfaces
- proof-bearing files dominate the visible layer
- compact live `status.md` and `TODO.md`
- historical plans and logs behind archive indexes
- docs grouped by purpose instead of mixed at `Docs/` root
- `DASHI/Physics/Closure` split into navigable topic lanes
- compatibility shims or aggregate modules before any high-risk Agda moves
- generated artifacts untracked or archived with provenance

Immediate reader-facing rule:

- a new external reader should be able to find the live corpus from
  `ROOT_INDEX.md` and `Docs/LiveSurfaceIndex.md` without browsing all of
  `Docs/`
- a new external reader should mostly see proof surfaces, not receipts or
  governance debris

## Four-Pass Structure

The cleanup must proceed in four passes:

```text
Pass 0: inventory only
Pass 1: root/doc/generated cleanup
Pass 2: index and aggregate modules
Pass 3: physical Agda moves, only if still needed
```

The first implementation should be deliberately boring:

- no theorem edits
- no claim renames
- no submodule edits
- no physical Agda moves
- only manifests, root/doc archive work, and live indexes

## Cleanup Stages

### Pass 0: Baseline Inventory

Goal: make sure we know what exists before moving or untracking anything.

Actions:

- create `.planning/repo-cleanup-manifest.md`
- create `.planning/repo-cleanup-move-plan.tsv`
- create `.planning/agda-import-map.tsv`
- record `git status --short --branch`
- record submodule status and note recursive submodule failures separately
- record tracked file counts by top-level directory and by `DASHI/` namespace
- record root tracked files
- record generated-looking tracked files
- record reverse-import counts for any Agda module proposed for movement
- classify each relevant path as `ours`, `external/JMD`, `generated`,
  `historical-ledger`, `live-proof-module`, `support-only-receipt`, or
  `submodule-owned`

Move-plan columns:

```text
current_path
proposed_path
kind
owner
tracked?
generated?
imported_by
safe_action
validation_required
```

Checkpoint:

- all three inventory artifacts exist under `.planning/`
- no files have been moved
- dirty worktree entries are classified as existing user/agent work vs cleanup
  candidates

Loss-prevention rule:

- never delete or move a file before it is classified as source, docs,
  generated artifact, external authority, submodule, or historical archive.

### Pass 1: Root, Docs, And Generated Hygiene

Goal: reduce root noise without touching Agda module semantics.

Candidate archive/untrack set:

- `all_code*.txt`
- `status.paper7-wave*.root-validation.log`
- `TEST_ADD_FILE.tmp`
- tracked `*.agdai`
- tracked files under `temp-DOWNLOADED/`
- generated build products that are already covered by `.gitignore`

Ignored local generated directories:

- `MAlonzo/`: Agda-to-Haskell generated output, ignored by Git, may be needed
  by `scripts/materialize_profile_summary_family.hs` until regenerated
- `_build/`: Agda build cache
- `artifacts/`: generated closure-hygiene and run artifacts

Actions:

- archive tracked historical artifacts first
- move historical logs/snapshots into `logs/archive/` or `artifacts/archive/`
  when they must be kept
- move status/TODO history into indexed docs before shortening live files
- add or update `ROOT_INDEX.md` as the root router
- only after archive/index work, untrack future generated equivalents with
  `git rm --cached` when `.gitignore` catches them
- leave an archive manifest for anything historically meaningful

Safe sequence:

```sh
git mv all_code*.txt Docs/archive/generated/YYYY-MM/
git mv status.paper7-wave*.root-validation.log Docs/archive/validation/YYYY-MM/
git rm --cached '*.agdai'   # only after confirming .gitignore catches them
```

Checkpoint:

- root file list is shorter
- `.gitignore` covers the removed generated classes
- no Agda source modules have moved
- `ROOT_INDEX.md` explains live proof spine, publication stack, generated
  archives, margin receipts, submodule boundaries, and validation commands

Validation:

```sh
git diff --check
git status --short
```

Loss-prevention rule:

- if a file contains evidence, authority material, or user-authored prose, move
  it to an indexed archive instead of deleting it.
- never combine archive and untrack into one conceptual step. First preserve
  history, then stop tracking future generated equivalents.

### Pass 1b: Live State Compaction

Goal: stop `status.md`, `TODO.md`, and `devlog.md` from acting as unbounded
search surfaces.

Target policy:

- `status.md`: current state only, capped and date-scoped
- `TODO.md`: open tasks only
- `devlog.md`: append-only engineering log
- `CHANGELOG.md`: release and claim-state history
- `.planning/`: historical plans and current planning snapshots, not canonical
  theorem truth

Target split:

```text
status.md                         # current live state, ideally under 300 lines
Docs/status/2026-06-margin.md      # detailed current margin programme
Docs/archive/status/YYYY-MM/*.md   # historical status snapshots

TODO.md                           # live blockers only
Docs/roadmaps/*.md                # detailed plans
Docs/archive/todo/YYYY-MM/*.md    # old blocker boards
```

Actions:

- create archive files for old status/TODO blocks by month or programme phase
- leave a short pointer in the live root file to the archive
- keep current open work visible at the top

Checkpoint:

- live state files are short enough to read in one pass
- archived sections retain original wording or an explicit provenance pointer

Validation:

```sh
git diff --check
```

Loss-prevention rule:

- status compaction must preserve all unresolved tasks or explicitly mark them
  superseded by a newer task.

### Pass 1c: Docs Taxonomy

Goal: make `Docs/` navigable by purpose.

Proposed buckets:

- `Docs/papers/live/`
- `Docs/papers/source/`
- `Docs/papers/legacy/`
- `Docs/roadmaps/`
- `Docs/authority/`
- `Docs/diagrams/`
- `Docs/domain-notes/`
- `Docs/archive/YYYY-MM/`

Intended membership:

- `Docs/papers/live/`: the current flagship manuscript corpus only
  - `Paper1NavierStokesClayDraft.md`
  - `Paper3YangMillsClayDraft.md`
  - `Paper8UnificationDraft.md`
  - `SupportCompendium.md`
  - `PaperCommonCitationLedger.md`
  - `PaperCommonNotationGlossary.md`
- `Docs/papers/drafts/`: skeletons, section drafts, clay targets, and working
  prose inputs
  - `NSPaper1ClayTarget.md`
  - `YMPaper3ClayTarget.md`
  - `Paper1DraftSkeleton.md`
  - `Paper3YangMillsGeometryDraft.md`
  - `Paper8Section*.md`
  - `PaperDraftWorkingFolder/`
- `Docs/papers/legacy/`: old manuscript lanes that now act as provenance or
  source reservoirs rather than live top-priority papers
  - `Paper0*`, `Paper2*`, `Paper4*`, `Paper5*`, `Paper6*`, `Paper7*`

Keep these live at `Docs/` root unless a later decision says otherwise:

- `Docs/LiveSurfaceIndex.md`
- `Docs/ProofFirstRepoPolicy.md`
- `Docs/RepoStructureCleanupRoadmap.md`
- diagram entrypoint docs that are actively referenced from `architecture.md`

Actions:

- classify docs by purpose and cited owner module
- move obvious paper drafts to `Docs/papers/<paper>/`
- move old tranche plans to `Docs/archive/YYYY-MM/`
- keep external authority receipts indexed and separate from generated outputs

Checkpoint:

- `Docs/` root contains entrypoints, not every historical note
- every moved doc has either an index entry or a redirect/pointer
- live paper files are visibly separated from prep and provenance files

Validation:

```sh
git diff --check
rg 'Docs/OldPathName' README.md architecture.md Docs || true
```

Loss-prevention rule:

- do not move authority receipts without preserving citation/provenance links.

### Pass 1d: Scripts And Data Split

Goal: separate executable scripts, test fixtures, authority data, caches, and
runtime outputs.

Target shape:

- `scripts/`: executable helpers and CLIs
- `tests/fixtures/`: small golden fixtures used by tests
- `scripts/data/authority/`: small source/authority packets
- `scripts/data/cache/`: large downloaded or generated cache material
- `artifacts/`: run outputs and generated results

Actions:

- classify `scripts/data/outputs/*` as fixture or artifact
- classify HEPData and PDF material as authority, fixture, or cache
- update scripts/tests only after paths are classified

Checkpoint:

- Python tests still know where fixtures live
- large downloaded data is either tracked intentionally or documented as cache

Validation:

```sh
python -m pytest tests
git diff --check
```

Loss-prevention rule:

- do not move data that tests depend on until the test path update is included
  in the same change.

### Pass 2: Index And Aggregate Modules

Goal: reduce navigation and validation drag before physical Agda moves.

First add grouping modules in the existing flat `Closure` directory:

```text
DASHI/Physics/Closure/Margin.agda
DASHI/Physics/Closure/Programme.agda
DASHI/Physics/Closure/NS.agda
DASHI/Physics/Closure/YM.agda
DASHI/Physics/Closure/Gate3.agda
DASHI/Physics/Closure/Authority.agda
```

Each grouping module imports the relevant existing flat receipt modules. This
gives most of the practical benefit of nesting while avoiding path-sensitive
Agda moves.

Operational note:

- this is the right first move for `DASHI/Physics/Closure`
- there are too many receipt-like modules to justify a big-bang folder move
- lane aggregate modules plus better doc routers will buy most of the context
  win before any semantic path migration

Actions:

- build grouping modules from the Pass 0 import map
- keep original flat receipt modules in place
- update `DASHI/Everything.agda` gradually only where low risk
- document focused grouped validation targets in
  `Docs/support/reference/AgdaValidationTargets.md`

Checkpoint:

- grouped modules compile directly
- `DASHI/Everything.agda` still compiles
- readers can enter NS/YM/Gate3/Margin/Programme lanes without scanning the
  flat receipt namespace

Validation:

```sh
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Physics/Closure/Margin.agda
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Physics/Closure/NS.agda
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Physics/Closure/YM.agda
timeout 300s agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Everything.agda
git diff --check
```

Loss-prevention rule:

- index modules are routers only. They must not strengthen, rename, or
  reinterpret any receipt status.

### Pass 3: Physical Agda Moves

Candidate lanes:

- `DASHI/Physics/Closure/NS/`
- `DASHI/Physics/Closure/YM/`
- `DASHI/Physics/Closure/Gate3/`
- `DASHI/Physics/Closure/CKM/`
- `DASHI/Physics/Closure/HEPData/`
- `DASHI/Physics/Closure/Margin/`
- `DASHI/Physics/Closure/Programme/`
- `DASHI/Physics/Closure/Authority/`
- `DASHI/Physics/Closure/Archive/`

Goal: physically reduce the flat `DASHI/Physics/Closure` receipt namespace only
after Pass 2 shows that grouped lane entrypoints are stable.

This pass is optional. If Pass 2 gives enough efficiency, physical moves can be
deferred.

Agda module paths are semantic: moving a file requires changing its
`module ... where` declaration and every import that names it.

Actions:

- generate reverse-import map for one lane at a time
- keep the Pass 2 lane aggregate module live
- add old-path compatibility wrappers before or during moves
- move only one small lane per batch
- update `DASHI/Everything.agda` after each batch

Wrapper policy:

If this old file:

```text
DASHI/Physics/Closure/NSTailFluxAbsorptionMarginReceipt.agda
```

moves to:

```text
DASHI/Physics/Closure/NS/NSTailFluxAbsorptionMarginReceipt.agda
```

then the old path temporarily becomes:

```agda
module DASHI.Physics.Closure.NSTailFluxAbsorptionMarginReceipt where

open import DASHI.Physics.Closure.NS.NSTailFluxAbsorptionMarginReceipt public
```

This avoids a big-bang import migration.

Checkpoint:

- the moved lane compiles directly
- `DASHI/Everything.agda` compiles after the batch
- no receipt status label changed during the move

Validation:

```sh
agda -i . -i DCHoTT-Agda -i cubical -l standard-library <moved-lane-aggregate>.agda
timeout 300s agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Everything.agda
git diff --check
```

Loss-prevention rule:

- folder location must not imply promotion. A `candidate`, `frontier`,
  `boundary`, or `receipt` remains that status after movement.

### Pass 2/3: Aggregate Validation Optimization

Goal: make daily checks cheaper while preserving full validation.

Actions:

- add or promote domain aggregate modules for daily checks
- keep `DASHI/Everything.agda` as the batch aggregate
- document focused validation targets in `Docs/support/reference/AgdaValidationTargets.md`
- avoid making `Everything.agda` the first file a reader or worker opens

Checkpoint:

- each active lane has a focused validation target
- aggregate validation still exists and passes as the final check

Validation:

```sh
scripts/run_agda_easy_to_hard.py
scripts/run_closure_full_check.sh
```

Loss-prevention rule:

- smaller validation targets are workflow helpers only; they do not replace the
  aggregate closure check for promotion.

## Promotion Gates

A cleanup batch is promotable only if:

- ownership boundaries are respected
- moved files have provenance or redirect pointers
- generated files are ignored or archived intentionally
- Agda module declarations match paths
- direct and aggregate validation pass
- no theorem/receipt status is strengthened by naming or placement
- current dirty work from unrelated tasks is not reverted or overwritten

## Immediate Next Checklist

- [x] Create `.planning/repo-cleanup-manifest.md` from the current scouting
      commands.
- [x] Create `.planning/repo-cleanup-move-plan.tsv`.
- [x] Create `.planning/agda-import-map.tsv`.
- [x] Add or refresh `ROOT_INDEX.md`.
- [x] Add `Docs/LiveSurfaceIndex.md`.
- [x] Add repo-local default search-noise reduction through `.rgignore`.
- [ ] Classify tracked generated-looking files into `archive`,
      `untrack-future-generated`, or `keep tracked`.
- [ ] Decide the archive location convention:
      `Docs/archive/generated/YYYY-MM/`,
      `Docs/archive/validation/YYYY-MM/`,
      `Docs/archive/status/YYYY-MM/`, and
      `Docs/archive/todo/YYYY-MM/`.
- [ ] Compact `status.md` and `TODO.md` only after copying old blocks to an
      archive.
- [ ] Move the six-file live paper corpus into an explicit live-paper bucket or
      preserve them at `Docs/` root with the same grouping made obvious by
      `Docs/LiveSurfaceIndex.md`.
- [ ] Add `DASHI/Physics/Closure/Margin.agda`,
      `DASHI/Physics/Closure/NS.agda`,
      `DASHI/Physics/Closure/YM.agda`,
      `DASHI/Physics/Closure/Gate3.agda`,
      `DASHI/Physics/Closure/Programme.agda`, and
      `DASHI/Physics/Closure/Authority.agda` as index modules.
- [ ] Only after import maps and wrappers exist, consider one low-risk
      physical Agda lane move.

## Non-Goals

- Do not solve submodule recursion issues during the first cleanup batch.
- Do not reorganize sibling repos.
- Do not move external dependencies.
- Do not rename concepts to change mathematical status.
- Do not physically move high-use root Agda modules until wrapper/import
  migration is complete.
