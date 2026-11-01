# Proof-First Repo Policy

Date: `2026-06-10`  
Declared surface level: `governance`

This policy defines the intended reader-facing shape of the repository.

The default rule is:

> if a file is not part of an explicit proof surface, it should not remain in
> the default human-visible layer of the repo.

This is a navigation rule, a drafting rule, and a cleanup rule.

## Why This Policy Exists

The repo currently mixes too many artifact classes in the same visible
directories:

- explicit theorem or proof developments
- proof-adjacent setup and background
- receipts, aggregates, and validation byproducts
- historical planning and governance state
- draft fragments and working folders
- external authority packets

That mixture harms both external readability and internal retrieval. A new
reader cannot tell which files carry the actual mathematical burden, and local
search repeatedly surfaces receipts or scaffolds instead of proof-bearing files.

The project also does not need to re-derive settled physical laws as though the
repo were writing a textbook from scratch. The physical and operator-theoretic
construction chain is standard setup. The visible surfaces should therefore be
organized around the hard open problems and the proof obligations they create.

## Core Principle

The repo should read from the outside as:

- a small set of live proof surfaces
- a bounded support layer that those proofs directly consume
- an archive layer holding provenance, historical drafts, receipts, and
  orchestration debris

The visible layer must follow the proof burden, not the total history of work.

## Repository Classes

Every repo surface should fit one of these classes.

### 1. Proof Surface

A file belongs in the visible proof layer only if it does at least one of the
following:

- states a theorem, proposition, lemma, or reduction that the current program
  relies on
- proves a theorem step or exposes the canonical formal entrypoint to such a
  proof
- acts as a current live paper whose body is directly organized around the
  proof chain

Examples:

- theorem-bearing Agda modules
- canonical proof-spine maps
- the three live paper drafts

### 2. Direct Support Surface

A file belongs in support only if a proof surface directly consumes it and the
reader may need it to interpret a proof without browsing the archive.

Examples:

- live notation glossary
- live citation ledger
- support compendium sections that are explicitly cited by live papers
- compact validation targets for current proof-bearing modules

Support is allowed, but it must remain visibly secondary to proof surfaces.

### 3. Archive Surface

A file belongs in archive if it is historically meaningful but not part of the
current proof burden.

Examples:

- receipts
- aggregates not required by a live proof
- worker packets
- old draft sections and skeletons
- audit notes, blocker maps, readiness packets, and historical submission prep
- generated logs and snapshots

Archive material is preserved for provenance. It is not a default reading path.

## Paper-Writing Consequence

The derivation chain should directly govern how papers are written.

Each paper should read in this order:

1. imported standard construction or setup
2. exact obstruction or hard interface
3. new reduction, closure mechanism, or theorem step
4. explicit claim boundary

That means:

- standard physical law or reconstruction background is imported as setup, not
  treated as the paper's novelty
- NS visible writing should center the analytic reduction chain
- YM visible writing should center the self-adjointness to continuum-transfer
  chain
- unification material should stay visible only where it carries genuine
  closure structure used by the live program

## Current Corpus Interpretation

Under this policy, the default visible paper layer is:

- `Docs/papers/live/Paper1NavierStokesClayDraft.md`
- `Docs/papers/live/Paper3YangMillsClayDraft.md`
- `Docs/papers/live/Paper8UnificationDraft.md`
- `Docs/support/live/SupportCompendium.md`
- `Docs/support/live/PaperCommonCitationLedger.md`
- `Docs/support/live/PaperCommonNotationGlossary.md`

Everything else in the paper family is presumed draft/support/archive material
unless a live proof surface directly cites it.

## Agda Consequence

The same rule applies to formal code.

Top-level human-visible Agda surfaces should be:

- theorem-bearing entry modules
- canonical lane entrypoints when they expose proof-bearing modules
- small aggregate checks that are actually used for validation

The following should not dominate the visible layer:

- receipt modules
- aggregate modules that exist only for historical bookkeeping
- stress-test or audit surfaces that no live theorem cites

If an aggregate or receipt is not needed by a current proof, it should move
into a clearly marked support or archive subfolder.

## Operational Rule For Reorganization

When reorganizing, classify first and move second.

For each file, ask:

1. Does this file carry a current proof obligation?
2. If not, is it directly consumed by a current proof surface?
3. If not, is it historically worth preserving?

Then apply:

- `yes` to 1 -> keep visible
- `no` to 1 but `yes` to 2 -> move to support
- `no` to 1 and 2 but `yes` to 3 -> archive
- otherwise -> treat as generated/noise and remove from the visible path once
  preservation policy is satisfied

## Default Visibility Policy

The default human-visible layer should contain only:

- root routers
- current proof papers
- current proof guides
- current theorem-bearing Agda entrypoints
- compact support surfaces directly cited by those proof surfaces

The default layer should not contain:

- receipts
- historical aggregates
- worker packets
- stale blocker ledgers
- long working folders
- authority dumps
- generated validation debris

## Immediate Execution Rule

The next cleanup pass should implement this policy in the following order:

1. classify proof vs support vs archive surfaces
2. move non-proof paper material out of the main visible layer
3. move receipt-like and aggregate-like Agda surfaces into lane subfolders
4. leave only proof-bearing entry modules at the visible namespace boundary
5. update routers so the default reading path exposes only proof-relevant files

No theorem claim is changed by this policy. It changes visibility and
organization so that the repo's shape matches the mathematical structure of the
program.
