# Live Surface Index

Date: `2026-06-10`
Declared surface level: `router`

This is the shortest serious map of which files are live, which files are
support, and which files are historical or prep surfaces.

## Root Entry Points

- `README.md`: top-level repo orientation.
- `ROOT_INDEX.md`: root router for live surfaces and cleanup policy.
- `Docs/RepoGuide.md`: human guide to repo structure and reading order.
- `Docs/AgdaValidationTargets.md`: focused validation policy.
- `architecture.md`: architecture and diagram entrypoint.

## Live Paper Corpus

These are the only active manuscript homes in the current paper corpus:

- `Docs/Paper1NavierStokesClayDraft.md`
- `Docs/Paper3YangMillsClayDraft.md`
- `Docs/Paper8UnificationDraft.md`

These are the shared live support surfaces for that corpus:

- `Docs/SupportCompendium.md`
- `Docs/PaperCommonCitationLedger.md`
- `Docs/PaperCommonNotationGlossary.md`

Historical or source-feeding paper material is still useful, but it is not a
coequal live manuscript unless it is one of the six files above.

## Live Support And Governance Docs

Use these as current support routers rather than browsing all of `Docs/`:

- `Docs/RepoStructureCleanupRoadmap.md`
- `Docs/CurrentGateStatus.md`
- `Docs/ClosurePipeline.md`
- `Docs/CrossPaperReceiptIndex.md`
- `Docs/CanonicalProofSpine.md`
- `Docs/CompleteVerifiedPhysicsUnificationRoadmap.md`

## What Is Not A Live Entry Surface

These categories are real repo material, but they should not be treated as the
default first files for a new reader:

- section drafts and skeletons such as `Paper6Section*.md`, `Paper8Section*.md`,
  and `Paper*Skeleton*.md`
- working folders such as `Docs/PaperDraftWorkingFolder/`
- authority packets under `Docs/ExternalAuthorityReceipts/`
- worker packets under `Docs/worker-packets/`
- historical planning under `.planning/`
- generated outputs, caches, and archives

## Practical Search Policy

Default code/doc search should focus on:

- `DASHI/`
- live root docs
- the six live paper-corpus files above

Default search should usually ignore:

- submodules
- generated outputs
- archived docs
- external authority packets
- working folders

The repo-local `.rgignore` now encodes that default search policy.
