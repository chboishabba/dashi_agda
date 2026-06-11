# Live Surface Index

Date: `2026-06-10`
Declared surface level: `router`

This is the shortest serious map of which files are live, which files are
support, and which files are historical or prep surfaces.

## Root Entry Points

- `README.md`: top-level repo orientation.
- `ROOT_INDEX.md`: root router for live surfaces and cleanup policy.
- `architecture.md`: architecture and diagram entrypoint.
- `Docs/ProofFirstRepoPolicy.md`: proof-first visibility rule for what should
  remain on the default human path.

## Live Paper Corpus

These are the only active manuscript homes in the current paper corpus:

- `Docs/papers/live/Paper1NavierStokesClayDraft.md`
- `Docs/papers/live/Paper3YangMillsClayDraft.md`
- `Docs/papers/live/Paper8UnificationDraft.md`

These are the shared live support surfaces for that corpus:

- `Docs/support/live/SupportCompendium.md`
- `Docs/support/live/PaperCommonCitationLedger.md`
- `Docs/support/live/PaperCommonNotationGlossary.md`

Historical or source-feeding paper material is still useful, but it is not a
coequal live manuscript unless it is one of the six files above.

Under the proof-first repo policy, draft, receipt, and archive surfaces should
move off the default reading path unless a live proof surface directly consumes
them.

## Live Support And Governance Docs

Use these as current support routers rather than browsing all of `Docs/`:

- `Docs/support/README.md`
- `Docs/RepoStructureCleanupRoadmap.md`
- `Docs/support/reference/RepoGuide.md`
- `Docs/support/reference/AgdaValidationTargets.md`
- `Docs/support/reference/CurrentGateStatus.md`
- `Docs/support/reference/ClosurePipeline.md`
- `Docs/support/reference/CanonicalProofSpine.md`
- `Docs/roadmaps/CompleteVerifiedPhysicsUnificationRoadmap.md`

## What Is Not A Live Entry Surface

These categories are real repo material, but they should not be treated as the
default first files for a new reader:

- section drafts and skeletons such as `Paper6Section*.md`, `Paper8Section*.md`,
  and `Paper*Skeleton*.md`
- working folders such as `Docs/papers/drafts/PaperDraftWorkingFolder/`
- authority packets under `Docs/archive/authority/ExternalAuthorityReceipts/`
- worker packets under `Docs/archive/worker-packets/`
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
- legacy paper lanes
- archived docs
- external authority packets
- working folders

The repo-local `.rgignore` now encodes that default search policy.
