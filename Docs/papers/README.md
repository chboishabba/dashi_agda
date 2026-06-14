# Papers Index

Date: `2026-06-14`
Declared surface level: `router`

This directory separates the paper-family materials by role so a reader does
not have to infer manuscript status from filenames alone.

## Subdirectories

- `live/`: the active paper manuscripts only
- `drafts/`: working drafts, section drafts, clay targets, and manuscript prep surfaces
- `legacy/`: older paper lanes and paper-specific support material kept mainly
  for provenance, source mining, or historical readiness context

## Current Live Corpus

- `live/Paper1NavierStokesClayDraft.md`
- `live/Paper3YangMillsClayDraft.md`
- `live/Paper8UnificationDraft.md`

The publication sequencing and old-eight-paper-to-current-corpus mapping are
tracked in:

- `PublicationRoadmap.md`

Shared live paper support has moved to:

- `../support/live/SupportCompendium.md`
- `../support/live/PaperCommonCitationLedger.md`
- `../support/live/PaperCommonNotationGlossary.md`

## Paper 8 Draft Support

The transcript-PNF / qualia boundary lane is Paper 8 support material only. It
records how ITIR/SensibLaw-style PNF over qualitative transcripts can constrain
public report structure without recovering phenomenal content:

- `drafts/Paper8QualiaTranscriptPNFSectionDraft.md`
- `../../DASHI/Interop/QualiaTranscriptPNFSemanticBridge.agda`
- `../../DASHI/Biology/ObserverPerceptualManifoldResidual.agda`

These surfaces are not inputs to the Paper 1 or Paper 3 Clay-facing
submissions.

The BT/Perelman finite-geometry lane is also Paper 8 or later satellite
support. It records constructible Bruhat-Tits product-tree formulas and
fail-closed Perelman/geometrization authority sockets:

- `../../DASHI/Physics/Closure/BTBallVolumeEntropyBoundary.agda`
- `../../DASHI/Physics/Closure/BTGaussianReducedVolumeBoundary.agda`
- `../../DASHI/Physics/Closure/BTNeckJSJGeometryAnalogueBoundary.agda`
- `../../DASHI/Physics/Closure/PerelmanRicciFlowAndGeometrizationBoundaryReceipt.agda`

These surfaces do not prove smooth Ricci flow, Perelman monotonicity, JSJ
decomposition, Thurston geometrization, or any Clay claim.

## Proof-Support Entry Points

For theorem-interface, adapter, and manifest lookups, start from the shared
support layer rather than browsing historical receipts:

- `../support/reference/AgdaValidationTargets.md`: canonical Agda frontier
  modules and aggregate check policy
- `../support/live/SupportCompendium.md`: paper-facing support synthesis,
  including theorem interfaces, adapters, and manifests
- `generated/core_papers_theorem_var_manifest.md`: generated Paper 1/Paper 3/Paper 8
  theorem-to-Agda variable map
- `generated/core_papers_theorem_var_manifest.json` and `.tsv`: machine
  readable forms of the same map

The older `generated/paper1_paper3_theorem_var_manifest.*` files are retained
as compatibility aliases while downstream references migrate to the core-paper
name.

Status wording for these surfaces is deliberately conservative: they describe
candidate proof packages that may be internally Agda-receipted/typechecked, but
remain pending peer review, external authority checks, and external acceptance.
They do not assert that any Clay problem has been solved.

Everything else under `papers/` is support, draft, or legacy material unless a
later router explicitly promotes it.
