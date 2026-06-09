# Paper 1 arXiv Submission Checklist

Date: 2026-05-29
Owner note: Worker A6, package validation/prep only.
Candidate source: `paper1-submission-candidate` tag (`1ef8e39`).

## Build Verification

- Build command, from repository root:
  `latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=Docs/PaperDraftWorkingFolder/build Docs/PaperDraftWorkingFolder/Paper1_Manuscript.tex`
- Clean tag audit location:
  `/tmp/dashi_paper1_tag_audit`
- Clean tag validation result: passed on 2026-05-29.
- Output PDF:
  `Docs/PaperDraftWorkingFolder/build/Paper1_Manuscript.pdf`
- PDF metadata from `pdfinfo`: 31 pages, letter page size, 868677 bytes, PDF 1.7.
- SHA256:
  - TeX: `0f86084ab1c72f960470d3d2c9ba4d00396266be4427298a7e9aa8f5ff02b8de`
  - BibTeX: `59ef5217623b3d083af0d37e871fd132357315a8bcae7d246086ece0de4a0460`
  - PDF: `2f6fde956678be3f82bc9eb7b5faa02b2aea511c5ddd7e94a3a8cab72b870a4f`
- Important path convention: compile from the submission root. The TeX source
  uses root-relative figure and bibliography paths under
  `Docs/PaperDraftWorkingFolder/...`; arXiv documents that top-level files may
  live in a subdirectory, but compilation is done from the root of the uploaded
  submission directory.
- Final log check found no unresolved citations, undefined references, missing
  figures, LaTeX errors, fatal errors, or rerun-required warnings.
- Non-blocking build warnings: dense tables produce underfull hbox warnings and
  one long path in the empirical section is overfull by about 17pt.
- Flattened arXiv source archive prepared at:
  `Docs/PaperDraftWorkingFolder/build/paper1-submission-candidate-arxiv-source.tar.gz`.
- Flattened archive SHA256:
  `b1092ebf4c68d7dd0547ee92102e0da07ff4abcd2edf2d0209c4cc79ce547573`.
- Clean flattened-package build command:
  `cd /tmp/dashi-paper1-arxiv-test && latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build Paper1_Manuscript.tex`.
- Clean flattened-package result: passed; output PDF is 31 pages and has
  SHA256 `bf70ab306b565b2086b9dffc5d07404535e3c2e9a6871cfb325343aceed73e48`.

## Source Package Manifest

Required files for the current TeX build:

- `Docs/PaperDraftWorkingFolder/Paper1_Manuscript.tex`
- `Docs/PaperDraftWorkingFolder/Paper1_References.bib`
- `Docs/PaperDraftWorkingFolder/figures/paper1-origin-figures/dashifine_ultrametric_grid_frame0.png`
- `Docs/PaperDraftWorkingFolder/figures/paper1-origin-figures/dashifine_ultrametric_tree_frame0.png`
- `Docs/PaperDraftWorkingFolder/figures/paper1-origin-figures/dashitest_tree_diffusion_tree_band_quotient.png`
- `Docs/PaperDraftWorkingFolder/figures/paper1-origin-figures/dashirtx_refinement_frame_100.png`
- `Docs/PaperDraftWorkingFolder/figures/paper1-origin-figures/fracdash_rank4_basin_branch_density.png`
- `Docs/PaperDraftWorkingFolder/figures/paper1-origin-figures/dashitest_tree_diffusion_rollout_mse.png`

Present in the candidate tag but not referenced by the current TeX build:

- `Docs/PaperDraftWorkingFolder/figures/PublicPaperNarrativeFlow.pdf`
- `Docs/PaperDraftWorkingFolder/figures/paper1-origin-figures/paper1_origin_diagnostics_plate.png`

Optional local audit/context files, not required for arXiv TeX compilation:

- `Docs/PaperDraftWorkingFolder/ArxivSubmissionChecklist.md`
- `Docs/PaperDraftWorkingFolder/ArxivSubmissionMetadata.md`
- `Docs/PaperDraftWorkingFolder/README.md`
- `Docs/PaperDraftWorkingFolder/ClaimLedger.md`
- `Docs/PaperDraftWorkingFolder/SourceLedger.md`
- `Docs/PaperDraftWorkingFolder/EarlyOriginThreadReference.md`

Do not include generated build auxiliaries in the arXiv source bundle. The
candidate builds from TeX plus `.bib` plus figures. A generated `.bbl` may be
included only if final upload testing shows arXiv does not resolve the BibTeX
step from the `.bib` file.

The flattened source archive uses this arXiv-friendly root-level layout:

- `Paper1_Manuscript.tex`
- `Paper1_References.bib`
- `figures/PublicPaperNarrativeFlow.pdf`
- `figures/paper1-origin-figures/*.png`

The flattened archive rewrites only local figure and bibliography paths; it
does not alter manuscript content. Compile it from the extracted package root.
Invoking `Paper1_Manuscript.tex` by an absolute path while the shell is outside
the package root will break relative figure lookup.

## Upload Metadata

See `Docs/PaperDraftWorkingFolder/ArxivSubmissionMetadata.md` for the title,
author string, abstract, comments, and category handoff.

- Verified TeX title: `DASHI: A Constructive Carrier Derivation Program for Physics-Unification Structures`
- Verified TeX subtitle: `Ultrametric Carrier Geometry, Projection-Defect Semantics, and Mechanized Closure Frontiers`
- Verified TeX author string: `DASHI project`
- Verified TeX date: `Draft of 2026-05-17`
- Verified abstract source: `Paper1_Manuscript.tex`, `\begin{abstract}` block.
- Recommended primary category: `math-ph`.
- Recommended cross-list: `hep-th`, if the submitter has a concrete reason to
  reach formal high-energy-theory readers. arXiv warns against excessive or
  inappropriate cross-listing and says bad cross-lists can be removed.
- Not recommended as primary: `physics.gen-ph`.

Category rationale checked against arXiv taxonomy on 2026-05-29:

- `math-ph` fits the manuscript's mathematical-physics framing: typed carrier
  geometry, projection-defect semantics, filtered/operator surfaces, and
  rigorous closure-frontier governance.
- `hep-th` is plausible only as a cross-list because the paper discusses formal
  QFT-facing target surfaces, operator algebras, gauge curvature, and
  high-energy-theory adjacent obstruction semantics. It should not be primary
  unless the submitter wants to frame the article mainly for formal QFT/string/
  supersymmetry/supergravity readers.
- `physics.gen-ph` remains weak because arXiv's taxonomy currently lists only
  "Description coming soon" for that category.

Sources checked:

- `https://arxiv.org/category_taxonomy`
- `https://info.arxiv.org/help/submit_tex.html`
- `https://info.arxiv.org/help/cross.html`

## Pre-Submission Gates

- Manager A content/build confirmation: complete for this tranche.
- Clean build from `paper1-submission-candidate`: complete.
- Confirm no forbidden terminal claims were introduced after this validation:
  complete for the candidate tag; the manuscript keeps new physics, accepted
  residual, continuum GR/YM/NS, GRQFT, and completed-unification claims
  fail-closed.
- Confirm title, author identity/affiliation details, date, abstract, keywords,
  and acknowledgements are final: pending human submitter.
- Confirm flattened arXiv source bundle compiles in a clean temporary
  directory: complete.
- Account-authenticated arXiv upload, PDF preview review, license selection,
  final submitter certification, endorsement checks, and any cross-list action:
  external to this audit and still pending.
- Git tag: `paper1-submission-candidate` points to the dedicated submission
  package commit; this audit did not submit to arXiv.
