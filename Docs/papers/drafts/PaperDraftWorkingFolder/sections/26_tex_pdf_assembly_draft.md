# TeX/PDF Assembly Draft

Status: Lane 6 assembly plan; non-promoting; no TeX build performed.

This file defines the assembly surface for converting the Paper 1 Markdown
manuscript into a TeX/PDF artifact after the section writers and integrator
stabilize the claim surface. It intentionally does not edit the main manuscript
or create a TeX skeleton yet, so it can coexist with active writing lanes.

## Assembly Principle

The first complete deliverable should remain:

```text
Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_Manuscript.md
```

TeX should be generated only after the Markdown manuscript has been integrated
against `ClaimLedger.md`. Markdown is the lower-conflict merge surface for
parallel workers; TeX is the production surface for figures, bibliography,
appendices, and PDF layout.

Every positive claim in the TeX/PDF artifact must cite one of:

- an allowed surface in `Docs/papers/drafts/PaperDraftWorkingFolder/ClaimLedger.md`;
- a source entry in `Docs/papers/drafts/PaperDraftWorkingFolder/SourceLedger.md` when the
  sentence is provenance, background, or literature positioning;
- a blocker, diagnostic, request-only, or future-work statement explicitly
  marked as non-promoting.

## Target File Layout

Recommended post-integration layout:

```text
Docs/papers/drafts/PaperDraftWorkingFolder/
  Paper1_Manuscript.md                  # canonical authoring surface
  Paper1_Manuscript.tex                 # generated/assembled TeX surface
  Paper1_References.bib                 # bibliography stub surface
  figures/
    PublicPaperNarrativeFlow.svg
    PublicPaperNarrativeFlow.pdf
    appendix/
      PhysicsUnificationMap.svg
      PhysicsRealityRoadmap.svg
      CanonicalProofSpine.svg
      HEPDataResidualCoordinationMap.svg
      ObservableSignatureGaugeEntryRound.svg
      TRAINING_DYNAMICS.svg
      RepoMetasystem.svg
  build/
    Paper1_Manuscript.pdf
```

If the repo later adopts a top-level `paper/` directory, this working-folder
layout can be copied or symlinked into that surface. Until then, keeping the
paper artifact under `Docs/papers/drafts/PaperDraftWorkingFolder/` preserves the existing
paper-writing boundary.

## Manuscript Assembly Map

The recommended Markdown-to-TeX order is:

| TeX section | Markdown source | Assembly note |
|---|---|---|
| Title and abstract | `Paper1_Manuscript.md`; `sections/01_intro_conclusion.md`; `sections/08_constructive_toe_framing.md` | Title must foreground physics unification; governance is enforcement architecture. |
| Introduction | `sections/01_intro_conclusion.md`; `sections/08_constructive_toe_framing.md` | Include the thesis: constructive physics-unification with explicit closure frontier, not completed TOE. |
| Background and related work | `sections/07_provenance_lit.md`; `sections/12_formal_methods_positioning.md`; `sections/13_math_prof_outreach_synthesis.md`; `sections/14_math_prof_outreach_update.md` | Literature/provenance only; no source here promotes a theorem. |
| Core constructive architecture | `sections/02_governance_method.md`; `sections/09_abstraction_layer.md`; `sections/15_cross_domain_variational_spine.md` | Present typed governance as part of the physics substrate, not as a separate paper thesis. |
| Mathematical constructions | `sections/03_formal_core.md`; `sections/10_g3_graded_quotient_gap.md` | G2/G3/G6/E8 positives must cite allowed ClaimLedger surfaces. |
| Empirical contact | `sections/05_empirical_appendix.md` | Preserve bounded W3 positive receipt versus strict-DY failure. |
| Obstruction frontier | claim-boundary content from `ClaimLedger.md`; `sections/11_physics_language_containment.md`; `sections/18_claim_lattice_cross_domain_risks.md` | Table-driven reviewer-facing gap section. |
| Compression and semantic geometry | `ArchiveTopicIntegrationPlan.md`; `sections/07_provenance_lit.md`; relevant UFT prose from current manuscript | Route UFT-C, Hensel/p-adic, Markov-after-quotient to appendix or late main text. |
| Cross-domain outlook | `sections/15_cross_domain_variational_spine.md`; `sections/17_braid_memory_current_event_boundary.md`; `sections/18_claim_lattice_cross_domain_risks.md` | Future-looking and explicitly non-promoting. |
| Reproducibility | `SourceLedger.md`; validation commands from current integration notes | Include Agda/PlantUML/grep commands and repo paths. |
| Conclusion | `sections/01_intro_conclusion.md`; `sections/08_constructive_toe_framing.md` | End on constructive physics-unification architecture with explicit closure frontier. |
| Appendices | `sections/06_gr_future_work.md`; `sections/16_outreach_email_research_note.md`; archive location reference; large diagrams | Put GR, outreach, current-event, and long-archive navigation outside the main positive inventory. |

## Figure Inclusion Rules

Main text figure:

- `Docs/PublicPaperNarrativeFlow.svg`
- `Docs/papers/drafts/PaperDraftWorkingFolder/figures/PublicPaperNarrativeFlow.pdf`

This should be Figure 1. Caption should say it is a reader-facing narrative
map of Paper 1: physics unification thesis, constructive substrate, inhabited
surfaces, empirical contact, explicit obstruction frontier, and routed future
material. The caption must not say the diagram proves unification.

Appendix-only figures:

- `Docs/PhysicsUnificationMap.svg`
- `Docs/PhysicsRealityRoadmap.svg`
- `Docs/CanonicalProofSpine.svg`
- `Docs/HEPDataResidualCoordinationMap.svg`
- `Docs/ObservableSignatureGaugeEntryRound.svg`
- `Docs/TRAINING_DYNAMICS.svg`
- `Docs/RepoMetasystem.svg`
- `Docs/WorkerCoordinationMap.svg`

Reason: these are valuable for internal traceability and reviewer audit, but
they are dense and repo-native. They should not compete with the main Paper 1
narrative figure.

Figure handling recommendation:

- Keep SVG as the canonical editable/rendered vector source.
- For `pdflatex`, convert SVG to vector PDF and embed the PDF; do not embed
  PNG except as a last-resort raster fallback.
- Keep PlantUML sources as canonical editable figure sources.
- Re-render all top-level diagrams before PDF assembly:

```bash
./scripts/render_docs_diagrams.sh
rsvg-convert -f pdf \
  -o Docs/papers/drafts/PaperDraftWorkingFolder/figures/PublicPaperNarrativeFlow.pdf \
  Docs/PublicPaperNarrativeFlow.svg
```

## Bibliography Stub Categories

`Paper1_References.bib` should be created only after the integrator approves
the final section order. Suggested categories:

| Category | Purpose |
|---|---|
| Proof assistants and mechanized mathematics | Agda, Coq, Lean, dependent type theory, inhabited versus uninhabited proof surfaces. |
| Proof-carrying artifacts and certified workflows | Position receipts, witnesses, and promotion gates as proof-carrying structures. |
| p-adics and ultrametrics | Background for valuations, filtrations, UFT-style refinement, and Hensel/p-adic language. |
| Lattice gauge theory and Wilson loops | Background for G2-style discrete carrier/gauge schema language. |
| Inonu-Wigner contraction and filtered/graded structures | Background for G3 filtration, contraction, and associated-graded quotient obligations. |
| E8 root systems and Weyl groups | Background for E8/LILA local/upstream boundary. |
| Drell-Yan and HEPData sources | Empirical-contact references only; must remain bounded by W3/W4/W5 authority status. |
| Minimum description length and compression | Background for projection-defect, UFT, motif, and semantic compression exposition. |
| Optional future-work physics | Anyon/braid-memory citation and GR/continuum references, clearly marked as future-work context. |

Do not cite NotebookLM, chat transcripts, or worklogs as paper authority.
Those belong in `SourceLedger.md` only.

## Claim-Citation Checklist

Before TeX assembly, the integrator should verify:

- The title/abstract uses "constructive physics-unification architecture" or
  equivalent physics-unification wording, not "governance tooling" as the
  primary thesis.
- Every G2 positive statement cites
  `canonicalG2SFGCGaugeFieldSchemaExtensionReceipt` or
  `noRemainingG2SFGCSchemaExtensionMissing`.
- Every G6 positive statement cites
  `canonicalG6OfficialTrackedCrossLaneCommutingTheorem` or
  `canonicalG6OfficialTrackedAboveThresholdCoordinateIndependence`.
- Every G3 positive statement cites
  `G3SelectedSubtractionCertifiedSupport`,
  `selectedFiniteSupportOperatorSubtractionCertifiedSupport`, or
  `selectedFiniteSupportOperatorSubtractionSupportWitnessFromCertified`.
- Every E8/LILA positive statement cites
  `integerIndexedRootsCompleteForTwoSparseShapeTheorem`,
  `canonicalE8RootEnumerationCompletePromotionBoundary`, or
  `canonicalE8UpstreamCompleteReceiptPromotionAudit`.
- Every bounded Drell-Yan positive statement cites
  `canonicalHEPDataW3ComparisonLawReceipt` or
  `canonicalDrellYanAdjacentRatioEmpiricalLaneReceipt`.
- Every strict Drell-Yan statement says the strict test fails unless it is
  explicitly describing a future missing receipt.
- Every cross-domain spine statement is schema-level and non-promoting.
- Every JMD/15 SSP/Monster statement is provenance/background only.
- No outreach document, NotebookLM answer, archive line band, or worklog is
  used as theorem authority.

## Forbidden Phrase Grep List

Run these before TeX conversion and manually inspect all hits:

```bash
rg -n -i \
  "validated|validation|completed TOE|complete TOE|solved physics|full unification|completed unification|derives Einstein|Einstein equations|Schwarzschild|continuum recovery|GRQFT|stress-energy|matter field|W3 accepted|accepted empirical authority|physical calibration|strict pass|chi2/dof <= 2|upstream E8RootEnumerationComplete|universal G6|chemistry closure|biology prediction|consciousness|DNA encodes" \
  Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_Manuscript.md \
  Docs/papers/drafts/PaperDraftWorkingFolder/sections
```

Allowed hits must be in one of these contexts:

- explicitly blocked;
- explicitly future-work;
- explicitly diagnostic-only;
- explicitly request-only;
- explicitly absent/missing;
- quoted only to forbid overclaiming.

## Proposed Build Commands

No build is run by this lane. When the integrated Markdown is ready, use one
of these routes.

Pandoc route:

```bash
mkdir -p Docs/papers/drafts/PaperDraftWorkingFolder/build
pandoc \
  Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_Manuscript.md \
  --from=gfm \
  --to=latex \
  --standalone \
  --bibliography=Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_References.bib \
  --citeproc \
  --metadata=link-citations:true \
  --output=Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_Manuscript.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=Docs/papers/drafts/PaperDraftWorkingFolder/build \
  Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_Manuscript.tex
```

Fallback direct PDF route:

```bash
mkdir -p Docs/papers/drafts/PaperDraftWorkingFolder/build
pandoc \
  Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_Manuscript.md \
  --from=gfm \
  --pdf-engine=xelatex \
  --bibliography=Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_References.bib \
  --citeproc \
  --metadata=link-citations:true \
  --output=Docs/papers/drafts/PaperDraftWorkingFolder/build/Paper1_Manuscript.pdf
```

Figure refresh and source hygiene:

```bash
./scripts/render_docs_diagrams.sh
plantuml -checkonly Docs/*.puml
git diff --check -- Docs/papers/drafts/PaperDraftWorkingFolder Docs README.md
```

Claim-surface checks:

```bash
rg -n "canonicalG2|canonicalG6|G3Selected|canonicalE8|canonicalHEPDataW3|canonicalDrellYan" \
  Docs/papers/drafts/PaperDraftWorkingFolder/ClaimLedger.md \
  Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_Manuscript.md
```

## Appendix Layout

Suggested appendices:

| Appendix | Content |
|---|---|
| A. Gate and claim matrix | Condensed positive/blocked rows from `ClaimLedger.md`. |
| B. Agda and receipt surfaces | Module names, receipt identifiers, and validation commands. |
| C. Empirical receipt details | Bounded W3 receipt, strict-DY failure, W4/W5 missing authority. |
| D. Diagrams and traceability | Appendix-only PlantUML diagrams and links to sources. |
| E. UFT/compression/provenance routing | JMD/15 SSP, Base369/trit, UFT-C, Hensel/p-adic, Markov-after-quotient, all non-promoting unless cited to exact surfaces. |
| F. Future-work boundaries | GR, braid-memory, cross-domain chemistry/biology/perception, orbit-shell/signature families. |
| G. Archive navigation | Pointer to `ArchiveRelativeLocationReference.md`, explicitly labeled as context navigation rather than authority. |

## Missing Dependencies / Unknowns

- No Paper 1-specific TeX template, journal class, or bibliography file exists
  in the working folder yet.
- `Docs/Theory.lagda.tex` and `build/latex/Book.tex` exist, but they are not
  obviously suitable Paper 1 templates without a separate template audit.
- `pandoc`, `latexmk`, `xelatex`, and BibTeX/Biber availability have not been
  checked by this lane.
- Citation keys are not assigned yet; bibliography work should follow the
  related-work lane and should not be invented from chat/worklog text.
- Final figure format depends on the chosen TeX engine. PNG fallback is safest
  for `pdflatex`; SVG can be used if the build route supports conversion.

## Lane 6 Return Summary

FORMAL MODEL: O/R/C/S/L/P/G/F

- O: Lane 6 owns TeX/PDF assembly planning only; no content sections or Agda
  files were edited.
- R: Created a Markdown-first, TeX-second assembly plan with figure,
  bibliography, appendix, build, and claim-check surfaces.
- C: Read current working-folder README, claim/source ledgers, narrative flow
  PlantUML, README diagram inventory, and existing manuscript start. Wrote only
  this assembly draft.
- S: The repo has a Markdown manuscript target and diagrams, but no dedicated
  Paper 1 TeX template or bibliography yet.
- L: Assembly map proceeds from manuscript map to figures, bibliography stubs,
  claim checklist, forbidden grep, and build commands.
- P: Proposed `PublicPaperNarrativeFlow` as the main figure and moved dense
  repo-native diagrams to appendices.
- G: Preserved the rule that every positive claim must trace to
  `ClaimLedger.md`; provenance/context sources remain non-promoting.
- F: Missing evidence is TeX tool availability, final template choice,
  bibliography keys, and final integrated section order.
