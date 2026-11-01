# Worker 6 TeX Assembly Plan: Derivation Spine

Status: Worker 6 draft only; no main TeX edits made.
Date: 2026-05-16

## Scope

This note inspects the current TeX/PDF assembly surface for adding a derivation
spine to Paper 1. It covers theorem/definition environments, diagrams,
SVG/PDF vector handling, current build command, and layout risks around
long tables and long code-like identifiers.

Files inspected:

- `Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_Manuscript.tex`
- `Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_Manuscript.md`
- `Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_References.bib`
- `Docs/papers/drafts/PaperDraftWorkingFolder/sections/26_tex_pdf_assembly_draft.md`
- `Docs/papers/drafts/PaperDraftWorkingFolder/README.md`
- `Docs/papers/drafts/PaperDraftWorkingFolder/figures/PublicPaperNarrativeFlow.pdf`
- `Docs/PublicPaperNarrativeFlow.svg`

## Current TeX Assembly State

The current manuscript is already a standalone `article` document rather than
only a generated stub. Its preamble currently loads:

```tex
\usepackage[margin=1in]{geometry}
\usepackage{graphicx}
\usepackage{amsmath}
\usepackage{booktabs}
\usepackage{longtable}
\usepackage{array}
\usepackage{hyperref}
\usepackage{xcolor}
\usepackage{enumitem}
\usepackage{microtype}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
```

The file uses one figure include:

```tex
\includegraphics[width=\linewidth]{Docs/papers/drafts/PaperDraftWorkingFolder/figures/PublicPaperNarrativeFlow.pdf}
```

It uses two `longtable` environments:

- lines around `350--359`: compact mathematical construction table;
- lines around `496--510`: obstruction frontier table.

It currently has no theorem-style package or environments:

- no `amsthm`;
- no `\newtheorem`;
- no `proof` environment;
- no `cleveref` or similar cross-reference layer.

That is acceptable for the current prose draft, but it is thin for a
derivation spine because definitions, propositions, lemmas, claim boundaries,
and obstruction statements will otherwise be encoded as ad hoc paragraphs.

## Confirmed Build Command

The current TeX source builds with `latexmk` and `pdflatex`. I compiled into a
temporary directory outside the repo to avoid changing shared build artifacts:

```bash
mkdir -p /tmp/dashi_paper_tex_check
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=/tmp/dashi_paper_tex_check \
  Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_Manuscript.tex
```

Observed result:

- build completed successfully;
- `pdflatex` was the engine;
- BibTeX ran against `Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_References.bib`;
- final temporary PDF was 10 pages;
- the checked repo-local PDF in `Docs/papers/drafts/PaperDraftWorkingFolder/build/` is also
  10 pages and was produced by pdfTeX.

Recommended current in-repo build command:

```bash
mkdir -p Docs/papers/drafts/PaperDraftWorkingFolder/build
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=Docs/papers/drafts/PaperDraftWorkingFolder/build \
  Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_Manuscript.tex
```

Tool availability observed:

- present: `latexmk`, `pdflatex`, `xelatex`, `rsvg-convert`, `plantuml`,
  `pdfinfo`;
- absent from `PATH`: `pandoc`.

Implication: the earlier Markdown-to-TeX route in
`sections/26_tex_pdf_assembly_draft.md` is not currently executable in this
environment unless `pandoc` is installed. Direct TeX-to-PDF assembly is
currently the reliable route.

## Derivation Spine Environment Needs

For a derivation spine, Paper 1 likely needs stable numbered environments for:

- definitions: carrier, projection, defect, admissible surface, filtration,
  lane action;
- propositions/theorems: positive inhabited surfaces such as G6 tracked
  commuting or G3 selected subtraction support;
- lemmas: local bridge steps inside the spine;
- assumptions or conventions: non-promoting choices and external conventions;
- obstructions: named missing primitives/tokens;
- remarks: explanatory containment notes that must not promote claims.

Small safe preamble suggestion for later integrator review only:

```tex
\usepackage{amsthm}

\theoremstyle{definition}
\newtheorem{definition}{Definition}[section]
\newtheorem{assumption}[definition]{Assumption}
\newtheorem{obstruction}[definition]{Obstruction}

\theoremstyle{plain}
\newtheorem{theorem}[definition]{Theorem}
\newtheorem{proposition}[definition]{Proposition}
\newtheorem{lemma}[definition]{Lemma}

\theoremstyle{remark}
\newtheorem{remark}[definition]{Remark}
```

This is deliberately conservative:

- `amsthm` is standard and compatible with the current `article` route;
- numbering within sections keeps a derivation spine readable;
- shared counters prevent over-numbering;
- `obstruction` as a theorem-style environment makes blockers first-class
  without making them positive theorems.

If the paper later needs stronger cross references, consider adding
`cleveref` after `hyperref`, but only after checking class/template
requirements:

```tex
\usepackage[nameinlink,noabbrev]{cleveref}
```

The current draft can also survive without `cleveref` by using explicit
phrases such as "Definition 3.1" and `\label`/`\ref`.

## Diagram And Vector Handling

Current state:

- `Docs/PublicPaperNarrativeFlow.svg` is PlantUML-generated SVG and starts as
  valid XML/SVG content with a `<?plantuml ...?>` processing instruction.
- `Docs/PublicPaperNarrativeFlow.png` exists as a raster fallback.
- `Docs/papers/drafts/PaperDraftWorkingFolder/figures/PublicPaperNarrativeFlow.pdf` exists
  and is included by the TeX source.
- `pdflatex` successfully embeds the PDF figure.

Recommended vector policy:

1. Keep `.puml` or source diagram text as the canonical editable source.
2. Keep `.svg` as the canonical rendered vector source for review.
3. Convert SVG to PDF before `pdflatex` assembly.
4. Include the PDF in TeX, not the SVG.
5. Use PNG only as a fallback when a vector conversion fails or a journal
   workflow explicitly requires raster.

Recommended refresh commands:

```bash
./scripts/render_docs_diagrams.sh
rsvg-convert -f pdf \
  -o Docs/papers/drafts/PaperDraftWorkingFolder/figures/PublicPaperNarrativeFlow.pdf \
  Docs/PublicPaperNarrativeFlow.svg
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=Docs/papers/drafts/PaperDraftWorkingFolder/build \
  Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_Manuscript.tex
```

Layout note: the current main figure is included at full line width and builds
without a TeX error. If more derivation-spine diagrams are added, prefer
single-column full-width PDF figures or appendix placement. Avoid embedding
dense multi-panel repo maps inline in the main derivation spine unless their
text remains readable at `\linewidth`.

## Long-Table And Overfull Risks

The temporary build succeeded, but the warning profile is real and should be
handled before a polished PDF pass.

Observed overfull warnings:

- `E8RootEnumerationComplete` in the mathematical construction table:
  `24.02052pt` too wide near lines `357--358`.
- table alignment near lines `350--359`: `1.0216pt` too wide.
- long identifiers in the E8/LILA paragraph near lines `413--422`:
  `116.50664pt` too wide, driven by
  `canonicalE8RootEnumerationCompletePromotionBoundary` and
  `canonicalE8UpstreamCompleteReceiptPromotionAudit`.
- `W3AcceptedEvidenceAuthorityToken` in the obstruction table near line
  `504`: `54.23201pt` too wide.
- `Chemistry/biology/perception` in the obstruction table near lines
  `507--508`: `56.89745pt` too wide.
- table alignment near lines `496--510`: `1.02162pt` too wide.

Observed underfull warnings are concentrated in the same two longtables and
in paragraphs with long `\texttt{...}` identifiers. They are not fatal, but
they indicate visibly loose columns.

Main risk drivers:

- narrow `p{...}` columns with long unbreakable `\texttt{...}` identifiers;
- slash-separated labels such as `Chemistry/biology/perception`;
- full module/receipt names placed inline in prose;
- four-column tables at 11pt with 1in margins.

Small safe TeX/layout suggestions for later integrator review only:

```tex
\usepackage{xurl}
\usepackage{tabularx}
\usepackage{ragged2e}
\usepackage{makecell}
```

Possible table pattern:

```tex
\newcolumntype{L}{>{\RaggedRight\arraybackslash}X}
\begin{tabularx}{\linewidth}{p{0.15\linewidth}LLL}
...
\end{tabularx}
```

For tables that must span pages, keep `longtable`, but widen problem columns
or shorten cell text. Since `tabularx` does not page-break by itself, do not
replace every `longtable` blindly.

For code-like identifiers, use a breakable macro rather than raw
`\texttt{...}` for long names. One conservative option is to keep prose short
and move full identifiers into a separate appendix list. If identifiers must
remain inline, a later TeX pass can introduce a breakable command such as:

```tex
\newcommand{\codeid}[1]{\texttt{\small #1}}
```

That alone reduces pressure but does not allow arbitrary breaks inside long
camel-case tokens. For production polish, prefer either:

- explicit manual breakpoints in the few worst identifiers;
- shorter display labels in main tables with full names in appendix;
- a receipt appendix using smaller type and wider table geometry.

## Recommended Derivation-Spine Assembly Shape

The derivation spine should be a short formal layer, not a full rewrite of the
paper. Suggested main-text sequence:

1. Definition: carrier tuple and surface projection.
2. Definition: projection-defect decomposition.
3. Definition: admissible claim surface.
4. Proposition: G2/G3/G6/E8 positive inventory as separately cited surfaces.
5. Obstruction: quotient/authority/upstream gaps as named residuals.
6. Proposition or Remark: empirical-contact receipt is bounded and
   non-authority-promoting.
7. Obstruction: strict-DY, W3 accepted authority, W4/W5 convention/correction.

Keep the formal statements short. Put full receipt names in nearby prose or an
appendix table. This will reduce overfull risk and make the derivation spine
readable to external reviewers.

## Immediate Risks Before PDF Polish

- `pandoc` is absent, so Markdown-to-TeX regeneration is currently blocked in
  this environment.
- The TeX source builds, but the layout has multiple overfull boxes from long
  identifiers and dense four-column `longtable` material.
- The main TeX lacks theorem/definition environments, so a derivation spine
  would currently have to be improvised unless `amsthm` environments are added
  in a later integration pass.
- Current bibliography entries are placeholders. They build, but they should
  not be treated as submission-ready references.
- Figure handling is sound for the current `pdflatex` route because the TeX
  includes a preconverted PDF. Direct SVG inclusion is not part of the current
  build path.

## Worker 6 Return

No main TeX, bibliography, figure, build artifact, or Agda source was edited.
Only this draft was written.

Confirmed current build route:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=Docs/papers/drafts/PaperDraftWorkingFolder/build \
  Docs/papers/drafts/PaperDraftWorkingFolder/Paper1_Manuscript.tex
```

Primary layout risks: two dense `longtable` environments and long unbreakable
receipt/module identifiers in `\texttt{...}`.
