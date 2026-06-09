# Papers 2-4 TeX Conversion Scope

Date: `2026-05-29`
Owner: Worker A6
Scope: scoping only; no TeX conversion performed.

## Reference Pattern: Paper 1

Paper 1 has the complete arXiv-oriented source pattern:

- Canonical Markdown working source:
  `Docs/PaperDraftWorkingFolder/Paper1_Manuscript.md`
- TeX submission source:
  `Docs/PaperDraftWorkingFolder/Paper1_Manuscript.tex`
- Bibliography:
  `Docs/PaperDraftWorkingFolder/Paper1_References.bib`
- Build artifact:
  `Docs/PaperDraftWorkingFolder/build/Paper1_Manuscript.pdf`
- Submission support:
  `Docs/PaperDraftWorkingFolder/ArxivSubmissionChecklist.md`
  and `Docs/PaperDraftWorkingFolder/ArxivSubmissionMetadata.md`

This is the right target pattern for any paper that is being prepared for
near-term arXiv upload. The TeX source is not merely a formatting duplicate:
it encodes theorem environments, long tables, bibliography handling, and a
known `latexmk` route.

## Paper 2 Assessment

Current source: `Docs/Paper2GRGeometryDraft.md`

Paper 2 is a complete working Markdown draft with a clear target journal
(`Classical and Quantum Gravity`), a receipt-anchor table, a consolidated
claim ledger, and mature Gate 4/Wald/Friedmann boundary language. It is closer
to submission than Paper 4 and has enough theorem/receipt structure that TeX
conversion would be useful before arXiv submission.

Conversion status recommendation: **convert to TeX next, but not inside this
scoping task**.

Rationale:

- Paper 2 already has referee-facing structure and target venue.
- Its long receipt-anchor tables need TeX layout decisions similar to Paper 1.
- The GR/Friedmann claim-governance language should be frozen into a buildable
  submission source before public circulation.
- Conversion should happen after the final Paper 2 receipt-audit pass, so the
  Markdown-to-TeX step does not preserve stale wording.

## Paper 3 Assessment

Current source: `Docs/Paper3YangMillsGeometryDraft.md`

Paper 3 is also mature enough to convert soon. It is a standalone draft with
an abstract, Theorem 3.1, a concrete finite curvature component, and explicit
Clay/YM non-promotion flags. It is shorter and narrower than Paper 2, which
makes it a good candidate for a low-risk TeX conversion after the numerical
curvature section is finalized.

Conversion status recommendation: **convert to TeX next, alongside or just
after Paper 2, but not inside this scoping task**.

Rationale:

- Paper 3 has a compact theorem-bearing structure suitable for TeX.
- The finite curvature computation should be prominent in a submission-format
  theorem/proof layout.
- The fail-closed Clay boundary must remain visible in abstract, theorem, and
  conclusion; TeX conversion is a good point to enforce that globally.
- Conversion should wait until the requested Paper 3 strengthening pass has
  merged the depth-9 curvature value directly into the main draft.

## Paper 4 Assessment

Current source: `Docs/Paper4PhysicalHilbertSkeleton.md`

Paper 4 is a substantive Markdown draft, but it remains a construction-route
paper rather than a near-submission manuscript. Its central content is the
finite Stone/GNS/physical Hilbert boundary, and the most important next edit is
conceptual: strengthen the physical completion boundary and its relation to
the Yang-Mills Hamiltonian blocker.

Conversion status recommendation: **defer TeX conversion; leave as Markdown
draft for now**.

Rationale:

- The file is still named as a skeleton even though it now contains substantive
  sections.
- The physical Hilbert completion boundary needs another prose and receipt
  consistency pass before layout work is useful.
- Paper 4 depends on cross-gate language with Papers 3 and 8, so freezing it
  into TeX now would likely create churn.
- It is not the next arXiv candidate; Markdown is the better editing surface.

## Decision

Do not convert any file as part of this Worker A6 scoping task.

Recommended next action:

1. Convert Paper 2 to TeX after its final receipt-audit pass.
2. Convert Paper 3 to TeX after the depth-9 curvature section is merged into
   the main draft.
3. Leave Paper 4 as Markdown until the Hilbert completion boundary and
   cross-gate Yang-Mills Hamiltonian blocker language are stable.

Near-term priority order for TeX conversion:

```text
Paper 2 first
Paper 3 second
Paper 4 deferred
```
