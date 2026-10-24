# Agent Notes

## Source attribution is mandatory repository style

For any source-derived module, theorem surface, empirical claim, calibration,
bridge, dataset use, standard, or external construction, attach **recoverable
source attribution whenever it is available**. Do not leave externally derived
claims source-free.

Prefer the strongest stable identifier available, roughly in this order:

1. DOI (and optionally its `https://doi.org/...` resolver URL);
2. another stable scholarly/standards/archive identifier (arXiv ID/DOI,
   PMID/PMCID, ISBN, RFC, Handle, dataset ID, etc.);
3. a canonical publisher, institutional, project, or repository URL;
4. author + title + venue/year;
5. any other accurate provenance that lets a reviewer recover the source.

A missing DOI is **not** permission to omit attribution. A link, author, title,
theorem/section locator, repository commit, dataset version, or other useful
provenance is preferable to silence. Never invent metadata that is not known.

For source-derived Agda, put provenance near the top of the module and, when
source identity is structurally important, expose it through a typed
source/registry/attribution surface rather than only a prose comment. Preserve
the distinction between:

```text
external source claim / datum
        !=
DASHI formal reconstruction
        !=
DASHI cross-source inference
        !=
new DASHI theorem / synthetic extension
        !=
promotion / external adjudication
```

If a source merely motivates a new DASHI witness or theorem, cite it as source
calibration and explicitly label the new mathematics as a DASHI extension; do
not attribute repository mathematics back to the source authors.

The normative detailed policy is [`Docs/SourceAttributionPolicy.md`](Docs/SourceAttributionPolicy.md).
A source-derived change should normally fail review when recoverable provenance
was available but omitted.

## Operational notes

The pre-existing operational, Agda/Nix, proof-lane, audit, and promotion notes
remain normative and are preserved verbatim in
[`Docs/AgentOperationalNotes.md`](Docs/AgentOperationalNotes.md). **Agents must
read that file before making repository changes.** This root file is the
front-door style contract; the linked operational notes are part of the same
agent instructions.

## Navier–Stokes: canonical workset before Round files

For any NS task, run `python scripts/ns_canonical_focus.py --route <goal>`
(e.g. `R823`, `B`, `B4`), then read the primary owner first. The registry
lives in `config/ns-round-extraction-targets.json`, backed by the merged
Round extractor from PR #1232. It is routing evidence, not proof authority.

Do not grep or load the entire RNNN archive into context, infer thousands
of independent obligations from its package count, or mint a new
`RoundNNNExact.agda`/`RNNN` Lean implementation before checking the
canonical route and its existing theorem dependencies. Inspect one exact
historical declaration using `--historical-symbol` only if still needed.

For the auxiliary R823 reserve decision, reuse
`dashi_lean4/NSBControl/Rational345R823DecisionFreeze.lean` and its
literal R760/R830/Round71 sources. That source-written negative-reserve
route is NOT the unforced Clay B theorem, nor kernel-certified by metadata.
The positive B estimates and continuation have their own canonical owners.

Guard newly added numbered source files with
`python scripts/ns_canonical_focus.py --guard-new-rounds <base-ref>`;
a new numbered unit requires an explicit, independently justified
mathematical need and source attribution. Preserve old theorem-bearing
history; don't delete or mechanically alias it without same-object proof.

### 2026-10-24 NS A/B physical negative-control priority

Before proving a new B4 physical signed covariance estimate, inspect
`scripts/ns_b4_literal_padding_adversary.py` and its exact test.
The **strict** R63 dyadic classifier yields a globally smooth fixed
real shear with unbounded full-fibre signed defect under zero-mode
padding, while the literal Core-Core companion is fixed from N>=9.
If the proposed `localED` is bounded on that same physical state,
the current cutoff-uniform B4 conjecture is mathematically false.
Do not build another Round module to 'prove' it; identify the actual
ED semantics and derive a padding-invariant same-source R440 estimate.

For whole-space A, reuse the existing
`NSTriadKNEuclideanCanonicalProjectedInteractionExact` local
divergence-form/Leray constructor and
`NSWholeSpaceFiniteConvolutionSingleLimitExact` energy-square
quadrature. The unpaid theorem is the *actual* space-to-Fourier
transform on one continuum NS solution, with the low/high physical
envelope and continuation. Never use an arbitrary `Set`-typed
transform equality or a free-variable positive R9 Gram majorant
as proof.