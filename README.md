## Start Here

This repo is a formal-and-bridge workspace around the DASHI program.

> **Source attribution is repository style, not optional decoration.** When a
> module, theorem surface, empirical claim, calibration, bridge, dataset use,
> standard, or external construction comes from an identifiable source, attach
> recoverable provenance wherever available. Prefer a stable DOI or comparable
> identifier; otherwise use a canonical link, author/title/venue, theorem or
> section locator, repository commit, dataset ID/version, or the best accurate
> attribution available. **No DOI does not mean no citation.** Do not fabricate
> missing metadata.

For source-derived Agda, provenance should normally be visible near the module
header and should be typed into a source/registry/attribution surface when the
source identity matters downstream. Keep source claims separate from DASHI
reconstruction, cross-source inference, synthetic witnesses/new theorems, and
promotion/adjudication claims.

See **[`Docs/SourceAttributionPolicy.md`](Docs/SourceAttributionPolicy.md)** for
the normative repository policy and preferred identifier order.

### Repository orientation and current status

The previous full README, including the detailed current lane/status orientation,
is preserved verbatim at
**[`Docs/RepositoryLongformREADME.md`](Docs/RepositoryLongformREADME.md)**.
Serious readers should continue there after reading the source-attribution rule
above.

Repository automation follows a resource-conscious, newest-run-wins policy;
see [`.github/WORKFLOW_PHILOSOPHY.md`](.github/WORKFLOW_PHILOSOPHY.md) before
adding or broadening a GitHub Actions workflow.

The high-level claim classes remain:

- `proved`: canonical Agda theorem spine and specifically discharged closure claims;
- `bridge`: connections from formal surfaces to interpretations without claiming full derivation;
- `packaging`: summaries that assemble existing lanes without strengthening them;
- `empirical`: data/measurement-facing surfaces that remain explicitly bounded;
- `speculative`: roadmap or intuition surfaces that are not current repo claims.
