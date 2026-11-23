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
