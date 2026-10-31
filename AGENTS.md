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


## Native proof-symbol snowball for active SAT/ETH max-cut

For the OpenAI SAT/ETH integration, **discover before writing a new proof**.
The authoritative [39 exact remaining lemma/certificate register](docs/superpowers/plans/2026-10-31-openai-math-exact-lemma-maxcut-ledger.md),
[175 prioritized symbol-search terms](docs/superpowers/plans/2026-10-31-local-symbol-snowball-terms.json),
and [workstation-agent workflow](docs/superpowers/plans/2026-10-31-local-symbol-snowball-agent.md)
are maintained on the existing Agda #1212 integration branch.
Run `scripts/run_openai_math_symbol_snowball.py` against the native
`dashi-repo` semantic index and, optionally, the sibling Lean repository.
Do **not** implement a competing symbol database, redefine the original
circuit evaluator or unique-gate proof, or treat a similar name/number/DA51
or QID as a kernel-verified same-object theorem.

The Agda Golden proofs and Lean downstream remain distinct authorities.
The original source-written P1/P2 and staged Lean P3/P4 require exact-head
compiler acceptance and a verified real executable source-to-machine
translation with time and **every-prefix** space costs.
No CI is required for this research workflow; executable Python checks
do not establish Lean or Agda kernel acceptance. Preserve the existing
attribution and operational policies above, including ESD import-only
and original Ibrahim Monster 3B proof ownership.
