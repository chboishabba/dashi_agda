# Aristotle 3/6/9 mathematics source snapshot and parity ledger

This directory records the user-supplied Aristotle mathematics archive used for the 3/6/9, sieve, Hecke, Delta, vertical-wall, Fibonacci, and Archimedes cross-pollination work on PR #555.

## Upstream attribution

The supplied upstream `README.md` states:

- “This project was edited by Aristotle.”
- GitHub attribution should tag `@Aristotle-Harmonic`.
- Commits derived from the project should include `Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>`.

This directory therefore records **Aristotle (Harmonic)** as the upstream editor of this mathematics snapshot. It does not silently infer James Michael DuPont authorship for this archive. The separate `third_party/jmdupont_wikidata_lean/` snapshot retains the James Michael DuPont / Aristotle provenance appropriate to that development.

## Snapshot identity

- supplied archive SHA-256: `2f7e5ec034d22e0d6acad21a6c5ea47ff4f1b16f190a9a60255141f5cf0aeed2`
- sorted `RequestProject/*.lean` raw-concatenation SHA-256: `b506c87807bcfe3b9ffe4c7aa2a7cba2bbdd974e0981237f8d11d64bcda1dc83`
- Lean modules: **18**
- Lean source lines: **4,302**
- named declarations inventoried: **409**

The archive contains the upstream README attribution but no license file was found in the supplied tree during intake. This repository records provenance and hashes without asserting a new license.

## Files

- `SOURCE_MANIFEST.tsv` — every Lean module, SHA-256, line count, named-declaration count, and direct imports.
- `DECLARATION_MANIFEST.tsv` — all 409 named declarations in source order.
- `PARITY_MANIFEST.tsv` — conservative module-level DASHI parity status and the exact remaining gap.

Parity status is deliberately fail-closed. “Partial” means that real theorem content has been ported, **not** that the source module is semantically complete. `unported` means exactly that. `near-core-parity` is reserved for a source whose main mathematical core is present but whose source-specific packaging/results still have named gaps.

## Scholarly provenance rule

Direct Agda ports should carry both layers when applicable:

1. **upstream source provenance** — Aristotle source module/snapshot and upstream role;
2. **primary mathematical source** — author, title, publication, DOI, or an explicit “no DOI asserted/assigned” note;
3. **DASHI contribution** — what was newly proved, transported, strengthened, or connected.

A shared cardinality or nearby theorem is never counted as source parity.
