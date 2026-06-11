# Monster / Monster-LILA External Artifact Intake

Status: external research artifact intake only.

This note records two `meta-introspector` repositories as pinned external
submodules. They are useful as historical, experimental, and implementation
context for Monster/Leech/E8/LILA-style transformer experiments, but they do
not promote any DASHI theorem, Paper 1 claim, LHC receipt, DCHoTT bridge, AQFT
surface, or GRQFT obligation.

## Submodules

| Path | Remote | Current role |
| --- | --- | --- |
| `monster` | `https://github.com/meta-introspector/monster.git` | Existing Monster/Lean/frackdash-style research artifact; reference material only. |
| `Monster-LILA` | `https://github.com/meta-introspector/Monster-LILA.git` | Leech/Conway/E8-inspired transformer experiment; reference material only. |

## Monster-LILA Intake Reading

The `Monster-LILA` README describes a transformer architecture with:

- a frozen Leech-style core `W_abs`,
- a Conway permutation over key projections,
- a trainable value projection and FFN stack,
- a resonance detector over hidden states using SVD spectra and a `137`
  sinusoidal score.

This may be relevant to future DASHI-side experimental lanes as an implementation
example for lattice-biased attention, resonance diagnostics, or geometric
inductive-bias experiments. It is not currently evidence for Paper 1, not a
proof of E8/Monster structure, and not a replacement for any typed Agda receipt.

## License Boundary

`Monster-LILA` is licensed under AGPL-3.0-or-later. The existing `monster`
repository also carries AGPL/commercial dual-license language. Treat both as
external submodules unless a future task intentionally accepts the relevant
license obligations.

Practical boundary:

- OK: cite, inspect, compare, run as a separate external artifact.
- OK: use as provenance for future non-promoting experimental notes.
- Not OK without an explicit license review: copy source into DASHI, integrate
  code into a service, or make it a required runtime dependency.

## Promotion Boundary

No DASHI promotion follows from these submodules. A future Monster/LILA receipt
would need at least:

1. a pinned submodule commit,
2. a runnable command with environment and input hashes,
3. an observation map from outputs to DASHI quantities,
4. a typed admissibility condition,
5. an explicit non-promotion or promotion gate,
6. license and redistribution notes.
