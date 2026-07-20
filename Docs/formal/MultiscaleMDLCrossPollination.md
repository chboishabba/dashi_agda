# Multiscale MDL cross-pollination

This note records the common theorem-shaped machine shared by several DASHI lanes without identifying their domain semantics.

## Shared exact machine

At scale `j`, a lane supplies:

1. a carrier `X_j`;
2. a projection `P_j : X_{j+1} -> X_j`;
3. a lift `L_j : X_j -> X_{j+1}` with `P_j (L_j x) = x`;
4. a residual `r_j(x)` and reconstruction law
   `reconstruct (P_j x) (r_j x) = x`;
5. a scale-indexed kernel commuting with projection;
6. an explicit symmetry action and orbit witness;
7. coarse and residual description costs.

This is the reusable core. It does not assert that the carriers in different domains are literally the same object.

## Canonical ternary seam

`DASHI.Foundations.SSPTritCarrier` is used as the canonical `-1, 0, +1` surface. The new interop module gives it an exact support/sign factorisation:

- `0` has no support;
- `+1` has support and positive polarity;
- `-1` has support and negative polarity.

The sign fibre is gated: when support is absent, its stored value is redundant. Canonicalisation quotients that redundancy while preserving decoded trits. This is the exact common seam behind mask/sign entropy coding, sparse signed fields, and orientation/twist payloads.

## Lane-specific readings

### Codec

- carrier: structured trit residual planes or symbol blocks;
- residual: support mask, gated sign, and prediction detail;
- symmetry: sign inversion, spatial transforms, dictionaries, or warp equivalence;
- evidence: bitrate, regret, speed, memory use, and rate-distortion benchmarks.

MDL is literal code-length accounting here, but Shannon optimality still requires a probability model and Kraft/regret proof.

### DNA

- carrier: admissible CAGT traces with grammar and biochemical state;
- residual: the fine sequence choice beyond a projected admissible state;
- symmetry: complement, reverse-complement, and grammar-preserving actions;
- evidence: biochemical constraint satisfaction, synthesis/sequencing performance, and effective information density.

The ternary layer is an optional structural intermediary. DNA is not reduced to three bases, and codec efficiency does not establish biological function.

### Wave / quantum branch

- carrier: phase/coherence amplitudes over a selected reversible sector;
- residual: phase or coherence detail omitted by coarse observation;
- symmetry: phase action and reversible evolution;
- evidence: norm preservation, interference predictions, dispersion, spectra, and measured constants.

The wave lift is a representation of the shared inference structure. It does not make a contractive kernel unitary. Projection/measurement and reversible evolution remain distinct.

### Lie and symmetry actions

- carrier: a state with a typed finite-group or Lie-group action;
- residual: orbit-local coordinate or representation detail;
- symmetry: an explicit action witness rather than an informal quotient;
- evidence: group laws, representation identities, invariant metrics, and domain-specific matching.

This is the natural home for affine, rigid, gauge, and other transform families. An atomic/exploded transform is represented as a selected action plus residual, not as a new primitive ontology.

### Sparse twist / vorticity

- carrier: sparse support plus signed orientation or circulation payload;
- residual: unresolved filament, twist, or local frame detail;
- symmetry: orientation reversal, frame action, or local transport;
- evidence: reconstruction error, enstrophy/circulation diagnostics, conservation defects, and solver benchmarks.

Support/sign factorisation prevents negative or oppositely oriented structure from being silently lost. A sparse twist proxy is not by itself a vorticity-closure theorem.

## Cross-lane transport

Transport between lanes requires an explicit scale-indexed map satisfying both:

- projection compatibility;
- kernel compatibility.

Vocabulary overlap is insufficient. In particular:

- codec MDL does not automatically equal physical action;
- a DNA complement action does not establish a gauge symmetry;
- wave interference does not prove that every pruning operation is quantum evolution;
- a Lie orbit quotient does not preserve an empirical metric unless an isometry theorem is supplied;
- sparse twist reconstruction does not imply continuum vorticity control.

## Hybrid metric refinement

The prefix ultrametric is appropriate for shared-branch refinement and exact `369` address geometry. It need not be the only metric used by an application. A domain may combine:

- an ultrametric branch/provenance term;
- a geometric or analytic norm;
- a semantic or observational distance.

Any weighted hybrid metric must be declared as a separate structure with its own non-expansion, contraction, and calibration obligations. No result for the pure prefix ultrametric is silently promoted to that hybrid metric.

## Practical synthesis

The main reusable unit is therefore:

> **coarse state + gated residual + symmetry action + admissibility/MDL receipt**

The carrier determines what the symbols mean. The receipts determine what has been proved or measured. Cross-pollination reuses the machine while retaining those distinctions.
