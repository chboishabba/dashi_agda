# Multiscale MDL cross-pollination

The shared exact machine is a scale-indexed carrier with projection/lift, exact residual reconstruction, a scale-compatible kernel, an explicit symmetry action, and coarse-plus-residual MDL accounting. The domains below instantiate that machine differently; they are not identified.

## Canonical ternary seam

`DASHI.Foundations.SSPTritCarrier` supplies the canonical `-1, 0, +1` carrier. `DASHI.Interop.MultiscaleMDLCrossPollination` factors it into support and gated sign:

- `0`: support absent;
- `+1`: support present, positive polarity;
- `-1`: support present, negative polarity.

The sign value is redundant when support is absent. Canonicalisation quotients that redundancy while preserving the decoded trit. This is the common exact seam behind mask/sign coding, sparse signed fields, and orientation/twist payloads.

## Lane readings

### Codec

Carrier: structured trit residual planes or symbol blocks. Residual: support mask, gated sign, and prediction detail. Symmetry: sign inversion, spatial transforms, dictionaries, or warp equivalence. Authority comes from bitrate, regret, speed, memory, and rate-distortion measurements.

### DNA

Carrier: admissible CAGT traces with grammar and biochemical state. Residual: fine sequence choice beyond a projected admissible state. Symmetry: complement, reverse-complement, and grammar-preserving actions. The ternary layer is an optional structural intermediary; DNA is not reduced to three bases.

### Wave / quantum branch

Carrier: phase/coherence amplitudes on a selected reversible sector. Residual: phase or coherence detail omitted by coarse observation. Symmetry: phase action and reversible evolution. A wave lift does not make a contractive kernel unitary; projection/measurement and reversible evolution remain distinct.

### Lie and transform actions

Carrier: a state with a typed finite-group or Lie-group action. Residual: orbit-local coordinate or representation detail. Affine, rigid, gauge, atomic, and exploded transforms belong here as selected actions plus residuals, not as new primitive ontologies.

### Sparse twist / vorticity

Carrier: sparse support plus signed orientation or circulation payload. Residual: unresolved filament, twist, or local-frame detail. Support/sign factorisation prevents oppositely oriented structure from being silently discarded. A sparse twist proxy is not itself a vorticity-closure theorem.

## Cross-lane transport

Transport requires an explicit scale-indexed map satisfying projection compatibility and kernel compatibility. Vocabulary overlap is insufficient. In particular:

- codec MDL does not automatically equal physical action;
- a DNA complement action does not establish gauge symmetry;
- wave interference does not make every pruning step quantum evolution;
- a group orbit quotient does not preserve a metric without an isometry theorem;
- sparse twist reconstruction does not imply continuum vorticity control.

## Hybrid metrics

The prefix ultrametric governs shared-branch refinement and `369` address geometry. Applications may additionally use geometric, analytic, semantic, or observational terms. A weighted hybrid metric is a separate declared structure with separate non-expansion, contraction, and calibration obligations. Results for the pure prefix ultrametric do not automatically transfer.

## Synthesis

The reusable unit is:

> coarse state + gated residual + symmetry action + admissibility/MDL receipt

The carrier fixes meaning. The receipts fix what has actually been proved or measured.
