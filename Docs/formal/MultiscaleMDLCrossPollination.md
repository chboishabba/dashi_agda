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
`DASHI.Foundations.SSPTritCarrier` is used as the canonical `-1, 0, +1` surface. The new interop module gives it an exact support/sign factorisation:
- `0` has no support;
- `+1` has support and positive polarity;
- `-1` has support and negative polarity.
The sign fibre is gated: when support is absent, its stored value is redundant. Canonicalisation quotients that redundancy while preserving decoded trits. This is the exact common seam behind mask/sign entropy coding, sparse signed fields, and orientation/twist payloads.
## Lane-specific readings
- carrier: structured trit residual planes or symbol blocks;
- residual: support mask, gated sign, and prediction detail;
- symmetry: sign inversion, spatial transforms, dictionaries, or warp equivalence;
- evidence: bitrate, regret, speed, memory use, and rate-distortion benchmarks.
MDL is literal code-length accounting here, but Shannon optimality still requires a probability model and Kraft/regret proof.
- carrier: admissible CAGT traces with grammar and biochemical state;
- residual: the fine sequence choice beyond a projected admissible state;
- symmetry: complement, reverse-complement, and grammar-preserving actions;
- evidence: biochemical constraint satisfaction, synthesis/sequencing performance, and effective information density.
The ternary layer is an optional structural intermediary. DNA is not reduced to three bases, and codec efficiency does not establish biological function.
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
- carrier: sparse support plus signed orientation or circulation payload;
- residual: unresolved filament, twist, or local frame detail;
- symmetry: orientation reversal, frame action, or local transport;
- evidence: reconstruction error, enstrophy/circulation diagnostics, conservation defects, and solver benchmarks.
Support/sign factorisation prevents negative or oppositely oriented structure from being silently lost. A sparse twist proxy is not by itself a vorticity-closure theorem.
Transport between lanes requires an explicit scale-indexed map satisfying both:
- projection compatibility;
- kernel compatibility.
Vocabulary overlap is insufficient. In particular:
- a DNA complement action does not establish a gauge symmetry;
- wave interference does not prove that every pruning operation is quantum evolution;
- a Lie orbit quotient does not preserve an empirical metric unless an isometry theorem is supplied;
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
