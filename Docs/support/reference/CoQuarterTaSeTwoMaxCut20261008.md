# Co1/4TaSe2 physical-identification max-cut — 2026-10-08

## Closed repository-side seams

- Co1/4TaSe2 lane is imported by `DASHI.Physics.CondensedMatter.Everything`.
- BNS metadata is pinned to `P6_3'/m'm'c`, BNS `194.268`, magnetic Hall symbol `-P 6c' 2c`.
- An exact-audit program now requires an independently acquired operation table and compares every `(Seitz triplet, antiunitary parity)` pair; it fails closed on any mismatch.
- The existing Bloch validator now checks the magnetic Seitz composition law and the sewing-matrix cocycle up to the unavoidable lattice-gauge phase, in addition to Hamiltonian covariance and nodal-plane degeneracy.
- A raw Igor-wave ingestion path now hashes and decodes deposited `.ibw` files without guessing channel semantics or calibration.
- The Co ARPES lane consumes the generic repository ARPES promotion boundary: reported spectra and symmetry do not automatically become an exact intensity witness.
- Twistronics cross-pollination is structural only; magic-angle/moire mechanisms are not identified with magnetic-sublattice exchange.

## Surviving literal leaves

1. **Independent magnetic operation authority** — acquire/store an independent BNS 194.268 magCIF/operation table and run `scripts/co_tase2_bns_operation_audit.py`. Matching metadata alone does not pay this leaf.
2. **Material Hamiltonian** — replace the four-band symmetry toy with a Ta/Se/Co orbital Hamiltonian including SOC and exchange, with parameters from DFT/Wannierisation or explicit quantitative fit.
3. **Raw ARPES payload** — the UCF STARS landing page is public and states that the minimal replication dataset consists of Igor binary waves, but the native payload endpoint returned HTTP 403 to the 2026-10-08 execution environment. Acquire the payload externally, then run `scripts/co_tase2_arpes_ibw_ingest.py`.
4. **Calibration and observation map** — bind wave axes, photon energy, spin/polarization channels, `k_parallel`, `k_z`, resolution and matrix-element/final-state assumptions into a literal spectral observer.
5. **Quantitative same-object validation** — fit/forward-model the material Hamiltonian against the literal spin-resolved intensity data with uncertainties and held-out residual receipts.
6. **Kernel/runtime receipts** — run Agda on the umbrella and the Python numerical validators in an environment with Agda, Gemmi, NumPy, SciPy and igor2.

## Stopping rule

Do not mark physical identification complete until leaves 1–5 are literal receipts. The repository-side representation and acquisition machinery is now present; the remaining blockers require external magnetic-operation/data authority or material-specific computation, not another abstract symmetry layer.
