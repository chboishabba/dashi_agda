# NS369 independent similarity certificate replay

27 November 2026. Companion to scripts/ns369_similarity_reconstruct.py and
ns369_similarity_certificate.py. Original Alpoge–Buckmaster equation and
certificate remain authoritative; DASHI independent trial basis is not their
published certificate. Existing exact adjoint identity and scalar-budget
consumer reused.

Run from repository root (no CI requested):

```sh
OPENBLAS_NUM_THREADS=1 python scripts/ns369_similarity_reconstruct.py --level 1 --seconds 90 --out Artifacts/ns369_similarity_candidate.json
OPENBLAS_NUM_THREADS=1 python scripts/ns369_similarity_certificate.py Artifacts/ns369_similarity_candidate.json --seconds 90 --radius 2 --cells 2
```

Replay rejects zero or still-forced candidates, reconstructs the same signed
basis, solves a normalized least-residual physical formal adjoint with
independent pressure coefficients, and encloses compact-cell momentum,
adjoint defects, divergence, mass and stretching integrands using interval
arithmetic. Exact dyadic endpoint strings preserve computed interval bounds.
Optional --budget accepts eight rational values in ns_cell_scalar_budget
order; this is only conditional replay, not profile-derived original bounds.
Checkpoint after each cell. No runtime acceptance performed.

Remaining: verify interval implementation and roundoff semantics, correct
any basis symmetry deficiencies, establish nonzero unforced solution via
validated nonlinear inverse, original weighted cell coordinates and infinite
tail, actual actuator and multiplier equation (residual pairing is not it),
global adjoint boundary conditions, original fifteen-field constructor
and all original coercivity/smallness links. All original fields remain
unpaid. Existing external C/D route and other Clay lanes unchanged.
