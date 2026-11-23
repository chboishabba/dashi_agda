# Cached temporal propagation and absolute-compliance refinement — 19 November 2026

PR #1530. This round completes original default-resolution finite-grid
propagation, not continuum or physical detector certification.

## Implementation and provenance

- scripts/warp_temporal.py: shared half-step geometry, radial and normal
  bands and their transposes, caller-owned stage outputs, reusable SSPRK3
  buffers, batched independent observers/controls.
- scripts/warp_temporal_weighted_adjoint.py: original finite-volume source
  owner, four native Weyl readouts, three independent mode checkpoints,
  configuration manifest, invalidation of forward files when kernels change.
- scripts/check_warp_temporal.py: random batched discrete adjoint tests.
- scripts/check_warp_temporal_donor.py: cached Euler-map comparison with
  original stage and sparse transpose, including default spatial dimensions.
- Local files for all four added scripts match the GitHub blob hashes.
  Source integration donor dec4e79e3a4899952a5deceb786324bc0745982c
  and sparse transpose 9a782292286ac4781ab0a924540c5a7203c5bfe0 match
  locally recovered bytes. The original forward stage was manually recovered
  as a function, not a byte-verified full original donor checkout.

Original-resolution runs used the identical temporal kernel and an earlier
driver with reconstructed finite-volume source primitives and no manifest.
The reconstructed source arrays were exactly array-equal to the original
source integration module at dr=.012,.010,.008 (maximum difference 0).
The final committed driver uses the original module directly and adds
configuration checkpoints; it was executed for coarse and intermediate
meshes. The whole original-resolution committed driver has not been
independently rerun as a byte-verified repository checkout.

## Reproduction

Run from repository root, with NumPy, SciPy, SymPy and Numba installed.

    OPENBLAS_NUM_THREADS=1 python scripts/check_warp_temporal.py
    OPENBLAS_NUM_THREADS=1 python scripts/check_warp_temporal_donor.py

For bounded execution windows, run each mode separately, using a fresh
checkpoint directory per configuration. Do not execute concurrent writers
against the same checkpoint directory.

    for q in 0 1 2; do
      OPENBLAS_NUM_THREADS=1 python scripts/warp_temporal_weighted_adjoint.py "{\"phase\":\"adjoint\",\"mode\":$q,\"checkpoint\":\"warp_full\"}"
    done
    for q in 0 1 2; do
      OPENBLAS_NUM_THREADS=1 python scripts/warp_temporal_weighted_adjoint.py "{\"phase\":\"forward\",\"mode\":$q,\"checkpoint\":\"warp_full\"}"
    done

The mode kernels are summed BEFORE optimizing. Independent forward
results are summed BEFORE comparison against the full kernel.
No separate mode budget is introduced; the mode split is an exact
linear decomposition of the same discrete map.

## Executed verification

Random temporal fixture: order 3, 20/20, max absolute residual
9.769962616701378e-15; order 4, 20/20, 3.552713678800501e-15.

Direct Euler-map comparison: 2 orders x 3 sizes x 3 times, 18/18
forward and 18/18 transpose. Max absolute difference 4.547473508864641e-13
forward and 4.440892098500626e-16 transpose on recovered donor stage
and byte-matched sparse transpose respectively. Nonzero source injection
included in forward comparisons.

## Fixed nominal domain refinement

Common parameters: r_outer=4.3, y_outer=3, eps=.04, final_t=12,
pulse=.065, order=4, same receiver construction, source moments checked,
four threads. Grid endpoints round outward with spacing; not precisely
identical boundary coordinates. Three independent spatial modes ell=0,2,4.
All 20 forward/adjoint comparisons passed at each resolution under
rtol=2e-6, atol=1e-13. All five weighted costs agree at rtol=1e-12.

| dr / dy / requested dt | grid nr x ny x nt | budget | maximum absolute forward/adjoint residual |
|---|---|---:|---:|
| .012/.030/.003 | 360 x 101 x 904 | .9466383880921752 | 8.674e-19 |
| .010/.018/.002 | 431 x 168 x 1355 | .9466386521683026 | 1.017e-17 |
| .008/.012/.0015 | 539 x 251 x 1807 | .9466386837093015 | 3.107e-18 |

| Mesh | E4 C | E5 C | E4 tangent C | E5 tangent C |
|---|---:|---:|---:|---:|
| Coarse | 6.46531483e-9 | 1.18324507e-11 | 6.45621179e-9 | 1.10145233e-11 |
| Middle | 2.00278827e-7 | 2.89487236e-10 | 2.00128584e-7 | 2.78653965e-10 |
| Original | 6.52474463e-9 | 1.89206635e-11 | 6.52183576e-9 | 1.86526417e-11 |

Original resolution forward responses, row=baseline/E4/E5/E4 tangent/E5
tangent control; columns E4/E5/E4 tangent/E5 tangent:

    [-2.6170866370004033e-05,-2.156745327859175e-06,-2.6181111477960644e-05,-2.1742574090861844e-06]
    [7.859119331775556e-05,4.1439986200195395e-06,7.857367064547432e-05,4.106526171400926e-06]
    [7.695435106624333e-05,4.232142720225079e-06,7.694064264185216e-05,4.201877772962407e-06]
    [7.859119140133335e-05,4.14418430538853e-06,7.85736725614681e-05,4.106719003811963e-06]
    [7.680441410293161e-05,4.231958718188219e-06,7.679089742606234e-05,4.202060467103668e-06]

Amplitude gains 3.00300312,1.96228209,3.00115878,1.93264167;
squared gains 9.01802773,3.85055098,9.00695402,3.73510382.
These are separate optimizers, not one simultaneous optimum.

The initial all-mode full-resolution batch timed out. Independent mode
execution completed: adjoint mode seconds 11.027,9.735,11.080;
forward mode seconds 11.918,11.409,10.218. Times exclude separate
process setup. Repeated coarse calculation on larger domain reproduced
the smaller-domain results to displayed precision.

## Roadmap / decision

- Cached temporal coefficients: PASS.
- Reusable SSPRK3 buffers: implemented and executed.
- Four-observer batched propagation: PASS, mode-chunked.
- Original-resolution propagation and same discrete weighted optimisation:
  PASS, finite grid only.
- Absolute compliance convergence: OPEN with explicit negative refinement
  evidence. Middle E4 compliance ~31 times coarse; E5 ~24.5 times.
  The large original-resolution relative gain reflects baseline changes as
  well as optimization. No continuum physical gain claim.
- Next numerical cut: independently vary dt at fixed dr/dy, then isolate dr
  and dy; use fixed exact boundary locations where possible; audit
  mode-resolved kernel cancellation, receiver interpolation sensitivity and
  source resolution, not just diagonal gain. Compare kernel functions in
  the same weighted continuous-time norm and establish uniform error bounds.
- Full moving coupled SSPRK3 stability and retarded receiver convergence:
  OPEN. Direct/tangent agreement and discrete photon margin do not prove it.
- Physical detector normalisation and calibrated energy/work budget: OPEN.
- Same-action conserved gravitational source: OPEN.

No measured gravitational anomaly, graviton detection, physical
antigravity, or SI energy efficiency is claimed.
