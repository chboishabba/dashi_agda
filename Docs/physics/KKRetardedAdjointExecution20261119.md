# Retarded adjoint execution — 2026-11-19

Original donor #1527 at 123eff9204d91e2b1967e9e72d3d68771f27287f, scripts/ksw668_f8_tt_multipole.py and ksw668_f8_fv_source_flux.py. Local sparse matrix transcription retained three radial modes, conservative radial flux, weak Israel SAT, stage times, compact source primitives and three-time intrinsic Weyl observation. Direct git checkout failed DNS; connector source inspected. This is not an execution of the exact donor file or an independently checked stencil-parity result.

| fixture | grid | steps | forward original | adjoint original | forward optimized | adjoint optimized | amplitude ratio |
|---|---|---|---|---|---|---|---|
| t=3, eps=.16, pulse=.15, dr=.04, dy=.06 | 64 x 35 | 163 | 3.615794044105739 | 3.615794044105771 | 5.369657337288811 | 5.369657337288810 | 1.4850561928553758 |
| t=12, eps=.04, pulse=.065, dr=.04, dy=.06 | 79 x 36 | 339 | 1.755908256311516e-7 | 1.755908256311461e-7 | 2.803815960314971e-7 | 2.803815960314967e-7 | 1.5967895533475673 |

Controls are source amplitude samples at half-steps with common compact spatial profile, optimized in Euclidean sample norm, not SI source energy. Both meet forward/adjoint floating numerical comparison. First fixture deliberately exceeds original parameter guards. Second fails original spatial resolution and half-cell photon-dark guard (nominal margin .01245911117, dr/2=.02). Fine run timed out. No continuum gain, same-observer acceleration, Agda kernel, physical energy gain or physical realization claim. Local executable supplied separately in conversation; only this receipt is committed here.

Next: exact donor stage parity, sparse or matrix-free cached transpose, original resolution and both Weyl readouts, source-work weighted norm, detector and SI normalization. Do not compare squared Weyl gain directly to static scalar compliance.
