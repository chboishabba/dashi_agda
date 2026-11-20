# Radial refinement and missing source moments — 20 November 2026

Parent cd0e8ff33bb2276fc57df7c244e2b162dcaf2292, PR #1530.
The native default source and physical readout remain unchanged.

## Provenance and tests
The independent local reciprocal-stage reconstruction reproduced the old
coarse four-channel compliance. The isolated sweeps and moment interventions
below used that reconstruction (same stage equations and source primitives).
The original warp_temporal.py and ksw668_f8_fv_source_flux.py were subsequently
recovered byte-for-byte, matching a2b0eb86ddf091232e6a1534f20193376e6bb19b
and dec4e79e3a4899952a5deceb786324bc0745982c. Native setup-only driver blob
1cc6738fdf5e57a97961ddac25dfecc5b724ec88 preserves the default path.
The new source-bank adjoint passed five independently called native adjoints
per order on a random 7x11 fixture for both orders 3 and 4. Native source-bank
moment checks ran at dr=.012,.010,.008,.004. The fixed-receiver check used the
native stage. Full fine-grid source-bank propagation remains open; we do not
claim all sweep cases have been rerun through the final committed audit driver.

## Isolated original-source sweeps
Common eps=.04, final_t=12, pulse=.065, order=4, r_outer=3.01, y_outer=2.01,
four threads. Boundaries round outward to the mesh. Requested dt is listed.

| dr | dy | dt | E4 C | E5 C |
|---|---|---|---|---|
| .012 | .030 | .003 | 6.46531483e-9 | 1.18324507e-11 |
| .012 | .030 | .0015 | 6.45452621e-9 | 1.22445631e-11 |
| .012 | .030 | .00075 | 6.46846741e-9 | 1.23941302e-11 |
| .010 | .030 | .0015 | 2.35115698e-7 | 3.19555635e-10 |
| .008 | .030 | .0015 | 1.57304978e-8 | 1.90279651e-11 |
| .012 | .018 | .0015 | 6.11168324e-9 | 1.22981288e-11 |
| .012 | .012 | .0015 | 6.16119301e-9 | 1.25548166e-11 |

E4 diagonal mode compliances at fixed dy=.03, dt=.0015:
dr=.012: [6.99176774e-9,2.50212040e-11,3.12442266e-13]
dr=.010: [2.55395957e-7,9.89344354e-10,1.66018131e-12]
dr=.008: [4.83994420e-11,1.38388279e-8,1.63103720e-11]
Gram trace / full compliance: 1.08716,1.09047,.88386.
The middle radial spike is monopole-dominated, not inter-mode cancellation.

Kernel comparison uses widths equal to accumulated SSPRK3 time quadrature
weights q_j, whitened value g_j/sqrt(w_j q_j), piecewise constant on cumulative
quadrature-mass time intervals, zero extension. Its L2 norm squared is exactly
the discrete compliance; it is a diagnostic embedding, not a convergence
theorem. Relative L2 denominator is the second kernel.

| comparison | E4 relative L2 | E4 cosine |
|---|---|---|
| dt .003 -> .0015 | .08451407 | .99643202 |
| dt .0015 -> .00075 | .05672701 | .99838987 |
| dr .012 -> .010 | .83452650 | .99891917 |
| dr .010 -> .008 | 3.44111595 | .53092809 |
| dy .030 -> .018 | .02816090 | .99998654 |
| dy .018 -> .012 | .00614668 | .99998917 |

## Source moment audit
For normalized sources let I_k=integral_0^1 u^k f(u) du and M_p =
integral_0^1 u^(d-1+p) S(u) du. Integration by parts gives
l0: M0=M2=0, M4=48 I2, M6=336 I4.
l2: M0=0, M2=120 I2, M4=720 I4.
l4: M0=27 I2, M2=99 I4.
Cell averages preserve M0 but their cell-centre quadrature can violate M2.
Monopole M2 at dr=.012,.010,.008,.006,.004,.002 respectively:
-7.62403696,-28.2237896,.227953524,-14.9811247,8.52563823,-.692114843.

Support-preserving minimum weighted-source-L2 corrections: vanishing variant
enforces M0,M2 for l0 and M0 for others; leading variant additionally enforces
M4 l0 and M2 l2; next variant adds another moment per mode. These are diagnostics
and can be large modifications, not certified superior approximations.

| dr | dt | original E4 C | vanishing | leading | next |
|---|---|---|---|---|---|
| .012 | .0015 | 6.45452621e-9 | 4.06747559e-11 | 3.72948934e-10 | 4.54365632e-10 |
| .010 | .0015 | 2.35115698e-7 | 3.86515452e-9 | 1.99094445e-9 | 2.00414969e-9 |
| .008 | .0015 | 1.57304978e-8 | 1.72335069e-8 | 1.93989071e-8 | 1.94827292e-8 |
| .006 | .001 | 1.80221369e-6 | 2.98871249e-7 | 7.66001740e-7 | 7.63652497e-7 |

At dr=.010 monopole C drops from 2.55395957e-7 to 1.02431844e-9
when the vanishing moment is enforced. This shows substantial sensitivity to
the source projection, not exclusive causal attribution to one moment because
the correction also changes higher moments. Finer .006 result remains strongly
nonconverged. Relative L2 changes in the source can be large (e.g. leading
monopole correction 3.42 at dr=.012); do not use as default production source.

## Structural alternative
With D=(1/u) d/du, Delta_d=d^2/du^2+(d-1)/u d/du, normalized original sources
are (2/5)Delta_3^2 f, (4/7)Delta_7 D^2 f, (1/35)D^4 f.
Use scaled native conservative operator L=eps^2 R on cell-averaged bump;
l0=(2/5)L^2 f_h, l2=(4/7)L (D^2 f)_h, l4 original source. The inner l2
weighted mass is 15 I2. Exact shell-volume symmetry and L u^2=2d
away from the projected outer boundary imply the l0 vanishing moments and
l2 prescribed leading moment for compact support. Native setup tests pass
the associated numerical moment identities. At dr=.004, operator l0 M2
~ -5.33e-14 and M4 ~4.57993429 (target 4.57985757); operator l2 M2
11.4496439153. The l0 support extends to .050, leaving photon guard .00245911;
l2 support .046, margin .00645911. At dr=.012,.010,.008 the operator l0
support fails the guard, so the new audit refuses to propagate it in those
cases. Full .004 propagation timed out before all three modes completed.
No physical measurement or continuum conclusion follows.

## Fixed-receiver readout discrimination
Native direct E4 monopole check at dr=.010, dy=.03, dt=.0015, identical
receiver and source: cubic/quintic compliances 2.55395957e-7,2.65545324e-7;
ratio 1.0397397334, kernel cosine .9998875502, relative L2 .0243499225.
Thus the choice between these two differentiation stencils cannot account
for the ~36-fold original radial spike in this particular comparison.

## Reproduce
Run from repository root:
    OPENBLAS_NUM_THREADS=1 python scripts/check_warp_receiver_readout.py '{"dr":0.01,"dy":0.03,"dt":0.0015,"r_outer":3.01,"y_outer":2.01}'
    OPENBLAS_NUM_THREADS=1 python scripts/warp_kernel_refinement_audit.py '{"path":"audit_dr010","dr":0.01,"dy":0.03,"dt":0.0015,"r_outer":3.01,"y_outer":2.01,"mode":0}'
Repeat mode 1 and 2 in same directory; then summary.npz contains all
mode kernels, Gram, norms and weights. Use separate directories for each mesh.
Compare two summaries with identical variant sets:
    python scripts/warp_kernel_refinement_audit.py compare audit_a/summary.npz audit_b/summary.npz
For operator experiment use include_operator=true on a sufficiently resolved
mesh with a positive actual support margin, not on the coarse meshes.

## Next maximum cut
Complete guarded operator-source propagation at .004 and finer, independently
vary radial spacing and temporal spacing, compare full kernel norms, and
establish uniform stability plus a source projection consistency estimate.
Source moment tests do not prove continuum retarded Weyl regularity.
Absolute compliance convergence OPEN, coupled SSPRK3 stability OPEN,
physical detector/SI normalization OPEN, same-action conserved source OPEN.
