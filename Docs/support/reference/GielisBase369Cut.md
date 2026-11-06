# Gielis superformula ↔ Base369 geometric/spectral max-cut

**Provenance.** Johan Gielis, "A generic geometric transformation that
unifies a wide range of natural and abstract shapes", *American Journal of
Botany* **90** (2003), 333–338, DOI: [10.3732/ajb.90.3.333](https://doi.org/10.3732/ajb.90.3.333).

This is a new DASHI formal/computational bridge, **not** a claim that Tesla
invented a 3–6–9 universal physical law and **not** a proof of the original
Gielis equation beyond the explicitly selected special case.

## Chosen exact special case

From Gielis's polar expression, choose a=b=1, n1=2, n2=n3=4.
The elementary identity cos^4(x)+sin^4(x)=(3+cos(4x))/4 gives

    r_m(theta) = 2/sqrt(3+cos(m*theta))
    r_m(theta)^(-2) = 3/4 + cos(m*theta)/4.

For integer m>0, the radius is positive and has C_m rotation and reflection
symmetry. It satisfies sqrt(1) <= r_m <= sqrt(2). The shape is a radial
graph over a circle, a star-shaped closed planar domain. A *different*
epsilon-dependent interpolation used in benchmarks is

    r_{m,eps}(theta) = 2/sqrt(3+eps*cos(m*theta)).

This is the selected Gielis case at eps=1; **eps!=1 is only a controlled
Gielis-inspired deformation**, not asserted to be a general Gielis equation.

## G1: 18-sector exact arithmetic

On theta_j = 2*pi*j/18, j=0..17, let

    s_m(j) = 2*cos(2*pi*m*j/18),  m in {3,6,9}.

Then s_3 is [2,1,-1,-2,-1,1] repeated 3 times;
s_6 is [2,-1,-1] repeated 6 times;
s_9 is [2,-2] repeated 9 times.
These are **integers**, not rationalized floating point samples.

    <s_3,s_3> = 36
    <s_6,s_6> = 36
    <s_9,s_9> = 72
    <s_3,s_6> = <s_3,s_9> = <s_6,s_9> = 0.

`DASHI/Geometry/GielisBase369FiniteExact.agda` imports the existing
`Base369CirclePhase.Phase18` and supplies native finite carrier functions,
integer Gram equalities and rotation/reflection preservation proofs.
The analytic identification of the Agda signal with a native real-valued
cosine remains an explicitly separate proof obligation.

## G2: finite dihedral geometry and continuous analogue

On Phase18, `rotate3`, `rotate6`, `rotate9` are shifts by 6, 3, and 2,
respectively, and `reflect18` sends j to (-j) mod 18. The Agda file has
equations for signal invariance, rotation orders, reflection involution,
two-sided inverses and r*s = s^(-1)*r (dihedral conjugation).

The continuum counterpart for the selected cosine curve is a direct
trigonometric identity. Native Agda lifting to the selected constructive
real/trigonometric carrier, including a same-object analytic equality to
Gielis's original definition and native smooth boundary normal, is NOT YET
kernel-checked here.

## G3: exact finite projectors and numerical Dirichlet experiment

Let V=Q^18. For m|18, define the rational averaging projector

    (P_m f)(j) = (1/m) sum_{k=0}^{m-1} f(j+18*k/m mod 18).

The Python exact-arithmetic implementation uses `fractions.Fraction`.
It checks, on all 18 standard basis vectors, both composition orders of

    P6 P9 = P18,    P3 P6 = P6,    P3 P9 = P9.

These are identities of linear maps on all of Q^18, not merely checks on
three specially selected signals. The theoretical reason is that iterated
averaging projects onto the common invariants of the two rotation subgroups,
whose generated subgroup is C_lcm(a,b).

For m in {3,6,9}, the script rasterizes the actual closed domain
Omega_m = {(r,theta): 0<=r<2/sqrt(3+cos(m*theta))}, assembles the
positive five-point discrete Dirichlet -Laplacian and computes four smallest
numerical eigenvalues with scipy.sparse.linalg.eigsh. Two grid resolutions
(41 and 61 nodes per Cartesian axis) are emitted for comparison. This is
**not** a converged continuum spectrum, a Galerkin theorem or any 4D
Yang–Mills mass-gap result.

## G4: open spiral, collisions, absorber and Pareto diagnostics

The separate optical curve is open, with 1.5 turns and fixed endpoint radii
0.75m and 1.55m. Let T=3*pi, t=theta/T, and

    h(theta) = -1/2 log[(3+eps*cos(m*theta))/3].
    log r(theta) = (1-t)log(.75)+t log(1.55)
                   +h(theta)-[(1-t)h(0)+t h(T)].

For eps=0 this is exactly the logarithmic spiral.
For eps>0 the detrended modulation preserves BOTH endpoint radii; it is
not a closed supershape or a direct numerical reproduction of the older
Kozyrev mirror simulations. A physical seam/cover is not postulated.

`scripts/gielis_base369_experiments.py` supports:
- ray/polyline intersection with nearest-hit selection;
- geometric specular reflection using segment normals;
- optional absorbing target disk centered at (0,0), radius 0.10m;
- outer circle exit gate radius 1.70m;
- collision and single-ray path export to JSON;
- bounded multiple reflections (default 8), no unproved infinite-reflection claim;
- deterministic 720-ray configurations and a focus/absolute-torque Pareto front.

The ray starts at (1.05,0), emitted uniformly in [0,2*pi). "Torque" is
a **normalized angular impulse proxy** (metres × unit momentum), sum over collisions of
cross(position, outgoing_unit_direction - incoming_unit_direction),
not a measured Newton-metre physical torque. Sampled 720-ray results should
not be compared to prior 13.61% results without matching source, walls and
termination semantics.

## Running and reproduction

    python -m pytest -q tests/test_gielis_base369_experiments.py
    python scripts/gielis_base369_experiments.py
    python scripts/gielis_base369_experiments.py --pde --optics \
      --rays 720 --segments 1536 --bounces 8 \
      --output /tmp/gielis_369_receipt.json

Requires numpy and scipy for the numerical phases, pytest for tests.
On the repository's Agda toolchain:

    scripts/run_agda29_parallel_check.sh \
      DASHI/Geometry/GielisBase369FiniteExact.agda

Note: the authoring environment used for this cut had **no installed Agda
compiler**, hence the Agda file is *source-written* and not claimed
kernel-accepted until the command above succeeds.

## Exact remaining max-cut (do not silently promote)

| Gate | Implemented now | Still required to close without conditions |
|---|---|---|
| G1 | Explicit Phase18 signals and Gram proofs in Agda source; Python exact rational checks | Run Agda kernel and fix any reported errors |
| G2 | Finite rotation/inversion/reflection/dihedral source; analytic tests | Constructive real cosine identity, positivity/regularity and same-object original Gielis identification inside Agda |
| G3 | Exact Q^18 projectors and basis tests; real numerical PDE eigenvalues | Native rational/complex projector laws; full Fourier inversion, selected PDE domain convergence and validated spectral approximation |
| G4 | Matched segment ray tracer, outward gate, absorber, collision output and Pareto sweep | Import original experimental geometry for same-object comparison, convergence of ray-segment refinement, physical absorber/torque calibration and any claimed infinite-reflection limit |

Do not confuse cyclic C27 (27 phases) with the product group C3^3 (27
independent ternary states); the established 27/729 fabric is a product
carrier. A true geometrical bridge to that fabric requires explicit product
actions and preservation maps, not state-count equivalence.

Preserve source/proof provenance: Gielis owns the superformula; the finite
special-case reduction and Base369 integration are new derivations in this
tranche; numerical claims must retain their seeds/geometries and settings.


## November 6 owner-reuse implementation and authoritative phase plan

See [GielisBase369Roadmap.md](GielisBase369Roadmap.md) for exact
G01–G21 lemma definitions, owner mapping, dependencies, P0–P5
phases and D0–D7 deliverable acceptance.

Additional new owners on PR #1466:
- `DASHI/Geometry/GielisBase369NyquistPhase36Exact.agda`:
  18-sector sine aliasing of modes 9 and 27 and 36-sector orientation
  separation in integer tables;
- `DASHI/Geometry/GielisBase369ExistingOwnersWeldExact.agda`:
  reexports prior native DNA dihedral, SO3/Hodge torque orientation,
  Base369 MDL, semantic-sampling boundary, and existing log-polar spiral
  results rather than duplicating those domains.

The Python benchmark now distinguishes minimising physical disturbance
from maximising delivered angular impulse, provides m=4/5/7 controls,
and refuses to record more reflections than the stated bounce budget.
An earlier standalone 720-ray receipt is **not** evidence that the new
committed head and expanded tests have run. Do not represent the
uncalibrated impulse as SI newton-metres or compare it with the
legacy Kozyrev HTML motor/torque result. The original HTML SDF collision
versus independent-boundary disagreement of approximately 1.349–1.832 mm
must be resolved at the same-apparatus/first-hit seam (G13).

Do not mix p-adic Kozyrev wavelets (different mathematical lane) with the
optical Kozyrev mirror apparatus.
