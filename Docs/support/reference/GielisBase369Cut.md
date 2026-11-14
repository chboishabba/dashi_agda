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


## New proof-round deliverables (2026-11-06)

- **Mathematical proof notebook:** [GielisBase369ProofTheorems.md](GielisBase369ProofTheorems.md)
  explicitly proves E01–E08 and E10–E11; E09 is a transverse,
  finite-reflection conditional theorem. The paper proofs *do not*
  replace ordinary Bishop-real Agda golden receipts.
- **Symbolic exact checks:** \`scripts/gielis_base369_symbolic_certificates.py\`
  verifies special-case trig identity, derivatives, curvature,
  half-angle area integral, angular momentum exchange and finite
  18→36 aliasing; tested independently with SymPy, no Agda claim.
- **Physical sign correction:** \`wall_impulse = incoming - outgoing\`,
  while the change of **ray** momentum is the negative. The previous
  \`mean_signed_torque\` sign described the ray, not the wall.
  Existing absolute-torque Pareto values are not a substitute for
  a newly run committed-head optical receipt.
- **Conditional SI torque:** for ideal specular walls and equal-power
  source rays, \`tau_Nm = (power_W / 299792458) * mean_wall_angular_impulse_m\`.
  The script supports \`--power-watts\`; this is an ideal-source model,
  not experimentally calibrated optics or antigravity.
- **Spectrum:** exact area \(\sqrt2\pi\), negative curvature for
  m≥3 at radial indentations, and classical Faber–Krahn bounds
  \(j_{0,1}^2/\sqrt2<\lambda_1(\Omega_m)\le j_{0,1}^2\).
  These do not certify the grid 41/61 discretization's eigenvalue errors.

All G01–G21 native/physical acceptance levels are recorded in
[GielisBase369Roadmap.md](GielisBase369Roadmap.md). No false automatic
promotion occurs from an external classical theorem, symbolic algebra,
or a simulated emitter to a fully kernel-checked empirical proof.


### Exact-head static source-audit evidence

\`scripts/gielis_base369_source_audit.py\` parses the actual
Agda tables and 342 explicit theorem clauses. Independent inspection
of the branch contents checked **648 literal integer/finite cases**
successfully. No Agda kernel run was available, so this is
**not** a Golden acceptance claim. See the [proof ledger](GielisBase369Roadmap.md).


## Nov 6 further code/proof tranche: E17–E19 and Kozyrev original-owner recovery

The original optical implementation has been found in
[Kozyrev PR #1404](https://github.com/chboishabba/dashi_agda/pull/1404),
head `337aabb00ed54bc1a4c28ada48364cb4dc54d46e`.
The canonical referee and physical ledger are
`scripts/kozyrev_first_forward_intersection_referee.py` and
`scripts/kozyrev_optical_event_ledger.py`. The matched-envelope
HTML runner and 3x3x3 ternary runner are also in that original PR.
**Do not equate** the HTML stroked SDF and independent normal-offset
walls until original event export acceptance.

New `scripts/gielis_kozyrev_pr1404_bridge.py` pins the exact Git
blob hashes of these original modules, proves the identical
epsilon-zero log centreline on matching parameters, constructs
matching finite-thickness normal-offset sides and caps, aligns the
first-forward 3mm threshold and invokes the original RayLedger
for conventional optical angular-momentum conservation. Set
`KOZYREV_PR1404_DIR` to the local original PR scripts when running
the integrated checker to require that exact cross-PR replay.

The independent rational
`scripts/gielis_raster_fd_positivity_certificate.py`
certifies the *original finite raster matrix* first eigenvalue using
Collatz–Wielandt and an exact integer positive vector, with
n=41 m=3/6/9 and n=61 m=3 verification. Its certified finite-matrix
error must not be promoted to continuum mesh convergence.

`scripts/gielis_optical_force_envelope.py` provides an exact rational
radiation-pressure-only torque ceiling given power, radius,
reflectivity and bounce count. Paired random-angle simultaneous
Hoeffding contrasts were added to
`scripts/gielis_optical_statistics.py`. Neither is a
measured apparatus calibration or an anomalous-gravity observation.

See [E17–E19 proofs](GielisBase369ProofTheorems.md) and
[G01–G21 acceptance roadmap](GielisBase369Roadmap.md) for
the exact remaining proof/measurement gates.


## Gielis–SI/Perron reuse seam, November 6

The original **SI carrier** is `DASHI.Physics.Units.SI`, with
`SIMetrologyBridge`, `MechanicalDimensionExact`, and
`YangMillsSIScalingEndpointExact`. The canonical exact c integer
belongs to `SIExactConstantParsedCarrierRequest`.

The new `DASHI/Geometry/GielisSIPerronOwnerWeldExact.agda`
retains those owners, proves `[P/c]×R = M L² T⁻²` as an
MLT/SI dimension equality, gives torque a distinct nominal role
from energy, and preserves SI measurement uncertainty/source/version.

For spectral reuse, the canonical
`BalabanFiniteInfluenceRowMassPowerExact` already proves
finite rational matrix sum and row-power estimates given a
nonnegative-powers witness. This is imported directly.
The original Gielis five-point discrete eigenvalue enclosure
E17 is an exact rational Collatz–Wielandt calculation, *not*
a claim that the repo has a fully accepted generic native
Collatz–Wielandt theorem. The Collatz/Syracuse integer iteration
modules address a different problem.

`scripts/gielis_si_owner_adapter.py` source-checks the existing
canonical c and Power/Force/Energy exponents; the Gielis ray solver
and rational torque envelope now use it as their numerical source.
An SI unit-typed equation is not a new source-power measurement.

CI and original HTML replay are excluded from this round's active
max-cut, while their earlier provenance remains documented.


### Gielis phase 2026-11-06: original mathematical producer advances

The existing SI/M-L-T carriers now construct *actual* rational-valued
optical torque with a signed dimensionless ray-response parameter,
rather than merely checking dimension tags; see E22.
The native eigenvalue scaling source preserves `m^-2` units, while
the exact continuum threefold spectral bound (9/(4L_+^2)<λ₁<
1273/(264L_-^2)) follows by domain monotonicity/Rayleigh/dilation.
The assumed-input radiation-pressure interval code preserves the
possibility of zero torque under cancellation; see E23–E24.

For G03, the same concrete Bishop real sine/cosine dataset now has
a conditional, source-written quartic trigonometric theorem derived
from existing ring, Pythagorean, setoid and cosine quadrupling
identities (E25), leaving ONLY the actual Round11 analytic
same-object inputs and kernel check rather than an abstract
geometry carrier.

For G12, the original finite raster PF numerical enclosure has
a stronger intrinsic proof: exact graph ground-state transform,
expressed as a nonnegative sum over edge squares. A native finite
edge-list theorem has been added with original rational ring,
sum/congruence and positivity owners, so this part need not
rebuild Perron–Frobenius/Collatz–Wielandt (E26). The
remaining active numerical theorem is **actual Cartesian FD-to-
continuum** compatibility. Existing Yang–Mills Mosco/recovery/no-
pollution files are donor gate inventories, not a substitute
for the selected Gielis recovery/liminf proof.


## E27: original raster FD exact-domain continuum repair

The selected Gielis raster eigenvalue code had a fixed normalised
inward radial cutoff 1e-12. This is not harmless in the
mathematical n→∞ limit, because it selects a fixed
slightly smaller analytic domain. Both the actual raster
PDE builder and independent rational eigenvalue certificate
now use the **vanishing** ε(h)=min(1e-12,h²), which is
identical at n41/n61 but tends to zero for h→0.

The source scripts/gielis_fd_energy_mosco.py checks
the exact zero-extension 5-point discrete energy
uᵀ(4I-B)u=Σ_axes,edges(u_i-u_j)² on the
original selected mask and several integer test-vector
families, with actual arithmetic identity not a float
tolerance test.

The proof notebook E27 gives a full paper-level
fixed-k qualitative Cartesian FD Dirichlet spectral
convergence proof for exact radial evaluation, using
compactness, recovery and min–max. This is stronger
than the earlier distinct sector-geometry convergence
alone, but is NOT a quantitative numerical eigenvalue
error guarantee for the existing binary64 run.
Source-native Agda compactness and actual numerical
boundary interval certification remain named leaves.


## 2026-11-07 final current mathematical cut — E28–E35

The selected existing Phase36 m9 Nyquist data now has a native rational
4x4 Fourier operator and inverse (E28); selected C6 modes now
have a full native C2×C3 Fourier transform/inverse using the pre-existing
C3CubeCyclotomicFourierExact field/theorem (E30). Exact original
Q(zeta36) interoperability checks covered 625+729 samples and
729 direct C6 DFT comparisons, but these are SUBSPACES of the still
outstanding full C36 Fourier operator.

The actual original Gielis finite-difference solver now uses
a strict Fraction-only unshrunken analytic rational grid classifier
for EVERY positive integer mode; the selected m3/6/9 n41 and m3 n61
masks agree with legacy (792,779,792,1788 sites) and contain no
binary64 radial classification tolerance. E27's paper-level fixed-k
continuum argument thus targets the literal ideal mathematical domain.
The original finite matrix eigenvalue certificate remains a different
exact result from any quantitative continuum error rate.

The optical force/torque magnitude already uses canonical SI c and
Mechanical.Quantity; E32 now replaces abstract deflection with the
literal signed planar wall moment x(iy-eta oy)-y(ix-eta ox).
It is right-hand-rule Hodge compatible and keeps torque N m distinct
from energy J, without identifying a hypothetical input as measured.

The same original Bishop complex carrier now has explicit algebra
laws for Cauchy multiplication (E34), and the Gielis quartic trig
identity reduces to one actual imaginary-axis complex exponential
multiplication proof (E33), reusing the existing REAL exponential
Cauchy theorem correctly rather than assuming it proves complex exp.

For the continuum selected special Gielis domain,
area(Ω_m)=sqrt(2)pi exactly for every positive integer m.
E35 now proves the stronger paper bound λ1(Ω_m)>224/55
by Faber-Krahn and exact alternating Bessel J0/J1 inequalities.
Native finite rational Bessel checks are source-written; the
physical inverse-square metre scaling consumer now uses this stronger
lower bound. This does not assign a physical wave frequency.

14 native Gielis Agda roots are in the pre-existing parallel checker.
The full analytic Bishop trig/weld and native C36 scalar, native
continuum compactness/quantitative mesh rate and independent measured
optical source calibration remain exact outstanding acceptances.
The source-written Agda terms have not been kernel-accepted here.


### E36: recovered existing theorem owners rather than duplicate implementations

The user correctly identified that P0/P1/P2/P3 had been overstated as
missing mathematical foundations. Direct source audit found:
BishopComplexSeriesConvergenceExact complexSeriesLimit/Convergence/Unique;
BishopComplexAlgebraExact complex arithmetic; BishopSetoidComplexExact
expC and setoid congruence; BishopExponentialCauchyProductExact.bishopExpAdd;
BishopMachinPiRationalWindowExact rigorous Machin bounds;
BishopNatSquareRootSemanticSquareExact natural radicand semantic root;
BishopPolarJacobianSameTrigWeldCompilerExact actual derivative and
pointwise determinant. The latter's measure consumer explicitly
declares measureTheoreticWeldClosed=false.

Fourier: ShorCyclicCharacterResolutionExact generic cyclic inversion,
external Lean DFT same-object weld, NSTriadKNLuoFiniteFourierInversionFromResolutionExact
and Parseval, plus C3CubeCyclotomicFourierExact, already own
the generic tasks. The remaining native C36 work is its
original 12-dimensional Q(zeta36) scalar and 36-character
orthogonality/normalization instantiation.

Spectrum: native finite Hermitian/Rayleigh and YM Mosco/recovery/liminf
theorems/interfaces exist, with conditional domain/density gates,
beside E17/E26/E27/E31 exact selected Gielis lattice and paper convergence.
Only the selected native continuum object and *quantitative*
n41/n61 error remain.

Physical: Kozyrev PR #1404 has literal RayLedger P/c,
reflection/absorption and signed r×impulse torque,
log-spiral geometry and independent intersection referee.
The new E32 restates this *existing* conventional optical
physical law natively; remaining is SAME-event integration
plus empirical calibration, not torque law invention.

These recovered donors are not new Gielis proof receipts,
and source-written current PR Agda is still uncompiled.
Exact selective remaining consumer details live in
GielisBase369Roadmap.md and E36 proof-owner archaeology.


## E37–E41 latest original-lemma max-cut

The actual Bishop complex series convergence and original Gielis complex
exponential now have a native same-carrier bridge. This includes literal
conversions, complex arithmetic equivalence, transported original complex
series limit/uniqueness, and the real exp(0)=1 reduction of the literal
Round11 expC(iθ) to its configured cosine/sine pair. Remaining analytic
work is actual imaginary-axis multiplication, period pi and variable
positive reciprocal root/integration, not generic complex convergence.

Full C36 Fourier inversion over the original Q(zeta36) polynomial
quotient is now justified for ALL 36-component signals by the checked
complete 36×36 character kernel and 36 basis round trips; the separate
native Agda cyclotomic scalar/character resolution is still missing.

The selected m3 finite Cartesian λ1 already has exact rational finite
matrix and rigorous continuum bounds. The new adapter combines these
into a machine-computable *quantitative* rational a posteriori
finite-to-continuum absolute/relative error; the actual mesh convergence
order O(h^p) and native compactness/operator theorem are distinct leaves.

Physical: the actual original PR1404 RayLedger owner is now required
by a strict SHA-pinned same-event exact-rational hit/terminal comparison.
The nonzero two-bounce synthetic event conserves power, momentum and
angular momentum exactly. Runtime replay requires the *exact original*
PR1404 checkout and has not been executed as a successful result here.
It does not supply real apparatus measurement or novel torsion evidence.

Sixteen native Gielis Agda roots are listed in the original parallel
checker. No new exact-head Agda kernel receipt is claimed.
