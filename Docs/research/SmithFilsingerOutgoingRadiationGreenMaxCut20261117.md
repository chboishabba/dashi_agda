# Smith/Filsinger maximum-cut continuation — outgoing Maxwell sheet Green
**17 Nov 2026.** F13 radiation boundary mathematical producer; F15 source-off
negative control; D1 exact SymPy verification. Source owner: PR #1524.

## Prior source reuse

Do NOT duplicate the canonical Green inverse, Maxwell jet, original
source/port or energy ledger. Reuse:
- SmithFilsingerCoerciveGreenRetardedWeldExact: static finite Green inverse,
  coercivity bound, and separately stipulated original launch delay
- BalabanSide4ScalarGreenConvolutionExact: periodic *elliptic* scalar Green
- SmithFilsingerTimeIndexedTransferExact: launch/flight/arrival theorem
- SmithFilsingerFullVectorIndexedFaceSampleExact and
  SmithFilsingerSpaceTimePoyntingTelescopeExact: signed field and work terms
- SmithFilsingerReplenishedCycleCapExact: full storage restoration and
  natural/controller work bound
- scripts/smith_filsinger_tangential_maxwell_sympy.py: already derived 4x4
  Maxwell tangential generator and three-layer Cayley transfer.

## Exact new finite-scheme radiation/source Green

New scripts/smith_filsinger_radiation_green_sympy.py implements actual
OUTGOING half-space radiation terminations for an incident tangential
sheet-current source at the upper face of a three-layer source-to-sensor
Maxwell slab. The state is [Ex,Ey,Hx,Hy], horizontal k_y=0 Fourier mode,
lossless homogeneous exterior with strictly positive outgoing normal
wave number q = sqrt(w² μ ε - kx²). Only propagating modes admitted.

The exterior outward admittance is

    H_up = Y E_up, H_down = -Y E_down,
    Y = [[0, -q/(w μ)], [w ε/q, 0]].

Let T=[[A,B],[C,D]] be the existing exact *finite Cayley-scheme* transfer
from lower interface to upper interface. Lower outgoing condition gives

    E_top=(A-B Ybottom) E_bottom = Q E_bottom,
    H_inside=(C-D Ybottom) E_bottom = N E_bottom.

For the sheet current J at the top, the correct Maxwell jump is

    R (H_inside - H_outside)=J,
    R=[[0,-1],[1,0]], H_outside=Ytop E_top.

Therefore the source-to-receiver electric Green map is the explicit
2x2 inverse

    E_bottom=[R(N-Ytop Q)]^(-1) J,
    E_top=Q [R(N-Ytop Q)]^(-1) J.

Its upper and lower outgoing magnetic traces and upper inside trace are
returned separately. The entire algebra uses SymPy exact integers/rationals,
sqrt rationals and i. No implicit choice of original Filsinger source.

A lossless layer generator satisfies the tangential flux identity
M† F + F M=0, with F encoding average Poynting (+z) cross-products.
The Cayley map satisfies T† F T=F, even with imaginary off-diagonal
Hermitian Hall dielectric tensor (gyrotropic lossless special case).
The sheet jump yields

    W_sheet = Φ_outward + Q_slab,

where Q_slab is the signed difference between the bottom flux and the
upper *inside* slab flux. For lossless layers Q_slab=0, and source work
equals upper outgoing minus lower incoming signed exterior work exactly.
No source term is counted twice.

Negative controls: reversing the jump sign fails; evanescent q²<=0 is
rejected pending a separate decaying branch/radiation certificate;
zero external sheet current yields exactly zero field, flux, and source
power (so cannot pay positive load with absent stored/controller work).
The off-diagonal Hall fixture produces real cross-polarization with no
loss of flux.

## Verification

Local exact arithmetic:
- Prior reduced layer/Hall and tangential Maxwell tests: 32/32 PASS
- New outgoing-radiation/Hall/source-sheet + F15 source-off/evanescence tests: 11/11 PASS
- Combined suite: 43/43 PASS using pytest/SymPy 1.14.0.

Committed files:
- scripts/smith_filsinger_radiation_green_sympy.py
- scripts/test_smith_filsinger_radiation_green_sympy.py
Both are wired into scripts/check_smith_filsinger_dynamic_replenishment.sh
and scripts/check_smith_filsinger_sympy_gate.py.

Source-equivalent local execution is independently verified, but **full
exact-GitHub-head consolidated tests have NOT been executed** here.
Agda 2.9 and Nix absent on current runtime; pinned Agda CI workflow already
exists at .github/workflows/filsinger-agda29-acceptance.yml. Current-commit
workflow runs and commit statuses returned no acceptance result. D1 kernel
OPEN. A SymPy algebraic proof is NOT Agda typechecking.

## Physical limits and exact next cuts

F13 model-conditional finite planar source-to-receiver boundary weld is a
mathematical advance but the actual 3D soil/air/ionosphere *retarded dyadic
Green* remains OPEN. The current exterior supports only homogeneous
propagating q>0; it excludes evanescent/radiation-continuation modes,
oblique geomagnetic angle, frequency-dependent Hall/Pedersen/parallel
dissipation, Maxwell longitudinal/gauge constraints at 3D arbitrary k,
nonlocal causal inversion, nonlinear local plasma, and realistic ground and
collector return geometry. The Cayley spatial transfer is not the exact
continuum exponential. The user-origin hypothesis of environmental
energy access is not verified by a positive toy source-sheet flux.

F15 actual independently replenished natural work remains OPEN. The
source-sheet *fixture* provides a modeled power source, not a measurement
of solar/magnetospheric replenishment. Use the existing original-gate
evidence checker to verify hashes and original IDs before any new field
data are treated as candidate original-world evidence; metadata checks
are necessary but not sufficient physical calibration.

High-alpha follow-on:
1. Derive/implement evanescent and absorbing radiation branches with
   correctly selected complex q and passivity checks.
2. Replace Cayley finite transfer by certified continuum matrix
   exponential / rational error enclosure where practical.
3. Generalise anisotropy to tilted geomagnetic conductivity, compare
   source-to-terminal projection with Maxwell surface work.
4. Add actual, independently calibrated same-original environmental
   forcing and electrode/ground return VI with uncertainty envelopes.
5. Run pinned Agda proof CI, fix first kernel counterexample without
   treating SymPy as an alternative compiler.
6. Only after such evidence certify restored-cycle F15 100x lower bound.

No ESD edit; same source-attribution discipline as earlier PR rounds.


## Strictly evanescent exterior branch, with no fictitious useful power

A second, separately guarded exterior admittance `evanescent_outgoing_admittance` implements a lossless `q_z=+i sqrt(kx²-w² mu eps)` for `kx²>w² mu eps`. A source sheet between two identical evanescent halfspaces has nonzero complex/reactive field, but exact zero **real** outward Poynting flux and zero real time-average sheet work for the tested lossless fixture. The exact zero-thickness sheet Green is `[-2 R Y_ev]^-1`. The frequency/angle cutoff and incorrectly selected propagating/evanescent branches are rejected instead of silently reinterpreted.

Added two tests. Final independent locally executed combined exact SymPy suite: **43/43 PASS** (32 preexisting + 11 radiation/source tests). This is evidence about the defined finite planar mathematical response only: neither zero real work for a pure evanescent mode nor positive propagating source-sheet work says anything about separately measured solar replenishment, a global Earth-ionosphere cavity or the Filsinger electrical terminal. Absorbing complex branch selection and the full k_parallel 2D inverse Fourier transform remain OPEN.


## Next high-alpha cut executed: arbitrary transverse Fourier vector and tilted geomagnetic Hall tensor

New `scripts/smith_filsinger_oblique_maxwell_sympy.py` now derives the exact **local Fourier-domain 4×4 Maxwell tangential generator** for both `k_x,k_y`, scalar μ and an arbitrary 3×3 complex permittivity tensor ε (with invertible ε_zz). Unlike the previous k_y=0 model, it eliminates BOTH longitudinal E_z and H_z using the actual Maxwell curl constraints, retaining ε_zx, ε_zy, ε_xz and ε_yz. `tilted_hall_permittivity` constructs a lossless Hermitian gyrotropic tensor `ε=ε_base I+i h [b]_cross` with arbitrary oblique direction b.

For isotropic homogeneous exterior halfspaces the strict propagating outgoing admittance is

    Y(kx,ky) = 1/(ω μ q)
      [[-kx ky, -(q²+ky²)], [q²+kx², kx ky]],
    q = sqrt(ω² μ ε - kx² - ky²) > 0.

The sheet source-to-field Green is the same exact Schur/boundary inverse previously proved for k_y=0, now with the full k-vector, and the existing three-layer Cayley transfer. This is a TRUE Maxwell four-tangential-component *spectral slice*, not a full 3D inverse-Fourier/retarded-space dyadic.

New `scripts/test_smith_filsinger_oblique_maxwell_sympy.py` gives **8/8** additional exact checks: correct reduction to the old k_y=0 generator, Hermitian tilted Hall flux-conservation `M†F+FM=0`, outgoing flux signs for three distinct wavevectors, exact lossless three-layer transfer and sheet-source work, longitudinal-singularity rejection, and spectral cutoff rejection.

**Latest full locally run independent source-equivalent exact suite: 51/51 PASS** (32 original + 11 outgoing/evanescent + 8 oblique/tilted). Both new tests wired into the same SymPy gate and consolidated Python runner. No Agda kernel claim. No physical material fit or original natural source calibration.
