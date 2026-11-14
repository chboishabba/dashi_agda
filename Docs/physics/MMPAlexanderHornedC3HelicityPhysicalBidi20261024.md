# Wild horned-sphere topology × MMP fermions × three driven plasma regions — discriminator max-cut
**Date:** 2026-10-24 · **Downstream PR:** #1248 · **Upstream horn geometry:** PR #1244 (current inspected head `401e85bb6e545ed6f6983b2522079d518bb21dfb`).

## Executive status

**Horned sphere is RELEVANT for non-Abelian holonomy, C3 actor, finite-collar spectral boundary and source-discrimination; it is NOT an automatic source of MMP magnetic flux, exotic stress, wild topology production or traversable spacetime.** Our higher-priority physically sourced alternative is a three-driven Maxwell field's helicity → massless Dirac chiral anomaly → changed fermion state. The subsequent renormalized `<T>` and backreaction are OPEN.

## Precise attribution and proof hierarchy

- J. W. Alexander (1924), classical wild horned sphere (embedding S² in S³), and standard Alexander duality for compact S²; John Hatcher, *Algebraic Topology* Example 2B.2, stage free-group commutator injections. These are original theorem roots, not our newly invented effects.
- PR #1244: **C3 three-arm geometry**, proposed complement colimit `G_A*G_A*G_A`, conditional noninner external C3, free-factor detector, source-written Agda/Lean, finite A5 quotient `A5³⋊C3`, 180-dimensional c=0 coordinate VOA and A5-to-internal-C3 restriction. Exact geometry-to-`pi1` collar/van-Kampen limit and exact-head Agda/Lean receipts remain OPEN; no full Monster realization follows.
- PR #1235: Hopf U1 transition cocycle, with smooth bundle/Chern principal-bundle proof obligations; PR #1239: braid/Pin and KK local gauge connection. PR #1215: actual finite C3 field/curvature/stress equivariance. Sibling PR state is not merged authority.
- J. Maldacena, A. Milekhin, F. Popov, arXiv:1807.04726 (2018), CQG 40 (2023) 155016, DOI 10.1088/1361-6382/acde30: a **different**, magnetically charged spin-c fermion wormhole. It needs a nonbounding magnetic S² flux, QFT negative stress and consistent two-ended metric.
- Stephen Adler (1969), John Bell/Roman Jackiw (1969): axial anomaly; MHD magnetic-helicity evolution is established classical theory (Berger/Field and successors); **not** a new derivation or gravitational proof. Conventions (one massless complex Dirac flavor, coupling e, hbar=c=1): `dQ5/dt=e²/(2pi²)∫E·B` with no axial boundary flow, and `dH/dt=-2∫E·B` for closed no-flux magnetic boundary. Signs are oriented by the chosen E,B convention.

## Exact topology: wild S² != magnetic throat

For every embedded S² in S³ (including Alexander's wild one), Alexander duality gives
`H~_i(S³\S²;Z) ≅ H~^(2-i)(S²;Z)` with reduced H0=Z, H1=H2=0.

Each of TWO connected complementary components is acyclic: `H1=H2=0`. By the universal coefficient theorem `H²(component;Z)=0`; the component by itself has **no nontrivial complex line-bundle first Chern flux**. Its `H1=0` also implies any flat Abelian U1 character of pi1 is trivial. Nevertheless one exterior can have a nontrivial perfect non-Abelian pi1, so genuinely nonabelian representations/flat holonomy may be possible on a **separately specified connection**.

In contrast spatial `R × S²` has `H₂=Z`: Maxwell `dF=0` does not force `∫S² F=0` on its nonbounding cycle. A physical spin-c index q follows from quantized `(e/2pi)∫S²F=q` and the actual charged Dirac operator. This is the source-free 'charge without charge' throat flux; the horn exterior alone cannot replace it.

For 3 disjoint ordinary 3D balls removed from R³, `H1=0`, `H2=Z³`, but smooth Maxwell fields extending through each ball with `dF=0` still have zero net flux on each bounding sphere. Three rotating/moving ordinary balls do not generate a monopole. Nor does a 2D projected B3 braid necessarily survive unconstrained 3D movement; only genuine spatial field tubes, paths with physical constraints, or a specified nontrivial gauge bundle may carry topological data.

`scripts/check_horned_vs_mmp_magnetic_topology_20261024.py` checks Alexander-duality-derived homology bookkeeping and independent finite perfect A5/C3 actor. It does **not** prove Alexander duality, the wild embedding, a nonabelian gauge-field existence theorem, or a three-arm geometric pi1 match.

**Topological wall P6.H1:** explicit sourced smooth finite-radius geometry `M_n`, a bundle map from actual horn complement to a selected physical gauge sector, an admissible SU2/SO3 or spin-c lift (A5 embeds in SO3, *not* as a faithful subgroup of SU2 without passing to binary icosahedral 2.A5), elliptic self-adjoint curved Dirac boundary operator, and spectral convergence in the wild limit. Any nonzero source-specific difference `Delta<T>` must be computed before Einstein coupling.

## Constructive three-source EM-fermion bridge: helicity and axial anomaly

Consider one analytically exactly solvable *periodic-volume toy* with three independently driven real Beltrami modes:
`a_x=(0,sin(kx),cos(kx))`,
`a_y=(cos(ky),0,sin(ky))`,
`a_z=(sin(kz),cos(kz),0)`.
Each has `curl a_i = k a_i`, `div a_i=0`, and distinct modes are orthogonal after spatial integration over the period cell. Let `A(x,t)=Σ_i f_i(t)a_i(x)` and `E=-∂_t A`, `B=curl A=kA`.

Then `H=∫A·B=kVol Σ_i f_i²` and
`∫ E·B = -kVol Σ_i f_i f_i' = -H'/2`.
The one-flavor massless Dirac axial anomaly gives
`dQ5/dt=(e²/2pi²)∫E·B`; hence under stated **closed / no boundary / no mass / no axial losses** conditions
`d/dt (Q5+ e² H/(4pi²))=0`.

**Nontrivial NEGATIVE CONTROL:** for equal 120° phase-wound sinusoidal rotating coefficients `f_i=a cos(ωt+2πi/3)`, `Σ f_i²=3a²/2` is constant, so the VOLUME-INTEGRATED `E·B=0` and `dQ5/dt=0`, even though local E,B and Fourier modes vary. Mere C3 phase rotation fails the net anomaly pump discriminator.

**Positive analytic control:** envelope-modulated `f_i=u(t)cos(ωt+2πi/3)` gives `H=(3/2)kVol u²`, `∫E·B=-(3/2)kVol uu'`, and the exact anomaly-helicity balance above. This is a classical field plus established QFT Ward identity, NOT a source-derived fermion `W_ren`, an engineered negative Casimir state or any gravitational effect. Plasma conductivity/fermion masses/chiral relaxation and open-boundary helicity injection can dominate in physical devices.

`scripts/check_three_drives_helicity_axial_anomaly_20261024.py` verifies Beltrami structure, exact balanced null, envelope response, and anomaly/helicity identity with SymPy. This is analytically 3D periodic field, **not** a rotating disk or three localized balls; model-specific localization and causal plasma boundary solve are the next physical promotion.

## Phase mapping and deliverables

| Phase | Horn donor relevance | Near-term acceptance |
|---|---|---|
| P0 baseline | keep sibling PR #1244 source/version fixed, don't copy unverified exactness | `check_mmp_global_effective_bvp_replay_20261024.py` reruns q=10,11,12,13,24; first exactly sourced numeric replay now committed in PR #1248 |
| P1 globally renormalized Dirac state | **not a prerequisite** | curved spin-c `W_ren[g,A;state]`, all stress/current/trace/Ward; invariant regulator convergence |
| P2 self-consistent two mouths | wild horn not required for MMP U1 flux | global Einstein–Maxwell–fermion BVP without quantum-source hard switch at P=0 |
| P3 stability/transmission | possible **optional** non-Abelian/scattering boundary conditions | identify physically admissible self-adjoint modes and spectrum; `l=0,1` etc |
| P4 three independent drives | primary priority: helicity/anomaly rather than wildcard topology | physical 3D localized sources, boundary helicity flux and `E·B` controls; mass/chirality losses; driven `δW`, `δ<T>` |
| P5 observables | direct source vs normal EM and artefact | probe gravity separately from electromagnetic torque, fields and thermal/vibration coupling |
| P6 wild-horn/SUSY/VOA optional | non-Abelian holonomy `A5³⋊C3`, source loss, C3 selection | actual geometric pi1, representation-to-connection/spectral lift and source-specific physical effect; no magnetism-from-number equivalence |

## Pareto rule

Spend research effort **first** on P0 replay and P1 source renormalization, then P2 global same-state solve. Within P4, test the explicit helicity `E·B` and axial-charge/mass relaxation channel before pursuing wild-horn shape. Horned PR #1244 already owns the finite combinatorial/topological development; don't duplicate it. If a physical boundary operator responds to non-Abelian horn holonomy with a computed fermion stress or actual measurable transmission difference, promote that **specific** operator map and only then connect to P2.

## Verification and limits

- Local committed-equivalent numerical q=10,11,12,13,24 replay: PASS with junction radii R=10.63758, 11.16712, 11.683162, 12.189933, 18.011908; no-thin-shell **effective** stress matching, not globally smooth quantum state.
- Local horn finite A5/topological logic script: PASS for finite checks. The homology conclusion is taken from Alexander duality, not established anew by code.
- Local three-field helicity/anomaly SymPy: PASS; proven identity for selected fields/normalizations, **not** a quantized physical plasma apparatus.
- The 4D curved Dirac determinant, renormalized global in-in response, induced Hall/Schwinger current, regular two-mouth quantum source and real three-plasma coupling are still unpaid. Agda/Lean exact-head receipts not obtained for horned sibling PR #1244.


## Stronger literal-three-region analytic Maxwell surrogate (post initial symbolic gate)

`scripts/check_three_localized_field_helicity_20261024.py` replaces the extended periodic-only field test with **three individually localized, internally twisted, smooth vector-potential packets**. For each center `c_i=(c_ix,c_iy,0)`, define `u=x-c_ix`, `v=y-c_iy`, `g_i=exp(-(u²+v²+z²)/(2σ²))` and `A_i=g_i(-v,u,β)`. Then `B_i=curl A_i` obeys `div B_i=0` EXACTLY, and its local self-helicity density is `A_i·B_i=2β exp(-|x-c_i|²/σ²)`.

For center separation `d=|c_i-c_j|`, the full-space cross-helicity is **analytically integrated**:
`h_ij=∫ A_i·curl A_j d³x = β π^(3/2) σ³ exp(-d²/(4σ²)) (2-d²/(2σ²))`.
For `i=j`, `h_0=2βπ^(3/2)σ³`. An independent 3D Gauss–Hermite numerical quadrature at `d=1.5,σ=1,β=0.7` matches `h_ij` within `1.4e-15` for a locally executed equivalent script.

Three centers at an equilateral triangle of circumradius R have common `h_1=h_ij(d=√3R)`; the full helicity is
`H=(h_0-h_1)Σ_i f_i²+h_1(Σ_i f_i)²`. For internal amplitudes `f_i=a cos(ωt+2πi/3)`, exact trig gives `H=3a²(h_0-h_1)/2` **independent of t**, even with overlap. Thus net `∫E·B=-H'/2=0`: pure symmetric phase rotation is a negative control. For `f_i=u(t)cos(ωt+2πi/3)`, `∫E·B=-(3/2)(h_0-h_1)uu'`; ideal closed-volume ABJ/helicity exchange follows.

These fields model **three localized electromagnetic regions**, NOT a rotating disk and NOT dynamical self-consistent plasma equilibria. Gaussian tails overlap; no hard plasma-fluid boundary, charge/current sourcing, power budget or in-in Dirac state is constructed. Since ordinary Maxwell stress satisfies NEC, these fields alone do NOT provide negative null gravitational stress. This gate asks whether the induced *fermionic* quantum state has a source-derived `δ<T_kk>_ren` with the required sign; the simple chiral Fock response tested in `check_fermion_axial_pump_nec_budget_20261024.py` instead raises NEC.
