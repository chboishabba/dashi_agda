# P3 actual single-centre KK monopole and original 369/Yang–Mills donor audit

Date: 2026-11-18; implemented on the existing draft PR #1531.

## 1. Classical solution: identify the original five-dimensional action

Take pure five-dimensional Einstein–Hilbert vacuum gravity,
\[
 S_5={1\over16\pi G_5}\int_{M_5}d^5x\sqrt{-G} R[G],
 \qquad R_{AB}[G]=0.
\]
With local coordinates \((t,r,\theta,\phi,\psi)\), \(m>0\), define
\[
 V(r)=1+{m\over r},\quad
 A=m\cos\theta\,d\phi,\quad
 ds_5^2=-dt^2+V(dr^2+r^2d\Omega_2^2)+V^{-1}(d\psi+A)^2.
\]
The fibre period is \(\psi\sim\psi+4\pi m\). This is the classical
single-centre Gibbons–Hawking / Taub–NUT metric times a static time
direction, historically used for the Gross–Perry–Sorkin KK monopole.
**This is a known explicit solution, not a new DASHI gravitational solution.**

Classical local criterion: \(\Delta_{\mathbb R^3}V=0\) away from the nut,
\(dA=*_{\mathbb R^3}dV\). The Gibbons–Hawking theorem then supplies a
hyperkähler Ricci-flat spatial 4-metric locally. The 5D Lorentzian product
is also Ricci-flat. Smoothness across the nut follows from the proper
fibre period and patch gluing; it is not established by a single
coordinate-chart calculation.

As \(r\to\infty\), \(V\to1\): asymptotic local geometry is
\(\mathbb R^{1,3}\times S^1\) with the magnetic fibration globally
nontrivial over the asymptotic sphere. The solution has finite positive
conserved ADM/KK mass for fixed compactification length, unlike an
infinite translationally invariant string. The numerical normalization of
that mass and its 5D boundary Hamiltonian are separate acceptance gates.

## 2. Exact Chern charge, local nut and the 369 spatial cycle

Writing \(\chi=\psi/m\), its period is \(4\pi\). The normalized
period-\(2\pi\) circle connection is
\[
 a={1\over2}(d\chi+\cos\theta\,d\phi),\quad
 da=-{1\over2}\sin\theta\,d\theta\wedge d\phi,\quad
 {1\over2\pi}\int_{S^2}da=-1.
\]
Hence the asymptotic circle has Chern number \(-1\) in this orientation.
One may use northern and southern potential coefficients
\((\cos\theta-1)/2\) and \((\cos\theta+1)/2\); the transition has unit
winding. The nonzero Chern number concerns the circle bundle, not a
particle's quantum spin or any nonabelian YM instanton number.

For \(\rho=2\sqrt{mr}\), the near-nut spatial metric becomes
\[
 d\rho^2+{\rho^2\over4}
 [d\theta^2+\sin^2\theta d\phi^2+
 (d\chi+\cos\theta d\phi)^2]+O(\rho^2/m^2).
\]
The leading angular metric is the round unit \(S^3\) metric in the
chosen Euler coordinates, avoiding a conical/orbifold singularity when
\(\chi\) has period \(4\pi\).

The monopole field in Cartesian notation is
\(\mathbf B=-m\mathbf x/|\mathbf x|^3\) (orientation as above).
Under \(P(x,y,z)=(z,x,y)\), \(\mathbf B(Px)=P\mathbf B(x)\) and
\(P^3=I\). This is the same **spatial-axis permutation pattern**
used by the original 369/YM source, but it acts on an independent
classical U(1) monopole field.

## 3. Which original 369/YM sources help?

| Existing source | Literal reusable result | Not yet established |
|---|---|---|
| `SU2Bracket369OrientationBridgeExact.agda` | quaternion su2 bracket = 2×oriented R3 cross product | SU2 YM connection equals KK gravitational U1 |
| `BalabanCMP109SpatialC3ActionExact.agda` | physical xyz spatial cycle from original CMP109 grid, order 3 | continuum map from generated Balaban gauge source to nut |
| `CompactLieLatticeGauge.agda` | endpoint-aware gauge-covariant holonomy | smooth continuum Wilson loops on KK monopole sourced by same physical YM theory |
| `YMClayNativeSixPlaneC3SourceReductionExact.agda` | selected literal six-plane C3 under orientation reversal witnesses | arbitrary continuum C3 YM covariance or continuum Clay mass gap |
| `HopfQuaternionAxisProjectionExact.agda` | quaternion Hopf-axis U1-phase invariance | concrete global smooth KK bundle identified with this exact SU2 carrier |
| `AlexanderHornedSpin360720Exact.agda` | finite central-sign witnesses | FR quantization of physical KK monopole |
| NEW `YM369KKHopfC3DonorWeldExact.agda` | same PR imports original YM bracket, original physical C3 cycle, existing Hopf phase proof | no unwarranted same-object coercion |

The SU2 ≅ unit-quaternion S3 geometry can describe a 3-sphere around
the nut; its Hopf U1 fibres have the right *geometric shape*. Nonetheless
a global gauge/metric map with matching normalization, orientation and
transition functions is needed before asserting equivalence of the
existing Agda carrier to the KK monopole.

## 4. Derived restricted configuration family, not fabricated FR spin

The known solution supplies a concrete restricted family
\(\mathcal M_1=\{g_X:X\in\mathbb R^3\}\) with
\(V_X(\mathbf x)=1+m/|\mathbf x-X|\), including the corresponding
translated monopole connection and nut at \(X\). Under asymptotically
framed gauge/diffeomorphism transformations that do **not** identify
distinct spatial positions, different X give different nut locations.
The natural translation-orbit parameter space is \(\mathbb R^3\).
It is contractible and supports no **nontrivial based rotational loop
from translations alone**. The centred monopole is spherically
symmetric up to appropriate U1 patch/gauge transformations, so treating
its orientation as an independent SO3 collective coordinate would
manufacture moduli.

This does **not** determine the fundamental group of the full physical
configuration space \(\mathcal Q\) of finite-energy 5D fields in
the same topological sector after specified gauge/diffeomorphism
quotients. Thus no contradiction with general FR soliton spin
construction is claimed. The actual \(\pi_1(\mathcal Q)\),
2pi rotation loop, exchange loop, representation and dynamics remain
separate gates.

## 5. What is checked; what remains

- [x] Explicit classical *original-action* five-dimensional KK vacuum candidate selected (known Gross–Perry–Sorkin / Gibbons–Hawking construction).
- [x] Exact SymPy check of \(\Delta V=0\), \(dA=*dV\), circle Chern number \(-1\), near-nut radial/angular limits, Cartesian C3 covariance, and north/south potential transition.
- [x] Original 369/YM Agda donors inspected and imported together without equating their field theories.
- [x] Restricted translated-one-nut family and its \(\mathbb R^3\) parameterization identified; not a complete physical phase space theorem.
- [ ] Independently construct the entire 5×5 Ricci tensor and verify zero in the same coordinates; current source uses the established Gibbons–Hawking theorem.
- [ ] Prove global completeness, correct patch transition, asymptotic KK/ADM mass and full energy/charge normalization in formal libraries.
- [ ] Prove actual YM gauge→KK U1 curvature/connection map on the same field, if one exists; avoid assuming SU2 curvature = spacetime spin connection.
- [ ] Classify full physical configuration space of finite-energy fields in the charge-one sector, including gauge, diffeomorphism and boundary structure; determine 2pi loop and two-soliton exchange.
- [ ] Dynamical perturbative and nonlinear stability in full 5D gravity; existence of local translation zero modes alone does not pay this.
- [ ] Other 369/YM continuum / mass-gap gates unchanged; no promotion from finite C3 symmetry.

## 6. Attribution snowball (mandatory)

- **Primary classical roots:** G. W. Gibbons and S. W. Hawking, *Gravitational Multi-Instantons*, Phys. Lett. B 78 (1978) 430–432; D. J. Gross and M. J. Perry, *Magnetic Monopoles in Kaluza–Klein Theories*, Nucl. Phys. B 226 (1983) 29–48; R. D. Sorkin, *Kaluza–Klein Monopole*, Phys. Rev. Lett. 51 (1983) 87–90. The Ricci-flat and bundle conclusions are prior classical work, NOT introduced here.
- **DASHI prior owners:** native 369 Yang–Mills source-C3/SU2/Hopf owners listed in §3, with exact existing paths.
- **User-directed hypothesis/question:** proposed reusing original 369/YM to obtain a KK/Hopf stable finite-energy solution and test soliton spin-½.
- **New bounded implementation:** this original-carrier comparison, explicit source solution register, SymPy check script `check_kk_gross_perry_sorkin_c3_monopole_sympy.py`, and Agda imported-source donor weld `YM369KKHopfC3DonorWeldExact.agda`; ChatGPT-assisted.
- **Verification:** identities checked in-session using SymPy; the committed exact source checkout and Agda kernel have NOT been executed in this environment. Global Ricci flatness invokes the historical GH theorem rather than a new machine-checked curvature derivation.
- **Nonpromotion:** geometric monopole ≠ electron, Hopf Chern ≠ half-spin, 369 finite YM ≠ smooth KK gravity, and ADM mass ≠ controlled anomalous propulsion.

## 7. Companion *same original SU(2) theory family* candidate: static BPST instanton particle

One route uses **5D SU(2) Yang–Mills on a fixed Lorentzian 4+1
background**, rather than replacing the 369/YM connection by the
*gravitational* U1 KK monopole. The original action is
\[
S_{5,YM}=-{1\over4g_5^2}\int d^5x\,F^a_{AB}F^{aAB}.
\]
Take \(A_0=0\), \(A_i(x)\) independent of time with
\(i=1,\ldots,4\) and the **classical charge-one BPST instanton**
on Euclidean \(\mathbb R^4\). Its self-dual field curvature satisfies
the Yang–Mills equations (by Bianchi/self duality), giving an explicit
time-independent 4+1-dimensional solution on that fixed background.
The standard convention has
\[
F^a_{ij}F^a_{ij}={192\rho^4\over(r^2+\rho^2)^4},\qquad
E={1\over4g_5^2}\int_{\mathbb R^4}F^a_{ij}F^a_{ij}
={8\pi^2\over g_5^2}.
\]
The radial integral uses \(\mathrm{vol}(S^3)=2\pi^2\) and equals
\(\int_0^\infty r^3 F^2dr=16\). This is finite energy and
nonzero instanton number, not an arbitrary hypothetical soliton.

**High-value negative control:** \(E\) is exactly independent of the
BPST size \(\rho>0\). Thus unlike the illustrative Skyrme
\(aR+b/R\) energy, ordinary 4+1-dimensional pure Yang–Mills
does not pick a preferred soliton radius at the classical level.
A topological energy bound and a size-zero mode are not full nonlinear
stability. Finite-energy does not mean a dynamically selected size.
The moduli of the charge-one framed instanton include at least
4 centre coordinates, positive scale, and an SU2-gauge-orientation
structure **whose quotient depends on framing and allowed gauge
transformations**. Neither a SO3 orientation coordinate nor spin-half
may be inserted without that choice.

For an asymptotic **KK compact dimension** (space \(\mathbb R^3\times S^1\))
a BPST configuration on \(\mathbb R^4\) is not automatically periodic:
one must use an actual caloron or other periodic solution with selected
holonomy and compactification radius. For **coupled 5D Einstein–YM**,
flat space plus this nonzero-energy YM field is NOT a solution of the
complete Einstein equations without gravitational backreaction.
These remain physical gates. We now have TWO separate explicit parent
actions, not one fabricated cross-theory identity:

1. Pure 5D Einstein vacuum → known KK magnetic monopole (gravity).
2. 5D SU2 YM on fixed Minkowski4+1 → known BPST instanton particle
   (gauge field, topological finite energy, scale modulus).

The new checker
`scripts/check_kk_ym369_bpst_instanton_particle_energy_sympy.py`
independently confirms the exact density integral and scale
degeneracy. It does not reconstruct the BPST connection in the
Agda-native bond carrier nor compute a coupled gravitational metric.

### Literature and contribution attribution for this extension

- **Original source:** A. A. Belavin, A. M. Polyakov, A. S. Schwartz,
  Yu. S. Tyupkin, *Pseudoparticle solutions of the Yang–Mills equations*,
  Phys. Lett. B 59 (1975) 85–87. The self-dual instanton and finite-action
  mechanism are classical, not DASHI inventions.
- **DASHI predecessors:** `BalabanSU2QuaternionCarrier`,
  `SU2Bracket369OrientationBridgeExact`, `CompactLieLatticeGauge`,
  and the native YM/C3 Wilson source constructors.
- **User original question:** test whether existing 369/YM makes the
  KK/Hopf soliton programme more concrete, while requiring original
  field/source identity.
- **Current original contribution:** side-by-side physical model
  separation and exact scale-neutrality countercontrol, with
  ChatGPT-assisted symbolic verification. No physical particle-spin
  inference or claim that the 369 finite YM construction is the
  classical BPST continuum solution.

### Revised maximum-cut choice

- **Route G (geometry):** prove exact source-metric KK monopole bundle and
  classical Ricci flatness with formal global energy; then study framed
  gravitational configuration-space rotation loops.
- **Route Y (Yang–Mills):** construct the actual BPST gauge field in the
  *existing SU2 quaternion carrier*, prove self-duality/Bianchi and
  normalize instanton number; then connect to R3×S1 caloron holonomy
  and a genuine gauge-configuration-space \(\pi_1\).
- **Weld G↔Y:** only after specifying a 5D Einstein–YM action, constructing
  nontrivial backreacted geometry, checking matching topology/source
  under reduction, and proving any proposed spin-fermion selection.
