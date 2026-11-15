# KSW/KK → AdS₅ brane bulk-shortcut maximum cut — Levin, SUSY, string, TSFV, wormholes, exotic gravity

**As of 2026-11-15 (Melbourne); ownership:** original existing DASHI Agda PR #1504, not a new PR or CI acceptance. **Source checked:** Caldwell & Langlois, *Shortcuts in the fifth dimension*, Phys. Lett. B 511 (2001) 129–135, DOI [10.1016/S0370-2693(01)00631-1](https://doi.org/10.1016/S0370-2693(01)00631-1), original [arXiv:gr-qc/0103070](https://arxiv.org/pdf/gr-qc/0103070), actual Eqs (1),(4),(7)–(20) verified against original PDF (especially pages 2–5).

## Crucial non-equivalence: internal KK projection ≠ curved brane geodesic comparison

Standard **spacelike-fibre principal-bundle KK** reduction:

\[
ds_5^2=g_{\mu\nu}dx^\mu dx^\nu+\phi^2(dy+\kappa A_\mu dx^\mu)^2,\quad \phi^2>0.
\]

Every 5D causal tangent projects causally **relative to this chosen 4D base metric**:
\(ds_5^2\le0\Rightarrow ds_4^2\le0\).
Existing original owner \`DASHI/Physics/Gravity/KSW668KaluzaKleinSpacelikeFiberCausalExact.agda\` proves the algebraic rational analogue conditionally. It does NOT assert an isometry between an arbitrarily curved embedded brane's **intrinsic path metric** and a 5D bulk's fastest causal path.

For brane \(\iota:\Sigma^{3,1}\hookrightarrow M^{4,1}\), the induced metric is
\(h=\iota^*g_5\).
Two physically distinct causal reachability relations matter:

- \(J^+_\Sigma(p)\): signals restricted to **the brane** \(\Sigma\);
- \(J^+_{M_5}(p)\cap\Sigma\): signals permitted to traverse **the bulk** and return to the brane.

An apparent shortcut is a same-source/receiver pair
\(q\in[J^+_{M_5}(p)\cap\Sigma]\setminus J^+_\Sigma(p)\), with actual bulk propagation/coupling.
It need NOT violate causal propagation in \(M_5\). This is the precise brane-metric versus ambient-metric distinction to be typed in a 3+1 Lorentz/KK proof.

### Cut D2.A — first complete same-metric counterexample: a cylindrical test brane

In flat 5D Minkowski, \(ds_5^2=-dt^2+dX^2+dY^2+du^2+dv^2\), embed
\(X=R\cos\theta,\;Y=R\sin\theta\). The induced 4D brane metric is
\(h=-dt^2+R^2d\theta^2+du^2+dv^2\). For antipodal brane observers, brane-constrained earliest light time \(t_\gamma=\pi R\); a genuine 5D null **geodesic** chord returns at \(t_g=2R\). Its earlier receiving event is **spacelike on the brane**, since \(ds^2_\mathrm{intrinsic}=R^2(\pi^2-4)>0\), but **null in 5D**. Speed never exceeds the 5D light cone.

\`scripts/ksw668_brane_bulk_shortcut_same_metric.py\` symbolically checks full induced metric, endpoints, 5D null chord, brane intrinsic null arc and nonzero extrinsic mean curvature \(K=-1/R\), plus a **static warp no-shortcut control**. A static RS-type shared warp \(ds_5^2=a(y)^2(-dt^2+d\mathbf x^2)+dy^2\) satisfies \(dt^2\ge d\mathbf x^2+dy^2/a(y)^2\), hence no early bulk arrival on its stationary planar brane purely from warping time and space identically. Tests distinguish a curved/moving brane from a static product KK or RS Minkowski slice. The finite 3–4–5 path against 6-unit ambient chord is source-written in \`KSW668BraneBulkRationalNullComparatorExact.agda\` (Agda kernel **NOT RUN**); it is a NON-SMOOTH rational skeleton, not the smooth cylinder or Einstein system.

### Cut D2.B — the test brane can carry real positive stabilising worldvolume stress

A purely tensionful static cylinder has \(K=-1/R\ne0\) and collapses as a free Nambu–Goto membrane. Rather than pretend it is supported, add a periodic worldvolume scalar \(\chi=n\theta\) with positive kinetic stiffness \(f^2\) and brane tension \(T>0\):

\[
S_\Sigma=-\int\sqrt{-h}\,[T+\tfrac12 f^2 h^{ab}\partial_a\chi\partial_b\chi],\quad
E(R)=2\pi TR+\frac{\pi f^2n^2}{R}.
\]

The radial Euler–Lagrange/shape balance and uniform-radius stability give
\(R_*=f|n|/\sqrt{2T}\),
\(\partial_RE|_{R_*}=0\),
\(\partial_R^2 E|_{R_*}>0\),
\(S^{ab}K_{ab}=0\);
and for a null brane tangent \(k^a\),
\(S_{ab}k^ak^b=f^2(k^a\partial_a\chi)^2\ge0\).
For \(T=2,f=2,n=1,R_*=1\), \(E/\text{noncompact area}=8\pi\), curvature stiffness \(8\pi\). **All were verified by independent exact local SymPy.** New owner \`ksw668_brane_winding_stability_source.py\`; finite Agda integer shape-balance owner \`KSW668BraneWindingSourceFiniteExact.agda\`.

This is a **consistent probe-worldvolume first-variation/source** with positive matter energy, not yet a coupled Einstein–Israel thin-brane solution, all-mode stability or actual localized graviton source/receiver. Massless 5D scalar \(F(t+X)\) solves the bulk wave equation as a field existence benchmark, not a localized message or gravitational wave.

### Cut D2.C — original AdS₅ Einstein/brane matter and original Eq.(19) reproduced

Original paper's flat \(k=0\), \(\mu=0\) Schwarzschild–AdS bulk:
\[
ds_5^2=-f(R)dT^2+f(R)^{-1}dR^2+R^2d\mathbf r^2,
\quad f(R)=R^2/\ell^2.
\]
Choose a *specific original-source allowed cosmological brane*:
\(\ell=1,\Lambda_5=-6,\kappa_5^2=6,\sigma=1\),
\(a(t)=t\), \(H(t)=1/t\) and
\(\rho(t)=\sqrt{1+t^{-2}}-1>0\).
Brane pressure \(p(t)=-\rho(t)-\dot\rho(t)/(3H(t))\) supplies
\(\rho+p=1/[3t^2\sqrt{1+t^{-2}}]>0\).

The original modified Friedmann Eq.(1)
\(H^2=\kappa_5^4(\rho+\sigma)^2/36+\Lambda_5/6\)
holds exactly. So do the FRW continuity equation and induced brane proper clock Eq.(4).

The bulk is **genuinely AdS curved Einstein–vacuum with cosmological constant**:
all 25 entries of \(G_{AB}+\Lambda_5g_{AB}\) vanish exactly, \(R_5=-20\).
The original paper Eq.(19),(20) are:
\[
r_g^2=\left(\int_{t_A}^{t_B}\frac{dt}{a}\sqrt{1+\ell^2H^2}\right)^2
     -\left(\int_{t_A}^{t_B}\frac{dt}{a}\ell H\right)^2,\qquad
r_\gamma=\int_{t_A}^{t_B}\frac{dt}{a}.
\]
At \(t_A=1\), \(t_B=2\), exact source quadratures give
\(I_1=[\operatorname{asinh}t-\sqrt{1+t^2}/t]_1^2\),
\(I_2=1/2\), \(r_g\simeq0.697797781099381\)
and \(r_\gamma=\log2\simeq0.6931471805599453\).
An actual null GEODESIC is reconstructed using original Eqs (12),(15)–(17) from source at \(R=1,r=0\) to receiving brane at \(R=2,r=r_g\).
Its 5D null norm and nonaffine geodesic equations are verified exactly.

**Same receiving brane worldline, not coordinate-speed sleight of hand:**
bulk arrival \(t_g=2\); brane-confined light at \(r=r_g\) reaches the receiver when \(\log t_\gamma=r_g\), namely
\(t_\gamma\simeq2.009322862731128\), advantage \(\Delta t\simeq0.009322862731128\) in *dimensionless brane proper time*. This is a **mathematical physical-model prediction** using the original AdS source paper, NOT an observed effect or a universal ratio.

Execution: \`scripts/ksw668_caldwell_langlois_original_eq19.py\` was built from actual original equations, with independent SymPy and high-precision mpmath local checks PASS. The added \`scripts/test_ksw668_brane_shortcut.py\` integrates source, kinematic, winding, and negative-control checks; the exact PR-head suite was **not** run in this isolated environment.

**Still OPEN**: full independent distributional Israel junction-tensor check with the actual same-source brane and orientation, all-mode stability, supported coupling of brane matter to 5D propagating gravitons and their observable on-brane detector response, emission lags, and physical frequency/band/curvature scales. Do not call a brane tensor with \(\rho+p>0\) an energy-generating anomaly.

### Cut D2.D — original Eq.(19) general inequality, not just a numerical example

For any \(w=dt/a>0\), \(x=\ell H\), set future unit timelike vector
\(V(x)=(\sqrt{1+x^2},x)\). The integral's Minkowski norm is at least the integral of the unit norms. The pair kernel obeys
\[
(1+x^2)(1+y^2)-(1+xy)^2=(x-y)^2\ge0,
\quad \sqrt{1+x^2}\sqrt{1+y^2}-xy\ge1.
\]
Therefore \(r_g^2-r_\gamma^2\ge0\), with equality if \(H\) is constant almost everywhere with positive source weight; a genuinely varying \(H\) yields strictly positive extra causal reach.

The **finite exact rational** version uses \(z_i\) with \(|z_i|<1\),
\(V_i=((1+z_i^2)/(1-z_i^2),2z_i/(1-z_i^2))\):
\[
r_g^2-r_\gamma^2
 =4\sum_{i<j}\frac{w_iw_j(z_i-z_j)^2}
  {(1-z_i^2)(1-z_j^2)}\ge0.
\]
For \(w_1=w_2=1,z_1=0,z_2=1/3\):
\(I_1=9/4,\ I_2=3/4,\ I_0=2,\ r_g^2-r_\gamma^2=1/2\).
Constant-H null control gives exact zero. Negative source weights are rejected. Independently verified with \`fractions.Fraction\`, lengths 2–14. \`KSW668CaldwellLangloisHorizonSourceRationalExact.agda\` source-writes the exact rational two-slice identity, constant-H equality and general reverse-Minkowski polynomial identity. Real-valued ordered sqrt and continuum integration are STILL NOT Agda-kernel certified.

### Cut D2.E — why standard KK, string, SUSY, quantum and wormholes do not collapse together

- **Ordinary compact KK mode no-go:** a 5D massless mode on \(\mathbb R^{3,1}\times S^1_R\) has \(\omega_n^2=|\mathbf k|^2+n^2/R^2\); for \(n>0\), \(v_{g}=|\mathbf k|/\omega_n<1\). Verified with \`ksw668_compact_kk_mode_dispersion.py\`. Extra dimensions or a KK mass tower *alone* do not imply shortcuts. This is compatible with curved-brane extrinsic shortcuts (different geometric input).
- **String/Dark Dimension owner:** \`DASHI/Physics/Closure/DarkDimensionStringPromotionBoundaryExact.agda\` separates Swampland/Distance conjectures, model parameters and KK observables from a uniquely identified UV string theory; source physical model not automatically a string compactification. A new UV source, compactification, spectrum and scale-to-lab coupling are required.
- **SUSY owner:** \`DASHI/Physics/QFT/WittenIndexSUSYBoundarySurface.agda\` explicitly leaves physical supercharges, Witten index, spin structure and superpartner evidence open. No sign of a SUSY-derived shortcut, positive source energy cancellation, or vacuum energy budget can be asserted.
- **TSFV owner:** \`DASHI/Physics/Closure/TSFVActionPhaseWeightSeparationExact.agda\` and \`DASHI/Physics/Foundations/TSFVFeynmanDerivationObligationsExact.agda\` distinguish candidate actions from \(S/\hbar\), amplitudes, quantum history and observed temporal causation. A retro-conditioned history or Feynman integral is not a controllable past-directed message.
- **ER=EPR, traversable wormholes:** Gao–Jafferis–Wall, \`10.1007/JHEP12(2017)151\`, achieves a conditional *theoretical* traversable solution using a boundary coupling and **negative averaged null energy** and explicitly does not permit causality violation. Kontou (2024), \`10.3390/universe10070291\`, reviews quantum energy inequalities and restrictions on wormholes. Negative renormalized QFT energy density ≠ thermodynamic free energy ≠ a freely available source for a device. Standard brane shortcut and traversable wormhole are physically DIFFERENT constructions.
- **Many worlds / Everett:** interpretation of a unitary quantum state does not furnish a physical inter-branch signalling Hamiltonian, source, detector or new classical energy. Distinguish interpretation from operational observable.
- **Existing physical promotion:** \`DASHI/Quantum/QuantumMereologySpacetimePromotionExact.agda\` correctly requires explicit dynamics/time/Einstein before promoting factor geometry to a spacetime. \`DASHI/Physics/Foundations/GRQFTExperimentDesignCrossPollinationExact.agda\` requires recovery regimes plus discriminating measurement.

The new Agda \`KSW668BraneLevinStringTSFVPromotionBoundaryExact.agda\` references the original Levin/String/SUSY/TSFV/Exotic owner types, proves their distinct carrier constructors and specifies eleven **uninhabited physical promotion premises** (same 5D geometry, induced metric, Einstein/junction, stability, bulk wave, source/receiver coupling, energy conservation, permitted quantum matter, global causal consistency, operational same-event proper time, independent observation). Merely constructing the interface does NOT pay those premises.

### Cut D2.F — Michael Levin is a useful *control-theoretic* cross-pollination, not extra spacetime

Original \`DASHI/Biology/Levin/ProblemSpaceAgency.agda\` distinguishes physical-3D, anatomical, physiological, transcriptional, social and abstract spaces; \`TravelingFieldControl.agda\` separates moving spatial neural/bioelectric patterns from a causal intervention; \`NeuralWaveAnalogComputation.agda\` refuses the inference wave→computation→conscious experience without an input/operation/output and perturbation witness.

Levin's pattern-regulation/target-morphology bioelectricity concerns **state-space geometry**, ion channels, gap junctions, tissue regulation and control policies (review DOI 10.1146/annurev-bioeng-071114-040647; 2026 Levin perspective DOI 10.1177/25763113261454327). The same C2/C3/Fraction/SSP residual/renormalisation techniques may analyse state compression, agency and morphogenetic memory, but the *dimension of an anatomical state space is not an extra Lorentzian spatial direction*. It cannot be fed into KK proper-time formulas without a physical metric coupling, source term and observations.

Relevant legitimate shared structure: **controller, plant, state estimator, intervention, residual, viable target set**. A candidate bioelectric controller must demonstrate actual intervention-driven state/phenotype changes; a brane shortcut requires five-dimensional propagation and detector timing. They share a proof architecture, not automatically their microscopic mechanism.

### Cut D2.G — adversarial exotic-gravity sources and GW constraints

The KSW video, Pais HFGWG, Li/Torr, Ning Li and Eskridge sources receive separate attribution, not invented common inventorship. Original existing \`DASHI/Physics/ExoticGravity/AntigravityProofSearchFrontierExact.agda\` identifies source-characterisation, phase/current, same-apparatus GR comparison and measured detector residual separately. \`LiTorrSIStressEnergyCompilerWeldExact.agda\` needs genuine energy/momentum/spatial-stress measurements rather than promoting mass-current alone.

The original GW170817/GRB170817A same-source observation constrained gravitational versus electromagnetic propagation speed at roughly \(10^{-15}\) under specified intrinsic emission-delay assumptions; source arXiv [1710.05834](https://arxiv.org/abs/1710.05834). A realistic expanding braneworld must **predict a physically scaled differential arrival in relevant bands** and compare to those bounds and short-range gravity tests. Our dimensionless 0.0093 advantage is NOT directly a contradiction until physical length/time units, curvature, ray coupling, source and detector band and emission lag are supplied.

### Exact remaining A/B/C proof gates, one PR per repo

| Priority | Concrete proof/producer | Status |
| --- | --- | --- |
| **A1 (formal source)** | Agda 2.9 kernel replay of original rational four modules and aggregator: no postulates/holes, same owner import | SOURCE WRITTEN — **kernel not run** |
| **A2 (analytical)** | Original real/ordered \(\sqrt{1+x^2}\) two-point reversed Minkowski inequality + weighted continuum double-integral strictness | finite exact algebra + external derivation; real Agda **OPEN** |
| **A3 (geometric)** | Same-solution induced \(h=\iota^*g_5\); exact 5D null geodesic; intrinsic 4D photon and common receiver proper-time arrival | source Eq17-20 checked in SymPy; Agda analytic weld **OPEN** |
| **B1 (dynamical)** | Full \(\Lambda_5\), matter, brane Israel jump, extrinsic \(K_{\mu\nu}\) plus worldvolume scalar/tension in same global solution | bulk G+Lambda and FRW/continuity checked; complete Israel **OPEN** |
| **B2 (stability/energy)** | Normal and tangential all-mode stability, material energy, quantum inequality/NEC and no closed causal loops | positive probe winding radial stability checked; full dynamics **OPEN** |
| **B3 (carrier)** | Real bulk graviton (or permitted field) mode PDE/boundary conditions; localized brane emission/detection response and nonzero amplitude | massless scalar homogeneous wave only; real graviton coupling **OPEN** |
| **C1 (observational)** | Source-calibrated length scales, GW/EM frequency-dependent delays, detector proper time, onset lag and source uncertainties | actual observational discriminators identified; physical prediction **OPEN** |
| **C2 (UV/quantum)** | Source-identified SUSY/string theory compactification, graviton localisation, mode spectrum, valid QFT state and TSFV/ER–EPR relation where relevant | source boundaries only; physics **OPEN** |
| **C3 (Levin/BioEM)** | Source-identified problem-space-to-tissue interventions and measured neural/morphogenetic residual, without confusing cognitive state dimension with spacetime | original causal field interfaces reused; **OPEN** |
| **D (exotic lab)** | Full SI stress/current/tensor field, pulse duration and control, measured gravitational residual, independent replication | original existing source apparatus obligations **OPEN** |

**Acceptance policy:** independent source science retains original author credit; local finite tests and symbolic equations are not Agda kernel receipts, and a mathematically consistent source candidate is not experimental validation. CI ignored by user request.

---

## Addendum: original Z₂ Israel junction **local source-equation closure** — 2026-11-15

The initial T8 roadmap marked the Israel source itself OPEN. That was correct before the following new calculation; this addendum supersedes that narrower status.

New \`scripts/ksw668_caldwell_langlois_israel_exact.py\` symbolically computes the original AdS5 \(k=\mu=0,\ell=1\) bulk Christoffels, moving FRW embedding \(R_b(t)=t\), \(dT_b/dt=\sqrt{1+t^2}/t^2\), *inward* spacelike unit normal covector
\[
n_A=(1,-\sqrt{1+t^2}/t^2,0,0,0).
\]
Its source-intrinsic \(h_{ab}=\mathrm{diag}(-1,t^2,t^2,t^2)\) and extrinsic mixed tensor obey
\[
K^t_{\ t}=-\frac{1}{\sqrt{1+t^{-2}}},\qquad
K^i_{\ j}=-\sqrt{1+t^{-2}}\,\delta^i_j.
\]
For the SAME brane worldline and SAME bulk metric, with \(\kappa_5^2=6,\sigma=1\),
\(\rho(t)=\sqrt{1+t^{-2}}-1\),
\(p=-\rho-\dot\rho/(3H)\),
\(S_{tt}=\rho+\sigma\),
\(S_{ij}=(p-\sigma)h_{ij}\), it checks the full exact classical \(Z_2\) Israel relation
\[
K_{ab}=-(\kappa_5^2/2)(S_{ab}-h_{ab}S/3)
\]
at **all 16 component positions**. Norm/orthogonality of the source normal, brane proper-clock normalization, positive matter density and \(\rho+p>0\) all PASS by symbolic identity. Locally executed in isolation; exact repository-head and Agda 2.9 replay NOT performed. No postulated "magic negative stress" is required for this original expanding-brane geometry.

**Corrected B1 gate:** The original-paper *classical homogeneous/isotropic AdS5 bulk + FRW + Z2 Israel source equations* now have a concrete algebraic same-metric source solution. Full nonlinear global existence/gluing, normal/tangential perturbative stability, graviton localization/brane-to-brane Green function and physical detector coupling/measurement remain OPEN. This is not a quantum-corrected/string-theory exact spacetime or experimentally observed fifth-dimensional graviton.

**Corrected T8 next mathematical primitive:** derive/source-check the actual retarded *tensor* Green function in the moving-brane AdS5 geometry with Israel-matched perturbation boundary conditions, then prove the brane-to-brane detector response is nonzero and its **front arrival** follows the source Eq19 geometry. A null geodesic alone does not guarantee that a physically generated or observable wave packet follows the path. Then test realistic \(\ell,\kappa_5\), graviton mode spectrum, tensor coupling scales, source emission lags and independent GW/EM timing.

---

## Tranche 2 / 2026-11-15: a physical test-field receiver, TT boundary no-go, all-mode probe and original distributional junction

**Source:** This extends, rather than duplicates, the original Caldwell–Langlois (2001) AdS₅ original metric / Israel 16-component work already in this same PR. Previously pasted notes that claimed the repository had no relativistic Israel implementation were stale: the original GRQFT owner \`DASHI/Physics/Foundations/GRQFTIsraelBranchMaxCutExact.agda\` and its Kottler thin-shell relatives were already present. Those use a 4D bulk with a 2+1D hypersurface rather than the **5D bulk and 3+1D FRW brane** selected here; their source terms cannot be identified by module name alone. Original Is​rael source: Werner Israel (1966) DOI **10.1007/BF02710419**.

### D2.B3(i) — an explicit retarded bulk *scalar* with localised emitter and same brane receiver

\`scripts/ksw668_brane_scalar_emitter_receiver_retarded.py\` upgrades the earlier 5D Minkowski cylindrical-brane shortcut from a **geometric null chord** to an actual **solution of the causal bulk scalar wave equation with a declared source and receiver coupling**. The source and receiver sit at opposite points of the same radius \(R>0\) cylindrical test brane. Define the switched-on, finite-duration *triangular* source \(q(t)=t_+-2(t-\tau)_++(t-2\tau)_+\), where the source is an ideal point on the brane (finite time duration but distributional in space), and a scalar detector returns \(g_{\rm det}\phi(t,B)\).

For the 4-spatial-dimensional wave equation \((\partial_t^2-\nabla_{\mathbb R^4}^2)\phi=q(t)\delta^4(\mathbf x-\mathbf x_A)\), the **true 4+1D retarded fundamental solution** follows by dimension-raising recurrence from the 2+1D Green function. For any \(d=|\mathbf x_B-\mathbf x_A|>0\), the Green response to \(q(t)=t_+\) is exactly
\[
F(t,d)=\frac{\mathbf1_{t>d}}{4\pi^2 d^2}\sqrt{t^2-d^2},\qquad
\phi_{\rm triangular}(t,d)=F(t,d)-2F(t-\tau,d)+F(t-2\tau,d).
\]
This solves the sourced wave equation distributionally with retarded support; away from the point source the 5D radial free wave equation was checked by exact differentiation. No detector pickup before \(t=d\); for \(d=2R\), \(\tau=R/4\), the source detector at \(t=2R+\tau/2\) already responds while the brane-confined light front cannot reach until \(t=\pi R\). For \(R=1\): bulk front **2**, sample scalar response at time **2.125** is **0.00454723349105** (dimensionless emitter and detector couplings); brane photon earliest time **3.1415926536**.

A discrete rational source check also exists: choose polyline brane intrinsic length \(10\), bulk spatial chord \(d=6\), time \(t=15/2\), \(\tau=2\). The first square-root is exactly \(9/2\), later source terms vanish causally, so **\(4\pi^2\phi=1/8>0\)** at the same receiver *before* the brane photon. New Agda finite source \`DASHI/Physics/Gravity/KSW668BulkScalarReceiverRationalSliceExact.agda\` proves the original rational gap/square/response identities (source-written; Agda kernel not run). The smooth cylinder and polygon are distinct test-brane geometry illustrations, not identical globally.

**Honest limitations:** This is a **test massless scalar**, not an Einstein perturbation/graviton or demonstrated device. The source is idealised as a spatial point, so the self-field energy at the emitter is singular; finite-energy spatial smoothing, finite-band source and pickup, brane reflection/transmission conditions and backreaction remain open. The carrier exists in the chosen same ambient flat 5D model; nothing guarantees a Standard Model brane can emit/detect it or that such a brane is in our Universe. Energy injection from the source is required; no free energy, negative-energy wormhole or ambient FTL is inferred.

### D2.B3(ii) — exact bulk AdS₅ *tensor* wave + moving Israel boundary obstruction

\`scripts/ksw668_ads5_tensor_mode_moving_israel_bc.py\` uses the same original AdS₅ bulk metric and moving \(a(t)=t\) FRW brane as our Caldwell–Langlois and original Israel 16-component scripts, in conformal Poincaré \(z=1/R\):
\[
ds_5^2=z^{-2}(-dT^2+dz^2+d\mathbf x^2),\qquad
z_b(t)=t^{-1},\quad T'_b(t)=\sqrt{1+t^2}/t^2.
\]
The transverse-traceless tensor perturbation equation with no anisotropic brane stress is
\[
(-\partial_T^2+\partial_z^2-\tfrac3z\partial_z+\nabla_{\mathbf x}^2)h=0,\quad
(n^A\partial_A h)_\mathrm{brane}=0,
\quad n^A=t^{-2}(-1,\sqrt{1+t^2},0,0,0).
\]
The **nontrivial separated exact bulk wave**
\(h=\cos(kx-\omega T)z^2J_2(mz)\), \(\omega^2=k^2+m^2\), solves the PDE exactly for all bulk positions. But at \(t=z=1,T=x=0,k=m=1\), its required moving-Neumann residual is
\(\sqrt2J_1(1)=0.6223255064907095\ne0\). Thus a Bessel bulk solution alone **cannot be labelled a physically coupled moving-brane graviton**, even when the background Einstein+Israel equations are solved. The homogeneous constant zero mode satisfies the boundary but carries no localized message. Full source-emission/reception needs a genuine superposition/retarded propagator solving the moving boundary *with anisotropic-stress source*, not a static Neumann mode.

Primary perturbation context: Maartens & Koyama, *Brane-World Gravity*, Living Rev. Relativ. **13:5** (2010), DOI 10.12942/lrr-2010-5; Koyama (2004), arXiv **astro-ph/0407263**; moving-mirror tensor analyses of FRW braneworlds. This is the main open B3 physical producer.

### D2.A2 — strict continuum shortcut horizon LOWER BOUND from expansion variance

The already derived exact original Caldwell–Langlois Eq.19 has a stronger **general quantitative theorem**. Set \(w=dt/a>0\), \(A=\int w\), \(x(t)=\ell H(t)\), and assume \(|x|\le M\) on the same physical interval. Rapidities \(\eta=\operatorname{asinh}x\) obey
\[
r_g^2-A^2=\iint w_s w_t[\cosh(\eta_s-\eta_t)-1]
\ge \frac{A^2\operatorname{Var}_w(x)}{1+M^2}.
\]
Since \(r_g+A\le A(1+\sqrt{1+M^2})\),
\[
\boxed{r_g-r_\gamma\ \ge\
 \frac{A\,\operatorname{Var}_w(\ell H)}
 {(1+M^2)(1+\sqrt{1+M^2})}.}
\]
Here \(\operatorname{Var}_w(x)=A^{-1}\int w(x-\bar x)^2\). The bound is **strict for nonconstant H** on a positive-weight interval, zero for constant H; its weak-curvature leading term is \(A\operatorname{Var}_w(\ell H)/2\). No local differential null-cone violation occurs. This is an analytical consequence of the original source Eq19 (nonnegative \(\cosh\) difference), not a claim about brane matter launch or experimental observation.

New \`scripts/ksw668_ads5_gravitational_horizon_variance_bound.py\` checks 280 finite positive-weight cases, the constant-H null and original \(a=t,H=1/t,\ell=1,1\le t\le2\) analytic moments. This exact same-interval example gives \(A=\ln2=0.69314718056\), \(r_g=0.69779778110\), actual horizon excess **0.00465060054**, and guaranteed lower **0.00296706141** (about 64% of the actual mathematical gap). This is a **horizon-radius gap** not the same-receiver clock-time advance; the latter remains the separately checked \(\simeq0.00932286273\). Ordered-real continuum Agda proof of \(\cosh\), inverse hyperbolic functions and the integral inequality remains OPEN.

### D2.B2 — full radial + compact-scalar **probe** perturbations, not merely uniform mode

The stabilized cylinder was previously checked only for the uniform radius. \`scripts/ksw668_brane_winding_allmode_linear_stability.py\` now expands the **actual exact worldvolume action** under arbitrary normal displacement \(R=R_0+\epsilon\eta(t,\theta,u,v)\) and an *independent* compact winding scalar disturbance \(\chi=n\theta+\epsilon\psi\). Using the exact determinant/inverse of the induced metric, the quadratic action density, after the background equation \(2TR_0^2=f^2n^2\), reduces to
\[
\mathcal L_2=
 TR_0(\eta_t^2-\eta_u^2-\eta_v^2)
 +\frac{f^2R_0}{2}(\psi_t^2-\psi_u^2-\psi_v^2)
 -\frac{f^2}{2R_0}(\psi_\theta-n\eta/R_0)^2.
\]
Therefore its **quadratic Hamiltonian is nonnegative**, a sum of squares. All integer angular Fourier modes \(m\) and real longitudinal \(|k|^2\ge0\) have the generalized eigenvalues
\[
\omega_-^2=|k|^2,\qquad
\omega_+^2=|k|^2+\frac{m^2+1}{R_0^2}.
\]
There is no tachyonic \(e^{+\gamma t}\) mode in the **linearized probe-worldvolume theory**. Importantly, \(\omega_-^2=0\) for \(|k|=0\), including genuine marginal modes with potential secular linear drift. Therefore **nonlinear stability and gravitational backreaction stability are NOT proved**. The direct quadratic action is stronger than only checking \(E''(R_*)>0\), and confirms the tension/winding competition without “free-energy” claims.

### D2.B1 — exact original Z₂ distributional source coefficient, not only K mixed

\`scripts/ksw668_ads5_z2_distributional_israel_coefficient.py\` computes the Gaussian-normal cusp \(g_{ab}(y)=h_{ab}+2|y|K^+_{ab}+\cdots\), source distribution identity \(\partial_y^2|y|=2\delta(y)\), and the **full 16-component** \(Z_2\) singular Einstein coefficient
\[
(G_{ab})_{\rm sing}=
 -2(K^+_{ab}-h_{ab}K^+)\delta(y)=\kappa_5^2 S_{ab}\delta(y)
\]
for the *same original AdS5 cosmology, tension and FRW matter*. At exact rational brane proper time \(t=4/3\), \(A=\sqrt{1+t^{-2}}=5/4\), \(\rho=1/4\), \(p=-1/10\), \(\rho+p=3/20>0\), \(S^a{}_a=-91/20\) and
\(K^a{}_b=\operatorname{diag}(-4/5,-5/4,-5/4,-5/4)\).
The singular Einstein coefficient's diagonal is exactly **\((15/2,-176/15,-176/15,-176/15)\)**, equal to \(\kappa_5^2 S_{ab}\); all off-diagonal 12 entries vanish. The local distributional *coefficient* is checked; the full global brane bulk metric with higher-order Gaussian-normal terms and all-mode perturbations is NOT thereby independently constructed.

\`DASHI/Physics/Gravity/KSW668AdS5IsraelOriginalRationalSliceExact.agda\` records the exact selected \(t=4/3\) **all-16 rational Israel component equations**, the Friedmann relation and positive-NEC normal form using original rational Agda tactics (source-written; kernel pending). It explicitly imports the preexisting \`GRQFTIsraelBranchMaxCutExact\` (4D Kottler shell) and \`MonsterGravityAuthorityAndDimensionExact\` (AdS3 Monster candidate), without identifying their dimensions.

### Cross-programme source owners, NOT same-spacetime identifications

Existing true owners reused:
- **Levin:** \`DASHI/Biology/Levin/ProblemSpaceAgency.agda\` (anatomical vs physiological state spaces), \`TravelingFieldControl.agda\`, \`NeuralWaveAnalogComputation.agda\` — causal biophysical control/observability, not extra Lorentzian dimensions.
- **Original physical Israel:** \`DASHI/Physics/Foundations/GRQFTIsraelBranchMaxCutExact.agda\` and \`GRQFTSourceAmplitudeDrivenIsraelKottlerExact.agda\` — 4D Kottler thin-shell jump and DEC/source stress. \(\mathbb Z_2\) Israel *normal-side reflection* is not a generic parity/ternary label.
- **Jordan/radion:** \`scripts/check_kk_jordan_sourced_sphere.py\` — 4D scalar fifth-force profile from a declared *external radion mass*, not a 5D null-mode/branelight shortcut or physical membrane actuator.
- **Monster gravity:** \`DASHI/Physics/Closure/MonsterGravityAuthorityAndDimensionExact.agda\`, \`DASHI/MonsterC3EntropyGravityEverything.agda\` — distinguish Witten AdS3/CFT Monster candidate and high-dimensional monstrous M-theory from this *specific* classical AdS5 FRW/Israel geometry. A duality, compactification and matching physical source are still needed.
- **Pants/cylinder:** \`DASHI/Topology/WormSoilPantsSheafBoundary.agda\` and \`ClopenNDimFibreBoundary.agda\` — gluing/refinement and topological cell roles do not confer Lorentz signature, Einstein stress, or timed geodesics.
- **Ultrametric/p-adic/trie:** \`DASHI/Geometry/SSP369ClopenBallBridge.agda\`, \`DASHI/Geometry/SSP369Ultrametric.agda\` — non-Archimedean distance and nested clopen cells differ from Lorentzian timelike/null length. A physically verified metric-emergence map is necessary before interpreting them as a bulk spatial direction.
- **String/SUSY/TSFV:** existing roles remain typed separately in \`KSW668BraneLevinStringTSFVPromotionBoundaryExact.agda\`; action phases, string UV claims, a SUSY state and many-world histories are not identical to a measured 5D classical signal.

The existing physical promotion Agda owner now imports these original donor objects and constructs **no-equality** proofs for the distinct carrier roles. Exact source coexistence is not physical identity. The canonical governance condition is the same \(5D\) metric + induced brane \(h\) + \(\Lambda_5\)/Israel + sourced moving tensor mode + nonzero detector response + independent observation.

### Exact next maximum-cut gates (do not call missing quantum/experimental data a lemma weld)

| Priority | Strongest delivered in this tranche | Next decisive mathematical/physical producer |
| --- | --- | --- |
| **A2 continuum horizon** | Rigorous analytic rapidity/weighted-variance lower bound and executed numerical example | Original *real* Agda ordered \(\cosh/\operatorname{asinh}\), Bochner/Fubini positive-weight integration, strict variance theorem |
| **B1 original 5D Israel** | Full original symbolic one-sided K/S; Z2 singular Einstein delta coefficient; all-16 rational Agda slice | Global Gaussian-normal thin-wall distributional solution, analytic metric/Israel Agda kernel, brane source microphysics |
| **B2 probe all-mode** | Exact full radial + scalar quadratic form and all Fourier spectral squares; no tachyons | Treat marginal \(\omega^2=0\), nonlinear effects, radiation/gravity backreaction, brane-bending and normal stability with full 5D field |
| **B3 receiver in flat 5D** | **Actual retarded scalar source-to-detector wave** before brane light; exact causal Green support and rational Agda sample | Finite spatial source/receiver smearing + finite total energy + fully coupled brane matter / boundary, physically available bulk field |
| **B3 moving AdS5 tensor** | Exact real TT PDE and original moving normal BC; explicit Bessel-mode obstruction | Construct/source numerical retarded tensor Green with correct moving Israel boundary, initial/brane anisotropic stress, positive spectral energy and nonzero on-brane receiver |
| **C1 observational** | Real physical quantity/event language defined; GW170817 dimensional constraints sourced | Choose ℓ, physical epoch and source/detector material, predict redshift/frequency-delay and strain, compare short-range gravity + GW/EM common-source limits |
| **Cross programme** | Reused exact Levin, Jordan, Monster, p-adic/pants, SUSY/string/TSFV owners without identifying dimensions | One real source geometry/UV action/scaling map that preserves original Lorentzian metric and target physical observables |
| **Acceptance** | Independent local SymPy/mpmath/Fraction mathematical checks; same existing PR #1504 and new Agda source modules | Run exact PR HEAD Python suite and local pinned Agda kernel on networked/code-equipped machine. **No CI requirement**. |

**Scientific takeaway:** We have a rigorous model **where an actual scalar disturbance reaches the same brane detector before confined light**, and a distinct sourced AdS5/Israel geometry that has earlier bulk *null causal reach*. These are NOT YET one fully coupled graviton-transport solution: the remaining same-object merger is the moving-brane sourced tensor propagator and detector. It is the true next decisive physical gate, not an unproved universal claim of FTL/free energy.


---

## 2026-11-15 exact-head continuation: finite-energy cylinder / sourced AdS5 TT trace

This continuation reuses the original Caldwell–Langlois / Z2 Israel and source/receiver scripts; it deliberately does not treat an early scalar test signal as a retarded gravity wave. New producer:
`scripts/ksw668_brane_finite_energy_and_sourced_tt_witness.py`.

### Phase F0 — established same-metric baselines (DO NOT repeat)
* `ksw668_caldwell_langlois_original_eq19.py`: bulk Einstein/FRW, null geodesic, same-receiver clock difference (dimensionless).
* `ksw668_caldwell_langlois_israel_exact.py` and `ksw668_ads5_z2_distributional_israel_coefficient.py`: original local 16-component Z2 Israel, plus singular coefficient.
* `ksw668_brane_scalar_emitter_receiver_retarded.py`: exact retarded point-scalar example on flat cylindrical probe brane.
* `ksw668_ads5_tensor_mode_moving_israel_bc.py`: exact bulk TT Bessel mode and **nonzero** unsourced moving-boundary residual.
* `ksw668_brane_winding_allmode_linear_stability.py`: all-mode quadratic probe spectrum, zero modes not controlled.
* All original Agda modules remain source-level pending an actual pinned local kernel run.

### Phase F1 — finite-energy test-scalar receiver on ORIGINAL cylindrical probe brane (new partial closure)
Define spatial source
\[
\rho_\epsilon(X)=\prod_{j=1}^4\frac{15}{16\epsilon}\bigl(1-(X_j/\epsilon)^2\bigr)^2\mathbf1_{|X_j|<\epsilon},
\quad J(t,X)=q_\tau(t)\rho_\epsilon(X-X_s).
\]
The compact triangular \(q_\tau(t)=t_+-2(t-\tau)_++(t-2\tau)_+\) has \(\int|q_\tau|dt=\tau^2\). The source is compactly supported and in \(L^1_tL^2_X\); \(\rho_\epsilon\in H^1\). Zero-data energy for \(\square_5\phi=J\) satisfies
\[
E(t)=\tfrac12\int_{\mathbb R^4}(|\partial_t\phi|^2+|\nabla\phi|^2)dX
\le\frac12\bigl(\tau^2\|\rho_\epsilon\|_2\bigr)^2,
\quad \|\rho_\epsilon\|_2^2=\left(\frac{5}{7\epsilon}\right)^4.
\]
For \(R=1,\epsilon=0.02,\tau=0.25,t_\mathrm{receive}=2.125\) and antipodal receiver at spatial distance 2 from centre, all source distances lie in
\([2-\epsilon,\sqrt{(2+\epsilon)^2+3\epsilon^2}]\).
This entire interval lies strictly below \(t_\mathrm{receive}\), but strictly above \(t_\mathrm{receive}-\tau\). Thus the *first* positive retarded ramp term survives everywhere on the source support; the later shifted terms vanish. A strictly positive receiver is therefore proved by positive integration (not just one quadrature value); a normalized five-node tensor-product quadrature is included for numerical replay. The response is before confined photon time \(\pi\). **This removes the ideal point-source infinite-energy objection for a scalar test source; it does NOT add scalar backreaction, tensor/graviton coupling or an apparatus.**

### Phase F2 — same original AdS5 background sourced TT *boundary-trace* (new partial closure)
The exact separated TT mode
\[
h(T,z,x)=\cos(kx-\sqrt{k^2+m^2}T)z^2J_2(mz)
\]
obeys \(L_{TT}h=(-\partial_T^2+\partial_z^2-3\partial_z/z+\partial_x^2)h=0\). On the original \(a(t)=t,z_b=1/t\) brane, its exact source-required normal derivative is
\[
\mathcal B h=\frac{-\omega\sin(kx-\omega T)z^2J_2(mz)
+\sqrt{1+t^2}\,mz^2\cos(kx-\omega T)J_1(mz)}{t^2}
\Big|_{z=1/t,T=T_b(t)}.
\]
In particular \(\mathcal B h|_{t=z=1,T=x=0,k=m=1}=\sqrt2J_1(1)\ne0\).
Specifying boundary data equal to this trace makes the **bulk PDE and sourced normal boundary equation** exactly compatible for this manufactured mode. But the trace is nonlocalized and was *inferred from a global standing wave*. It is NOT an independently justified Israel anisotropic-stress coupling, retarded Green function, finite-energy localized tensor source, or observable shortcut. No claim of physical B3 closure.

### Precise outstanding lemmas — one-owner policy (theorem targets are specifications, not already established exports)

| Rank | Proposed exact lemma / producer | Required mathematical content | Disposition |
| --- | --- | --- | --- |
| A1 | `cylinderCompactEmitterL1L2FiniteEnergy` | Ambient 4-space source norm, energy estimate and retarded uniqueness for compact spatial pulse | external proof + new local regression; **Agda OPEN** |
| A2 | `cylinderCompactEmitterEarlyNonzeroReceiver` | 5D retarded Green distribution, spatial convolution, rigorous distance support and strictly positive response at same receiver before brane photon | analytic source proof + quadrature witness; **Agda OPEN** |
| A3 | `cylinderWindingPerturbedIsraelBackreaction` | Solve original coupled 5D Einstein–matter thin-shell and Israel for curved stabilized cylinder including scalar stress | **OPEN**; probe action is insufficient |
| B1 | `ads5TensorPDEMovingNormalExact` | Same AdS5 TT operator, moving normal and exact Bessel bulk mode | external SymPy source, **Agda OPEN** |
| B2 | `ads5TensorSourceIsraelTTNormalization` | Derive source coefficient and signs from *linearized* Israel with physical transverse-traceless brane anisotropic stress (include brane bending/gauge where needed) | **OPEN**; inverse boundary trace is not stress |
| B3 | `ads5RetardedTensorGreenMovingBoundary` | Well-posed finite-energy forward propagator for original moving geometry, correct initial data, exact moving boundary and chosen AdS side/horizon condition | **OPEN** |
| B4 | `ads5LocalizedTTSourceProducesEarlyFront` | Brane-localized compact stress, convolution with B3, prove nonzero same-receiver TT gauge-invariant observable strictly before photon, and prove bulk causal support | **OPEN** |
| B5 | `ads5TensorLinearEnergyStabilityAndModes` | Positive/controlled physical energy for permitted tensor sector and boundary flux; exclude uncontrolled tachyon/ghost and unstable zero modes | **OPEN** |
| C1 | `ads5ObservationalArrivalBound` | Dimensional parameters \(\ell,\kappa_5\), emission lags, frequency/attenuation, detector proper-time and realistic GW–EM comparison | **OPEN** |
| C2 | `braneBulkOriginalAnalyticAgdaKernel` | Agda 2.9 typecheck of original horizon continuum, differential geometry, distributional Israel and new F1–F2 owners | **OPEN**; SOURCE WRITTEN != KERNEL ACCEPTED |
| D1 | `physicalGravitonObservation` | Independently measured, calibrated faster bulk-carrier response discriminating brane photon, clock and mundane coupling | **OPEN** |

### Minimum implementation phases and acceptance receipts
1. **F1:** execute `python scripts/ksw668_brane_finite_energy_and_sourced_tt_witness.py` locally; require positive compact receiver and finite analytic energy bound, symbolic TT bulk and moving boundary trace. Revalidate original scripts alongside. Record actual exact-head output/hashes. No CI gate.
2. **F2:** prove exact linearized Israel source normalisation; do not equate \(\mathcal Bh\) automatically with physical anisotropic stress.
3. **F3:** construct a retarded tensor boundary-value operator on *the same original a=t AdS5 Einstein/Israel background*, with chosen bulk side and physically specified source; energy estimates and initial/boundary compatibility.
4. **F4:** smear source, calculate brane-to-brane response, identify gauge-invariant detector, wavefront/tail and compare actual arrival with intrinsic brane photon at same receiver.
5. **F5:** nonlinear/zero-mode/global stability; dimensional scales, observational constraints, local pinned Agda kernel acceptance; independent evidence is a separate experimental gate.

**Scope guard:** F1 and F2 are real but *partial* mathematical advances. No theorem currently joins the finite-energy flat cylindrical scalar receiver to a physical retarded graviton on the expanding AdS5 brane; the two spacetime metrics must not be silently equated. No empirical faster-than-light transmission or free-energy device is claimed.


### F1 thickness qualification / exact remaining thin-brane lemma

The F1 profile is supported in a compact **ambient four-spatial-dimensional neighborhood** of a point of the cylinder, not strictly on its three-spatial-dimensional infinitely thin worldvolume. Consequently the finite-energy estimate is for a **finite-thickness (bulk-neighborhood) scalar source**. It resolves the singular ambient point-source idealization but not an exactly brane-confined emitter. No claim is made that the original worldvolume winding action supplies this scalar emitter coupling.

Additional exact missing target: `cylinderThinBraneDeltaSourceEnergyTrace` — formulate (J=q(t)f(\theta,u,v)\delta_{\Sigma}) on the actual cylindrical worldvolume, establish the correct Sobolev trace/dual-source estimate, causal retarded solution, nonzero antipodal pickup, and stress-energy/backreaction compatibility. The smooth thick-source limit may require uniform renormalized energy estimates; the F1 (L^2(\mathbb R^4)) estimate is **not uniform as thickness tends to zero**, so it cannot pay this lemma.

The source manuscript and the exact PR-head new Python file were not jointly executed in this tool runtime. Independent quadrature of the explicit F1 kernel with tensor-product Gauss–Legendre orders 3/5/7/9 converged near **0.004545273184896** at (t=2.125), compared with the ideal point-source value **0.004547233491053**; the rigorous support-based positive lower estimate at this parameter point is **0.00408853005758**. These are independent numerical sanity checks, not a replacement for repository-head execution or Agda kernel acceptance.


---

## 15 Nov 2026 — second max-cut: genuine thin emitter, static self-gravitating winding cylinder, normalized AdS5 TT source and moving-energy negative controls

**This addendum supersedes the earlier F1 thickness-only assessment for the NEW A3 model.** Keep the former four-dimensional ambient *thick* source as a separate control. The new source is precisely supported on the original cylindrical three-spatial-dimensional hypersurface in ambient \(\mathbb R^4\). Both sources are TEST SCALARS. The shell construction below is a DIFFERENT Z2-glued geometry and does not automatically inherit the flat test-scalar propagator.

Executable: \`scripts/ksw668_brane_original_maxcut_exact.py\`; local analogue ran with SymPy and positive quadrature. Rational-only Agda sources: \`KSW668CylinderZ2WindingIsraelRationalExact.agda\`, \`KSW668AdS5LinearIsraelTTRationalSliceExact.agda\`; both imported in the existing \`KSW668BraneBulkMaxCutEverything.agda\`. Exact new PR-head Python and Agda 2.9 kernel execution has not been performed by this tool runtime; local-first runner updated, CI irrelevant.

### A1/A2/A3: a truly thin, compact, finite-energy source on the original FLAT cylinder

Take flat 5D \(ds^2=-dt^2+dX^2+dY^2+du^2+dv^2\), cylindrical brane \(X=\cos\theta,Y=\sin\theta\), \(R=1\), source at \((1,0,0,0)\), receiver at \((-1,0,0,0)\). Define
\[
p_\delta(s)=\frac{15}{16\delta}(1-(s/\delta)^2)^2 {\bf1}_{|s|<\delta},
\quad f_\delta(\theta,u,v)=p_\delta(\theta)p_\delta(u)p_\delta(v)
\]
and the ambient **surface distribution**
\[
F(\varphi)=\int_{\Sigma_t}f_\delta(\theta,u,v)
\varphi(\cos\theta,\sin\theta,u,v)\,d\theta\,du\,dv,\qquad
J(t,X)=q_\tau(t)F(X),
\]
with \(q_\tau(t)=t_+-2(t-\tau)_++(t-2\tau)_+\), \(q_\tau(0)=0\). This \(F\) is supported exactly on the cylinder, not in a thick neighborhood.

The 4D spatial free-wave operator \(A=-\Delta_{\mathbb R^4}\) has \(F\in \dot H^{-1}(\mathbb R^4)\) for smooth compact surface density on a 3D hypersurface. One explicit proof is its positive Newtonian quadratic form:
\[
\|F\|_{\dot H^{-1}}^2=
\frac1{4\pi^2}\int_{\Sigma_t}\int_{\Sigma_t}
\frac{f_\delta(\xi)f_\delta(\eta)}{|\xi-\eta|^2}\,d\Sigma_\xi d\Sigma_\eta<\infty.
\]
The diagonal singularity is locally \(r^{-2}r^2dr\), integrable in three surface dimensions, and the compact, smooth density controls the remaining pairs. This is *not* an \(L^2(\mathbb R^4)\) source. For zero initial data, Duhamel gives
\[
\partial_t\phi+iA^{1/2}\phi
=\int_0^t e^{i(t-s)A^{1/2}}F q_\tau(s)\,ds.
\]
Integrate by parts in \(s\) using \(q_\tau(0)=0\). Spectral unitarity yields
\[
\sqrt{2E(t)}\le\|F\|_{\dot H^{-1}}
\left(|q_\tau(t)|+\int_0^t|q_\tau'(s)|ds\right)
\le 3\tau\|F\|_{\dot H^{-1}},
\quad E(t)\le\frac{9\tau^2}{2}\|F\|_{\dot H^{-1}}^2.
\]
Thus existence/uniqueness of the standard flat-space retarded finite-energy mild wave follows from the spectral Duhamel construction. The limiting spatial point source is not covered.

The **correct four-spatial-dimensional** retarded ramp kernel is
\[
G_{\mathrm{ramp}}(t,d)={\bf1}_{t>d}\frac{\sqrt{t^2-d^2}}{4\pi^2d^2}.
\]
The attachment's \(\delta(t-d)/(4\pi d)\) is a *three-spatial-dimensional* retarded kernel, NOT the present 5D wave. With \(\delta=0.02,\tau=0.25,t_\mathrm{rec}=2.125\), every surface-source to antipodal-receiver distance obeys
\[
2\cos(\delta/2)\le d\le\sqrt{4+2\delta^2},
\]
hence \(t_\mathrm{rec}-\tau<d<t_\mathrm{rec}<\pi\). Only the strictly positive first ramp contributes to the receiver. Numerical normalized three-dimensional surface convolution:
**response 0.004546916546865**, lower **0.004542796011697**, upper **0.004549451795781** (unit scalar couplings). Analytic inequalities prove strictly positive early response; numbers are cross-checks, not physical units. This closes A1/A2/A3 for the **flat-bulk test scalar**, not for dynamical gravity or the glued shell.

### A4: static fully sourced 5D Einstein–Israel *background* via two interior discs

Original probe cylinder \(K\neq0\) cannot be a pure-tension, source-free junction. A more substantial model glues two flat five-dimensional regions with transverse discs \(0\le r\le R\) along their common cylindrical timelike shell \(\Sigma=\mathbb R^{1,2}\times S^1_R\). This Z2 double-disc spacetime is smooth and flat **away** from its shell; it is not the unglued global \(\mathbb R^{4,1}\) used for the exact scalar Green calculation. With normals pointing *into each disc*, the mixed extrinsic tensor and trace are
\[
K^a{}_b=\mathrm{diag}(0,-1/R,0,0),\qquad K=-1/R.
\]
The full Z2 Israel tensor \([K^a{}_b-K\delta^a_b]=-\kappa_5^2 S^a{}_b\) requires
\[
S^a{}_b=-\frac{2}{\kappa_5^2R}\operatorname{diag}(1,0,1,1).
\]
For the original positive-tension compact winding-scalar brane action
\(S_\Sigma=-\int\sqrt{-h}\,[T+(f^2/2)(\partial\chi)^2]\), \(\chi=n\theta\), define \(a=f^2n^2/(2R^2)\). Its **actual full** stress is
\(S^a{}_b=\operatorname{diag}(-(T+a),-T+a,-(T+a),-(T+a))\).
The complete 16-component junction matches iff
\[
T=a=\frac1{\kappa_5^2 R}
\quad\Longleftrightarrow\quad f^2n^2=\frac{2R}{\kappa_5^2}.
\]
Example \(R=1,T=2,f=2,n=1,\kappa_5^2=1/2\) exactly reproduces the prior probe parameters. The compact-scalar worldvolume equation \(\Box_h\chi=0\) and source conservation hold; the stress satisfies NEC and saturates DEC. The old uniform probe radial potential has \(E'(1)=0,E''(1)=8\pi\). **The background is an exact piecewise-flat distributional Einstein–Israel source candidate**, not a proof of coupled perturbation stability or the same globally Minkowski bulk scalar receiver. A *new* Green function on the doubled-disc geometry and normal/brane perturbation estimates remain needed to combine them.

### B1/B2: genuine TT projection of LINEARIZED Israel on the same expanding original AdS5

For the existing \(a(t)=t,z_b(t)=1/t,\kappa_5^2=6\) homogeneous/isotropic brane, use *mixed-index*, dimensionless TT perturbations in Gaussian-normal gauge:
\[
q_{ij}=a^2(\delta_{ij}+H_{ij}),\quad
K^i{}_j=K_{\mathrm{spatial}}\delta^i_j+\tfrac12 n^A\partial_A H^i{}_j+O(H^2).
\]
The background \(K_{\mathrm{spatial}} H\) terms cancel when raising an index. Write the actual brane stress \(S^i{}_j=(p-\sigma)\delta^i_j+\pi^i{}_j\), \(\pi^i{}_i=\partial_i\pi^i{}_j=0\). The variation of its trace vanishes in the pure tensor sector, so the original Z2 Israel equation implies
\[
\boxed{n^A\partial_A H^i{}_j=-\kappa_5^2\pi^i{}_j=-6\pi^i{}_j},\quad
n^A\partial_A=\frac{-\partial_T+\sqrt{1+t^2}\partial_z}{t^2}\Big|_{z=1/t,T=T_b(t)}.
\]
This **resolves B2's tensor-sector algebraic normalization and sign** for the existing dimensionless H. It does NOT derive that some independently localized matter apparatus generates a given \(\pi^\mathrm{TT}\). For a covariant metric perturbation \(\delta g_{ij}=a^2H_{ij}\), its covariant derivative contains connections; the attachment's added \(-H/L\) term cannot be transplanted to the *dimensionless* \(H\) unchanged. A rational two-polarization and nine-component source check is added in Agda source.

### B3/B5: exact moving-boundary energy identity; zero-mode negative control

In Poincare coordinates \(ds^2=z^{-2}(-dT^2+dz^2+d\mathbf x^2)\), one tensor-polarization wave is
\(\partial_T^2H=\partial_z^2H-3z^{-1}\partial_zH+\Delta_{\mathbf x}H\).
Let \(b(T)=z_b(T)=1/t\), \(v(T)=db/dT=-1/\sqrt{1+t^2}\). In the physical one-sided domain \(z\ge b(T)\), absent outer/infinite flux, the bulk positive quadratic energy
\[
E(T)=\frac12\int_{b(T)}^\infty dz\,z^{-3}\int d^3x
\bigl(H_T^2+H_z^2+|\nabla_{\mathbf x}H|^2\bigr)
\]
has the **exact Reynolds/moving-wall flux identity**
\[
\boxed{\frac{dE}{dT}=-\int d^3x\,b^{-3}
\left[H_T H_z+\frac v2(H_T^2+H_z^2+|\nabla_{\mathbf x}H|^2)\right]_{z=b}.}
\]
At zero anisotropic stress the *moving* Neumann condition is \(H_z=-v H_T\); the flux reduces to
\[
\frac{dE}{dT}=\int d^3x\,\frac{v}{2b^3}
\left[(1-v^2)H_T^2-|\nabla_{\mathbf x}H|^2\right]_{z=b}.
\]
This is **not sign definite** and is not simply zero. A finite-time retarded moving-wall Green theorem still needs precise initial data, compatible source, coercive boundary estimate, chosen AdS side and horizon condition; do not assert a naive method-of-images solution.

Static brane (\(b=\)const) control: with \(H=z^{3/2}\psi\),
\[
\mathcal H=-\partial_z^2+\frac{15}{4z^2}
=Q^\dagger Q,\quad Q=\partial_z+\frac{3}{2z}
\]
under the *correct transformed Neumann boundary* \(Q\psi(b)=0\). The normalizable radial zero mode \(\psi_0=z^{-3/2}\) satisfies \(Q\psi_0=\mathcal H\psi_0=0\) and \(\int_b^\infty|\psi_0|^2dz=1/(2b^2)\). Thus the attachment's \(\omega^2>0\) assertion is FALSE. Correct stationary conclusion is **nonnegative** radial operator, zero mode present; nothing about fully moving nonlinear stability follows.

### Explicit correction of unsupported promotions in attached 232-line proposed proof

* A1: a wave **on** a cylinder has no bulk shortcut; retain the R4 ambient spatial operator.
* A2: the 3-spatial \(1/(4\pi d)\delta(t-d)\) kernel is the wrong dimension; positive everywhere until photon arrival is not true for arbitrary finite pulses. The narrower positivity window above is proved.
* A3: trace of \(H^1\) alone is not a wave-energy theorem; the \(\dot H^{-1}\) source and time-integration-by-parts provide the missing argument for the **test scalar**.
* A4: Israel requires all mixed components and tuned \(\kappa_5^2\), not the scalar condition \(1/R=4\pi G_5\tau\) alone.
* B2: the correct boundary source is stated for an explicit variable (\(H\)); derivative/Robin coefficients cannot be imported between \(H\) and \(\delta g\) without change of variables.
* B3: dynamic-wall flux is nonzero, and static images do not solve the generic moving wall; Green existence/nonzero source coupling remain open.
* B4: causal **support** does not imply an excited nonzero gauge-invariant receiver amplitude. \(R_{0i0j}=-\ddot H_{ij}/2\) is a *local linear TT Minkowski limit*, not a general FRW Riemann/Weyl identity.
* B5: positive \(15/(4z^2)\) does not imply strict mode gap with this Robin boundary; explicit zero mode above.
* C1: GW170817 relative-speed limits are conditional on source lag and propagation model. NO \(\ell\le10^{-19}\mathrm m\) follows from that timing datum alone.

### Updated exact primitive frontier

| Cut | Accepted scope from this tranche | Remaining genuine primitive |
|---|---|---|
| A1–A3 | analytic thin-source \(\dot H^{-1}\to E\) argument, retarded same-receiver positive convolution in unglued flat bulk; source-equivalent Python checks | formal Agda analytic Sobolev/spectral/Green integration; couple scalar stress/backreaction to Einstein |
| A4 | exact tuned static double-disc Z2 Israel background with winding source, NEC/DEC; rational Agda 16-component slice source | coupled normal/tangential gravitational perturbation and retarded wave on the **doubled-disc** global geometry |
| B1 | existing bulk TT PDE/moving normal; confirmed in independent originals | Agda differentiable tensor owner and kernel receipt |
| B2 | exact linearized mixed TT Israel coefficient and 2-polarization algebraic check | *physical* localized \(\pi^\mathrm{TT}\) generated by a conserved brane source, with any required scalar/vector gauge sectors |
| B3 | exact moving-boundary energy identity and static factorization/zero-mode control | full retarded Green operator, positivity/coercivity, uniqueness, horizon, source/initial data |
| B4 | geometric same-receiver early null; original scalar control separate | nonzero, finite-energy *AdS5 tensor* source/receiver at same original clock with calibrated gauge-invariant tidal observable |
| B5 | stationary radial spectrum nonnegative, zero mode; moving energy sign indefinite | moving/coupled stability and spectral transfer |
| C1 | prior dimensional geometric benchmark; timing observational comparisons identified | physically scaled \(\ell,\kappa_5,\omega,D\), emission delay, GW/EM constraints; no unsupported \(\ell\) bound |
| C2 | two rational Agda source files integrated in brane rollup | **Agda 2.9 local kernel acceptance** for both and original analytic continuum |
| D1 | independent operational test defined | actual source-characterised gravitational response and independent observations |

**Next highest-alpha order: B3 (+ local B2 physical stress) → B4 same-source Green convolution and tidal receiver → moving B5, then C1/D1.** Also separately A4 → doubled-disc scalar/tensor evolution on exactly that new metric. Use one PR (#1504) per repo; no invented kernel acceptance, universal FTL, free energy or observational signal.


### B4 added: correctly gauge-invariant induced 4D electric-Weyl discriminator (NOT retarded transport)

On the original homogeneous/isotropic \(a=t\) FRW brane, background 4D Weyl is zero. Its first-order perturbation is therefore gauge invariant. In conformal time \(\eta=\log t\), with plus-polarized TT \(H_{yy}=H_+(\eta,x),H_{zz}=-H_+\), the linear Weyl electric component in an orthonormal 4D receiver frame is
\[
\delta E_{\hat y\hat y}=\frac{1}{a^2}\delta C_{0y0y}
=-\frac{1}{4a^2}(\partial_\eta^2+\partial_x^2)H_+.
\]
This expression **does not require** the intrinsic 4D vacuum Einstein equation. Only if \(H_+\) satisfies the *4D* vacuum wave equation does it reduce to \(-\partial_\eta^2 H_+/(2a^2)\). Using \(-\ddot H/2\) for a generic expanding brane and calling the 4D Riemann equal to Weyl is otherwise wrong.

New source \`scripts/ksw668_ads5_induced_weyl_receiver_partial.py\` inserts the already constructed **nonretarded**, nonlocalized, separated AdS5 mode at the same original geometric receiving location \(r_g=0.697797781099381,t=2\), with \(T_b(1)=0,k=m=1\). It computes \(\delta E_{\hat y\hat y}\approx-0.008053773977753403\) in the declared mathematical mode normalization. This proves that the existing manufactured tensor mode induces a nonzero *candidate gauge-invariant brane curvature observable*, not an early physical message: there is still no finite-energy compact emission, no retarded moving-boundary tensor Green solution, and no calibrated detector. B4 remains OPEN on those exact original source-to-observer obligations.

Relevant source studies: Kodama–Ishibashi–Seto, Phys Rev D 62, 064022 (2000), DOI 10.1103/PhysRevD.62.064022, treats gauge-invariant bulk/brane junction variables; Maartens–Koyama 2010 section 7 explains nonseparable cosmological moving-brane tensor propagation and the anisotropic stress boundary; Caldwell–Langlois 2001 owns the geometric horizon only.


### B5/C1 original model extra negative control — basis mode has divergent total radial energy; SI scaling is conditional

The exact \(z^2J_2(mz)\cos(kx-\omega T)\) tensor basis mode from the original source is an *infinite spatial plane wave* and additionally fails the required finite **radial** energy criterion on the noncompact AdS side \(z\in[b,\infty)\). For \(k=m=1,\omega=\sqrt2\), the time-averaged radial quadratic energy per unit brane spatial volume is
\[
\overline{\mathcal E}(z)=\frac{z}{4}[3J_2(z)^2+J_1(z)^2].
\]
Using the genuine large-\(z\) Bessel asymptotics, its oscillation-average is \(1/\pi>0\). Thus \(\int_b^\infty \overline{\mathcal E}(z)\,dz\) diverges **linearly**. The nonzero electric Weyl response previously computed for this nonretarded basis element cannot count as finite-energy emission. A localized spectrally integrable packet and its nonzero retarded receiver must still be constructed.

For any declared AdS physical length \(\ell\) in metres, simply rescaling **the entire existing dimensionless a=t solution** gives the conditional same-event clock advance
\[
\Delta t_{\rm phys}=0.009322862731128\frac{\ell}{c}.
\]
At \(\ell=1\,\mathrm m\), this is only \(3.10977\times10^{-11}\) s, **but** the same original model then has \(H(t=1)=c/\ell\simeq2.9979\times10^8\,\mathrm{s^{-1}}\), wildly unlike today's expansion. Changing \(\ell\) without the associated cosmological epoch is not a valid modern signal prediction.

For the same manufactured \(k=m=1\) mode, a fixed brane receiver's instantaneous *proper phase* frequency is \(\sqrt2(dT_b/dt)c/(2\pi\ell)\), which decreases from approximately \(95.427\ \mathrm{MHz}/(\ell/\mathrm m)\) at \(t=1\) to \(37.721\ \mathrm{MHz}/(\ell/\mathrm m)\) at \(t=2\). This is a kinematic scale control, NOT a measured detector band or dispersion spectrum. In particular neither GW170817 timing nor these dimensional conversions alone imply the attachment's claimed \(\ell\le 10^{-19}\ \mathrm m\).

Local producer \`scripts/ksw668_ads5_mode_energy_scale_guard.py\` symbolically verifies the Bessel derivative identity, checks the large-z radial energy density numerically and computes original same-worldline SI rescaling. It is in the local-only acceptance runner. Physical C1 and experimental D1 remain OPEN.


---

## 2026-11-15 continuation — compact TT source, moving-wall reduction, static packet, cubic proper-time law

**Provenance:** original PR #1504 was CLOSED after manual integration to master (comment: "Merged into master and verified on Colab in b38e3ce9ca"). Its branch is an ancestor of the current master. This continuation starts from **current master**; do not resurrect the obsolete original PR or duplicate its 32-file content. The active new source owner is
\`scripts/ksw668_ads5_tt_clock_maxcut.py\`, with \`scripts/test_ksw668_ads5_tt_clock_maxcut.py\`. The scripts and tests were independently executed source-equivalently on SymPy 1.14: **9/9 PASS**. Exact connected-GitHub head scripts and pinned Agda kernel have NOT been run here; don't promote a source-equivalent replay into a kernel receipt.

**Source attribution:** Caldwell and Langlois, "Shortcuts in the Fifth Dimension" (2001), DOI 10.1016/S0370-2693(01)00631-1, owns the original FRW/AdS bulk horizon. Maartens and Koyama, "Brane-World Gravity" (2010), DOI 10.12942/lrr-2010-5, owns the physical moving-brane tensor equations. Koyama, "Late time behavior of cosmological perturbations in a single brane model" (2004), astro-ph/0407263, demonstrates numerical moving-boundary mode summation. Pawłowski, "Geometric time in quantum cosmology" (2014), arXiv:1403.3879v1, addresses choices of internal geometric time in an isotropic quantum-cosmology model; it does **NOT** derive an AdS5 Green operator, photon shortcut, or same-receiver signal. Seokcheon Lee, "Revisiting the Duff Argument in Cosmology: From Dimensional Quantities to Cross-Epoch Observables" (2026), arXiv:2609.35903v2, addresses dimensional unit conventions, clock standards and operational cross-epoch maps; no new fifth-dimensional causal cone follows from reparametrization alone.

### A4: rigidity of the EXACT doubled-interior-disc flat-bulk shell (NEW obstruction)

For any time-dependent but exactly flat interior shell \(r=R(\tau)\), retaining flat longitudinal \((u,v)\) directions,
\[
(K^\tau{}_\tau,K^\theta{}_\theta,K^u{}_u,K^v{}_v)
=(-\ddot R/\sqrt{1+\dot R^2},-\sqrt{1+\dot R^2}/R,0,0)
\]
with the inward orientation of the prior static doubled-disc model. For fixed tension \(T>0\), winding \(f,n\), \(a(R)=f^2n^2/(2R^2)\), the mixed shell stress is
\(S^a{}_b=\operatorname{diag}(-T-a,-T+a,-T-a,-T-a)\).
The \(Z_2\) Israel source is
\(K^a{}_b=-\frac{\kappa_5^2}{2}(S^a{}_b-\delta^a_b S/3)\).
Its **longitudinal \(u\)-component** demands
\[
0=K^u{}_u=-\frac{\kappa_5^2}{6}(T-a(R))
\quad\Rightarrow\quad R^2=f^2n^2/(2T).
\]
For fixed \(T,f,n\), \(R(\tau)\) must be constant. Therefore an actual moving radial perturbation **cannot** stay within the restrictive model of two exactly flat interior bulks with the same fixed winding matter and flat longitudinal directions. It must disturb the bulk metric, add material sectors, or alter assumptions. This is an exact ansatz obstruction, not a proof that the fully gravitating shell is stable or unstable. The prior static junction solution remains valid.

### B2: explicit conserved, compact TT anisotropic stress on the ORIGINAL a=t brane (NEW constructive result)

For \(D_i=\partial/\partial x_i\), define the local second-order transverse operator \(P_{ij}=-\delta_{ij}\Delta+D_iD_j\). Pick smooth compact spatial \(\varphi\), compact temporal drive \(g(t)\), and constant symmetric \(Q=\mathrm{diag}(0,1,-1)\). Define the **fourth-order local compact** tensor
\[
\boxed{\pi_{ij}(t,\mathbf x)
=g(t)\left(P_{ik}P_{jl}-\frac12P_{ij}P_{kl}\right)Q_{kl}\varphi(\mathbf x).}
\]
In Fourier variables \(P_{ij}(k)=|\mathbf k|^2\delta_{ij}-k_i k_j\), with \(k_iP_{ij}=0,\ P_{ik}P_{kj}=|\mathbf k|^2P_{ij},\ \mathrm{tr}P=2|\mathbf k|^2\).
It follows *identically for arbitrary k* that \(\pi=\pi^\top,\ k^i\pi_{ij}=0,\ \pi^i_i=0\). Support remains compact because no inverse Laplacian occurs. Choose \(\varphi=x^4\) near the origin inside a \(C_c^\infty\) cutoff to witness \(\pi_{yy}(0)=24,\ \pi_{zz}(0)=-24\); the source is not identically zero. For mixed-index perturbative stress on the original isotropic FRW brane, \(\bar\nabla_a\delta S^a{}_i=\partial_j\pi^j{}_i=0\) and \(\bar\nabla_a\delta S^a{}_0=-H\,\mathrm{tr}\pi=0\). Therefore this defines a conserved **prescribed linear TT source** compatible with the original tensor Israel condition
\[
n^A\partial_AH_i{}^j=-6\pi_i{}^j.
\]
On \(1\le t\le 2\), \(\rho+p\ge1/(6\sqrt5)>0\). A sufficiently small amplitude keeps the instantaneous perturbed principal stresses inside this strict background dominant-energy margin. **Not yet solved:** a microphysical brane action generating that source and the corresponding full perturbed matter/metric constraints. Conserved source existence does not alone imply a sourced retarded response.

### B3: fixed-domain moving boundary and coercive PRINCIPAL geometry (NEW exact reduction, Green OPEN)

Write original Poincaré brane \(z=b(T)=1/t\), \(v(T)=b'(T)=-1/\sqrt{1+t^2}\) and \(y=z-b(T)\ge0\). With \(H(T,z,\mathbf x)=u(T,y,\mathbf x)\),
\[
\boxed{u_{TT}-2v u_{Ty}-(1-v^2)u_{yy}
+\left(\frac3{y+b}-v'\right)u_y-\Delta_{\mathbf x}u=0.}
\]
Here \(v'=t^3/(1+t^2)^2\). The true original unit-normal source is
\[
\boxed{\frac{\sqrt{1+t^2}}{t^2}
\left[(1-v^2)u_y+v u_T\right]_{y=0}
=-6\pi^{TT}(t,\mathbf x).}
\]
For \(1\le t\le2\), \(1-v^2=t^2/(1+t^2)\ge1/2\): no characteristic-wall degeneracy. The existing exact moving-wall energy flux remains
\[
E_T=-\int_{\Sigma_T}b^{-3}[H_T H_z+\tfrac v2(H_T^2+H_z^2+|\nabla_\mathbf xH|^2)]\,d^3x
\]
without incoming horizon flux. Under \(g=H_z+vH_T\), the integrand transforms to
\[
E_T=b^{-3}\big[-(1-v^2)H_T g
+\tfrac v2(1-v^2)H_T^2-\tfrac v2(g^2+|\nabla_\mathbf xH|^2)\big]
\]
and has **either sign** even when \(g=0\). The transform and checks close the moving coefficient/normal/flux *algebra*. Full finite-energy existence/uniqueness with an incoming-horizon condition and a retarded boundary-to-brane operator, including compatibility and energy/trace estimates, remain open. General hyperbolic timelike-boundary theory is relevant but ultrastatic Robin/Neumann results cannot be imported without verifying hypotheses; see Dappiaggi–Drago–Longhi (2019/2020) DOI 10.1007/s00023-020-00929-x and Fournodavlos–Smulevici (2023) DOI 10.1093/imrn/rnab359 for related but nonidentical IBVPs.

### B5: a genuine FINITE-ENERGY stationary AdS5 tensor wavepacket (NEW positive control)

Fix a *stationary* AdS wall \(z=b>0\) with source-free Neumann \(H_z|_{b}=0\), but retain the same AdS5 bulk tensor PDE. Choose any nonzero \(f_{ij}^{TT}\in C_c^\infty(\mathbb R^3)\) supplied by the B2 differential construction. Then
\[
\boxed{H_{ij}(T,z,\mathbf x)=
\cos(T\sqrt{-\Delta_{\mathbf x}})\,f^{TT}_{ij}(\mathbf x)}
\]
is independent of \(z\), satisfies \(-H_{TT}+H_{zz}-3H_z/z+\Delta_{\mathbf x}H=0\), remains transverse/traceless and meets stationary Neumann exactly. Its compact initial profile gives finite 3D wave energy and
\[
\int_b^\infty z^{-3}\,dz=\frac1{2b^2}<\infty,
\]
so it is **finite total bulk perturbative energy**. This is a localized brane-spatial 4D massless tensor zero-mode packet, not the divergent \(z^2J_2\) separated radial basis, and not a solution to the original **moving** boundary unless the correct source is supplied. The static radial spectral gap remains zero; a nonnegative radial operator does not imply a strict mass gap.

### C1 / clock: invariant short-baseline cubic source horizon advance (NEW analytic asymptotic)

For \(A=\int_{\tau_0}^{\tau_0+\delta}d\tau/a,\ x(\tau)=\ell H(\tau)/c\), \(w=d\tau/a>0\), Caldwell–Langlois's exact horizon difference reads
\[
r_g^2-r_\gamma^2 =
\iint w(s)w(t)
[\cosh(\operatorname{asinh}x(s)-\operatorname{asinh}x(t))-1]\,ds\,dt.
\]
Expand \(x(s)=x_0+\dot x_0(s-\tau_0)+O((s-\tau_0)^2)\) and the integrand. The identity
\(\int_0^\delta\int_0^\delta(s-t)^2\,ds\,dt=\delta^4/6\) yields
\[
\boxed{\delta\tau_{\mathrm{advance}}
=\frac{\dot x_0^2}{24(1+x_0^2)}\delta^3+O(\delta^4).}
\]
For original dimensionless \(a=t,\ell=1,\tau_0=1\), \(\dot x_0=-1,x_0=1\), so coefficient = \(1/48\). High-precision original exact Eq19 checks for \(\delta=.1,.03,.01,.003,.001\) approach this coefficient; ratio for .001 is 0.9990007474. For a short local baseline \(D\simeq c\delta\tau\),
\(\delta\tau_{\mathrm{advance}}\simeq
\ell^2\dot H_0^2 D^3/[24c^5(1+(\ell H_0/c)^2)]\).
This is a **GEOMETRIC, local asymptotic** under smooth expansion, not the retarded graviton detector prediction and not an observational AdS bound. An illustrative \(\ell=D=1\) metre and \(\dot H=-H_0^2\) with \(H_0=2.2\times10^{-18}\mathrm s^{-1}\) gives \(4.03\times10^{-115}\) seconds (illustrative, no empirical extrapolation claim).

Conformal-time \(\eta=\log t\) gives \(ds_{\rm brane}^2=t^2(-d\eta^2+d\mathbf x^2)\) and lapse \(N=t\). The same geometric receiver at \(t_g=2,r=r_g\) has coordinate \(\eta_g=\log2\), while the brane-photon arrival coordinate is \(\eta_\gamma=r_g\). Their coordinate difference is \(r_g-\log2\simeq0.00465060054\), but the proper time difference is uniquely
\[
\int_{\log2}^{r_g}e^\eta d\eta=e^{r_g}-2\simeq0.00932286273.
\]
A change of homogeneous time coordinates does not change measured receiver proper time. Physical clock standards, source-equivalence and propagation maps are separate empirical/model obligations (Pawłowski and Lee crosswalk, not a shortcut theorem).

### Exact remaining B3/B4 B5/C1/D1 proof targets

1. \`ads5MovingNeumannRetardedGreenFiniteEnergy\`: choose correct AdS bulk side, compatible zero data and compact causal TT boundary source, prove finite-energy operator existence, uniqueness, support and appropriate horizon condition on a closed proper-time interval.
2. \`ads5CompactTTMatterActionRealization\`: find genuine conserved matter fields/action on the original FRW brane implementing the compact TT stress while satisfying full linearized Einstein–matter constraints, without merely prescribing \(\pi\).
3. \`ads5FiniteEnergyLocalizedTTReceiverNonzero\`: convolve B3 Green with B2 stress, prove nonzero **gauge-invariant Weyl** on the SAME comoving receiver strictly before the intrinsic photon; account for direct, reflected and KK-mode tails, and specify signal bandwidth.
4. \`cylinderDoubledDiscPerturbedBulkAndRetardedGreen\`: permit genuine gravitational departures from two exactly flat discs, derive coupled shell normal/tangential stability and the new metric-specific tensor/scalar propagator; do not borrow the unglued Minkowski receiver.
5. \`ads5LocalShortBaselineObservedComparison\`: fix \(\ell,H,\dot H\), epoch, clock standards, source equivalence, attenuation and detector band, and propagate uncertainties to GW+EM tests. The cubic geometric law alone does not pay this.
6. \`braneBulkOriginalAnalyticAgdaKernel\`: type-check all original rational owners plus new finite analytic bridges in the pinned Agda kernel; source-level polynomial checks are NOT formal kernel receipts.
7. \`physicalGravitonObservation\`: independently acquire source-characterized gravitational signal and control measurements. No qualifying experimental data presented.

**Acceptance:** local source-equivalent SymPy scripts/tests PASS 9/9; current repository PR-head execution and Agda kernel not verified. No claim of a physically demonstrated bulk carrier, FTL in full 5D spacetime, free energy, phenomenological bound on \(\ell\), or complete TOE.


### B3 stronger 2026-11-15 result: tangential energy, exact boundary flux cancellation, homogeneous uniqueness

The ordinary \(\partial_T\) energy flux is sign-indefinite for a moving Neumann wall. This does *not* mean uniqueness is unavailable. The original physical brane admits the globally timelike-on-this-interval tangent multiplier \(X=\partial_T+v(T)\partial_z\), \(v=b'(T)\), with \(|v|\le 1/\sqrt2\).

Let \(w(z)=z^{-3}\) and
\[
e_X=\frac w2\left[H_T^2+H_z^2+|\nabla_xH|^2+2vH_TH_z\right]
=\frac w2\left[(H_T+vH_z)^2+(1-v^2)H_z^2+|\nabla_xH|^2\right].
\]
For \(E_X(T)=\int_{b(T)}^\infty\int_{\mathbb R^3}e_X\,d^3x\,dz\), the original tensor PDE implies the **exact** multiplier identity
\[
\frac{dE_X}{dT}
=-\int_{\mathbb R^3}b^{-3}(H_z+vH_T)(H_T+vH_z)\big|_{z=b(T)}\,d^3x
+\int_{b(T)}^\infty\!\!\int_{\mathbb R^3}
\left[v' w H_T H_z+\frac{v w'}2(-H_T^2+H_z^2+|\nabla_xH|^2)\right]d^3x\,dz,
\]
assuming zero flux at the distant spatial/horizon ends. The boundary factorization is a genuine **moving-normal** formula: \(H_z+vH_T=(t^2/\sqrt{1+t^2})\,n^A\partial_AH=-6t^2\pi^{TT}/\sqrt{1+t^2}\).

With \(\pi^{TT}=0\), the boundary term vanishes. The bulk deformation is bounded because \(|v'|<1\), \(|v|\le1/\sqrt2\), \(b\ge1/2\) and \(w'/w=-3/z\), so
\[
E'_X(T)\le C E_X(T),\qquad
C=\frac{1+3\sqrt2}{1-1/\sqrt2}
\]
is a conservative uniform coefficient on \(1\le t\le2\). Thus \(E_X(T)\le E_X(T_0)e^{C(T-T_0)}\). For two smooth finite-energy solutions with the same initial data and homogeneous boundary data, their difference has zero initial energy and hence vanishes: **finite-interval homogeneous uniqueness**. This is the exact mathematical result, conditional on the usual regularity, compact/decaying data and no incoming infinity flux; it is not a proof of global nonlinear stability, inhomogeneous boundary trace bounds, or construction of a retarded Green operator.

For nonzero tensor boundary source \(g=H_z+vH_T\), the boundary energy term is \(-b^{-3}g\,XH\). An inhomogeneous trace/energy estimate, data compatibility at the initial slice, an outgoing-horizon condition and existence by approximation remain the explicit B3 primitives. The fixed-domain PDE in the previous section and this tangential multiplier supply an exact **non-characteristic hyperbolic plus coercivity** starting point.

Source-equivalent independently checked 1+1+one Fourier spatial-axis stress-energy differential identity returned exact SymPy zero residual after substituting the original tensor PDE. New \`tangential_wall_energy()\` symbolically proves pointwise coercive completion of squares, boundary factorization and sign control; \`test_B3_wall_tangent_energy_unique\` brings the local test total to **10/10 PASS**. The pinned Agda kernel and new exact GitHub-head scripts remain unexecuted in this tool runtime. No detector signal is inferred.
