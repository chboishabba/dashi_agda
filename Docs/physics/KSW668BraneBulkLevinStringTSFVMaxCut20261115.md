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


---

## 2026-11-15 maximum-cut continuation: RS2 Hankel source benchmark + ORIGINAL moving-AdS Neumann theorem application

**Owner:** current original-master-based PR #1508, reusing the original #1504 results already manually integrated to master; no new PR. **New scripts:** \`scripts/ksw668_hankel_moving_maxcut.py\`, \`scripts/test_ksw668_hankel_moving_maxcut.py\` (9 locally passed). Previous 10 script tests remain independent. Exact PR-head checkout/pinned Agda kernel are not executed here. The source is a properly attributed mathematical linear tensor model, not an observed source/detector or a complete self-gravitating Einstein-matter perturbation.

### Relevant original sources and corrections

1. **Giddings, Katz & Randall**, *Linearized Gravity in Brane Backgrounds*, JHEP 0003:023 (2000), arXiv:hep-th/0002091, DOI 10.1088/1126-6708/2000/03/023: scalar-derived stationary brane graviton resolvent, Green function and correct brane source matching.
2. **Mannheim**, *Causality in the brane world* (2006), arXiv:hep-th/0607041: argues that a particular normalized-mode propagator constructed without the correct large-complex-energy contour term fails causality and junction-source matching. Do **not** conclude that an arbitrarily delta-normalized mode basis itself violates causality; the correct retarded spectral calculus, contour and boundary source prescription must be specified. The GKR outgoing-Hankel formula is **stationary**, not the moving cosmology answer.
3. **Ginoux & Murro**, *On the Cauchy problem for Friedrichs systems on globally hyperbolic manifolds with timelike boundary*, arXiv:2007.02544, **Theorem 6.8**, Neumann example and **Proposition 5.1**: provides smooth compatible data wellposedness for normally hyperbolic equations with admissible Neumann conditions, and advanced/retarded Green operators for the associated homogeneous-boundary problem. This is the exact external theorem now invoked for the moving background; cite attribution, do not pretend we reproved the general theorem in Agda.
4. **Caldwell & Langlois** (2001), DOI 10.1016/S0370-2693(01)00631-1: original AdS5 \(a=t\), bulk-null vs intrinsic-brane photon horizons.
5. **Pawłowski** (2014), arXiv:1403.3879: relational geometric time in quantum minisuperspace, NOT the graviton shortcut; Lee (2026), arXiv:2609.35903v2: cross-epoch clock/reference maps and unit rescaling, NOT new bulk causality.

### F6 / B5s: exactly sourced stationary AdS5 radial retarded resolvent and KK packet — DONE at symbolic/model level

The **stationary** positive-tension RS2-type slice \(z\ge b>0\), tensor scalar operator
\[
L H=(-\partial_T^2+\partial_z^2-3z^{-1}\partial_z+\Delta_{\mathbf x})H=0
\]
with \(\partial_zH|_b=g\) has, for positive Laplace \(s\) and spatial \(\mathbf k\), \(q=\sqrt{s^2+|\mathbf k|^2}\),
\[
\boxed{\widetilde H(s,\mathbf k,z)
=-\,\frac{z^2K_2(qz)}{b^2qK_1(qb)}\widetilde g(s,\mathbf k).}
\]
This solves \(\partial_z^2H-3z^{-1}\partial_zH-q^2H=0\), \(\partial_zH(b)=g\), and decays for \(z\to\infty\). The brane impedance is
\(Z_b=-K_2(qb)/(qK_1(qb))\), with \(\lim_{q\downarrow0}q^2 Z_b=-2/b\), the normalizable massless pole. A correct retarded distribution is recovered by inverse Laplace with the analytic causal/outgoing prescription; an arbitrary time-symmetric Bessel sum is not a substitute.

The Neumann KK continuum generalized eigenfunctions in \(L^2([b,\infty),z^{-3}dz)\) are
\[
H_m(z)=\frac{\sqrt m\,z^2}
{\sqrt{J_1(mb)^2+Y_1(mb)^2}}
\{Y_1(mb)J_2(mz)-J_1(mb)Y_2(mz)\},\qquad m>0,
\]
and the normalized zero mode is \(H_0(z)=\sqrt2\,b\). The Bessel derivative/Wronskian identities give \(H'_m(b)=0\), \(H_m(b)=2b/(\pi\sqrt m D(m))\); \(\psi_m=z^{-3/2}H_m\) has the scattering asymptotics of \(\sqrt{2/\pi}\) sinusoidal waves and is delta-normalized in \(m\). Individual \(H_m\) are generalized and have infinite integrated energy, whereas a \(C_c^\infty\) spectral amplitude \(A(m)\) supported in \([0.6,1.4]\), multiplied by Schwartz transverse/traceless spatial Fourier data \(\widehat f_{ij}^{TT}(\mathbf k)\), has
\[
\|H(0)\|_{\rm energy}^2\propto
\int d^3 k\int dm\,(|\mathbf k|^2+m^2)|A(m)|^2
|\widehat f^{TT}(\mathbf k)|^2<\infty.
\]
The radial continuum and zero-mode spectral measures are **not** to be treated as a physically measured carrier; this is a finite-energy stationary control, not the original moving-brane solution. All differential identities, Laplace signs, Neumann Wronskian and spectral band integrals passed local regression.

### F7 / B3 abstract existence: ORIGINAL moving AdS5 retarded *operator* for smooth compatible TT boundary sources — THEOREM APPLICATION DONE, explicit kernel OPEN

Original conformally flat bulk
\[
g_5=z^{-2}(-dT^2+dz^2+d\mathbf x^2),\quad
\mathcal M=\{T\in[T_1,T_2],\;z\ge b(T),\;\mathbf x\in\mathbb R^3\}.
\]
Here \(b(T)=1/t(T)\), \(dT/dt=\sqrt{1+t^2}/t^2\), \(v=b'(T)=-1/\sqrt{1+t^2}\), \(v'=t^3/(1+t^2)^2>0\), \(1-v^2\ge1/2\) for \(1\le t\le2\). The wall is uniformly **timelike**; the conformal factor is smooth and positive because \(b\ge1/2\). The constant-T slices are spacelike and Cauchy on the finite strip: causality is Minkowskian under conformal change; a causal curve cannot escape to \(z,|\mathbf x|\to\infty\) in finite T, and the wall is included. Extend \(b(T)\) smoothly outside the time strip with \(b>0,|b'|<1\), if invoking a global-in-time theorem.

The tensor channel \(L H=0\) equals the normally hyperbolic scalar \(\Box_{g_5}H=0\) up to the everywhere positive multiplier \(z^2\). The brane anisotropic-stress source satisfies
\[
n^A\partial_A H=-6\pi^{TT},\quad
n^A\partial_A=\frac{z}{\sqrt{1-v^2}}(\partial_z+v\partial_T).
\]
Fix \(y=z-b(T)\ge0\) and let \(u(T,y,\mathbf x)=H(T,y+b(T),\mathbf x)\). Then \((1-v^2)u_y+v u_T=G(T,\mathbf x)\) with
\(G=-6\pi^{TT}\sqrt{1-v^2}/b\).
Take \(\pi^{TT}\in C_c^\infty((T_1,T_2)\times\mathbb R^3)\) from the prior fourth-order TT source; it vanishes near the initial slice, ensuring all corner compatibility conditions. Choose a \(C_c^\infty\) cutoff
\[
\chi(y)=
\begin{cases}e^{-y^2/(1-y^2)},&0\le y<1,\\0,&y\ge1,\end{cases}
\quad \chi(0)=1,\quad\chi'(0)=0.
\]
Then
\[
\boxed{W(T,y,\mathbf x)=
y\,\chi(y)\,\frac{G(T,\mathbf x)}{1-v(T)^2}}
\]
is smooth, compactly supported in space/time and has **exact** boundary datum \(BW=G\). Setting \(U=u-W\) gives homogeneous Neumann \(BU=0\) and compact smooth interior forcing \(F=-\Box_{g_5}W\), zero compatible initial data. Ginoux–Murro Theorem 6.8 and Proposition 5.1 (Neumann admissible) apply to this globally hyperbolic timelike-boundary scalar/tensor channel. Therefore the original linear tensor IBVP for such prescribed data has the **abstract retarded operator**
\[
\boxed{H_{\rm ret}=W+G^{\rm ret}_{N}[-\Box_{g_5}W],}
\]
where \(G_N^{ret}\) is the *homogeneous-Neumann, causal interior-source* operator defined by that theorem; causality is ensured by uniqueness/domain of dependence, not manifest termwise in the artificial lift. The earlier tangential-multiplier coercive energy verifies uniqueness independently. This is a legitimate **mathematical abstract existence/wellposedness closure** for smooth compact compatible **prescribed tensor sources** on \(1\le t\le2\), with the outgoing/no-incoming infinity condition supplied by causal support. It is **NOT** an explicit nonstationary Hankel kernel, globally nonlinear Einstein perturbation, microscopic source action or proof that the chosen physical receiver responds before the intrinsic photon.

For a geometric nonvanishing-front test, the conformal null ray from the original source \(t=1,z=1\) to receiver \(t=2,z=1/2\) has
\[
\Delta T=0.8584414617824675,\quad
\frac{\Delta z}{\Delta T}=-0.582450897655619,\quad
v(1)=-0.70710678<\Delta z/\Delta T<v(2)=-0.4472135955.
\]
Since \(b''(T)=v'(T)>0\), \(b(T)\) is strictly convex: its straight null chord lies strictly in \(z>b(T)\) between endpoints and enters/exits the wall **transversely**, with no spurious crossing into the excluded side. The reachable comoving receiver has \(r_g=\sqrt{\Delta T^2-(\Delta z)^2}=0.697797781099381>\log2=0.693147180559945\). This is an exact original-background **bulk causal reachability** witness; it still does *not* imply a nonzero source-excited Weyl amplitude without the boundary-to-boundary Schwartz kernel or a microlocal nonvanishing-amplitude proof. The source Fourier polarization must be nonzero at the ray, and possible cancellations or the detector bandwidth must be treated explicitly.

### Exact updated remaining A/B/C/D ledger and phases (as of 2026-11-15)

| Rank | Exact theorem/producer | Status and decisive proof object |
| --- | --- | --- |
| A4 | \`cylinderDoubledDiscPerturbedBulkAndRetardedGreen\` | **OPEN** — earlier flat-pair Israel radial rigidity proves departures from exact-flat ansatz are necessary; solve coupled metric plus shell dynamics and compute same-global-metric propagator |
| B2a | \`ads5CompactTTBoundarySourceConserved\` | **Math solved** — compact local fourth-order TT differential source, nonzero, divergence- and trace-free; tensor Israel coefficient \(n\cdot\partial H=-6\pi\) |
| B2b | \`ads5CompactTTMatterActionRealization\` | **OPEN** — genuine generating brane matter fields/action and complete perturbed Einstein-matter constraints |
| B3a | \`ads5StationaryHankelNeumannResolventExact\` | **Source checked** — modified Bessel K2/K1 Laplace Neumann response, zero-mode pole and strict stationary source signs |
| B3b | \`ads5StationaryKKContinuumWavepacketFiniteEnergy\` | **Source checked** — continuum Bessel/J/Y basis, zero-mode and compact spectral TT packet, stationary only |
| B3c | \`ads5MovingNeumannRetardedOperatorByIBVP\` | **External theorem application complete** for smooth compact supported prescribed TT sources on finite original interval — timelike boundary, positive conformal metric, causal T-slices, admissible Neumann, compact boundary lift and homogeneous Green; **no explicit kernel** |
| B3d | \`ads5MovingBoundaryGreenKernelOrConvergentSolver\` | **OPEN** — physically normalized moving-wall source-to-brane Schwartz kernel, convergent numerical solver, reciprocity, bandwidth, normalization |
| B4a | \`ads5OriginalBulkNullChordStaysPhysical\` | **Math solved** — convex moving wall and strict transverse interior null chord; no glancing or excluded-side shortcut |
| B4b | \`ads5LocalizedTTSourceProducesNonzeroEarlyWeyl\` | **OPEN** — show \(\delta E_{\hat y\hat y}\ne0\) at the same receiver *for retarded* localized source, before photon, by rigorous nonzero microlocal coefficient or controlled Green inversion; manufactured Bessel Weyl ≠ retarded signal |
| B5 | \`ads5MovingModeStabilityAndBackreaction\` | **OPEN** — existing coercive **linear tensor** finite-strip energy, stationary packets and zero mode do not control coupled scalar/vector/brane-bending modes or nonlinear backreaction |
| C1 | \`ads5PhysicalScaleSourceDetectorComparison\` | **OPEN** — actual \(\ell,\kappa_5\), epoch, GW frequency, clock standards, emission lag, attenuation; cubic small-baseline geometric law ≠ observable graviton arrival |
| C2 | \`braneBulkOriginalAnalyticAgdaKernel\` | **OPEN** — pinned Agda 2.9 continuum differential/integration/kernel receipts; existing rational modules source-written, not replaced by Python |
| D1 | \`physicalGravitonObservation\` | **OPEN** — original source-characterised calibrated physical measurements and independent controls; cannot be completed by math alone |

**Phase plan:** F6 stationary outgoing Hankel, radial packet and mode normalization [producer + local tests]; F7 original moving-domain timelike geometry, explicit compact source lift and abstract retarded existence [external Ginoux–Murro theorem application + local checks]; F8 **new Pareto target** compute moving retarded kernel/validated discretization, source-to-Weyl transfer and wavefront amplitude [OPEN]; F9 coupled matter action and cylinder perturbative Einstein–Israel stability [OPEN]; F10 physical calibration and empirical discriminator [OPEN]; F11 local Agda kernel/source-governance closure [OPEN]. All original authored source equations preserve attribution and do not imply 5D FTL, free energy, an observed gravitational shortcut or a unique string/TSFV/KK UV completion.

**Acceptance commands:**
\`\`\`bash
python3 scripts/ksw668_hankel_moving_maxcut.py
python3 scripts/test_ksw668_hankel_moving_maxcut.py
# Existing repo local max-cut owner includes these two, alongside original checks:
bash scripts/run_ksw668_local_maxcut.sh --math
# Kernel is a SEPARATE local step: requires the repository's pinned Agda 2.9 toolchain
\`\`\`
Local new suite **9/9 PASS** on a source-equivalent copy (SymPy/SciPy/MPMath); old 10 tests independently source-equivalent passed in prior round. Exact new connected-GitHub branch runner, full old acceptance and Agda kernel have not been executed by this runtime. No CI results substituted.


### F6 numerical packet actually evaluated; static no-shortcut negative control (11/11 new tests)

The stationary Neumann outgoing calculation is supplemented by an actual finite-energy TT packet rather than only a symbolic norm integral. For the radial continuum take \(m\in[0.6,1.4]\) and
\[
A(m)=
\begin{cases}
\exp[-0.03/((m-0.6)(1.4-m))],&0.6<m<1.4,\\0,&\text{else.}
\end{cases}
\]
For a symmetric tracefree \(Q=\operatorname{diag}(0,1,-1)\), use the real-space local TT fourth-order construction. In Fourier form
\(\widehat f^{TT}_{ij}(\mathbf k)=[P_{ik}P_{jl}-P_{ij}P_{kl}/2]Q_{kl}\,e^{-|\mathbf k|^2/2}\), \(P=|\mathbf k|^2I-\mathbf k\mathbf k^\top\). The angular averages at \(\mathbf x=0\) are
\[
\langle\widehat f_{yy}^{TT}\rangle_{S^2}=\tfrac25 k^4 e^{-k^2/2},
\qquad
\langle\|\widehat f^{TT}\|^2\rangle_{S^2}=\tfrac45 k^8e^{-k^2}.
\]
Hence the *explicitly evaluated* stationary tensor packet is
\[
H_{yy}(T,z,0)
=\frac{8\pi}{5(2\pi)^{3/2}}\int_{0.6}^{1.4}dm\,A(m)H_m(z)
\int_0^\infty dk\,k^6e^{-k^2/2}\cos(T\sqrt{k^2+m^2}),
\]
with positive finite initial energy
\[
E(0)=\frac{8\pi}{5}\left[
\tfrac12\Gamma(\tfrac{13}{2})\int |A(m)|^2dm+
\tfrac12\Gamma(\tfrac{11}{2})\int m^2|A(m)|^2dm
\right].
\]
Independent SciPy quadrature: \(\int |A|^2dm=0.41073100423980546\), \(\int m^2|A|^2dm=0.4249976277102043\), \(E(0)=353.08728191472755\) (chosen model amplitude), \(H_{yy}(0.2,1.5,\mathbf0)=1.5683695535242972\). The exact source script tests these quantities and fail-closes physical promotion.

**Static no-shortcut negative control:** in stationary planar AdS conformal coordinates, both emitter and receiver have \(z=b\), so a causal bulk path must satisfy \(\Delta T\ge\sqrt{|\Delta\mathbf x|^2+(b-b)^2}=|\Delta\mathbf x|\), exactly the intrinsic photon earliest time. The stationary outgoing Hankel kernel cannot by itself demonstrate the *expanding-brane* early arrival. The strict shortcut requires the convex moving \(b(T)\) boundary separately certified above.

The new \`scripts/test_ksw668_hankel_moving_maxcut.py\` now contains **11** source-equivalent locally passed tests: radial PDE/Neumann/pole; outgoing static Laplace decay; generalized Bessel Wronskian; normalized zero mode; finite compact KK band; nonzero actually evaluated finite-energy TT packet; compact moving boundary lifting; Ginoux–Murro timelike-Neumann theorem preconditions plus strict interior null chord; illegal parameter rejection; static no-shortcut control; and the physical fail-closed guard. This does **not** mean 11 Agda kernel acceptances or 11 physical results.

**Revised exact terminal status:** A1–A3 analytic test-scalar positive receiver on flat cylinder; A4 static self-gravitating shell background with moving-flat-bulk rigidity only; B2 mathematical compact TT stress and linearized Israel coefficient, **microphysical action open**; B3 abstract smooth prescribed-source moving retarded operator **exists by Ginoux–Murro theorem application**, explicit brane-to-brane Green kernel/constructive evaluation open; B4 physical nonzero early TT Weyl reception open; B5 stationary TT packet finite energy but moving full coupled stability open; C1 realistic observation/scale fit open; C2 pinned Agda analytic kernel open; D1 experimental evidence open.

**Next maximum-cut implementation** must compute the original moving background boundary-to-boundary *Schwartz kernel* or a convergently validated discretization of its abstract \(G_N^{ret}\), choose the prepared compact TT source with nonzero ray polarization, calculate an early \(E_{\hat y\hat y}\) receiver and explicit source normalization, then weld a genuine brane matter action and full constraints. The stationary resolvent is a correct test/limit, not a substitute for that moving kernel.


---

## 15 Nov 2026 F8 steelman: ORIGINAL moving AdS5 source-to-Weyl time-domain simulation, plus UV fail-closed compact TT extension

**Authoritative existing PR:** #1508, branch \`research/ksw668-brane-tt-clock-maxcut-20261115\`. New source \`scripts/ksw668_f8_moving_maxcut.py\`, local unit tests \`scripts/test_ksw668_f8_moving_maxcut.py\`, three-grid \`scripts/ksw668_f8_refinement.py\`, smoke/full gate \`scripts/check_ksw668_f8_maxcut.sh\`; new record \`Artifacts/ksw668/ads5_f8_moving_receiver_refinement_20261115.json\`. We are **not** copying stationary RS2 onto a moving wall; same original a=t, original \(\kappa_5^2=6\), original Israel source. Independent source-equivalent local 8/8 unit PASS. The full F8 convergence gate returns **exit 42** by design for the unresolved compact 3D Weyl endpoint.

### Primary-source ownership and corrections

- **Hiramatsu, Koyama & Taruya**, hep-th/0308072 (2003), hep-th/0410247 (2004): direct Poincaré-coordinate 5D tensor cosmological evolution and KK suppression — the appropriate *numerical algorithmic precedent*, not an early compact-source detector claim.
- **Gorbunov, Rubakov & Sibiryakov**, hep-th/0108017 (2001): inflating and terminating dS brane, Bogoliubov mixing; not the present a=t source/receiver experiment.
- **Clarkson & Seahra**, gr-qc/0505145 (2005), *Braneworld resonances*: **two** authors, stationary Einstein-static brane in Schwarzschild–AdS, quasinormal time-domain resonance analysis. The supplied description attributing this paper to "Seahra, Clarkson & Maartens" and saying it proves **moving AdS5 early Weyl arrival** is incorrect. Seahra–Clarkson–Maartens are authors of a *different* 2005 black-string/KK spectroscopy paper.
- **Shiromizu, Maeda & Sasaki**, gr-qc/9910076 (2000): the brane effective field equation features **projected electric 5D Weyl** \(\mathcal E_{ij}^{(5)}=C^{(5)}_{ABCD}n^A e_i^B n^C e_j^D\), *not identical* to our **intrinsic 4D electric Weyl** \(\delta C^{(4)}_{\hat0\hat i\hat0\hat j}\). Both gauge-invariant readout definitions require explicit distinct normalization and weld.
- **Bridgman, Malik & Wands**, astro-ph/0107245 (2001/02): bulk/brane perturbations and gauge-invariant master fields; tensor-only positive results are not full scalar/vector/coupled Einstein-matter closure.
- **Ginoux & Murro**, arXiv:2007.02544, *Advances in Differential Equations* 27 (2022) 497–542: theorem 6.8 supplies smooth compatible Neumann IBVP existence, as previously stated; it is not a quantitative numerical error estimate.
- The original **flat spatial** \(k=0,\ a=t\) model is *linear-coasting flat FRW*, **not Milne** (the empty Milne form uses spatial curvature \(k=-1\)). Calling this original model "Milne" confuses physically distinct geometries.
- Do not infer that only dS permits all possible analytic Green kernels: this would require an exhaustive nonexistence theorem, not provided.

### F8.01 Exact original moving-wall tensor PDE and boundary source

Define \(T(t)=\operatorname{arsinh}t-\sqrt{1+t^2}/t\), \(z_b=b(T)=1/t\), \(v=b'=-1/\sqrt{1+t^2}\), \(y=z-b(T)\). For spatial Fourier \(e^{ikx}\), use
\[
p=H_T|_{z},\quad w=H_z,\quad q_\pm=p\pm w,
\]
where derivatives \(\partial_T\) on \(p,w,q_\pm\) in the displayed equations below are taken at fixed moving \(y\). Then the **original** bulk tensor PDE and sourced Israel normal reduce exactly to
\[
\begin{aligned}
\partial_T q_+&=(v+1)\partial_y q_+ -\frac{3}{y+b}\frac{q_+-q_-}{2}-k^2H,\\
\partial_T q_-&=(v-1)\partial_y q_- -\frac{3}{y+b}\frac{q_+-q_-}{2}-k^2H,\\
\partial_T H&=\frac{1+v}{2}q_++\frac{1-v}{2}q_-.
\end{aligned}
\]
At \(y=0\),
\[
\boxed{q_-(T,0,k)=\frac{2g(T,k)-(1+v)q_+(T,0,k)}{v-1}},\qquad
g=-6\frac{\sqrt{1-v^2}}{b}\widehat{\pi}^{TT}.
\]
Thus only the **incoming** characteristic is prescribed. The source is a compact smooth \(C^\infty\) temporal bump in \(T\), with the correct original moving Israel coefficient. Spatial one-sided 2nd-order characteristic upwind and SSP-RK3 are used. Initial data are exactly zero; the remote boundary has zero incoming characteristic, with a domain width chosen so its return cannot contaminate the tested physical causal window.

### F8.02 Two source models; finite-energy distinction is mandatory

**Control P (plane-symmetric).** \(H_{yy}=-H_{zz}=H(T,y,x)\), uniform in the other two brane spatial directions. The compact \(C^\infty\) source \(f(x)\) with support \(|x|<\epsilon\) supplies a well-defined, finite-energy-*per-transverse-area* retarded linear tensor solution. Its total energy integrated across the infinite transverse plane is **infinite**. It is a genuine mathematical moving-boundary source/receiver **control**, not the full physical 3D compact B4 witness.

**Control C (genuinely compact 3D TT).** Let \(\varphi(\mathbf x)\) be smooth radial bump of support \(r<\epsilon\), normalized spatial integral one. Apply the earlier local fourth-order divergence-free/traceless TT projector \(Q=\mathrm{diag}(0,1,-1)\) to obtain a smooth, spatially compact 3D tensor boundary source. This has a finite-energy retarded tensor solution at the *continuum/theorem* level. In Fourier \(k\), its \(yy\) angular factor on the \(x\)-axis is
\[
W(\mu)=\frac{\mu^4+6\mu^2+1}{8}
=\frac25P_0(\mu)+\frac47P_2(\mu)+\frac1{35}P_4(\mu).
\]
Thus \(H_{yy}(T,r)\) is reconstructed from \(\frac1{4\pi^2}\int_0^\infty k^6\widehat\varphi(k)\widehat H_{\rm transfer}(T,k)\mathcal A(kr)\,dk\),
\[
\mathcal A(\xi)=2\left[\tfrac25j_0(\xi)-\tfrac47j_2(\xi)+\tfrac1{35}j_4(\xi)\right].
\]
The \(x\)-second-derivative reconstruction requires the distinct \(\mu^2W(\mu)\) angular weights
\[
\mu^2W(\mu)=\frac{22}{105}P_0+\frac47P_2+\frac{81}{385}P_4+\frac2{231}P_6.
\]
This **fourth-order compact TT construction strongly magnifies ultraviolet/spectral truncation errors**. The implemented mesh and cutoff do not yet resolve those errors.

### F8.03 Physical photon-dark receiver, and two distinct electric Weyl observables

Choose source onset \(t=1\), receiver time \(t=6\) (a *longer* same-original-background window than the original t=2 comparator, to avoid falsely resolving a tiny signal with inadequate grid spacing). Exact source-metric horizons are:
\[
r_g(6)=1.8300210521210103,\quad
r_\gamma(6)=\log6=1.791759469228055.
\]
Choose \(r_{\rm obs}=r_g(6)-0.008=1.8220210521210103\), \(C^\infty\) source spatial support half-width \(\epsilon=.024\), and temporal support \(0<T-T(1)<.007\). Then
\[
r_{\rm obs}-\epsilon-r_\gamma(6)=
\boxed{0.006261582892955309>0}.
\]
**Every brane-confined photon emitted from the stated compact source after t=1 still lies outside this receiving location at t=6.** However this is an enlarged geometric comparator, not a substituted proof for the earlier specifically requested t=2 receiver.

For the induced FRW brane metric in conformal time \(\eta=\log t\), the **intrinsic 4D** electric Weyl plus component on the \(x\)-axis is
\[
\boxed{\delta E_{\hat y\hat y}^{(4)}
=-\frac{1}{4t^2}(\partial_\eta^2+\partial_x^2)H_{yy}},
\quad \frac{dT}{d\eta}=\frac{\sqrt{1+t^2}}t.
\]
Time differences are centred at the **same actual physical t** for each grid. We do *not* equate this to the **projected 5D Weyl** tensor \(\mathcal E_{ij}^{(5)}\) in Shiromizu–Maeda–Sasaki without an independent Gauss–Codazzi/Israel gauge weld. The latter is an explicit new B4 subgate.

### F8.04 Measured source-equivalent LOCAL mesh results (mathematical model units)

| Source | N_x | dy | H_yy | intrinsic electric Weyl |
|---|---:|---:|---:|---:|
| Plane control | 256 | 0.012 | +0.00606200 | +0.0603973 |
| Plane control | 512 | 0.007 | +0.00645275 | +0.1043860 |
| Plane control | 768 | 0.005 | +0.00655405 | +0.1123832 |
| Compact 3D TT | 256 | 0.012 | +0.02690186 | −0.775852 |
| Compact 3D TT | 512 | 0.007 | +0.09542997 | −15.6923 |
| Compact 3D TT | 768 | 0.005 | +0.06429828 | −92.4320 |

Fine-to-medium relative drift: plane field **1.55%**, plane Weyl **7.12%**; compact 3D TT field **48.42%**, compact 3D Weyl **83.02%**. Near a receiver beyond the entire bulk null future the 768-grid plane residual is \(1.35\times10^{-11}\) versus early field \(0.00655\); the compact 3D TT residual is \(1.32\times10^{-4}\), numerically **not negligible**. Numerical Fourier truncation can leak outside a compact continuum light cone, so a nonzero early grid value alone is **not** a causality/nonvanishing certificate.

**Disposition:** This is the first executable ORIGINAL moving-wall retarded TT receiver and electric-Weyl *numerical* test with a strictly brane-photon-dark support window, but it has **NOT** passed the full 3D compact TT convergence gate. No change to physical B4 = OPEN. A claimed finished 'nonzero graviton signal' would be mathematically premature.

### Phases, exact remaining lemma contracts, and next big cut

| Phase | Exact lemma / deliverable | Acceptance |
|---|---|---|
| F8a | \`ads5MovingTTCharacteristicIsraelBoundaryExact\` | Algebraic transform and incoming-only source; source written/checks; Agda continuum OPEN |
| F8b | \`ads5MovingTTPlanarReceiverAndPhotonDarkControl\` | True original moving PDE; local 8 unit cases PASS; plane early *numerical control*, not total-energy 3D |
| F8c | \`ads5MovingTTCompact3DSpectralCutoffConvergence\` | **OPEN (failed)**: show 3D compact TT field and both 4D Weyl, 5D projected Weyl converge under independent k-cutoff, angular resolution, dy, dt, source-width and outer-boundary refinements; eliminate outside-cone Fourier leakage |
| F8d | \`ads5LocalizedTTSourceProducesNonzeroEarlyWeyl\` | **OPEN**: original same-worldline compact 3D source gives finite-energy and stable *nonzero* retarded Weyl before the photon with controllable error; need also t=2 comparator |
| F8e | \`ads5OriginalNoGlancingNeumannPoissonPrincipalSymbol\` | **OPEN**: non-glancing Neumann boundary microlocal principal symbol, no caustics, transverse source/detector polarization and non-cancelling leading coefficient; prior Melrose–Sjöstrand boundary-propagation literature relevant but not automatically a proof |
| F9a | \`ads5CompactTTMatterActionRealization\` | **OPEN** microphysical stress generating action satisfying complete perturbed Einstein–matter constraints |
| F9b | \`cylinderDoubledDiscPerturbedBulkAndRetardedGreen\` | **OPEN** separate same-global-metric coupled shell/gravity perturbation |
| F9c | \`ads5MovingModeStabilityAndBackreaction\` | **OPEN** all physical modes and backreaction, not only tensor linear finite-strip energy |
| F10 | \`ads5PhysicalScaleSourceDetectorComparison\` | **OPEN** physical AdS length, cosmological epoch, frequency, source emission lag, attenuation, GW constraints; zero free-energy or 5D FTL inferred |
| F11 | \`braneBulkOriginalAnalyticAgdaKernel\` | **OPEN** pinned local Agda 2.9 acceptance, actual differentiable geometry and source/Green/projection proof |
| D1 | \`physicalGravitonObservation\` | **OPEN** independent controlled measurements and independently replicated evidence |

**Acceptance and exact commands**
\`\`\`bash
bash scripts/check_ksw668_f8_maxcut.sh --smoke
# 8 local unit/control tests PASS, not B4 acceptance
bash scripts/check_ksw668_f8_maxcut.sh --full
# 3-grid BOTH source classes; presently exits 42 (correct failed 3D convergence)
python3 scripts/ksw668_f8_refinement.py
# saves scripts/ksw668_f8_refinement_receipt.json
\`\`\`
The existing \`scripts/run_ksw668_local_maxcut.sh --math\` imports F8's **smoke** checks, leaving the expensive/failed convergence gate explicit and separate. CI is not substituted for local verification. Exact new PR-head GitHub checkout and pinned Agda have not been executed in this tool environment; the local source-equivalent producer and its **8/8** unit cases ran independently here.

**Highest-alpha cut next:** fix compact 3D \(k^4\) ultraviolet/angular reconstruction using high-order/validated spectral inversion with independent \(k_{\max}\) and \(\Delta k\) control, then implement the **projected 5D Weyl** source-to-receiver observable and the same *t=2* original comparator. An alternative rigorous route is a non-glancing, no-conjugate-point boundary Fourier-integral principal-symbol nonvanishing theorem with a prepared compact high-frequency TT pulse. Both routes need actual proof; no shortcut by model-label coincidence or arbitrary waveform threshold.


### F8.05 Steelman: exact ORIGINAL t=2 non-glancing compact-source microlocal preflight (5 additional tests)

The exploratory \(t=6\) finite-difference control deliberately enlarged the photon-dark window but does **not** replace the original \(t=2\) endpoint. Now independently check the original **same receiver** \(r=r_g(2)=0.697797781099381\), \(t_{\rm obs}=2\) with a **smooth compact 3D TT source genuinely supported inside** \(|\mathbf x|<\epsilon=0.001\) and a temporal drive with interior point \(T_e-T(1)=0.0002\). The corresponding actual emission proper time and brane spatial point are
\[
t_e=1.000141436357416,\qquad
x_e=r_g(2)-r_g(t_e,2)=0.00014471324980684235,
\]
so \(\boldsymbol x_e\) is **strictly inside the source's compact spatial support**, not a zero-amplitude boundary point. The intrinsic photon exclusion, even allowing the entire spatial source support, is
\[
r_g(2)-\epsilon-\log2=0.003650600539435688>0.
\]
The direct null interior chord has radial Poincaré slope \(\dot z/\dot T=-0.5824218543413765\), while the brane velocities at its two endpoints are
\[
v_{\rm emit}=-0.707056777651097,\qquad v_{\rm recv}=-0.4472135954999579.
\]
Thus \(v_{\rm emit}<\dot z/\dot T<v_{\rm recv}\) (strictly enters the allowed bulk at emission, exits to receiver), and convexity \(b''(T)=t^3/(1+t^2)^2>0\) ensures the straight chord lies in \(z>b(T)\) at all intermediate times. The actual unit-normal principal factors for \(\omega_{\rm bulk}=1\) are
\[
\boxed{n\cdot\xi|_e=+0.17622301193802767,\quad
n\cdot\xi|_r=-0.07558371447219975}
\]
and therefore neither brane interaction is glancing. Constant-curvature AdS5 has \(R(J,k)k=0\) for orthogonal screen Jacobi fields along a null \(k\), excluding an interior null conjugate-point focusing obstruction for this direct chord. For \(Q=\operatorname{diag}(0,+1,-1)\) and spatial wavevector along the x-ray, the **local compact TT projector** has nonzero \(yy\) principal symbol, and the **intrinsic 4D electric-Weyl** principal factor at the receiver is
\[
\boxed{\frac{\omega_\eta^2+k_x^2}{4a^2}=0.0840263224215478>0.}
\]
All these **geometric and algebraic** factors are exact original-model expressions and were independently checked numerically at high precision in \`scripts/ksw668_f8_non_glancing_source.py\`; \`scripts/test_ksw668_f8_non_glancing_source.py\` passed **5/5** local cases including too-small-source failure. The same conditions hold with wider margin at \(t=6\).

**Next theorem to import rigorously rather than assert:** the non-glancing boundary Neumann-to-Dirichlet wave operator is a microlocal elliptic Fourier integral operator associated with the lens relation, with nonzero principal trace symbol. Useful original sources: Melrose–Sjöstrand, *Singularities of boundary value problems I/II* (1978/1982); Stefanov–Yang, *The inverse problem for the Dirichlet-to-Neumann map on Lorentzian manifolds*, *Analysis & PDE* 11 (2018), elliptic FIO lens relation; and *Inverse boundary value problems for wave equations with quadratic nonlinearities*, *J. Differential Equations* (2022), §6.4 Lemma 13, which explicitly constructs Neumann boundary waves with a singularity reaching a transversally-hit receiving boundary and nonzero incident/reflected trace principal symbol. This theorem route, composed with the now **nonzero original Neumann factors**, the nonzero compact TT differential symbol and the nonzero Weyl symbol, has a serious prospect of proving an **existential** nonzero early retarded smooth high-frequency wavepacket for *prescribed* brane TT stress without brute-force \(k^4\) numerical inversion. One must check the precise hypotheses of the source FIO theorem on the original noncompact time strip and construct compatible compact microlocal oscillatory data; it is **not yet a kernel-accepted proof** of the composition or the full physical receiver.

**Precise additional lemma:** \`ads5OriginalT2NonGlancingCompactTTRayPrincipalExact\` — **PASS mathematical exact-model algebra/smooth interior support check; Agda OPEN**. \`ads5OriginalT2NeumannToWeylEllipticFIOComposition\` — **OPEN analytic theorem application**. \`ads5OriginalT2CompactTTActualEarlyNonzeroWeyl\` — **OPEN final prescribed-source existential wave proof**. The microphysical stress-generating brane action, SMS projected 5D electric Weyl, nonlinear/all-mode stability, physical scale, Agda kernel and empirical observation remain distinct and OPEN.

**Local checks:** \`bash scripts/check_ksw668_f8_maxcut.sh --smoke\` now includes 8 original time-domain controls plus 5 original t2 non-glancing controls (**13 new independent tests**), and prints the exact t2/t6 ray contract. \`--full\` continues to **exit 42** for unresolved 3D Fourier/Weyl numerical convergence. The canonical model does not assume that one failed finite-difference discretization refutes the five-dimensional shortcut hypothesis; the microlocal and spectral/convergent-numerical paths are complementary.


---

## 2026-11-15 F8 max-cut III: strict null-convex ORIGINAL 5D boundary; dimension-correct lens literature; SMS projected 5D Weyl readout

**Owner:** PR #1512, post-merge continuation FROM CURRENT MASTER of merged #1508. All previous original-model producers remain in master; do not reopen/duplicate merged PRs. New \`scripts/ksw668_f8_null_convex_lens.py\`, \`scripts/ksw668_f8_projected_weyl_sms.py\` with six and four fail-closed tests respectively. The total F8 smoke contains **8 moving-PDE + 5 original-t2 non-glancing + 6 null-convex + 4 SMS = 23 independently tested source-equivalent checks**. Exact GitHub-head runner and pinned Agda kernel have not run here; the compact 3D numerical convergence gate **still exits 42**.

### F8.06 New exact ORIGINAL 5D null-convexity lemma

For the *original* Poincaré AdS5 physical one-sided domain \(\mathcal M=\{z\ge b(T)\}\), metric \(g=z^{-2}(-dT^2+dz^2+d\mathbf x_3^2)\), outward unit normal and covector are
\[
\nu_{\rm out}=-\frac{b}{\sqrt{1-v^2}}(v,1,0,0,0),\qquad
(\nu_{\rm out})_\flat=\frac{1}{b\sqrt{1-v^2}}(v,-1,0,0,0),\quad v=b'(T).
\]
For a boundary-tangent null vector \(L=(1,v,\mathbf u)\), with \(|\mathbf u|^2=1-v^2\), the null second fundamental form in the *outward normal* convention used by Uhlmann–Zhang satisfies
\[
\boxed{\kappa_{\rm out}(L,L)=g(\nabla_L\nu_{\rm out},L)
=\frac{b''(T)}{b\sqrt{1-v^2}}
=\frac{t^3}{(1+t^2)^{3/2}}>0.}
\]
The conformal Christoffel term cancels identically in this null contraction (both \(g(L,L)=0\) and \(g(\nu,L)=0\)). Thus the ORIGINAL \(a=t\) boundary is *strictly null-convex in five spacetime dimensions* on \(1\le t\le2\), not merely timelike. At the actual source/receiver crossing pair from F8.05:
\[
\kappa_e=0.3536283958961996,\quad
\kappa_r=0.7155417527999327.
\]
Stationary \(b''=0\) gives a **non-strict** control, consistent with the static planar no-shortcut geometry. The strict convexity is an original-model geometric result with exact SymPy derivation, independent of the unstable numerical 3D Fourier inversion.

### F8.07 Correct dimension and precise available Fourier-integral theorems

**Caution: do not claim Uhlmann–Zhang 2022 Lemma 13 directly proves our 5D B4.** Uhlmann & Yang Zhang, *Inverse boundary value problems for wave equations with quadratic nonlinearities*, JDE 309 (2022) 558–607, DOI 10.1016/j.jde.2021.11.033, **explicitly begin with a 1+3-dimensional** globally hyperbolic Lorentzian manifold with a timelike/null-convex boundary. Their Lemma 13 (§6.4) constructs Neumann boundary input and shows that the outgoing (incident+Neumann-reflected) receiver trace has a nonvanishing principal symbol, recovering the lens relation. The mechanism is directly relevant, but application to the **1+4** original bulk requires a dimension-check/transfer.

A direct dimension-correct upstream theorem is **Plamen Stefanov & Yang Yang**, *The inverse problem for the Dirichlet-to-Neumann map on Lorentzian manifolds*, Analysis & PDE 11 (2018) 1381–1404, DOI 10.2140/apde.2018.11.1381, original paper §§3–4:
- explicitly \((M,g)\) has dimension **\(1+n,\ n\ge2\)**, so includes our \(1+4\);
- **Theorem 3.1:** local outgoing **Dirichlet-to-Neumann** is an *elliptic pseudodifferential* operator of order 1 near a **timelike tangential covector** (its microlocal inverse exists and is an elliptic local Neumann-to-Dirichlet parametrix of order \(-1\));
- **Theorem 4.2:** semiglobal reflected **Dirichlet-to-Neumann** map is an *elliptic Fourier integral operator* of order 1 on the non-glancing, first-reflection lens canonical graph. The geometric optics principal transport is nonzero along a direct null ray with no interior conjugate point; it is local/semiglobal, so the original noncompact radial horizon is not a blocking global compactness hypothesis;
- their Eq. (58) exhibits the incident-plus-reflected factor 2, and Eqs. (59)–(60) explicitly introduce local Neumann-to-Dirichlet and interior propagation parametrices.

**Exact distinction:** this paper constructs an elliptic **Dirichlet-to-Neumann**, not by itself our *source-Neumann-to-receiver-boundary-trace-and-Weyl* operator. To convert it, one must (a) apply the elliptic \(\Lambda_{\mathrm{loc}}^{-1}\) at the emitting boundary, (b) propagate the nonzero incident FIO along the unique direct interior chord and (c) impose **homogeneous Neumann**, rather than Dirichlet, reflection at the receiving boundary, giving receiver *trace* factor +2, as in Uhlmann–Zhang's local argument. The known endpoint Neumann principal symbols are nonzero, so the local reciprocal factor is finite. An **explicit detailed 1+4-dimensional Neumann trace/FIO operator composition proof**, with its support cutoffs and remainder estimate, is still the honest \`ads5OriginalT2NeumannToWeylEllipticFIOComposition\` terminal analytic obligation. Do NOT label it kernel-accepted or fully demonstrated simply because the geometry and upstream dimension match.

### F8.08 New exact original projected FIVE-dimensional Weyl SMS tensor coefficient

Do not silently identify the earlier **intrinsic 4D electric Weyl** \(C_{\hat0i\hat0j}^{(4)}\) with the physically distinct **5D projected electric Weyl**
\[
\mathcal E^{(5)}_{\mu\nu}=C^{(5)}_{ABCD}n^A e_\mu^B n^C e_\nu^D
\]
in Shiromizu–Maeda–Sasaki, *The Einstein equations on the 3-brane world*, PRD 62 024012 (2000), DOI 10.1103/PhysRevD.62.024012.

The original tension-tuned \(\sigma=1,\kappa_5^2=6,\ell=1\) background has \(\Lambda_4=0,\ \kappa_4^2=\kappa_5^4\sigma/6=6\). In mixed-index effective-brane form:
\[
G^\mu{}_\nu=\kappa_4^2T^\mu{}_\nu+
\kappa_5^4\Pi^\mu{}_\nu-\mathcal E^{(5)\mu}{}_\nu,\qquad
\Pi=-\tfrac14T^2+\tfrac1{12}\operatorname{tr}(T)T+
\big(\tfrac18\operatorname{tr}(T^2)-\tfrac1{24}\operatorname{tr}(T)^2\big)I.
\]
For original perfect-fluid \(T^\mu{}_\nu=\operatorname{diag}(-\rho,p,p,p)\) and a pure TT source \(\delta T^i{}_j=\pi^i{}_j\), direct *matrix differentiation* yields
\[
\boxed{\delta\Pi^i{}_j\big|_{\rm TT}
=-\frac{\rho+3p}{12}\pi^i{}_j},
\quad
\boxed{\delta\mathcal E^{(5)i}{}_j\big|_{\rm TT}
=[6-3(\rho+3p)]\pi^i{}_j
-\frac12\left(\partial_t^2+3H\partial_t-a^{-2}\Delta\right)H^i{}_j.}
\]
**Correct sign:** in Minkowski TT gauge, \(\delta G_{ij}=+\tfrac12(h_{tt}-h_{xx})_{ij}\) (not minus). This check corrects a tempting false sign in previous draft exploration. At the original kernel-friendly \(t=4/3\), \(\rho=1/4,p=-1/10\), the TT source coefficient is **exactly \(123/20\)**, independently SymPy-checked.

At the original \(t=2\) receiving event, the source is absent, \(\pi_{\rm recv}=0\). The *high-frequency projected-5D-Weyl* principal multiplier from the SMS formula is
\[
\sigma(\delta\mathcal E^{(5)})=
+\frac12(n\cdot\xi)^2\,\sigma(H)
\quad\Rightarrow\quad
\boxed{\frac12(-0.07558371447219975)^2
=0.002856448946707509>0}.
\]
This uses the bulk null relation to identify the squared **timelike boundary projection**, and is distinct from the already-checked positive intrinsic-4D Weyl principal factor \(0.0840263224215478\) for the original ray. Both are *local ellipticity/nondegeneracy factors*, **not measured curvatures and not a retarded amplitude**. The unsupplied lens-FIO global principal transport multiplier remains explicitly unknown. The 5D projector is now algebraically linked to the same original TT source/metric field; its *numerical retarded value* remains open and must not be inferred by combining unrelated model waveforms.

### F8.09 Precise steelman existential proposition and proof gap

**Proposed proposition (P), for prescribed—not microphysically generated—stress.** There exists a real, smooth, compactly supported, background-conserved, nonzero TT boundary anisotropic source of arbitrarily small amplitude whose unique finite-energy retarded *linear* tensor field on the original \(a=t\) AdS5 brane has nonzero **intrinsic 4D** and **projected 5D** electric Weyl response at the original \(t=2,r=r_g(2)\) receiver, strictly before any photon emitted by that source could arrive.

**Proof strategy:** Prepare a microlocal oscillatory \(C_c^\infty\) bump near the exact \((T_e,x_e)=(T(1)+0.0002,\,0.0001447132498)\) in the source ball radius 0.001; apply the earlier compact local fourth-order TT operator with \(\lambda^{-4}\) normalization. The spatial TT \(yy\) symbol is 1 along the selected ray, and the boundary tangential projection of the null covector is strictly timelike. By Stefanov–Yang Thm 3.1, the local outgoing DN operator is elliptic and microlocally invertible: this supplies the Neumann incidence amplitude \(\propto(n\cdot\xi_e)^{-1}\ne0\). Their Thm 4.2 gives an elliptic FIO along the non-glancing direct interior lens relation with nonzero principal propagator, and the original 5D wall is strictly null-convex; constant AdS curvature gives no null screen focusing. Impose homogeneous Neumann at arrival: the leading incident and reflected boundary **trace** coefficients add, rather than cancel. Compose the two **nonzero Weyl** principal multipliers above. An appropriately phased smooth real oscillatory bump then has nonzero leading boundary Weyl value at the same original event for some sufficiently high \(\lambda\), unless the operator composition acquires a cancellation of identical canonical relations not covered by the local microlocal cutoffs. Any nonzero source amplitude may be further rescaled small so that the linear perturbative approximation remains meaningful.

**ACCEPTANCE MUST STILL PROVE:** the full Neumann receiving-boundary reflection/FIO symbolic product in 1+4 dimensions and its \(O(\lambda^{-1})\) remainder after localization, including the removal of all *competing lens branches* near this target, and the selected real smooth compact support. This is now a **single sharply delimited analytic theorem-transfer/weld**, not an undefined “construct a propagator from scratch” task. Source-level B4 existential claim (P) is a **strong steelman conditional conclusion, NOT accepted until this weld**. A physically generated matter action, nonlinear Einstein/Israel perturbations, calibrated amplitude/observations, original C2 Agda kernel and D1 experiment remain separate original gates.

### Revised maximum cuts / deliverables / local acceptance

| Cut | What is DONE in this continuation | Real missing primitive |
|---|---|---|
| F8-GEO | exact \(t=2\) photon-dark source-point, allowed strict bulk chord, non-glancing endpoints, **strict 5D null-convex outward K**, nonfocusing | original continuous Agda kernel proof of differential metric/second fundamental form |
| F8-PDE | original moving retarded operator by Ginoux–Murro theorem, 8-case plane numerical early-wave positive control; compact 3D numerical attempt | full 3D numerical convergence (currently 48% field /83% Weyl drift, exit42) **or** F8-FIO route |
| F8-FIO | dimension-correct Stefanov–Yang 2018 local DN ellipticity, semiglobal FIO lens, nonzero source normal/TT/Weyl symbols | **\`ads5OriginalT2NeumannToWeylEllipticFIOComposition\`** with real compact source, 5D Neumann receiving reflection/remainder/noncancellation |
| F8-SMS | exact 5D projected electric Weyl **algebra** and \(t=4/3\) coefficient \(123/20\), nonzero receiver principal | actual retarded \(\delta\mathcal E^{(5)}\) from fully evaluated moving TT field or FIO composition |
| F9-MAT | prescribed conserved source satisfies homogeneous background conservation | actual generating matter action, full linearized Einstein-matter constraints and DEC under perturbation |
| F9-CYL | static doubled-disc shell and flat-bulk rigidity proven | bulk/shell perturbations and same-global-metric dynamics |
| F9-STAB | coercive finite-interval linear tensor energy and static normalizable packet | all physical modes and nonlinear backreaction |
| F10 | geometric cubic horizon law and proper clock map | correct \(\ell,H,\dot H\), source detector band/attenuation, GW timing and empirical constraints |
| F11 | symbolic identities/rational modules and source-equivalent tests | actual pinned local Agda 2.9 continuum kernel acceptance |
| D1 | prospective detector discrimination | source-characterized independent gravitational observation |

Local command \`bash scripts/check_ksw668_f8_maxcut.sh --smoke\` now executes **23 source-equivalent PASS** test cases (8 moving PDE, 5 original-t2 ray, 6 strict 5D null convex, 4 SMS). \`--full\` remains **exit 42** until its 3D compact TT and both Weyl numerical convergence gates are actually satisfied. These results are not Agda kernel receipts; CI remains out of acceptance.
