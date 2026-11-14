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
