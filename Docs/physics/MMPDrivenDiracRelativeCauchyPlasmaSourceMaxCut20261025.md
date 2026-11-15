# Charged Wilson–Dirac relative Cauchy evolution: max-cut 2026-10-25

**Implementation owner** draft `dashi_agda` PR #1248. **This deliverable is a finite, unitary, free-fermion in-in response**, not a constructed globally Hadamard charged four-dimensional quantum state, exact MMP wormhole, Maxwell–MHD plasma device or Einstein–Maxwell solution. The date supersedes earlier state-fixed-only Wilson/Hadamard PR notes.

## Source roots and attribution boundaries

- **Ko Sanders**, *The locally covariant Dirac field*, arXiv:[0911.1304](https://arxiv.org/abs/0911.1304) (2009; published mathematical physics work): original covariant CAR field construction, Hadamard scope, Dirac relative-Cauchy evolution and the stress commutator. Source theorem, **not** a DASHI-discovered physical mechanism.
- **Jochen Zahn**, *The renormalized locally covariant Dirac field*, arXiv:[1210.4031](https://arxiv.org/abs/1210.4031), *Reviews in Mathematical Physics* 26 (2014) 1330012, DOI [10.1142/S0129055X13300124](https://doi.org/10.1142/S0129055X13300124): locally covariant charged fields, renormalized Ward-compatible current and stress, finite renormalization ambiguity.
- **Jochen Zahn**, *Locally covariant charged fields and background independence*, *Reviews in Mathematical Physics* 27 (2015) 1550017, DOI [10.1142/S0129055X15500178](https://doi.org/10.1142/S0129055X15500178): perturbative background agreement in the charged Dirac setting, **most direct new source for actual changing A/g weld**.
- **Felix Finster, Simone Murro, Christian Röken**, *The Fermionic Projector in a Time-Dependent External Potential: Mass Oscillation Property and Hadamard States*, arXiv:[1501.05522](https://arxiv.org/abs/1501.05522) (2015): nonperturbative pure quasifree Dirac Hadamard construction under specified Minkowski time-decaying potential/norm assumptions; not a theorem that every electromagnetic pulse on our curved handle yields a supporting state.
- **Christopher J. Fewster, Alexander Schenkel**, *Locally Covariant Quantum Field Theory with External Sources*, arXiv:[1402.2436](https://arxiv.org/abs/1402.2436) (2014, journal 2015): relative-Cauchy/source algebra for **affine inhomogeneous Klein–Gordon**, separate lineage; cannot silently credit as a charged Dirac theorem.
- **Kenneth G. Wilson** (1974) lattice holonomy conceptual root. Existing `DASHI/Physics/YangMills/CompactLieLatticeGauge.agda` proves exact `holonomyGaugeCovariant` and gauge-invariant closed class-function Wilson loops; `BalabanGaugeTransformationCovariance.agda` proves periodic lattice covariance. They are genuine in-repo finite path theorems.
- **Radzikowski (1996), Sahlmann–Verch (2001), Gérard–Stoskopf (2022), Capoferri–Murro (2025)** own the distinct curved 4D microlocal/Hadamard and Cauchy-source constructions. Their hypotheses, curved spin connections and all required singular WF properties are NOT supplied by a finite Wilson–Dirac matrix.

Existing PR #1248 modules `MMPWilsonHadamardSameBackgroundBidiExact.agda`, `MMPDiracCauchyNoncompactCompactDoubleBidiExact.agda`, and `CasimirResidualCauchyToLimitExact.agda` remain the **same-background / finite-local-time / conditional Cauchy limit** owners. This new tranche addresses only their next dynamic source comparison, at finite size.

## Mathematical result 1 — exactly sourced finite U1 relative transport

On an N=9 circle with a two-component charged spinor at each site let
```
H[A,V](t) = ∑j ψj†[mj σz+Vj(t)]ψj
          + ∑j {ψj† exp(i Aj(t)) B ψ(j+1) + h.c.}
B=−0.31(0.55 σz+i σx).
```
The real inhomogeneous m_j are smooth sampled bounded coefficients and are not a 4D spin connection.

For `G(t)=diag_j(exp(i χ_j(t)) I2)`:
```
A'_j = A_j + χ_j − χ_(j+1),  V'_j=V_j−∂tχ_j
H'[t] = G(t)H[t]G(t)† + i(∂t G(t))G(t)†
U'(T,0)=G(T)U(T,0)G(0)† .
```
Omitting the **scalar V correction** for a time-dependent gauge transformation is wrong. The closed spatial Wilson loop `exp(i∑_j A_j)` is gauge-invariant but is not sufficient to specify the local time-dependent electric fields.

For `U_0` undriven and `U_1` driven, `R=U_0† U_1` is unitary and transforms `R'=G(0)R G(0)†` under a common time-dependent gauge change. The new Agda `DASHI/Physics/QFT/MMPDrivenRelativeWilsonCauchyExact.agda` specializes the pre-existing endpoint-indexed `CompactLieLatticeGauge` theorem to a **driven-forward/reference-backward closed contour**. It proves (conditional on supplied group laws and time-step elements) relative holonomy factorization, undriven identity, gauge conjugation, and class-function gauge invariance. It does NOT construct the time-evolution operator, spin-c Dirac bisolution or charged Hadamard state. Agda kernel status unverified.

## Mathematical result 2 — one finite CAR state, causal in-in linear response

Take `P0=1_{H0<0}` with 9 occupied negative-energy modes and a positive one-particle gap 0.4869856269 in this finite model. Then `P_ε(T)=U_ε(T,0)P0U_ε(T,0)†` remains a positive CAR projector, retains total charge, and obeys
```
∂t P=-i[H[A,V](t),P].
∂t n_j+J_(j,j+1)-J_(j−1,j)=0.
J_(j,j+1)=−2 Im tr(H_(j,j+1) P_(j+1,j)).
```
No continuum/renormalized 4D Ward theorem is claimed.

For `A_j(t)=ε f(t) s_j`, `f(t)=sin²(πt/T)` supported on `[0,T]`, define `X_s=∂_εH|_{ε=0}` at unit envelope. The ground-state retarded response at final T is
```
dP_ε(T)/dε |_(ε=0)
 =−i∫_0^T f(t)U0(T−t)[X_s,P0]U0(T−t)† dt .
```
This is the finite Duhamel/Dyson/Kubo identity. It is a **source-consistent response with a fixed reference CAR state**, rather than naively subtracting two incompatible continuous background Hadamard parametrices. Its 4D charged in-in analogue requires correct Møller transport, local renormalization and potentially gauge/diffeomorphism anomalies and physical source equations.

## Mathematical result 3 — positive work/passivity and a more discriminating C3 negative control

The external pulse vanishes at endpoints. Therefore `H(T)=H(0)=H0`. For the occupied negative-energy projector:
```
ΔE=Tr(H0(P(T)−P0)) = ∫_0^T Tr(P(t)∂t H(t))dt >= gap * L_ph >= 0
L_ph = ∑_(a<0,b>0)|<b|U(T)|a>|².
```
This finite-dimensional spectral gap inequality and work identity are **not** statements about 4D ANEC or wormhole-supporting negative stress. They show that driven local response in this ground-state toy consumes nonnegative external work.

Three separately positioned smooth normalized bond profiles centered on sites (1,4,7) are combined into:
- balanced amplitudes (1, −0.58, −0.42), `∑s_j=0`, so no net circular Wilson-phase change at any time; nevertheless `P(T)≠P0`, local particle-density response is nonzero and positive work is injected;
- unbalanced amplitudes (1, 0.6, −0.2), `∑s_j=1.4`, with phase peak 0.28 radians for drive ε=.2, also with nonzero particle and work response.
These are **prescribed classical electromagnetic link potentials**, not physically self-consistent three Maxwell–MHD plasma balls with separately evolved charges, velocities and boundary conditions.

### Executed local expanded fixture results

`/mnt/data/mmp_rce_maxcut/check_mmp_dirac_relative_cauchy_driven_20261025.py` ran in the Python container (NumPy/SciPy) and passed.

| Check (9 sites × 2 spin components, T=3) | Balanced drive | Unbalanced drive |
|---|---:|---:|
| Spatial closed Wilson phase at pulse peak | ~0 | 0.280000 |
| Norm of relative final propagator minus identity | 0.133142 | 0.128432 |
| Norm of final local occupation change | 0.0266292 | 0.0266430 |
| Total U1 charge deviation | ~6.03e−14 | ~6.23e−14 |
| Local continuity equation error | ~2.43e−17 | ~1.99e−17 |
| Finite CAR projector error | ~3.68e−14 | ~3.43e−14 |
| Gauge-related direct time-evolution error, 180 steps | 1.8232e−5 | 1.8263e−5 |
| Kubo central-difference error, 180 steps | 1.9751e−5 | 1.9007e−5 |
| Final ground-state energy gain | 0.00740769 | 0.00677142 |
| Integrated source work minus gain | 3.76e−7 | 3.44e−7 |
| Spectral-gap lower bound on energy | 0.00416520 | 0.00384437 |

Step-refinement for the BALANCED drive (90/180/360 steps): gauge errors `7.29381e−5/1.82316e−5/4.55773e−6`, and retarded response errors `7.87212e−5/1.97512e−5/5.00829e−6`. These converge approximately quadratically, so the residual is from the midpoint numerical integration rather than a physically broken U1 gauge identity.

**More interesting physical discriminator:** the balanced waveforms are an adversarial counterexample to `δθ_Wilson=0 => δ<J>=0`. The **spatial magnetic holonomy** stays trivial, while localized time-dependent bond electric fields still drive charge redistribution. The earlier static circle Bernoulli `B2(α)` cannot capture this dynamical response by itself.

The committed GitHub self-contained smoke checker `scripts/check_mmp_dirac_relative_cauchy_driven_20261025.py` is source-written. Its expanded local equivalent passed, but **we do not claim the exact GitHub text executed locally** until a retrieved-file/CI receipt is produced. The full expanded local test adds integrated source work, occupied-to-empty excitation lower bound and midpoint refinement. This is a bounded mathematical implementation, not a 4D renormalized physical proof.

## Highest-value outstanding physics/analysis and exact acceptance

1. Construct ONE noncompact, one-universe magnetic handle `(M,g,L,A,s)` with actual compactly supported gauge/metric deformations; import global spinorial Hadamard existence and build a PHYSICALLY SELECTED charged quasi-free CAR state `ω[g,A]`, not just any admissible state.
2. On a real curved charged spin-c operator, construct retarded/advanced Møller maps and relative Cauchy evolution between **different** gauge/metric backgrounds with globally consistent initial data, gauge covariance and causal support. Attach the existing Wilson path transport theorem, not a new parallel gauge algebra.
3. Compute `δ<J^μ>_ren`, `δ<T_{μν}>_ren` from correct Hadamard subtraction on each background and prove the sourced Ward identities and renormalization-scheme matching, using Sanders 2010 / Zahn 2014/2015 and covariant microlocal references at their stated scopes. A finite CAR commutator is not proof of continuum microlocal spectral condition.
4. Solve the **same state** Maxwell field equation `dF=0, d*F=*J_total` and Einstein semiclassical equation with prescribed boundary/return-path physics; prove no horizon/illegal shell, renormalization control, stability and incoming probe consistency.
5. Make all three plasma regions genuinely dynamic Maxwell–MHD materials and attach input/output LLL modes and environmental Fock loss to the SAME physical response. Compare zero drive, pure time-dependent gauge, balanced local drive, nonbalanced Wilson drive, and independent ordinary EM pickup. Do not reclassify mathematical wormhole theory as an observed antigravity or faster-than-light device.

**Source-originality ledger:** Sanders, Zahn, Finster–Murro–Röken, Wilson and the microlocal/Hadamard/Cauchy authors own the published physics/math; the finite lattice source/Agda path adapter is a DASHI bounded implementation. Existing Boltzmann/finite CAR/Cauchy/majorana/Hadamard matrix papers remain separately typed. Original source existence ≠ physical device ≠ Agda kernel receipt ≠ numerical confirmation of Einstein equations.


## Second independent-source cut: three separately timed pulses and causal ports

The first numerical fixture used three separate spatial localized profiles but one shared envelope. To avoid counting spatial separation as independently dynamic source timing, this follow-on uses **three individually specified pulse supports**:
```
source 1: t ∈ (0.20,1.18)
source 2: t ∈ (1.04,2.12)
source 3: t ∈ (2.28,3.04)
```
with `f_i(t)=sin²(π(t−a_i)/(b_i−a_i))` within its support, zero elsewhere, and independent amplitudes ε_i. The source is an imposed external lattice gauge potential `A_j(t)=∑ ε_i f_i(t) g_(i,j)` with three spatial Gaussian bond profiles centered at j=1,4,7; **it is not yet self-consistent Maxwell–MHD**.

The causal 9×3 density response `χ_(j,i)(tobs)=∂_(ε_i)Tr(n_j P(tobs))|_(ε=0)` is obtained **twice**, by physical finite unitary evolution and the retarded Duhamel/Kubo commutator on the SAME initial CAR ground projector. Three selected detector sites 1,4,7 form a useful 3×3 port submatrix. Local expanded script `/mnt/data/mmp_rce_maxcut/check_mmp_three_independent_retarded_sources_20261025.py` executed PASS.

| Independent source | Response norm at observation t=1.7 | Response norm at t=3.2 | Early/late maximal finite-diff residual |
|---|---:|---:|---:|
| 1, early | 0.0348686161 | 0.0296211069 | <8×10^-7 |
| 2, middle | 0.0656515824 | 0.0795465123 | <1.2×10^-6 |
| 3, late | **0 exactly** | 0.0317380383 | <5×10^-7 |

The late source's support begins at 2.28, so no external disturbance at 1.7 can be attributed to it: this is an exact **retarded time-order negative control** in the selected finite model. It is NOT a proof of a continuum 4D microcausal light cone or propagation velocity. Combined independent amplitudes (0.18,−0.14,0.11) give final energy gain `0.002744940709`, total charge error `3.87e−14`, final local density-change norm `0.0130482758` and observed nontrivial instantaneous Wilson angle magnitude `0.139526685` over selected times.

**Committed self-contained companion source:** [`scripts/check_mmp_three_independent_retarded_source_ports_20261025.py`](https://github.com/chboishabba/dashi_agda/blob/research/mmp-s2-fermion-three-plasma-maxcut-20261024/scripts/check_mmp_three_independent_retarded_source_ports_20261025.py). The local expanded run PASSED; the exact committed smoke checker has not been independently executed as GitHub CI. It leaves the true materials source, 4D microcausal CAR Dirac response, local renormalization, Ward identities and backreaction **OPEN**.

**Key promotion distinction:** source 3's exactly zero *earlier-time* response derives from temporal support, while a balanced *total Wilson phase* can still support nonzero local response. These are different negative controls and should both be retained in future physical Maxwell–MHD experiments.


### Actual cross-port Jacobian, not just norm summaries

Selected rows are local density readouts at sites `j=1,4,7`, columns are independent source envelopes `i=1,2,3`. At observation **t=1.7**, finite model susceptibility:
```
         source1       source2       source3 (future)
site 1   +0.023412441  -0.000001735   0
site 4   +0.001229863  -0.044602278   0
site 7   -0.000057859  +0.000129596   0
```
At **t=3.2**:
```
         source1       source2       source3
site 1   -0.018955382  -0.000294773  +0.000288721
site 4   +0.001261704  +0.055991796  -0.000010926
site 7   -0.000519738  +0.002728978  -0.021250543
```
These are derivatives of final expected lattice occupations with respect to independently chosen **source amplitudes at zero drive**, not measured fermion transport probabilities. Spatial cross-coupling and later nonzero entries should be used to reject a false three-independent-scalar-channel simplification. The full 9×3 response and both time slices are in the executed local JSON; all 9 density derivatives sum to zero columnwise by finite U1 conservation.
