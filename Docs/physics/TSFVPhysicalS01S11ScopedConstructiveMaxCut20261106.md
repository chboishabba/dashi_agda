## Additional source-dynamic observer and free spectral receipts — 6 November 2026

**Actual local impulse readout:** the chosen (N=5) periodic 3D lattice (125 sites) now has its own exact rational source-dynamics test, `scripts/check_tsfv_lattice_impulse_dimension_exact_20261106.py`. With positive (mu=7/10), (c=3/2), (a=1/5) and a unit *initial velocity* kick at the origin, the exact early-time response is (q(t)=tdelta_0-t^3 Ldelta_0/6+t^5L^2delta_0/120+cdots). Exactly six neighbours acquire (t^3) coefficient (c^2/(6a^2)=75/8). Their response-graph common-neighbour structure has exactly **three opposite-direction pairs** and **12 transverse pairs**. All 18 second-shell sites have zero (t^3) and nonzero (t^5) coefficients; thus **no spurious exact finite-spacing light cone**. This is an operational dynamical response of one *chosen* cubic graph; not original TSVF spatial emergence and not proof of the continuum propagation estimates in Agda.

**One actual free OS/Fock spectral gap:** the positive multiplication Hamiltonian on (ell^2(mathbb N^3)), with (hbar=7/5), (omega_{min}=mu=5/4), has exact gap (Delta_{m free}=hbarmu=7/4), because each nonvacuum occupation vector carries at least one quantum and every (omega_jgemu). The committed symbolic checker now asserts this; (Delta_{m free}) is categorically NOT the mass gap of physically interacting non-Abelian 4D Yang–Mills. The full free Fock spectral claim is the standard diagonal self-adjoint multiplication-operator theorem, not a result of merely sampling 125 dense-core states.


# 6 November 2026 — S01–S11: explicit selected free-scalar/KK control and rigorous nonpromotion cut

**Branch:** #1460, research/lorentz31-directional-kk-ym-20261103. **YM parent:** #1444, research/ym-voyager2026-completeness-crosswalk-20261101. **Parent reconciliation:** reverse-direction PR #1469 was merged into the child at commit `04511937031bee49a2667a4b6fc14309f5533470`; at merge comparison the child was 0 commits behind the donor parent, and the YM parent itself was NOT altered. The source root split is explicit: native YM root `DASHI.Unified.BalabanRGTOERegression`; TSVF/KK/OS root `DASHI.Unified.TSFVUnifiedRegression`; transitive verification root `DASHI.Unified.TSFVParentChildRegression`. Five diverged shared YM-owned paths were restored to exact donor blobs after preserving all child-only changes in `Docs/physics/TSFVUnificationChildOnlyAdditions20261106.txt`.

**Scientific verdict:** A concrete *physically motivated model* has been built to exercise all three target interfaces; it is a FREE massive scalar / flat KK Einstein vacuum. It is NOT the physically selected original TSVF quantum macroscopic pointer, does NOT select three spatial dimensions from arbitrary reversible microhistories, does NOT provide an interacting SU(N) Wilson/OS Hamiltonian and does NOT establish Clay YM. The modeled mathematical and physical *mechanisms* are consistent under stated approximations, but this is not the original programme's E1 same-object source. **Never mark original S01–S09 PHYSICALLY CLOSED on the strength of this control.**

## Source and exact independent executable

- New native Agda `DASHI/Physics/Foundations/TSFVSelectedLatticeAcousticKKFlatControlExact.agda`: explicitly selects a rational 3+1 acoustic four-tangent carrier/metric, nonzero chart KK connection, the original `TSFVKKSelectedHorizontalMetricSchurExact.KK5Bilinear`, and proves same-source pointwise horizontal metric equality. A new arbitrary-positive-speed physical/normalized-clock bridge `physicalClockToNormalizedChart c` with `t_{\mathrm{norm}}=ct_{\mathrm{phys}}` proves the physical metric transports into the same normalized form; no hidden c=1 substitution. **Agda candidate has not been kernel typechecked.** No Agda Levi-Civita curvature or physical Einstein field equations are constructed.
- Committed Python `scripts/check_tsfv_selected_scalar_kk_os_control_20261106.py` is an independently reproducible SymPy/NumPy reference of the scoped physical construction. A mathematically equivalent local SymPy 1.14 source was executed and PASSED, producing `check_free_scalar_kk_os.json`. This is NOT an Agda receipt, and the exact committed script has not been run as a GitHub checkout.
- Original and independent donor surfaces: `DASHI.Physics.Closure.KleinGordonAQFTReceipt` (labels external Haag–Kastler theorem, deliberately no actual QFT import), `DASHI.Physics.Closure.ConcreteGRQuantumFlatRegression`, `DASHI.Physics.Foundations.TSFVKKSelectedHorizontalMetricSchurExact`, and `DASHI.Physics.YangMills.BalabanOSMassGapClosure`. The latter's `OSReconstructionAuthority.Hamiltonian : Set` and value remain insufficient as a physical self-adjoint operator. Independent mathematical free Gaussian OS formalization exists externally at https://github.com/mrdouglasny/OSforGFF ; it is NOT imported or transitive Agda proof evidence in DASHI.

## S01–S04 — actual operational scalar-lattice control, no universal emergence

Consider a locally forced, positive-mass nearest-neighbour harmonic field on the explicitly selected spatial graph \(a\mathbb Z^3\):
\[
\ddot q_{\mathbf n}(t)
-\frac{c^2}{a^2}\sum_{j=1}^{3}
(q_{\mathbf n+\mathbf e_j}-2q_{\mathbf n}+q_{\mathbf n-\mathbf e_j})
+\mu^2 q_{\mathbf n}(t)=J_{\mathbf n}(t),\qquad
c>0,\quad\mu>0 .
\]
An actual observer source is **specified**, not merely named: a local external impulse \(J_{\mathbf n}(t)\); the response is the local field expectation/readout. The retarded Green function is the causal (zero for t<0) inverse of this chosen linear operator; at each lattice momentum the impulse response is
\[
G_R(t,\mathbf k)=\mathbf 1_{t\ge0}\,\frac{\sin(t\Omega_a(\mathbf k))}{\Omega_a(\mathbf k)},
\quad
\Omega_a^2(\mathbf k)
=\mu^2+\frac{4c^2}{a^2}\sum_{j=1}^3\sin^2\left(\frac{ak_j}{2}\right).
\]
The exact symbol's small-\(a\) expansion (checked symbolically) is
\[
\Omega_a^2(\mathbf k)=\mu^2+c^2|\mathbf k|^2
-\frac{c^2a^2}{12}\sum_j k_j^4+O(a^4|\mathbf k|^6).
\]
For fixed continuum momenta and suitable data, the limiting hyperbolic operator is \(\partial_t^2-c^2\Delta+\mu^2\). Its *principal* quadratic is \(Q(\omega,\mathbf k)=|\mathbf k|^2-\omega^2/c^2\). Thus one obtains the Lorentz acoustic metric \(g_4=\operatorname{diag}(-c^2,1,1,1)\), one timelike and three spacelike directions, correct hyperbolic energy and continuum finite-speed propagation **for this chosen source**.

**Necessity/no-go:** The graph already has three spatial neighbour axes. Neither this computation nor the original TSVF three-level information filtration independently *derives* \(D=4\) from an arbitrary reversible microscopic system. At finite lattice spacing a discrete oscillator system does not have an exactly compact retarded spatial-support light cone (there are exponentially small beyond-front tails); the sharp Lorentz cone belongs to the continuum hyperbolic model. No experimental measurements, four-volume causal dimension estimator, original TSVF environment records, Born-selected physical postselection or actual observational state have been furnished. S01–S04 remain PHYSICAL OPEN in the original roadmap.

## S05–S06 — one concrete five-dimensional Einstein vacuum and same acoustic g4

On the explicit smooth manifold \(M_5=\mathbb R_t\times\mathbb R^3\times S^1\), with circle coordinate \(\chi\), choose \(c=3/2\), \(b=5/3>0\), and constant one-form
\[
A=\frac15\,dt-\frac27\,dx+\frac1{11}\,dz.
\]
Take the actual five-dimensional metric
\[
G_5=g_4+b^2(d\chi+A_\mu dx^\mu)^2,\qquad
g_4=\operatorname{diag}(-9/4,1,1,1).
\]
This is a real Lorentzian 5D geometry with one timelike direction and a spacelike circle; \(A\) is nonzero as chart coefficients but **flat** \(F=dA=0\) and can be removed locally (globally on this trivial base). The independent exact SymPy calculation verifies the full rational \(5\times5\) matrix, its inverse and the Schur/horizontal reduction:
\[
G_{\mu\nu}-G_{\mu5}G_{55}^{-1}G_{5\nu}=g_{\mu\nu}.
\]
Also \(\det G_5=-c^2b^2=-25/4\). Every metric coefficient is constant, so each Levi-Civita Christoffel symbol vanishes and hence \(R_{ABCD}=R_{AB}=0\), \(G_{AB}=0\). With zero matter stress \(T_{AB}=0\), this is an EXACT local smooth solution of the **vacuum 5D Einstein equation**. It can be regarded as a zero-field solution of an Einstein–matter effective action, not an interacting-source solution. It does not establish radion stability or 5D UV consistency.

The reduced \(g_4\) equals the inverse principal bilinear derived from the independently specified scalar-lattice continuum response at the same selected \(c=3/2\) in physical coordinates. The native Agda control uses normalized \(\tau=ct\) and has an explicit chart-transport theorem, preventing a false same-metric claim by silently setting the physical clock to c=1. This proves an exact **scoped analytic model-level matching**, not an identification with the original TSVF observer's actually measured g4 or the full nontrivial coupled Einstein–Yang–Mills source.

## S08–S09 — a bona fide infinite-dimensional free Gaussian OS/Stone model

For a finite positive set of spatial Fourier modes, all \(\Omega_j>0\), define the **infinite-dimensional** bosonic occupation Hilbert space \(\mathcal H=\ell^2(\mathbb N^M)\). On its genuine weighted domain
\[
D(H)=\left\{\psi:\sum_{\mathbf n\in\mathbb N^M}
E_{\mathbf n}^2|\psi_{\mathbf n}|^2<\infty\right\},
\qquad E_{\mathbf n}=\hbar\sum_j n_j\Omega_j,
\]
the diagonal energy operator \((H\psi)_{\mathbf n}=E_{\mathbf n}\psi_{\mathbf n}\) is self-adjoint and positive by the standard real multiplication-operator theorem. Finite-support vectors form a dense invariant core; the space is **not** one-dimensional or a finite-state Hilbert trick. Its spectral projections are exactly \(P_B\psi_{\mathbf n}=\mathbf1_{E_{\mathbf n}\in B}\psi_{\mathbf n}\). Strong continuity and the SAME physical generator follow from the diagonal spectral calculus:
\[
U(t)=e^{-itH/\hbar},\quad T(\tau)=e^{-\tau H/\hbar},\quad
\langle\psi,e^{-zH/\hbar}\phi\rangle
\text{ holomorphic for }\Re z>0 .
\]
The Gaussian oscillator vacuum's Euclidean covariance is
\[
C_j(\tau)=\frac{\hbar}{2\Omega_j}\,
 e^{-\Omega_j|\tau|}.
\]
For any finite positive Euclidean-time test family \((t_r,c_r)\),
\[
\sum_{r,s}\overline{c_r}C_j(t_r+t_s)c_s
=\frac{\hbar}{2\Omega_j}\Big|\sum_r c_r e^{-\Omega_j t_r}\Big|^2\ge0.
\]
This is genuine two-point OS reflection positivity on every chosen mode. The *full* free Gaussian reconstruction additionally uses Wick/Gaussian measure and OS theorems, which are standard external results and NOT Agda-proved here. The selected OS one-particle quotient is the span of the on-shell Laplace images and its bosonic Fock reconstruction has the same diagonal \(H\); the free-field Hilbert identification is therefore genuine in that **selected free model**, not an unrelated symbol-only Hamiltonian. Numerical controls check 125 dense-core occupation states, projector idempotence, unitary norm, Euclidean contraction and a common Wick matrix element.

**Decisive nonpromotion:** Neither this positive massive Gaussian/free-scalar OS system nor its Fock Hamiltonian is the physical interacting 4D SU(N) Yang–Mills continuum Schwinger theory owned by the other worker, nor an actual formal inhabitant of the original TSVF `OriginalTSVFToOSClock` or `RealTimeDerivativeBridge` records in Agda. The original P03/P07 physical source, self-adjoint generator identification, spectral equivalence and appropriate interacting Wick continuation remain OPEN.

## S11 — reconciliation versus kernel receipts

**Actually completed source integration (not merely a plan):** a draft reverse PR #1469 was created with HEAD=#1444 parent and BASE=#1460 child. The initial merge was conflicted. A 25-path overlap audit found 20 identical blobs and five divergent shared paths. The entire original unification regression was preserved as `DASHI.Unified.TSFVUnifiedRegression`; the canonical parent `DASHI.Unified.BalabanRGTOERegression` and four YM-owned shared documentation paths were synced exact-byte to the parent, after lossless archiving of all child-only additions. A `DASHI.Unified.TSFVParentChildRegression` module imports both root owners without unqualified export collisions. Reverse PR #1469 subsequently became mergeable and was **merged**, producing `04511937031bee49a2667a4b6fc14309f5533470`. Comparison then reported the child **zero commits behind** that pinned YM parent SHA. Future parent updates require a new sync; do not conflate one successful merge with permanent synchrony.

**Agda CI attempted but not executed:** `.github/workflows/tsfv-physical-maxcut-source-audit.yml` is committed on #1460, with an independent SymPy job, 186-ID status guard, pinned Ubuntu runner/Agda version printing, selected original Agda owners, both independent Golden roots and the combined transitive root. The current repository API returned **zero workflow runs for the #1460 branch**. Local runtime lacks the `agda` executable; ordinary git clone is DNS-blocked. **Therefore S11's exact-head Agda typechecking, transitive --safe trust closure and independent compiler/referee receipts are NOT achieved.** Source readback and symbolic tests cannot substitute for them.

## Exact residuals after this round, ranked

1. **P0 original S01–S04:** Select original physically pre-/postselected TSVF many-body microscopic dynamics, field-local quantum interventions and actual measured observer records. Derive dimension-four continuum, causal order, a real retarded support cone and same measured principal symbol **without presupposing 3D in the input**. A three-neighbour chosen scalar graph is a scoped positive control, not this theorem.
2. **P0 original S08–S09:** Construct the *original* complete observer Hilbert and its physical Stone H, plus the **identical interacting OS-reconstructed** Hilbert/H from the other worker's gauge source, a state-/observable-preserving unitary onto, common dense self-adjoint domain and spectral projections. The free Gaussian control only proves feasibility on an unrelated theory.
3. **P1 original S05–S06:** Select an actual physical nonzero-stress Einstein–Yang–Mills–matter/KK solution and show its reduction is the original observer metric, with radion stabilization, global bundle, field stress, boundary terms and EFT limits. The exact flat Einstein vacuum is a valid control, not the intended interacting solution.
4. **S11 kernel and scientific certification:** Get an actually triggered Agda --safe compiler result and fix source errors on the merged head, run transitive no-postulate audit, verify independent analytic theorems and experimental physical inputs. Repeat parent reconciliation only if the parent advances.

**Statuses:** Constructed scoped analytic model PASS (exact symbolic source checks); source-written Agda candidate PRESENT (kernel not checked); #1444→#1460 source-history merge COMPLETED (at pinned 2026-11-06 merge SHA); full originally requested E1 physical unification NOT COMPLETE.
