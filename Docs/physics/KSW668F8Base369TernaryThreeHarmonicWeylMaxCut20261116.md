# KSW668 F8 maximum-cut X — Base369 unbalanced-ternary indexing of the original 0/2/4 TT harmonic source and BOTH Weyl readouts

**Date:** 16 November 2026. **Owner:** existing KSW PR #1520 following merged #1512. **Origin:** user proposal \(0,2,4\mapsto2[0,1,2]\) and request to reuse the native DASHI unbalanced ternary as a 369-relevant physical source consumer. This report tests the *same original object*: moving \(a(t)=t\) Poincaré AdS₅ tensor \(\ell=0,2,4\) compact source and actual original F8 \(H_{yy}\), intrinsic \(E^{(4)}_{yy}\) and projected \(E^{(5)}_{yy}\). **No new gravitational detection, C3 physical symmetry, 3/6/9 effective dimensions, or solved FIO theorem is claimed.**

## Prior art was reused; no new ternary foundations invented

- \`Base369.agda\` already defines \`TriTruth = tri-low | tri-mid | tri-high\`, \`tri-index = 0|1|2\`, and \`rotateTri\` as the **three-label permutation**. Existing \`DASHI/Algebra/TritTriTruthBridge.agda\` preserves the distinction between signed balanced trits and the unsigned \`Base369.TriTruth\` rank chart.
- \`DASHI/Interop/SensibLawWikidataBalancedTernaryAdmissibilityHyperfabricExact.agda\` separately documents the conventional 0,1,2 unsigned ternary digits; do NOT import its Wikibase truth meaning or proof maturity into this physical harmonic index.
- \`DASHI/Physics/Gravity/KSW668AdS5TTMultipoleAngularRationalExact.agda\` already proves the ORIGINAL spin-2 source polynomial decomposition with the exact Legendre weights and radial 3/7/11 identities.
- \`DASHI/Foundations/Base369Ternary27HypervoxelFabricGeometryExact.agda\` is a **different** 27-site 3×3×3 geometry; the original F8 spectrum has THREE modes, not 27 sites or an intrinsic spatial Cube27 action.
- The new \`DASHI/Physics/Gravity/KSW668AdS5TTUnbalancedTernary369ConsumerExact.agda\` is a consumer that imports the original TT owner and \`Base369\`, proves a two-way codec to the three *even harmonic labels*, and records a **physical C3 no-intertwiner** on the radial operator. Imported into \`KSW668BraneBulkMaxCutEverything.agda\`, \`JInvariantBase369CrossPollinationEverything.agda\`, \`EverythingTOESymmetryResolved369.agda\` and \`Unifier.agda\`. These imports only expose exact finite maths; they do not create a Monster/j-invariant/TOE physics identification.

## Exact mathematical map

For the selected axial \(H_{yy}\) fourth-order local TT source with \(Q=\mathrm{diag}(0,1,-1)\), \(\mu=k_x/|\mathbf k|\), the *source-specific* angular factor is
\[
\boxed{
\frac{\mu^4+6\mu^2+1}{8}
=\frac25P_0(\mu)+\frac47P_2(\mu)+\frac1{35}P_4(\mu).}
\]
No odd or \(\ell>4\) angular harmonic occurs in **this exact polynomial**, not a theorem about every tensor polarization or every source.

Define native unsigned Base369 trit rank \(q\in\{0,1,2\}\). Its physical harmonic and radial effective dimension are:
\[
\boxed{q\leftrightarrow\ell=2q,\quad
d_{\mathrm{eff}}=3+2\ell=3+4q.}
\]

| \`Base369.TriTruth\` | unsigned \(q\) | original even \(\ell\) | exact Legendre weight | effective radial \(d\) |
|---|---:|---:|---:|---:|
| \`tri-low\` | 0 | 0 | 2/5 | 3 |
| \`tri-mid\` | 1 | 2 | 4/7 | 7 |
| \`tri-high\` | 2 | 4 | 1/35 | 11 |

These are **three independent arbitrary real/complex radial functions**, not three possible values of a single trit. The encoding changes only indexing/ownership, not physical resolution or the number of required amplitudes. Writing \(H_\ell=(r/\epsilon)^\ell V_\ell\), the original physical 3D angular Laplacian becomes the effective-dimensional radial operator \(V_\ell''+(2\ell+2)V_\ell'/r\). At the physical receiver axis, \(P_\ell(1)=1\), so
\[
\boxed{H_{yy}=\sum_{q=0}^2 (r/\epsilon)^{2q}V_{2q}.}
\]
The equivalent original source cell moments/TT weights and finite-volume origin are unchanged.

## 369 root-of-unity test — exact invertible presentation, negative physical symmetry

The three-label \`Base369.rotateTri\` acts \(q\mapsto q+1\bmod3\). On the actual three-channel radial differential operator \(\mathrm{diag}(L_3,L_7,L_{11})\), this permutation does **NOT** commute with evolution. The most direct discriminant is the exact FV first-cell identity
\[
L_d(r^2)=2d
\quad\Rightarrow\quad[6,14,22].
\]
Cycling a lowest-channel \(r^2\) profile to the next channel changes the required evolution \(6\to14\), a discrepancy of **8**. The new Agda source proves ground Nat non-equality after cycling \`tri-low\`; the source-equivalent Python owner tests this exact same-object radial witness.

A \(3\)-point cyclotomic transform **is** an invertible change of basis: for \(\omega^3=1,\ 1+\omega+\omega^2=0\), let \(F_{jk}=\omega^{jk}\), \(F^{-1}=F^\dagger/3\). But under that change of basis, even the coefficient matrix for the radial dimensions becomes
\[
F\,\operatorname{diag}(3,7,11)\,F^{-1}
=\begin{pmatrix}
7 & -2+\frac{2i\sqrt3}{3} & -2-\frac{2i\sqrt3}{3}\\
-2-\frac{2i\sqrt3}{3} &7&-2+\frac{2i\sqrt3}{3}\\
-2+\frac{2i\sqrt3}{3}&-2-\frac{2i\sqrt3}{3}&7
\end{pmatrix}.
\]
The off-diagonal entries are nonzero. Therefore the root-of-unity code **does not diagonalize away the genuine different physical radial PDEs**, and no actual C3/Monster/TOE geometric action follows from the ordinal chart. This is the desired fail-closed 369 consumer distinction.

## Actual original tensor and BOTH Weyl observation consumer

The existing \`scripts/ksw668_f8_tt_multipole.py\` \`read_all\` is now extended to retain **per-channel** receiver and beyond-cone observables, all with the *same original readout equations*:
\[
\begin{aligned}
H_q&=(r/\epsilon)^{2q}V_{2q},\\
E^{(4)}_q&=-\frac{H_{\eta\eta,q}+\partial_x^2H_q}{4t^2},\\
E^{(5)}_q&=-\frac{H_{\eta\eta,q}+2H_{\eta,q}-\Delta_3H_q}{2t^2}.
\end{aligned}
\]
Because these original readout maps are linear, their aggregate identities are **exact** at the same finite grid:
\[
H=\sum_qH_q,\qquad E^{(4)}=\sum_qE^{(4)}_q,\qquad E^{(5)}=\sum_qE^{(5)}_q.
\]
New runtime checks reject inconsistent sums. The source-specific \`normal_order=3\` original compact three-dimensional TT, receiver \(t=12\), \(\epsilon=.04\), Poincaré pulse .065, exact physical photon-dark margin and far bulk-null control pass **13** new actual PDE/receiver tests. This is a **linear decomposition theorem at the tested finite grid**, not numerical convergence, continuum Neumann-to-Weyl or physical detection.

## Maximum-cut discriminator: actual two-grid signed channel errors

On the same original physically constraint-preserving \`normal_order=3\` solver, compare the coarse \((\Delta r,\Delta y,\Delta T)=(.012,.016,.0025)\) and medium \((.008,.012,.0018)\) original \(t=12\) runs. The following are **signed coarse-to-medium changes** in identical observable normalization:

| Original harmonic | \(\Delta H_{yy}\) | \(\Delta E^{(4)}_{yy}\) | \(\Delta E^{(5)}_{yy}\) |
|---|---:|---:|---:|
| \(\ell=0\) | \(+5.604\times10^{-6}\) | \(+7.232\times10^{-5}\) | \(+2.969\times10^{-6}\) |
| \(\ell=2\) | \(-6.558\times10^{-6}\) | \(-3.214\times10^{-5}\) | \(-2.290\times10^{-6}\) |
| \(\ell=4\) | \(-1.219\times10^{-7}\) | \(-9.156\times10^{-7}\) | \(-7.485\times10^{-8}\) |

The aggregate differences are \(-1.077\times10^{-6},+3.926\times10^{-5},+6.041\times10^{-7}\) respectively. These aggregates **hide substantially larger opposing channel changes**. The exact observed finite difference triangle cut gives
\[
\boxed{
|\Delta O_{\mathrm{total}}|\le\sum_{q=0}^2|\Delta O_q|,
\qquad O\in\{H,E^{(4)},E^{(5)}\}.}
\]
Ratios \(\sum|\Delta O_q|/|\sum\Delta O_q|\): **11.41** for tensor field, **2.684** for intrinsic Weyl, **8.829** for projected Weyl. This proves why any aggregate-only grid drift can dramatically understate modal uncertainty due to cancellation. The two strongest nonconvergent contributions are \(\ell=0\) and \(\ell=2\), **not simply \(\ell=4\)** despite its 11D radial stiffness.

Machine receipt: \`Artifacts/ksw668/ads5_f8_base369_three_harmonic_signed_weyl_maxcut_x_20261116.json\`. Reproducer \`scripts/ksw668_f8_ternary_channel_drift.py --reproduce\` writes its detailed full two-grid signed per-mode receipt and exits **42** deliberately. It is NOT a certified convergence rate, higher-order derivative error, causal leakage bound, or observed gravitational signal.

## Verification and highest-value remaining work

New source-equivalent cases **40/40 PASS**: 20 algebra/source/369 codec and C3 no-go; 13 actual original \(t=12\) H/E4/E5 receiver and far-null readout; 7 signed per-channel error acceptance tests. A reconstructed combined earlier F8 replay plus these new suites passed **359/359 local tests**. The exact connected GitHub PR-head full acceptance and pinned Agda 2.9 kernel were **NOT RUN**; source-written Agda lemmas are not kernel certificates.

The **exact next numerical/analytic maximum cut** is now a **per-channel error budget** \(\delta H_q,\delta E^{(4)}_q,\delta E^{(5)}_q\) with independently refined radial/normal/time meshes, source-to-boundary \(\mathcal H^{4+\epsilon}\) regularity and true weak Israel compatibility. Validate the \(\ell=0\) and \(\ell=2\) time derivative and second-derivative stencils first, then apply the triangle sum, rather than overindexing on the \(\ell=4\) d11 CFL alone.

| Exact remaining endpoint | Status |
|---|---|
| \`ads5OriginalTTBase369UnsignedTernaryEvenHarmonicCodec\` | **Finite algebra CLOSED**, Agda source written kernel open |
| \`ads5OriginalTTThreeModeWeylReceiverLinearity\` | **Actual finite-grid algebra CLOSED**, all new tests pass, continuum error open |
| \`ads5OriginalTTC3LabelRotationIsPhysicalEvolutionSymmetry\` | **REFUTED** — exact radial \(\ell=0\to2\), \(6\to14\) witness |
| \`ads5OriginalTTPerChannelThreeObservableConvergence\` | **OPEN/FAILED numerically** — signed per-channel two-grid drift and far leakage |
| Original weak SAT global physical characteristic constraint | **OPEN**, exact boundary \(1/\Delta y\) negative control retained |
| Full coupled moving SSPRK3 stability and source lift/trace | **OPEN** |
| Original \(t=2\) prescribed compact Neumann-to-both-Weyl FIO theorem application | **OPEN independent mathematical acceptance** |
| F9 source-generating matter action and backreaction/cylinder; F10 scale/detection; F11 pinned kernel and observer semantics; D1 independent experiment | **OPEN** |

The user-suggested ternary bridge is now an actual **same-physical-object consumer** imported into the authoritative gravity and 369/TOE graphs, with a concrete signed-Weyl numerical discriminator and an explicit physical non-equivariance proof.
