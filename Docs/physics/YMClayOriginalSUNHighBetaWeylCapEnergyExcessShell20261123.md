# YM P0 — original SU(N) weak-coupling Haar-cap and connected local-energy-excess animals

**23 November 2026.** Original four-dimensional periodic Wilson \(\mathrm{SU}(N)\), any **fixed** integer \(N\ge2\), native positive link carrier on \((\mathbb Z/L\mathbb Z)^4\), \(L\ge3\), changing finite volumes and bare \(\beta\ge16\). No finite subgroup replaces Haar. Uses original existing group/Haar/Gibbs sources \`YMClaySUNMatrixWilsonTraceGaugeExact\`, \`YMClaySUNVariablePeriodicProductHaarExact\`, \`YMClaySUNVariablePeriodicGibbsGaugeExact\`, original native six-plane action/F19, and **the already-proved original 8/12 transverse link colouring and 196 rooted animal enumeration** \`YMClayOriginalWilsonPeriodicConflictColoring12R44520261121.md\` and \`YMClayOriginalWilsonCoherentConnectedPolymerPacking20261109.md\`. Earlier \`YMClaySU2OriginalWilsonUniformPlaquetteDeficit20261109.md\` owns the sharper SU2-only pressure argument. No new Agda operator/KP/RG/large-field record.

## 1. Explicit continuous SU(N) Haar identity-cap mass — source-level analytic proof

Write \(t(U)=\operatorname{ReTr}(U)/N\in[-1,1]\) and \(d(U)=1-t(U)\). The exact matrix identity for EVERY unitary \(U\) is

\[
\|I-U\|_{\mathrm F}^{2}=\operatorname{Tr}[(I-U)^*(I-U)]=2N\,d(U).
\]

Let \(0<\delta\le1/4\) and \(A_\delta\subset\mathrm{SU}(N)\) be the **conjugation-invariant** event that every eigenvalue is \(e^{i\theta_j}\) with a chosen determinant-one set of eigenangles \(|\theta_j|\le\delta\). Its true continuous normalized Haar measure satisfies

\[
\boxed{H_N(A_\delta)\ \ge\ \delta^{N^2-1}/K_N,\qquad
K_N=N!(128N^2)^{N-1}(16N)^{N(N-1)}.}
\]

Proof, explicitly tracking the Weyl constant. On the \((N-1)\)-dimensional SU(N) maximal torus write \(\theta_N=-\sum_{j<N}\theta_j\); the normalized Weyl measure of any conjugation-invariant event is
\[
\frac1{N!(2\pi)^{N-1}}\prod_{j=1}^{N-1}d\theta_j
\prod_{i<j}|e^{i\theta_i}-e^{i\theta_j}|^2.
\]
The Weyl constant-term identity is \(N!\), checked independently in the executable for \(2\le N\le6\). Select \(\theta_j=c_j+\xi_j\), \(j<N\), where \(c_j=(j-(N+1)/2)\delta/(4N)\) and \(|\xi_j|\le\epsilon=\delta/(32N^2)\), and set \(\theta_N=-\sum_{j<N}\theta_j\). Since \(\sum_jc_j=0\), all \(N\) eigenangles lie within the \(\delta\)-cap, and \(|\theta_i-\theta_j|\ge\delta/(8N)\) for all \(i\ne j\). Thus the squared Vandermonde is at least \((\delta/(16N))^{N(N-1)}\) by \(|e^{ix}-e^{iy}|\ge|x-y|/2\) on these small angles. Integrate over the \((N-1)\)-box of volume \((\delta/(16N^2))^{N-1}\), use \(2\pi\le8\), and obtain the displayed exact \(K_N\). This invokes ordinary SU(N) Weyl–Haar integration, not a newly postulated measure.

For a product of four arbitrary **noncommuting** cap matrices \(U_1U_2U_3^{-1}U_4^{-1}\), unitary invariance of the Frobenius norm and its product telescoping yield
\[
\|I-P\|_{\rm F}\le4\sqrt N\,\delta,\quad
d(P)=\frac{\|I-P\|_{\rm F}^2}{2N}\le8\delta^2.
\]
No commutativity, gauge fixing, action factorization or coarse Wilson replacement is needed.

## 2. True original Wilson Gibbs pressure and plaquette deficit, uniform in volume

There are \(V=L^4\) original sites, \(4V\) original positive links and \(6V\) original six-plane plaquettes. The normalized product-Haar Wilson partition is
\[
Z_{N,L}(\beta)=\int_{\mathrm{SU}(N)^{4V}}
  \exp\bigl(\beta\sum_{p=1}^{6V}t(U_p)\bigr)\,dH_N^{4V}.
\]
It differs from the usual \(e^{-\beta\sum d_p}\) convention by the field-independent factor \(e^{6V\beta}\). For \(\delta=\beta^{-1/2}\) with \(\beta\ge16\), restrict all \(4V\) links to \(A_\delta\). Every original plaquette has \(d_p\le8/\beta\); therefore
\[
Z_{N,L}(\beta)\ge
 \exp[6V(\beta-8)](\beta^{-(N^2-1)/2}/K_N)^{4V}.
\]
Writing \(P_{N,L}=(6V)^{-1}\log Z_{N,L}\) and
\[
 B_N(\beta)=8+\frac23\log K_N+\frac{N^2-1}{3}\log\beta,
\]
we have \(P_{N,L}(\beta)\ge\beta-B_N(\beta)\). The real finite compact-group pressure is convex because \(P''=(6V)^{-1}{\rm Var}(\sum t_p)\ge0\), and \(P(0)=0\), hence \(P'(\beta)\ge P(\beta)/\beta\). Original periodic translation/rotation symmetry then gives for **each genuine original plaquette** \(p\)
\[
\boxed{0\le\mathbb E_{\mu_{N,L,\beta}}d_p
\le B_N(\beta)/\beta
=O_N((\log\beta)/\beta)}
\]
uniformly for all finite \(L\ge3\). These very conservative \(K_N\) constants are NOT optimized; for SU2 the previous repository SU2-only result is stronger.

For any threshold \(\varepsilon>0\), the original gauge-invariant bad-plaquette fraction \(R_\varepsilon=\#\{p:d_p\ge\varepsilon\}/(6V)\) therefore satisfies \(\mathbb E R_\varepsilon\le B_N/(\beta\varepsilon)\); moreover for \(\eta>0\) the same original normalized integral proves the **extensive-density** large deviation
\[
\Pr(R_\varepsilon\ge\eta)
\le\min\{1,\exp[-6V(\beta\varepsilon\eta-B_N(\beta))]\}.
\]
This last bound is not a sparse connected-contour bound.

## 3. Genuine high-beta SU(N) six-staple *conditional* local-energy-excess tail

Fix one ORIGINAL positive link \(\ell\), condition on every other original link, and write its exact six adjacent original Wilson terms with oriented SU(N) staples \(V_{\ell,j}\) as
\[
E_\ell(U;\mathrm{ext})=\sum_{j=1}^{6}[1-t(UV_{\ell,j})],\qquad
e_{\min}(\mathrm{ext})=\min_{U\in\mathrm{SU}(N)}E_\ell(U;\mathrm{ext}).
\]
This is a compact minimum **of the true full original Wilson one-link action**. Negative orientations are absorbed using \(t(W^{-1})=t(W)\), without altering any other plaquette. The conditional density of \(U_\ell\) in the full original Wilson Gibbs law is precisely proportional to \(e^{-\beta E_\ell(U;\mathrm{ext})}dH_N(U)\); all 1,024 link slots and all other interacting plaquettes remain.

Let \(U_*\) attain the minimum (compactness). In the genuine left-Haar cap \(U_*A_\delta\), \(\|I-W\|_{\rm op}\le\delta\) and each of the six Wilson terms moves by at most \(\delta\), hence \(E_\ell\le e_{\min}+6\delta\). The conditional normalizer is at least \(H_N(A_\delta)e^{-\beta(e_{\min}+6\delta)}\); the numerator on \(E_\ell-e_{\min}\ge\Delta\) is at most \(e^{-\beta(e_{\min}+\Delta)}\). Put \(\delta=1/\beta\le1/4\) for \(\beta\ge16\), and let \(d=N^2-1\). **Uniformly in every exterior staple configuration**, rank-fixed \(N\), finite volume and original link,
\[
\boxed{
\Pr_{\mu_{N,L,\beta}}\bigl(E_\ell-e_{\min}\ge\Delta\mid U_{\ne\ell}\bigr)
\le p_{N,\beta,\Delta}
=\min\{1,K_N\beta^d e^{6-\beta\Delta}\}.}
\]
Because the local energy and its minimum transform together under true native site gauge transformations, the **excess event** is gauge invariant. At any fixed \(\Delta>0,N\), this conditional probability decays faster than a power of \(\beta\) as \(\beta\to\infty\). This is a newly source-specific SU(N) local Gibbs estimate, not SU2 quaternion/S³ substitution.

## 4. Original **connected** high-beta animal estimate: consume existing 8/12 colouring

The PRE-EXISTING native original link colouring has \(\kappa_L=8\) colours for even \(L\), \(\kappa_L=12\) for odd \(L\), with **at most one link of any colour in any original Wilson plaquette**. Among any \(n\) original links, at least \(\lceil n/\kappa_L\rceil\) belong to one common colour. Condition on the other links: all six-staple one-link conditional laws for those colour-selected links factor exactly, and every individual excess event depends only on its own link and the fixed exterior staples. Thus for ANY actual native set \(S\)
\[
\Pr\bigl(\bigcap_{\ell\in S}
\{E_\ell-e_{\ell,\min}\ge\Delta\}\bigr)
\le p_{N,\beta,\Delta}^{\lceil|S|/\kappa_L\rceil}.
\]

Reuse the ORIGINAL positive-link endpoint-adjacency graph degree \(\le14\), its existing canonical DFS rooted animal count \(\le196^{n-1}\), **not** an invented polymer counting model. Put \(q=196p_{N,\beta,\Delta}^{1/\kappa_L}\). Whenever \(q<1\), uniformly in \(L\), volume, root and physical bare \(\beta\),
\[
\boxed{\Pr\left[
\exists\text{ original endpoint-connected }S\ni\ell_0,\ 
|S|\ge m,\ \forall\ell\in S:E_\ell-e_{\ell,\min}\ge\Delta
\right]
\le \frac{p_{N,\beta,\Delta}^{1/\kappa_L}\,q^{m-1}}{1-q}.}
\]
For \(p<1\), a sufficient and equivalent strict numerical criterion is
\[
\beta\Delta>6+\log K_N+(N^2-1)\log\beta+
\kappa_L\log196.
\]
For \(\Delta=1\), examples of thresholds for the conservative analytic constants are SU2 \(75.043\) (even L) / \(96.923\) (odd L), SU3 \(126.035\)/\(148.458\), SU4 \(203.952\)/\(226.647\). These are **BARE-\(\beta\) diagnostic thresholds**, NOT physical mass or W3 shell-rate estimates. Existing SU2 coherent-staple conditional estimates use a different event and are not replaced.

## 5. Counterexample: local energy excess does NOT dominate the physical bad field

This distinction matters to the mass-gap P0. On the genuine original \(L=4\) SU2 lattice, fix \(\ell=((0,0,0,0),\mu=0)\). Each of the six adjacent native plaquettes has a distinct opposite positive time-oriented link at \(x\pm e_\nu\), \(\nu=1,2,3\). Assign the three \(+e_\nu\) opposite links the genuine SU2 centre matrix \(-I\) and three \(-e_\nu\) opposite links \(+I\); leave every other exterior link \(+I\). The exact ORIGINAL six staples are \(3(-I)+3(+I)\), so
\[
E_\ell(U;\mathrm{ext})=6\ \text{for EVERY }U\in\mathrm{SU}(2),
\qquad E_\ell-e_{\ell,\min}=0.
\]
Yet at central \(U=I\), three original adjacent plaquettes have **maximal** Wilson deficit \(d_p=2\); the other three have \(d_p=0\). This is a real original-4D configuration of continuous SU2 matrices (centre-valued subset for the single counterexample), not a proposed replacement SU2 Haar law. Hence **physical bad plaquettes, frustrated near-minimizers and mixed regions need not contain ANY locally suboptimal link**. The new connected all-excess animal tail cannot be used as a domination of a full CMP116 large-field cluster.

The ACTUAL remaining mathematical P0 is now sharpened: either source-control the **near-minimizing frustrated-connected** sector including Wilson gauge-fixing/background/FP and all original globally unique F/G insertions, or obtain a different genuine CMP119/122 source-normalized multiscale decomposition whose differentiable connecting-activity charges are pointwise dominated by integrated small+large+mixed shells. Reuse \`YMClayOriginalConnectingChargeSectorWeldExact.physicalShellPaymentFromIntegratedSectors\` (exists on master/#1444/#1544, absent from #1536) and \`BalabanLiteralTwoWilsonCMP116ConnectingTailExact.chargeSumBelowPhysicalRootedShell\` only after their actual same-source estimates are proved.

## 6. Evidence and strict limits

The **identical committed** source [compact checker](../../scripts/check_ym_p0_sun_energy_excess_shell_compact_20261123.py) was executed locally with **30,693 PASS** before GitHub upload and Git blob identity confirmed on readback. It checks exact rational SU(N) torus box geometry (N2–8), SU(N) Weyl Fourier constant term (N2–6), high-precision Vandermonde gap, genuine native 8/12-colour incidence for L3–7, large-beta animal arithmetic for N2–6, and the original L4 SU2 six-staple negative control. A larger local 35,967-check reference also independently covered the pressure coefficients and diagonal four-link Wilson deficit. Neither executable is a full continuous-Haar quadrature or native Agda 2.9 typecheck: the analytic proof above explicitly invokes classical Weyl integration and finite real pressure convexity.

**Admission:** PROVED at ordinary finite-original-Wilson mathematical level subject to standard SU(N) Weyl–Haar and finite Gibbs calculus; LOCAL EXACT REFERENCE PASS; kernel NOT RUN. NOT proved: SU(N) renormalized physical CMP119 Eq2.18/122 Eq1.71 same-original-source T, a small/large/mixed domination by true differentiated global two-mark cluster charges, physical cutoff/volume-uniform CMP116 absolute W3, full interacting continuum E1, same-H OS positive nonvacuum D2 gap, N1 and G1 all compact simple groups. No Clay completion. Original Wilson/Haar, Weyl/Schur, Bałaban, established 8/12 original colouring/animal, existing SU2 pressure and existing DASHI CMP116/W3 ownership explicitly retained.
