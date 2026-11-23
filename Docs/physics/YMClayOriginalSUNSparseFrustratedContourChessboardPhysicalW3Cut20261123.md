# Yang–Mills mass gap P0 — original SU(N) gauge-invariant sparse frustrated-contour bound, plus physical W3 cut

**23 November 2026. Mathematical finite-Wilson source result, not continuum Yang–Mills.**

**Precedence / reuse:** the EXACT four-dimensional Wilson SU(N) finite source, Haar/product Gibbs and original F19 globally unique two marks already exist on master/#1536: \`YMClaySUNMatrixWilsonTraceGaugeExact\`, \`YMClaySUNVariablePeriodicProductHaarExact\`, \`YMClaySUNVariablePeriodicGibbsGaugeExact\`, \`YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact\`. The **original SU2** high-beta pressure already exists in \`YMClaySU2OriginalWilsonUniformPlaquetteDeficit20261109.md\`; the **original SU2** fixed-contour chessboard proof and corrected 24-class geometry already exist in \`YMClayOriginalWilsonSparseChessboard20261120.md\`, \`YMClayOriginalWilsonSparseChessboardBidi20261119.md\`, and \`YMClayOriginalWilsonPeriodicConflictColoring12R44520261121.md\`. Their actual 22-Nov corrected four-axis reflection face map is REUSED unchanged. The NEW input is the fixed-N continuous **SU(N)** pressure/Haar cap proved on #1536 in \`YMClayOriginalSUNHighBetaWeylCapEnergyExcessShell20261123.md\`; the result below lifts sparse geometric bad-region control to every fixed SU(N), rather than redoing the original SU2 machinery. **No new universal abstract KP compiler, artificial measure or alternative Wilson carrier.**

## 1. Source, scope and exact original large-field event

For **fixed integer N>=2**, bare beta>=16, and periodic **dyadic even** side L=2^k>=4 (conservative site-reflection chessboard dissemination regime), take the ORIGINAL fully interacting four-dimensional six-plane Wilson positive-link source:

\[
E_L=\{(x,\mu):x\in(\mathbb Z/L\mathbb Z)^4,\ 0\le\mu<4\},\quad
P_L=\{(x,\mu,\nu):0\le\mu<\nu<4\}.
\]
There are L^4=V sites, 4V ORIGINAL links, 6V ORIGINAL plaquettes; each link belongs to exactly six plaquettes, each plaquette to exactly four positive link variables. No link, spectator, FP source or globally marked F/G is silently discarded in the action.

Let \(t_p(U)=\operatorname{ReTr}U_p/N\), \(d_p(U)=1-t_p(U)=\|I-U_p\|_{\mathrm F}^2/(2N)\in[0,2]\). Under arbitrary local site gauge transformations, \(U_p\mapsto g(x)U_pg(x)^{-1}\); thus **d_p is exactly gauge invariant** for the genuine SU(N) source. For \(0<\epsilon\le2\) and original positive link \(\ell\), define a concrete nonvacuous *gauge-invariant* event
\[
B_\ell^\epsilon=\{\exists\,p\in P_L:\ell\in\partial p,\ d_p\ge\epsilon\}.
\]
This is an original SOURCE plaquette-deficit event, not a generic assumed RG \`LiteralBadTraversal\`, and not the complete CMP119 or CMP116 large-field condition. It detects the pre-existing **near-minimizing frustrated** counterexample: the original SU2 six-staple central link with 3(+I),3(-I) has zero local excess but 3 incident plaquettes with d=2, so its B_l^epsilon is true for any epsilon<=2. Thus the new event controls an actual channel the previous SU(N) connected **local-energy-excess** proof could not.

## 2. Physical input ALREADY paid by the SU(N) pressure source

For normalized product-Haar Wilson
\[
Z_{N,L}(\beta)=\int e^{\beta\sum_{p\in P_L}t_p(U)}dH_N^{E_L}(U),
\]
the SAME source \`YMClayOriginalSUNHighBetaWeylCapEnergyExcessShell20261123.md\` establishes via Weyl–Haar identity caps (not SU2 rational quaternions) and convexity that
\[
Z_{N,L}(\beta)\ge \exp[6V(\beta-\mathcal B_N(\beta))],\quad
\mathcal B_N(\beta)=8+\frac23\log K_N+\frac{N^2-1}{3}\log\beta,
\]
\[
K_N=N!(128N^2)^{N-1}(16N)^{N(N-1)}.
\]
This bound is **uniform in every finite volume** for each fixed N. The mathematical theorem is proven for arbitrary finite L>=3; restricting to dyadic L in THIS new argument is because of the *iterated chessboard theorem*, NOT a weakness of SU(N) Haar or the full original Gibbs law. For SU2 the original sharper SU2 pressure result has precedence.

## 3. SU(N) site reflection and imported standard chessboard inequality — with exact native scope

For coordinate site planes at x_j=0 and x_j=L/2, the original native six-plane plaquette action splits into: boundary-only plaquettes; positive-half original plaquettes; reflected negative-half original plaquettes. Under the original reflected oriented link map, invert links pointing opposite the direction and use t(U^{-1})=t(U) and Haar bi-invariance. Conditional on the actual shared tangential boundary variables the positive/negative original fine-link sets are disjoint, and the reflected half integrals are equal. Therefore the site-reflection Gram form is an integral of a squared real half-integral, nonnegative, for the selected gauge-invariant real half observable. This is source-specific pure SU(N) Wilson **site** reflection positivity, not a generic assumption that arbitrary nonlocal Wilson actions are RP.

The **repeated site-reflection Cauchy–Schwarz/chessboard estimate for closed unit 4-cubes** is the standard external theorem; its exact algebra of reflected gauge-invariant closed-cube observables and shared boundary link variables needs a pinned Agda kernel proof before upgrading formal acceptance. Use the conservative dyadic L=2^k to guarantee the sequence of reflection planes used in dissemination. This is the same conditional mathematical authority as the PREEXISTING original SU2 chessboard donor, now applied to the same original SU(N) Wilson reflection-positive real trace action. Primary provenance: Osterwalder–Seiler, *Gauge field theories on a lattice* (Ann. Phys. 110, 1978); Menotti–Pelissetto, *General proof of Osterwalder–Schrader positivity for the Wilson action* (1987); Fröhlich–Israel–Lieb–Simon, *Phase Transitions and Reflection Positivity* I (1978); Biskup, *Reflection positivity and phase transitions in lattice spin models*, arXiv:math-ph/0610025, standard chessboard inequality. This is NOT an independent kernel proof of these established theorems.

**CRITICAL corrected native geometry:** there are 6 original two-plane choices and 4 parity shifts in the transverse coordinates = **24** actual classes. For tile base x and transverse coordinate k with prescribed parity s, the true face coordinate is
\[
x_k+\bigl((s-x_k)\bmod2\bigr)\pmod L.
\]
It lies on THAT tile's closed unit 4-cube, unlike the old wrong source formula. The complete unit-cube dissemination of one marked face in a class creates **V tile marks representing V/4 DISTINCT native positive plaquettes, each with exact multiplicity FOUR**. The source checker independently re-enumerates every tile and every class on L4/L6/L8, with L6 intentionally geometry-only.

## 4. TRUE SU(N) fixed arbitrary plaquette support: a sparse, not extensive, probability theorem

For any fixed set A of m **distinct** ORIGINAL positive plaquettes, any 0<epsilon<=2, define \(\mathcal D_A^\epsilon=\bigcap_{p\in A}\{d_p\ge\epsilon\}\). On fully disseminating one original chosen face, the action includes V/4 distinct constrained plaquettes, so D(U)=sum_p d_p(U)>=epsilon V/4. The *normalized* original Wilson Gibbs integral and pressure lower bound from Section 2 give
\[
\Pr_{\mu_{N,L,\beta}}(\mathcal D_{\mathrm{full}}^\epsilon)
\le\exp\left[V\left(6\mathcal B_N(\beta)-\beta\epsilon/4\right)\right].
\]
The original SU(N) site-reflection chessboard inequality bounds m' marked plaquettes from ONE class by the m'-th power of the Vth root of that probability, i.e.
\[
\Pr\big(\mathcal D_{A\cap\mathrm{class}}^\epsilon\big)
\le\exp\left[-|A\cap\mathrm{class}|
\left(\beta\epsilon/4-6\mathcal B_N\right)\right].
\]
Among 24 geometric classes at least m/24 marked plaquettes lie in one class. If \(\beta\epsilon/4-6\mathcal B_N>0\) (the only regime used downstream), the event for ALL A implies the event for this class, yielding **uniform in V**, with NO independence of plaquettes:
\[
\boxed{
\Pr_{\mu_{N,L,\beta}}(\mathcal D_A^\epsilon)
\le e^{-m k_{N,\beta,\epsilon}},\qquad
k_{N,\beta,\epsilon}
=\frac{\beta\epsilon}{96}-\frac{\mathcal B_N(\beta)}4 .
}
\]
When k<=0 this displayed RHS may exceed 1: the bound is then **not a useful suppression**, and no negative physical conclusion is drawn. This is precisely the existing original 24-class SU2 method with the NEW SU(N) source pressure input, not an independently named polymer gas.

## 5. TRUE original gauge-invariant sparse bad links and rooted animals

Given any fixed S subset E_L with |S|=n, if every B_l^epsilon occurs, select ONE incident bad plaquette witness for each link; at most 6^n assignments, using the exact original six-plaquette incidence. Each distinct original plaquette can witness at most four ORIGINAL positive links, so each assignment involves at least ceil(n/4) distinct bad plaquettes. The preceding real SU(N) bound yields
\[
\boxed{
\Pr\left(\bigcap_{\ell\in S}B_\ell^\epsilon\right)
\le\min\{1,u_{N,\beta,\epsilon}^{n}\},\quad
u_{N,\beta,\epsilon}=
6\exp\left[\frac{\mathcal B_N(\beta)}{16}
 -\frac{\beta\epsilon}{384}\right].
}
\]
Only source incidence/union bound and standard RP/chessboard were used. No configuration-wise independent link events were claimed.

The previously established positive-link endpoint adjacency has maximum degree 14 and a canonical rooted depth-first animal count <=196^(n-1). Define
\[
q_{N,\beta,\epsilon}=196u_{N,\beta,\epsilon}.
\]
If q<1, for EVERY native original root positive link and every m>=1,
\[
\boxed{
\Pr\{\exists\text{ endpoint-connected all-}B^\epsilon
\text{ ORIGINAL link animal containing root, size}\ge m\}
\le\frac{u_{N,\beta,\epsilon}q_{N,\beta,\epsilon}^{m-1}}
{1-q_{N,\beta,\epsilon}}.
}
\]
The explicit rank/coupling/threshold **necessary-and-sufficient condition for this stated sufficient bound** is
\[
\boxed{
\beta\epsilon>
384\log1176+24\mathcal B_N(\beta).
}
\]
For any **fixed N,epsilon>0** the condition eventually holds as beta->infty, since beta epsilon grows linearly while B_N=O_N(log beta). It is NOT a condition proven to hold at finite physical weak-coupling cutoff on the actual \(\beta(a)\) trajectory; selecting beta as needed only establishes existence of a bare-parameter regime, not a physical RG coupling realization.

**Numerical threshold diagnostics (conservative nonoptimal source constants):** for epsilon=1, root q=1 occurs around beta=3323.25 (SU2), 4064.56 (SU3), 5147.73 (SU4), 6590.55 (SU5), 13215.68 (SU8). These large numbers show this argument is very weak quantitatively. The previous SU2-specific pressure/chessboard theorem gives sharper constants for SU2 and is NOT superseded.

## 6. Fixed physical distance, shrinking thresholds and the precise MASS GAP nonimplication

Suppose along a specified physical cutoff a>0 a bad-link connected animal crosses a physical coordinate distance R, using n>=ceil(R/a) ORIGINAL link steps. If its q(a)<1 then the theorem yields an **exceptional-event-only** exponential \(\lesssim q(a)^{R/a}\), with corresponding formal event rate \(-\log q(a)/a\). This is NOT the Yang–Mills mass or the CMP116 **sum of ABSOLUTE differentiated two-Wilson activities**. The existence of a path of good small-field quantum fluctuations connecting F and G is not excluded by absence of a bad-link contour.

More importantly, for a scale-dependent microscopic threshold \(\epsilon(a)\), the ACTUAL sufficient condition is \(\beta(a)\epsilon(a)>384\log1176+24\mathcal B_N(\beta(a))\). If \(\epsilon(a)=c/\beta(a)\) at fixed c, the LHS is constant while the RHS grows as a positive O_N(log beta) along beta->infty: the *bare chessboard suppression criterion FAILS* at sufficiently small a, even though beta->infty. This is an explicit quantitative **no-go for this estimate**, NOT a no-go for true physical large-field suppression or the Clay gap. Renormalized CMP119 good/large-field thresholds may be scale-dependent and need their OWN actual source matching. High-beta source entropy suppression at a fixed bare plaquette threshold is not a proof of a small physical-block J estimate, FP or W3.

## 7. Exact remaining P0 witness obligation and original typed ownership

The native \`YMClayOriginalConnectingChargeSectorWeldExact.physicalShellPaymentFromIntegratedSectors\` is **already byte-identically imported onto #1536** from master and connected to \`DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda\`; do NOT duplicate this compiler. \`BalabanLiteralTwoWilsonCMP116ConnectingTailExact.TwoWilsonCMP116PhysicalShellPayment\` consumes the actual \`connectingClusters\` charge list and requires its \`chargeSumBelowPhysicalRootedShell\` FIELD to be SOURCE-DERIVED.

The theorem above pays only the *unmarked ORIGINAL SU(N) bare high-deficit fixed-contour probability*, conditional on standard closed-cube chessboard applicability. It does NOT produce:
1. the original nonlinear CMP98 Eq.(119–121) Q_B, all true CMP119 (2.18–2.22) Omega/Lambda/S with **S summed INSIDE T**, CMP122 Eq.(1.71) constrained Haar R/FP/gauge/Jacobian/background E/R/B/V operation with all ORIGINAL 896 F19 spectators, at running beta(a); 
2. globally unique F/G and 1/F/G/FG differentiated **normalized** original Wilson marked cluster jets, both inherited mixed Hessian and first-score covariance, with pointwise *absolute* support-localized activity domination by small+large+mixed sector charges;
3. cutoff/volume-independent physical rooted-shell entropy and rate, controlled good-field propagators and near-minimizing sectors when the actual RG large-field threshold shrinks; 
4. the same **interacting noncollapsed** reflection-positive continuum Schwinger source and one **dense same-H_OS** nonvacuum spectral gap; N1 and G1 separately open.

**P0 NEXT MAX-CUT:** identify WHICH actual CMP119/122 selected physical field/history/domain/witness conditions mean \(d_p\ge\epsilon_j\) at each scale, whether its literal C2/Step V sector activity can be dominated by an original gauge-invariant high-deficit contour at threshold \(\epsilon_j\), and whether the running \(\beta(a)\epsilon_j(a)\) beats the preceding source entropy. Any positive outcome must still pay mixed two-mark Hessian and ABSOLUTE source cluster charge; it cannot be populated by a generic \`Set\` record field without actual original Wilson measure estimates.

## 8. Local executable/trust

[Source-identical standalone Python/SymPy checker](../../scripts/check_ym_p0_sun_sparse_bad_contours_20261123.py): **442,255 PASS**, original actual L4/L6/L8 4D 6L^4 plaquettes and 4L^4 positive links, 24/24 native classes, V/4 distinct faces per class, exact fourfold multiplicity, actual original 6-per-link/4-per-face incidence, arbitrary sampled witness mappings; symbolic rate algebra; mpmath high-precision source constant/rate thresholds for N2/3/4/5/8 and epsilon=1,1/2,1/4; explicit shrinking-threshold and sparse-spanning-density negative controls. **Exact committed checker Git blob \`a0feccdd82c4e3eebd8dfe9872eca9e4ca2d7aac\` matches the 7,181-byte locally executed file**; this is a real exact-content check, NOT Agda/Lean kernel or GitHub CI.

**Status:** ordinary mathematical source argument **conditional on the externally established standard SU(N) Wilson site-reflection chessboard theorem for the selected closed-cube observable algebra**, source geometry locally exact PASS; all-group generality only SU(N) at fixed rank, and L dyadic for the dissemination claim. No complete physical running CMP119/122 source, absolute W3 or interacting same-H mass gap. Attribution Wilson, Haar/Weyl, Osterwalder–Seiler, Menotti–Pelissetto, FILS/Biskup chessboard, original DASHI SU2 chessboard and original SU(N) Weyl-cap pressure owners retained. 
