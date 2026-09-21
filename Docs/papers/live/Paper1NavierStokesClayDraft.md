# Signed Resolvent Commutators and Critical Barriers for Three-Dimensional Navier-Stokes

**Periodic and whole-space reductions, with source-audited forced alternatives**

**Johl Brown**  
21 September 2026

**Status.** Goal-1 submission-facing working manuscript. The unforced alternatives A/B contain explicitly named open mathematical seams. The forced alternatives C/D are source-backed routes undergoing independent referee reconstruction. This document is not a claim of Clay acceptance, publication, or community validation.

## Abstract

We organize four routes to the three-dimensional incompressible Navier-Stokes Millennium problem in the A/B/C/D form of the official statement. The principal original contribution is a cancellation-first reduction for the unforced periodic problem together with a parallel whole-space reduction. On the periodic side, the nonlinear interaction is retained as a signed helical multiplier-difference object until an exact fixed-output covariance decomposition is reached. The modern endpoint partitions the literal physical interaction into deep far-low, deep high-high, and critical regions without inserting a norm or a fibre-cardinality loss. The remaining periodic proof-production burden is five explicit claims: two exact physical welds and three analytic estimates, the hardest being a strict critical signed-operator inequality with coefficient \(\theta<1\). On the whole-space side, the generic integration and convolution machinery is already available; the active proof reduces to two physical same-object seams, identifying the actual Euclidean resolvent kernel with the kernel controlled by the established near-origin/high-frequency estimates and identifying the actual state majorants with finite-energy convolution envelopes.

We separately audit the recently released forced-breakdown construction underlying alternatives C and D. Direct Lean routes now connect the pinned source endpoints to an independently stated Clay specification, but the manuscript treats those theorem terms only as provenance evidence. The Goal-1 task for C/D is a conventional mathematical referee audit of candidate construction, viscosity scaling, periodisation/localization, all-derivative forcing decay, uniqueness hypotheses, pressure periodicity, and the terminal obstruction. The purpose of this paper is therefore twofold: to state the strongest current A/B reductions in ordinary PDE language with every remaining theorem gap visible, and to expose the exact source-proof spine that must survive independent scrutiny for C/D.

## 1. Problem statement and claim boundary

We consider
\[
\partial_t u+(u\cdot\nabla)u=\nu\Delta u-\nabla p+f,\qquad
\nabla\cdot u=0,\qquad u(\cdot,0)=u_0,
\]
with \(\nu>0\).

The official formulation permits four logically separate alternatives:

- **A.** Global smooth bounded-energy solutions on \(\mathbb R^3\) for every smooth, rapidly decaying, divergence-free initial datum with \(f=0\).
- **B.** Global smooth spatially periodic solutions for every smooth, divergence-free periodic initial datum with \(f=0\).
- **C.** For every \(\nu>0\), admissible rapidly decaying whole-space data and forcing for which no global smooth bounded-energy solution exists.
- **D.** For every \(\nu>0\), admissible periodic data and rapidly time-decaying periodic forcing for which no global smooth periodic velocity/pressure solution exists, including periodicity of the pressure as required by the official erratum.

The four lanes are not treated as implications between one another. For Goal 1 their roles are now:

| Lane | Mathematical role | Current submission-level frontier |
|---|---|---|
| A | proof production | two physical same-object seams |
| B | proof production | B1/B7 exact welds; B2/B3/B4 analytic estimates |
| C | source-proof validation | candidate/scaling/decay/finite-energy uniqueness/obstruction audit |
| D | source-proof validation | periodisation/decay/periodic uniqueness/obstruction audit |

Machine-checked artifacts are supplementary evidence. A proof assistant is not used as a substitute for the ordinary mathematical proof.

## 2. Periodic Galerkin and helical carrier

Let \(P_N\) be the Fourier projection onto nonzero modes \(|k|\le N\) on \(\mathbb T^3\), and let \(u_N=P_Nu_N\) solve the projected unforced Navier-Stokes system
\[
\partial_tu_N-\nu\Delta u_N+P_N\mathbb P((u_N\cdot\nabla)u_N)=0,
\qquad \nabla\cdot u_N=0.
\]

For each \(k\ne0\), choose helical eigenvectors \(h_\sigma(k)\), \(\sigma\in\{+,-\}\), satisfying
\[
ik\times h_\sigma(k)=\lambda_\sigma(k)h_\sigma(k),
\qquad
\lambda_\sigma(k)=\sigma|k|.
\]
Then
\[
\widehat u(k)=u_k^+h_+(k)+u_k^-h_-(k).
\]

For a resonant triad \(p+q=k\), define
\[
X_{\sigma\tau}(p,q;k)
=
P_k\!\left(u_p^\sigma h_\sigma(p)\times
u_q^\tau h_\tau(q)\right).
\]

The basic signed commutator is exact before any norm is taken:
\[
M_{\sigma\tau}(p,q;k)
=
\bigl(\lambda_\tau(q)-\lambda_\sigma(p)\bigr)
X_{\sigma\tau}(p,q;k).
\]
The four helicity channels recombine to the physical interaction. The proof strategy is to exploit the sign, phase and multiplier difference before positive majorization.

## 3. Centering, complete-graph covariance and the modern fixed-output normal form

Earlier versions of the periodic argument emphasized an opposite-shift Taylor representation and a one-sided second-moment estimate. That finite theorem remains valid and yields the sharp coefficient
\[
A_1G_2+A_2G_1,
\]
equal to \(3E_0\) in the canonical normalization.

The modern route is stronger at the same-object level. Fix an output mode \(k\) and enumerate the literal physical incidences by \(\alpha\). Let \(A_\alpha\in\mathbb C^3\) denote the mixed-product cell and let \(r_\alpha\) denote the physical input-Laplacian rate. The complete-graph identity
\[
\sum_{\alpha<\beta}(r_\alpha-r_\beta)(A_\alpha-A_\beta)
=
n\sum_\alpha r_\alpha A_\alpha
-
\left(\sum_\alpha r_\alpha\right)
\left(\sum_\alpha A_\alpha\right)
\]
collapses the pair graph to one centered vector residual.

For the physical rates,
\[
2(r_\alpha-r_\beta)
=
\nu\Bigl(|d_\alpha|^2-|d_\beta|^2\Bigr),
\]
and the fixed-output parallelogram identity converts the centered displacement-square residual into twice a centered input-mass residual. This lands on the same weighted-amplitude carrier used downstream, without applying pairwise Young inequalities and without introducing an \(O(n^2)\) cardinality loss.

The literal physical incidence list is then filtered into three regions:

\[
\mathrm{DFL}\quad\text{(deep far-low)},\qquad
\mathrm{DHH}\quad\text{(deep high-high)},\qquad
\mathrm{Core}\quad\text{(critical core)}.
\]

The full covariance splits exactly into six signed blocks:
\[
\begin{aligned}
\mathrm{Cov}(\mathrm{DFL})
&+\mathrm{Bip}(\mathrm{DFL},\mathrm{DHH})
+\mathrm{Bip}(\mathrm{DFL},\mathrm{Core})\\
&+\mathrm{Cov}(\mathrm{DHH})
+\mathrm{Bip}(\mathrm{DHH},\mathrm{Core})
+\mathrm{Cov}(\mathrm{Core}).
\end{aligned}
\]
This decomposition is over the actual filtered physical lists. It introduces neither norms nor a fibre-cardinality estimate.

## 4. The five remaining claims for alternative B

The present periodic proof is no longer blocked by generic combinatorics. Its Goal-1 frontier consists of five claims.

### B1. Physical DFL to literal infinity-shell receipt

For each fixed output and shell, the R236-filtered deep-far-low coefficient family must be identified with a literal duplicate-free \(\mathrm{InfinityShellSupport}\) receipt.

Minimal support construction is unnecessary: one may use the literal duplicate-free outer cube and assign coefficient zero to non-DFL entries. Thus the remaining statement is an exact coefficient/mass weld:
\[
\text{physical DFL shell mass}
=
\text{literal shell coefficient mass},
\]
with the same local energy and derivative coefficient used by the existing Bernstein-to-\(E\!\cdot\!D\) payment.

Once this receipt is supplied, the finite shell fold is already available.

### B2. DFL-DHH signed shell estimate

For a DFL shell and a DHH shell on the same fixed-output fibre, prove a signed bipartite estimate of the form
\[
\mathrm{Bip}_{j,\ell}(\mathrm{DFL},\mathrm{DHH})
\le
C_{j,\ell}\,ED_k,
\]
where the shell coefficients are summable uniformly in the Galerkin cutoff.

The intended proof combines the low-leg Bernstein payment with the high-high low-output/null gain while retaining the signed block structure long enough to avoid a cardinality tax.

### B3. DHH intra-shell signed \(\ell^2\) aggregation

Prove the fixed-output high-high aggregation
\[
\sum_j \mathrm{Cov}_j(\mathrm{DHH})
\le C_{\mathrm{HH}}\,ED_k
\]
in a form compatible with the already established all-four-helicity low-output estimate and cutoff-uniform gap summation.

This is an aggregation theorem, not a request for another local helical estimate.

### B4. Strict critical signed operator estimate

Let \(S_k\) denote the literal critical-touching signed block value and \(Q_k\) the associated core companion mass. Prove
\[
S_k
\le
\theta\,Q_k+C_{\mathrm{core}}ED_k,
\qquad
0\le\theta<1,
\]
uniformly in the output and Galerkin cutoff.

The exact signed block-operator certificate interface is already constructed. The substantive missing content is precisely the strict bound above. No generic positive-Schur detour is required.

### B7. Literal R406 same-object equality

Finally prove the exact identity
\[
R_{406}(N,T)
=
4\sum_{k\in\mathcal K_N} C_k(T),
\]
where \(C_k\) is the live fixed-output covariance generated by the same physical decomposition. The recursive list/fibre aggregation needed to build the R432 decomposition is already available; the remaining statement is equality with the literal R406 remainder consumed by the terminal critical slice.

### Periodic completion theorem

Once B1-B4 and B7 are supplied, the existing fixed-output payment and uniform-output family yield the cutoff-uniform critical barrier in the physical critical Sobolev currency
\[
u_N\in L^\infty(0,T;H^{1/2}(\mathbb T^3))
\cap L^2(0,T;H^{3/2}(\mathbb T^3)),
\]
uniformly in the Galerkin cutoff.  Interpolation and the periodic Sobolev embedding give
\[
u\in L^4(0,T;L^6(\mathbb T^3)),
\qquad \frac{2}{4}+\frac{3}{6}=1.
\]
The final regularity step is therefore the classical Serrin continuation criterion in the endpoint pair \((p,q)=(4,6)\), applied to the same limiting solution.  Passage from the Galerkin sequence to that limiting solution uses the standard Aubin--Lions--Simon compactness theorem together with the equation-derived negative Sobolev time-derivative bound and lower semicontinuity.  These are conventional imported results, but the submission must state their hypotheses on the same Galerkin sequence and limit rather than merely say that “standard continuation applies.”

Thus the remaining *new* periodic mathematics is exactly B1-B4 and B7; the continuation/compactness step is a mandatory cited theorem invocation rather than an additional conjectural Navier--Stokes estimate.

## 5. Negative control: why positive same-output Gram separation is not enough

An earlier route compressed each fixed-output fibre into block vectors and attempted to pay the positive Gram residual from incidence separation.

For vectors \(B_1,\dots,B_n\),
\[
\sum_{\alpha<\beta}\|B_\alpha-B_\beta\|^2
=
n\sum_\alpha\|B_\alpha\|^2
-
\left\|\sum_\alpha B_\alpha\right\|^2.
\]

This identity is useful bookkeeping but does not by itself produce a positive separation theorem. The compressed block is many-to-one in the underlying incidence data: distinct incidences may carry identical velocity arguments and therefore identical compressed kernels. Hence incidence separation alone cannot imply
\[
\|B_\alpha-B_\beta\|\ge c>0
\]
for every distinct pair. This rules out that specific positive-payment strategy without ruling out signed resolvent, block-operator, Schur or Cotlar-type estimates using additional physical information.

## 6. Whole-space alternative A: two physical seams

The whole-space Fourier route has now been recut so that generic measure theory is not counted as unresolved Navier-Stokes research.

Let \(K_u\) be the actual Euclidean centered-resolvent kernel generated by a smooth whole-space trajectory. Existing results already provide:

1. a near-origin projected-saturation estimate for the intended physical kernel object;
2. a high-frequency scale-relative curvature estimate;
3. fixed-output \(L^2\times L^2\to L^1\) convolution integrability and a quantitative bound;
4. finite-energy tail control;
5. preservation of \(L^1\) integrability under the bounded high-frequency multiplier used by the inverse-sixth branch.

The current theorem-level compiler consumes only two physical witnesses.

### A1. Physical kernel same-object seam

On the same actual Fourier interaction, identify:

- output frequency;
- the two input/pair resolvents;
- output resolvent;
- centered residual;
- signed projected Gram scalar;
- near-origin saturation coefficient;
- high-frequency scale-relative curvature quantity.

The object appearing in the near-origin and high-frequency estimates must be literally the physical kernel generated by \(u\), not an analogous abstract rational carrier.

A recent audit exposed precisely why this typing matters: a previous high-frequency witness was insufficiently indexed by the physical kernel and could in principle certify an unrelated scale-floor theorem. The active formulation forbids that mismatch. Where rational estimates are reused, the repository already provides the rational-to-Bishop-real embedding needed to state an exact same-object bridge.

### A2. Physical state/convolution-majorant seam

Prove pointwise domination of the actual low/high physical state majorants by the finite-energy convolution envelopes:
\[
M_{\mathrm{low}}^{\mathrm{phys}}\le \widetilde M_{\mathrm{low}},
\qquad
M_{\mathrm{high}}^{\mathrm{phys}}\le \widetilde M_{\mathrm{high}},
\]
with \(\widetilde M_{\mathrm{low}},\widetilde M_{\mathrm{high}}\in L^1\).

On the high region, the inverse-sixth physical multiplier is bounded, so no second bespoke convolution theorem is needed. The remaining work is its concrete physical instantiation and same-object identification.

### Whole-space completion theorem

Given A1 and A2, the existing two-seam compiler transports the established near-origin and high-frequency estimates to the actual physical kernel and proves integrability of the actual physical majorants.  The manuscript must then state the precise a-priori norm obtained from these physical bounds and invoke a conventional whole-space continuation theorem whose hypotheses are *literally* those bounds on the same solution.  Until that norm-to-continuation implication is written explicitly, A1/A2 close the physical Fourier-integrability seam but do not by themselves constitute alternative A.  No generic Fubini/Young/tail theorem is being treated as novel research; the remaining publication obligation is an exact standard-theorem invocation after the two physical identifications.

## 7. Forced whole-space alternative C: source-proof referee reconstruction

For C, the Goal-1 task has changed category. The direct source route is
\[
\texttt{selected\_candidate\_one\_with\_initial\_rest}
\to
\text{viscosity scaling}
\to
\texttt{NavierStokesR3.theorem\_1\_1}
\to
\text{whole-space exclusion}
\to
\text{independent ClayOptionC}.
\]

For fixed \(\nu>0\), the source construction supplies a compact whole-space candidate starting from rest, scales it to viscosity \(\nu\), and derives a smooth compactly supported forcing. A hypothetical global smooth bounded-energy solution with the same data is compared with the candidate on each interval \(0\le t\le T<1\) by a whole-space classical uniqueness theorem.

The referee audit must verify, directly in the source:

1. **Candidate identity.** The candidate used in the terminal obstruction is the same object transported through viscosity scaling and comparison.
2. **Exact viscosity scaling.** Velocity, pressure and force scaling preserve the same forced Navier-Stokes equation at the arbitrary requested \(\nu>0\).
3. **Decay hypotheses.** Compact support and smoothness imply the exact all-jet rapid space-time decay quantified in the official statement.
4. **Bounded-energy semantics.** The hypothetical Clay competitor supplies exactly the finite-energy/local hypotheses used by the uniqueness theorem; no stronger substitute is silently assumed.
5. **Whole-space uniqueness.** The proof of \(\texttt{classical\_uniqueness\_on\_Icc}\) uses only these hypotheses and standard local analysis.
6. **Terminal obstruction.** The selected candidate carries the explicit blow-up mechanism used by the source. In the traced slow-base regime,
   \[
   \|u(t,0)\|=(1-t)^{-A(h)}j,
   \qquad A(h)>0,\ j>0,
   \]
   and the later candidate is proved eventually equal to that base along the relevant axis.
7. **Non-circular provenance.** Candidate construction and uniqueness do not assume an equivalent form of the desired breakdown theorem.

If these checks survive independent reconstruction, the contradiction is conventional: pre-singular uniqueness identifies a hypothetical global smooth bounded-energy solution with the candidate for every \(T<1\), while smooth continuation through \(t=1\) is incompatible with the candidate's terminal obstruction.

The Lean submission surface is an audit/provenance receipt for this chain, not the manuscript proof itself.

## 8. Forced periodic alternative D: source-proof referee reconstruction

The direct periodic route is
\[
\text{compact candidate}
\to
\text{compression/periodisation}
\to
\texttt{PeriodicPaper.periodic\_corollary}
\to
\text{periodic candidate exclusion}
\to
\text{independent ClayOptionD}.
\]

The source spine currently traced is:
\[
\texttt{theorem\_1\_1\_with\_initial\_rest}
\to
\texttt{compressedCandidate}
\to
\texttt{PeriodicPaper.of\_compact\_candidate}
\to
\texttt{CandidateProperties.no\_global\_solution}.
\]

The decisive referee checks are:

1. **Exact periodisation.** \(\texttt{navier\_stokes\_periodize}\) must preserve the nonlinear PDE and rule out cross-cell contamination on the active support.
2. **Same force and viscosity.** The hypothetical global solution and source candidate must use identical \(\nu,u_0,f\).
3. **All-derivative force decay.** The source future-jet theorem must imply the official arbitrary-polynomial time decay for every required spatial/time derivative, uniformly in space.
4. **Pressure periodicity.** Both the candidate semantics and the hypothetical global-solution predicate must include the official pressure-periodicity erratum.
5. **Periodic uniqueness.** \(\texttt{classical\_uniqueness\_on\_Icc}\) must require only hypotheses supplied by a hypothetical Clay solution.
6. **Actual terminal obstruction.** The periodized selected candidate, not an auxiliary surrogate, must carry \(\texttt{SpeedUnboundedAtOne}\).
7. **Arbitrary viscosity.** The entire construction must work for every \(\nu>0\) with the official quantifier order.

Several central attack points have already survived direct source inspection: the arbitrary-viscosity transport, the classical uniqueness route, and the provenance of the explicit unbounded-speed base formula. The remaining audit should nevertheless be written out lemma by lemma rather than promoted from wrapper composition.

If these checks pass, a hypothetical global smooth periodic solution is bounded on a compact space-time slab through \(t=1\). Pre-singular uniqueness transfers that bound to the candidate on every \(T<1\), contradicting the candidate's unbounded speed as \(t\uparrow1\).

## 9. Relation between the four lanes

The forced and unforced routes are logically separate.

- C/D do not prove A/B.
- A/B do not rely on the forced construction.
- The C/D source audit does not claim independent discovery of the released singular candidate.
- A/B remain the original proof-production programme.

For publication it is useful to separate two products:

1. **C/D verification paper.** A conventional, independently reconstructed audit of the released source proof against the official clauses.
2. **A/B original paper.** The signed-resolvent/critical-barrier programme, with A1/A2 and B1/B2/B3/B4/B7 displayed as the only remaining proof-production claims.

The present manuscript records both so that the complete ABCD status is visible in one place.

## 10. Goal-1 completion cut

The shortest current frontier is:

\[
\boxed{
\begin{array}{ll}
A:& A1\ \text{physical kernel same-object},\quad
   A2\ \text{physical majorant/convolution weld};\\[1mm]
B:& B1,\ B2,\ B3,\ B4,\ B7;\\[1mm]
C:& \text{independent audit of the selected R3 candidate and obstruction};\\[1mm]
D:& \text{independent audit of the periodized candidate and obstruction}.
\end{array}}
\]

More specifically:

- **A** is no longer a measure-theory project. The active new mathematics is physical identity; publication additionally requires the exact conventional continuation theorem consuming the resulting physical norm.
- **B** is no longer a generic combinatorics project. B2/B3/B4 are the remaining analysis; B1/B7 are exact welds. Once they yield the uniform \(L^\infty_tH^{1/2}_x\cap L^2_tH^{3/2}_x\) barrier, the standard endpoint Serrin route \(L^4_tL^6_x\) supplies continuation after the conventional Aubin--Lions--Simon passage to the same limit solution.
- **C/D** should not be measured by unfinished bespoke Agda reconstruction. Their Goal-1 stop condition is a referee-readable source proof matching the official hypotheses and conclusion.

Writing the manuscript is itself a proof-search tool: any claim that cannot be stated in conventional mathematics with an exact source theorem or proof becomes visible immediately as a remaining gap.

## 11. Formal provenance and reproducibility

The formal development is supplementary.

For A/B, Agda records the finite identities, literal physical carriers, region decompositions and same-object interfaces. For C/D, Lean independently states the Clay semantics and exposes direct source routes from the pinned theorem endpoints through clause-level submission witnesses.

The relevant current branches are:

- \(\texttt{dashi\_agda}\): \(\texttt{agent/ns-clay-b-canonical-critical-endgame}\);
- \(\texttt{dashi\_lean4}\): \(\texttt{agent/ns-a-euclidean-cubature-boundary-defect}\).

Submission artifacts should record exact commit hashes and observed build/axiom receipts. Source-written code without a fresh build receipt is not described as freshly kernel-verified.

## 12. Conclusion

The Navier-Stokes programme has crossed from architecture-heavy proof search into a small number of visible mathematical claims.

For the unforced whole-space route A, two physical same-object identifications remain. For the unforced periodic route B, the exact physical decomposition is already in place and the remaining burden is three analytic estimates plus two physical welds. For C and D, the relevant source theorem routes already reach an independent statement of the official alternatives, so the remaining Goal-1 work is independent mathematical reconstruction and hostile-referee checking of the source construction.

This claim boundary is intentionally conservative. It is designed so that finishing the paper and finishing the mathematics become the same task: every load-bearing proposition is either proved, source-backed and independently audited, or displayed explicitly as an open obligation.


## 13. Exact conventional continuation seam

The manuscript does not treat compactness and continuation as new PDE discoveries, but they are part of a complete proof and therefore must be stated exactly.

For the periodic route, the critical barrier is to be consumed as follows.  Uniform Galerkin control in
\[
L^\infty(0,T;H^{1/2})\cap L^2(0,T;H^{3/2})
\]
gives, by interpolation and the periodic Sobolev embedding,
\[
\|u\|_{L^4(0,T;L^6)}^4
\le C_S^4
\Bigl(\sup_{0\le t\le T}\|u(t)\|_{H^{1/2}}^2\Bigr)
\int_0^T\|u(t)\|_{H^{3/2}}^2\,dt.
\]
The exponent identity \(2/4+3/6=1\) is exactly Serrin's regularity line.  Hence the limiting solution is regular and extends past any putative finite maximal time.  The Galerkin-to-limit step is justified by the usual Aubin--Lions--Simon compactness argument, using the Navier--Stokes equation to bound the time derivative in a negative Sobolev space and lower semicontinuity to retain the critical estimates.

For the whole-space route, the corresponding final theorem invocation must be written only after A1/A2 have been instantiated, because the exact physical norm delivered by those two identifications determines which classical continuation theorem applies.  The paper will not replace that implication by an unspecified phrase such as “standard continuation.”
