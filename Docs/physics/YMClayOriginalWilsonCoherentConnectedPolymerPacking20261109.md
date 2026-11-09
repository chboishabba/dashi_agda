# D1 ORIGINAL WILSON: 4D star-packing, conditional factorization and coherent connected-polymer decay

Date: 2026-11-09. Scope: real **four-dimensional periodic finite SU(2) Wilson model**, side length at least 3, coupling beta>0, genuine normalized product Haar/Wilson Gibbs measure. This is an unconditional **coherent-staple polymer upper bound**, not the full connected covariance or the missing frustrated-polymer estimate. Attribution: Wilson finite lattice/Haar measure, DASHI original SU2 single-link conditional cap source and same-source geometric polymer count.

## Physical source and finite geometry, no independence assumptions

Let V=(Z/LZ)^4, L>=3, with E=V×{0,1,2,3} positively oriented links, and plaquettes P=V×{(mu,nu):0<=mu<nu<4}. A link belongs to exactly 2(4−1)=**6** original plaquettes. Each such plaquette has exactly **3 other** links, so the *plaquette conflict graph* on E has degree at most 6×3=**18**. Hence every set S of n distinct marked links contains a subset T⊆S with **|T|>=ceil(n/19)** for which no two links of T occur in a common plaquette. This follows constructively by greedy maximal independent set: one selected vertex eliminates at most 19 marked links (itself + 18 neighbours).

Let \(U\in SU(2)^E\) and \(t(W)=\frac12\operatorname{Re}\operatorname{Tr}(W)\). The original Wilson density is

\[
d\mu_\beta(U)=Z_\beta^{-1}
  \exp\bigl(\beta\sum_{p\in P}t(U_p)\bigr)
  \prod_{\ell\in E} dH(U_\ell).
\]

For each selected link \(\ell\), orient its six original staples \(V_{\ell,j}\) so \(\sum_{p\ni\ell}t(U_p)=\sum_{j=1}^6 t(U_\ell V_{\ell,j})\); set \(S_\ell=\sum_j V_{\ell,j}\), \(R_\ell=\|S_\ell\|\in[0,6]\) and, when \(R_\ell>0\), \(S_\ell=R_\ell V_\ell\) for \(V_\ell\in SU(2)\). Let the *original local misalignment event* \(B_\ell=\{t(U_\ell V_\ell)\le0\}\) and the *coherent-staple event* \(A_\ell(r)=\{R_\ell\ge r\}\), with \(0<r\le6\). When R=0 choose V arbitrarily; the coherent event excludes this ambiguity.

**Exact conditional factorization:** if T has pairwise disjoint incident plaquette sets, the exponent factors by selected links conditioned on U_{E\setminus T}; each original plaquette contains at most one selected link. Thus the joint conditional law of (U_ell)_{ell∈T} is the **product** of the authentic, original one-link Haar conditionals, with the *actual frozen exterior staples*. Unlike full Wilson plaquette independence, this factorization is mathematically exact. Crucially A_ell(r) and V_ell depend only on U_{E\setminus T}, because none of the six staples contains any other link in T.

By the existing original SU(2) Haar conditional estimate, for each exterior configuration and \(\ell\in T\),

\[
\Pr(B_\ell\mid U_{E\setminus T})\mathbf1_{A_\ell(r)}
 \le q_{\beta,r}\mathbf1_{A_\ell(r)},\qquad
 q_{\beta,r}=\min\{1,3e^{-\beta r/2}\}.
\]

Consequently, *without pretending to have independent Gibbs plaquettes*,

\[
\boxed{\Pr_{\mu_\beta}(\,\bigcap_{\ell\in S}
 (B_\ell\cap A_\ell(r))\,)\le
 q_{\beta,r}^{\lceil |S|/19\rceil}.}
\]

This holds uniformly in periodic lattice volume. It is the original **coherent portion** of the full bad-link connected-polymer event, not a bound on all bad links. For a general all-bad S, the exact decomposition gives
\[
\Pr(\bigcap_{\ell\in S}B_\ell)
\le q_{\beta,r}^{\lceil |S|/19\rceil}
 + \Pr\bigl(\exists\ell\in T:\ R_\ell<r\bigr),
\]
for a fixed geometrically selected conflict-free T⊆S. The latter term is precisely the still-unpaid *joint frustrated-staple* problem; a union bound from earlier one-link pressure estimates fails to decay with polymer distance.

## Connected event and entropy, same original Wilson measure

Define links to be geometrically adjacent if they share an endpoint. For L>=3 this graph has maximum degree **14** (two endpoints, eight incident oriented-positive link variables per vertex, subtract the link at each endpoint). Every finite connected set S of n≥1 links containing a fixed root link admits a canonical deterministic rooted spanning tree and a depth-first exploration walk of length 2(n−1), hence the number of such sets is at most \(14^{2(n-1)}\). (Choose a canonical ordered spanning tree; distinct connected sets cannot share its visited-vertex set.)

For q=q_{beta,r} and \(a=14^2 q^{1/19}\), summing the union bound across all connected *coherent-and-misaligned* sets gives, when a<1,

\[
\boxed{
\Pr\{\exists\text{ connected }S\ni\ell_0,\ |S|\ge m,
 \ \forall\ell\in S:\ B_\ell\cap A_\ell(r)\}
 \le \frac{q^{1/19}}{1-a}\,a^{m-1}.
}
\]

This is a bona fide, volume-uniform *connected-polymer exponential size tail for the coherent-staple subset*, at sufficiently large bare beta: it follows from actual Wilson Gibbs conditional factorization, not i.i.d. plaquettes, and no total-volume pressure estimate is required. A sufficient explicit (nonoptimal) beta condition is \(14^2\,[3e^{-\beta r/2}]^{1/19}<1\), i.e. \(\beta>(2/r)(19\log196+\log3)\). For q=1 the condition cannot hold. Finite-volume n cannot exceed |E|; extending the sum to infinity only enlarges its bound.

**Clarification of the event:** a path with alternating coherent and frustrated links can traverse macroscopically far with no large connected component made *entirely* of coherent bad links. This theorem alone therefore does NOT imply original full-Wilson connected covariance decay. The hard remaining statement is an original-Wilson joint estimate for **frustrated connected supports** or a valid multiscale block decomposition handling them with enough entropy suppression.

## Non-vacuity, physical scaling and exact remaining lemmas

This bound concerns the full original finite lattice event class for every source cutoff and periodic volume satisfying L>=3; the event is a concrete geometric cylinder event and cannot be made vacuous by an arbitrary AdmissiblePerturbation predicate. It is **not** enough for original physical CMP116 marked-domain applicability: that also needs source-covariance identity, nonvacuous remote supports, physical time/distance scaling and a uniform original small+large-field estimate.

The following exact proposed analytic lemmas, separated from the original Agda declaration names, are now distinguishable:

- **D1-COH-01** literal 4D Wilson incidence: 6 plaquettes/link, degree-18 conflict graph and degree-14 endpoint graph; same selected original product Haar source
- **D1-COH-02** conflict-free greedy packing: |T|≥ceil(|S|/19)
- **D1-COH-03** full Wilson Gibbs conditional factorization over T (all incident plaquettes disjoint)
- **D1-COH-04** original SU(2) one-link coherent-event conditional suppression ≤min(1,3exp(-beta r/2))
- **D1-COH-05** volume-independent original coherent-bad connected animal tail with explicit 196q^(1/19)<1
- **D1-FRU-01 (HARD)** source-true joint frustrated-staple connected-polymer activity/entropy bound, not one-link pressure/Markov
- **D1-FRU-02 (HARD)** mixed coherent/frustrated contour decomposition, fixed physical-block scaling, actual original CMP116 marked-source applicability and full Wilson covariance decay
- **E1.03/D2-OS-03/N1.02/G1.03 (HARD)** unchanged original continuum, dense-OS decay, noncollapse and group-complete physics.

**Verification:** the proof above is analytic mathematics; companion explicit lattice-incidence/greedy-packing script covers concrete 4D periodic source geometry and bounded combinatorics. Neither this document nor a finite regression is a native Agda 2.9 kernel proof. The original full-Clay mass gap remains unsolved.
