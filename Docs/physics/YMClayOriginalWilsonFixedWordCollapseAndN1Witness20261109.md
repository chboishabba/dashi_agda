# E1/N1 exact source: fixed-length original Wilson plaquette words collapse along beta→infinity

Date: 2026-11-09. A finite-original-Wilson *negative/control theorem*, not an interacting R4 construction or an N1 positive witness. Owner: original changing-cutoff all-length gauge-invariant word compiler `DASHI/Physics/YangMills/YMClayE1D1OriginalVariablePlaquetteWordsExact.agda`, original normalized Wilson Gibbs measure `YMClayOriginalVariableWilsonCovarianceSourceExact.agda`.

## Same-source SU(2) theorem (all actual finite volumes)

Use the original normalized four-dimensional SU(2) Wilson measure \(\mu_{\beta,L}\) and bounded real plaquette traces \(t_p=\frac12\mathrm{Re\,Tr}(U_p)\in[-1,1]\), including arbitrary duplicated/repeated plaquette symbols in original word \(w=(p_1,\dots,p_k)\). Define the **original** gauge-invariant cylinder test \(W_w(U)=\prod_{j=1}^k t_{p_j}(U)\), with \(W_{[]} = 1\). This is precisely the `originalWordObservable` semantics already in the repository, not a fresh random process.

For any real numbers \(z_1,\dots,z_k\in[-1,1]\), telescoping and \(|z_i|\le1\) give
\[
\left|1-\prod_{j=1}^k z_j\right|
\le\sum_{j=1}^k |1-z_j|
=\sum_{j=1}^k (1-z_j).
\]
Since also \(|1-W_w|\le2\), the pointwise square obeys
\[
|1-W_w|^2\le 2\sum_{j=1}^k (1-t_{p_j}).
\]
Taking expectation under the *same original Wilson Gibbs measure*, whose periodic symmetries give the same plaquette deficit expectation at every plaquette (even when the word repeats a plaquette), and using the previously proved original pressure/Haar estimate, for \(\beta\ge16\):
\[
\boxed{
\mathbb E_{\mu_{\beta,L}}|W_w-1|^2
\le 2k\,\frac{8+\frac23\log24+\log\beta}{\beta}.
}
\]

The original real connected variance is also controlled:
\[
\boxed{
0\le \mathrm{Var}_{\mu_{\beta,L}}(W_w)
\le\mathbb E_{\mu_{\beta,L}}|W_w-1|^2
\le2k\,\frac{8+\frac23\log24+\log\beta}{\beta}.
}
\]
Proof of the variance inequality: the mean minimizes \(\mathbb E|W-c|^2\) over real constants \(c\), so taking \(c=1\) gives an upper bound. Equivalently, expand \(\mathbb E(W-1)^2-(\mathbb EW-1)^2=\mathrm{Var}(W)\).

The bounds hold **uniformly in finite lattice volume, original site count, and choice of the k actual plaquette positions**, without assuming independent or nonintersecting plaquettes. They apply to any bounded \(k\)-length original changing-cutoff word selection; the test functions can change position with cutoff.

## Exact consequence for interacting-continuum and N1 proof design

Along **any selected Wilson sequence** \(\beta_n\to\infty\), for every fixed k:
\[
\mathbb E_{\mu_{\beta_n,L_n}}|W_{w_n}-1|^2\to0,
\qquad
\mathrm{Var}_{\mu_{\beta_n,L_n}}(W_{w_n})\to0
\]
uniformly over word selections \(|w_n|\le k\). Thus **NO such fixed-length bare plaquette-trace product can certify N1.02 noncollapse** as a continuum random observable in its unrenormalized normalization.

This is **not** a proof that the continuum theory is trivial. As the physical lattice spacing \(a_n\to0\), a loop approximating a fixed physical contour generally uses a growing number of links; `k_n` may grow. The bound \(2k_n C(\beta_n)/\beta_n\) becomes noninformative unless \(k_n=o(\beta_n/\log\beta_n)\). Likewise, field-strength composite renormalization may magnify a vanishing bare plaquette signal. The finite fixed-degree cylinder algebra is not the same as the full renormalized local observable algebra.

### Specific max-cut for E1 and N1

- **E1-LOC-01:** construct the actual refining **fixed physical support** loop/plaquette composite family in `YMClayE1D1OriginalVariablePlaquetteWordsExact`; do not keep a bounded number of UV plaquette factors and call their limit interacting
- **E1-CONV-01:** prove the original all-multiword Schwinger expectation Cauchy/convergence theorem under the real Wilson measure on the UV/IR trajectory, including reflection positivity/covariance and QFT regularity
- **N1-WIT-01:** choose a physically renormalized original changing-cutoff observable \(F_n\) and prove a same-source **nonzero lower bound** \(\liminf\mathrm{Var}(F_n)>0\) or another nontrivial connected Schwinger witness. A fixed k bare plaquette product cannot do it when beta→infinity
- **N1-WIT-02:** identify that witness with the **same** E1 Schwinger limit, excluding counterfeit independent observable carriers
- **D1-FRU-01:** prove original connected frustrated-staple contour suppression, as specified in `YMClayOriginalWilsonCoherentConnectedPolymerPacking20261109.md`
- **D2-OS-03:** recover a physical-time exponential decay rate for a dense full OS cylinder family in precisely the E1 limit
- **G1.03:** supply these E1/D2/N1 witnesses for every chosen compact simple group, not just the finite Haar pressure theorem.

## Group extension

For each fixed compact simple G with faithful unitary normalized Wilson trace \(t_\rho(U)\in[-1,1]\), the existing group-dependent finite pressure bound `YMClayCompactSimpleOriginalWilsonFiniteHaarPressure20261109.md` yields the identical telescoping result:
\[
\mathbb E_G|W_w-1|^2\le 2k C_G(\beta)/\beta
\]
with the group-specific original source constant \(C_G(\beta)=8L_G^2+\frac23\log(1/c_G)+\frac{\dim G}{3}\log\beta\). This is a *finite original G1.02 / N1 no-go*, not the all-group continuum N1 witness.

Attribution: Wilson finite gauge theory, finite Haar pressure convexity and elementary bounded-product inequality. Agda original all-length word source exists, but this analytic inequality has not been kernel checked in the source real-inequality APIs. No Clay endpoint is claimed.


## Exact original two-word covariance and D2 nonvacuity corollary

Let `w,v` be any two original source plaquette words, of lengths `k,l`, and let `C_beta=8+(2/3)log24+log beta`. The original connected covariance is precisely the `YMClayOriginalVariableWilsonCovarianceSourceExact` same-measure covariance (and matches the finite mixed formal source jet). Ordinary Cauchy–Schwarz in `L²(mu_beta)`, the already proved fixed-word variance bounds, and no assumption on *any* spatial separation yield

```
|Cov_{original Wilson}(W_w,W_v)|
  <= sqrt(Var(W_w) Var(W_v))
  <= (2 C_beta/beta) sqrt(k l),   beta>=16.
```

This holds uniformly over periodic finite volume, source plaquette positions and their separation, even if the words overlap or repeat. It is a **genuine original two-word connected-covariance amplitude inequality**, not a physical exponential-in-distance bound (the RHS has NO distance factor). It is also not the original CMP116 analytic differentiated-source identity, which remains a separate source theorem.

**D2 original-sector nonvacuity consequence:** along `beta_n→∞`, every bounded-length bare plaquette word has `Var(W_w)→0`, so its mean-subtracted original `L²` vector collapses. If the E1 OS continuum cylinder map identifies those centered words with vectors in the OS Hilbert space via reflection-positive correlations, their norms must be handled carefully: a vector whose norm tends to zero cannot detect an invisible subgap spectral sector. Therefore using only fixed-length original bare words as the claimed *dense* nonvacuum test family would be a false D2 proof, even if a fast-decay estimate for their vanishing correlators were available. The actual D2-OS-02/03 must use renormalized physical-scale observables with noncollapsed continuum vectors. Source-normalization, reflection and reconstruction still must be proved before asserting actual OS null vectors.

**G1 extension:** the same bound holds for each fixed compact simple G with the group-specific `C_G(beta)` from the finite Haar pressure theorem, once true Hilbert-space Cauchy–Schwarz is used on the original normalized finite Wilson probability measure. No universal uniform-in-G constant is asserted.

This clarifies why D1 small amplitude + E1 weak cylinder convergence is not the Clay full-sector mass gap. Physical-time exponent and nontrivial OS test density must both be source-proved.
