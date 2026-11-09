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
