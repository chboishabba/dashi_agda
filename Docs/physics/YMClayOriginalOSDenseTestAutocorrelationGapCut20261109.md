# Yang–Mills D2 physical max-cut: dense OS tests + one common Euclidean-time exponent

Date: 9 November 2026. Analytic spectral theorem, not a proof of interacting four-dimensional YM or an original Wilson physical estimate.

## The smallest sufficient original-source D2 theorem

Fix the **same** OS-reconstructed Hilbert space `H_OS`, vacuum `Omega`, self-adjoint Hamiltonian `H>=0` and strongly continuous time semigroup `e^{-tH}` arising from the *actual* E1 continuum Euclidean Yang–Mills Schwinger family. Let `H_0=Omega^perp`, with the appropriate uniqueness/no-extra-zero-modes source fact. Suppose:

1. `D` is a linear subspace of **the actual OS cylinder-generated nonvacuum vectors**, norm-dense in `H_0` (the zero-vacuum projection is removed).
2. There is a single `m>0` such that **for each** `psi∈D` there exists a finite `C_psi>=0` satisfying the *original physical-time autocorrelation bound*
   `0<= <psi,e^{-tH}psi> <= C_psi exp(-mt)` for all real `t>=0`.
   **The exponent m is common; the prefactor C_psi is allowed to depend on psi.**
3. This is exactly the **same** `H` reconstructed from E1; no selected auxiliary transfer matrix or invisible direct-sum sector.

Then the full nonvacuum spectrum satisfies
`sigma(H|H_0) subseteq [m,infinity)` (with the usual closed-spectrum interpretation), hence the physical spectral gap is at least `m`.

## Proof (spectral theorem, no extra all-sector oracle)

For every `0<=lambda<m`, write `E_lambda=1_[0,lambda](H)|H_0` for the positive spectral projection. By the self-adjoint positive-semigroup spectral theorem,

```
e^(-lambda t) ||E_lambda psi||²
  <= <psi,e^(-tH) psi>
  <= C_psi e^(-mt).
```

Therefore `||E_lambda psi||² <= C_psi e^(-(m-lambda)t)`. Sending `t->infinity` shows `E_lambda psi=0` **for every psi in the dense source D**. Because orthogonal projections are bounded operators, `E_lambda=0` on **all** `H_0`. Let `lambda↑m`, using the spectral resolution/monotone convergence; every spectral projection in `[0,m)` vanishes. Hence `sigma(H|H_0)∩[0,m)=∅`, proving the full nonvacuum gap.

Notice that the proof does **not** assume a source uniform bound `C||psi||²` for every Hilbert-space vector. Separate “every subgap eigenvector is seen by a chosen Wilson test” and “no continuous subgap spectrum” lemmas are both consequences of **dense source tests + same exponent**. This is the correct response to the earlier negative control with an invisible slow sector: a family living in a proper summand is NOT dense in the full OS `H_0`.

## Exactly what remains source-uninhabited

**D2-OS-01:** original E1 Schwinger limit reconstructed to the same `H_OS,Omega,H` and physical time scale, with nonnegative spectrum and correct nonvacuum `H_0`.

**D2-OS-02:** prove genuine OS cylinder-state density `closure(span D)=H_0` from the actual original positive-time gauge-invariant observable algebra. The GNS/OS construction commonly makes cyclicity automatic for its *chosen* observable algebra, but this must be the **complete relevant physical observable sector**, not an arbitrarily selected smaller family.

**D2-OS-03 (decisive physical estimate):** prove the common physical-time exponent `m>0` for ALL `psi∈D`, allowing `C_psi` to depend on the source vector, and establish that it survives original UV/IR scaling. A spatial-rooted-shell bound must be transported to exactly these same time tests through the actual Euclidean symmetry/OS source; static bare-link suppression is not this theorem.

**D2-OS-04:** prove vacuum uniqueness/no extra zero-energy sectors and the appropriate Clay interpretation, together with N1 noncollapse in the SAME E1 continuum. If zero-energy degenerate vacua remain, a gap on the selected `Omega^perp` must not be claimed.

**Reuse, do not duplicate:** `DASHI/Physics/YangMills/BalabanOSExponentialClusteringImpliesHamiltonianGapExact.agda` already exposes `OSExponentialClusteringImpliesHamiltonianGap` by consuming the genuine `Gap.OS4SpectralInterpretation` and `Limit.Clustered`. The existing `BalabanUniformPhysicalMassGapAnalyticInhabitation.agda` lists dense physical observable vectors and the semigroup-to-spectrum implication. They are conditional until the original-source inputs above are genuinely constructed; the weak `Set` fields themselves cannot do that.

**High-alpha relationship with D1:** The original physically uniform full-Wilson connected covariance estimate is only one possible way to produce D2-OS-03. Once it provides the same E1 physical-time correlations with a common exponent and all dense OS cylinder tests, the spectral exclusion in D2.04 is **standard calculus**, not an independent nonperturbative estimate. Thus focus analytic work on E1.03, D1.03 and D2-OS-02/03, not a redundant all-modes spectral oracle.

Attribution: Osterwalder–Schrader reconstruction; self-adjoint spectral theorem; Penrose–Lebowitz decay literature; existing DASHI original OS/transfer owners. No new claim of four-dimensional YM existence or Clay mass gap.
