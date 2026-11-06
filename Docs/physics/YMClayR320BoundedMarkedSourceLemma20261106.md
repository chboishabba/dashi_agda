

### Native original finite-source implementation (6 November follow-on)

`DASHI/Physics/YangMills/YMClayOriginalWilsonAffineMarkedPartitionExact.agda` now defines the *actual unnormalized* variable-cutoff original SU(N) Wilson product-Haar marked source, not an independently supplied response oracle, and source-writes:

[
Z^{\mathrm{aff}}_{n}(s,t)
=\int \rho_n(U)(1+sF(U))(1+tG(U))\,dH_n(U)
= Z_n+sN_n(F)+tN_n(G)+stN_n(FG).
]

The source terms `originalAffinePartitionIsExactNumeratorPolynomial` and `originalNormalizedAffineIsLiteralMomentPolynomial` derive the corresponding unnormalized and normalized polynomial equalities from the pre-existing actual original product-Haar integration laws and real-division algebra. Thus, where the selected real division has its **standard positive-denominator field laws**, the actual finite normalized source has coefficients (1,E_nF,E_nG,E_n(FG)). The already existing normalized-cumulant proof then derives (\partial_s\partial_t\log Z(0,0)=\mathrm{Cov}_{\mu_n}(F,G)). For a bounded *exponential* marked source the same Taylor coefficients follow by the finite compact-Haar dominated-convergence proof already given above. No fresh source-independent calculus or "finite derivative mystery" is required.

This is not the full CMP116 *localized renormalized* source application: CMP119/122's E/R/B/V/ghost/background effective density, exact selected polymer root/support, uniform marked localization, physical-rate calibration, RG crossing positivity and continuum/OS limit still require the source-specific proofs. Source-written Agda is not a green kernel receipt.

# R320 bounded marked-source theorem — 6 November 2026

**Scope:** rigorous finite continuous-SU(N) Wilson–Gibbs mathematics for two bounded plaquette marks. No Agda kernel receipt, CMP116 rooted-shell estimate, UV/IR limit, OS gap or Clay theorem is asserted.

For any finite four-dimensional periodic lattice, real compact G=SU(N), normalized Borel Haar H and real continuous Wilson action S, let
[
dmu_Lambda(A)=Z_Lambda(0,0)^{-1}e^{-S_Lambda(A)}prod_{ein E_Lambda}dH(A_e).
]
The action and original Gibbs state must be **the same selected source**; substituting pure Wilson S for additional CMP119 E/R/B/V terms requires a separate physical identity. The positive finite partition follows by compactness and positivity of the exponential.

For plaquette holonomies U_p,U_q, define F_p=1-ReTr(U_p)/N and F_q=1-ReTr(U_q)/N. Both marks belong to [0,2]. Introduce the *same-source* marked partition
[
Z_Lambda(s,t)=int e^{-S_Lambda(A)+sF_p(A)+tF_q(A)}prod_e dH(A_e),quad M_Lambda(s,t)=Z_Lambda(s,t)/Z_Lambda(0,0).
]

## Theorem A: a cutoff- and volume-independent bounded-mark source domain

For complex s,t,
[
|M_Lambda(s,t)-1|le e^{2(|s|+|t|)}-1.
]
Proof: |exp z - 1| ≤ exp |z| - 1, |sF_p+tF_q| ≤ 2(|s|+|t|), and integration against the normalized positive mu_Lambda. Thus whenever |s|+|t| < log(2)/2 the function M never vanishes, lies in the disk |z-1|<1, and has a canonical holomorphic logarithm. Differentiation under the finite compact-group integral is valid by bounded domination. The same source domain works for *every* cutoff, volume, beta and pair of plaquettes. For general bounds |F|≤M_F and |G|≤M_G the sufficient domain is |s|M_F+|t|M_G<log 2. **These hypotheses do not cover unbounded, cumulatively summed or cutoff-renormalized sources without further uniform bounds.**

## Theorem B: actual mixed logarithmic derivative

At s=t=0,
[
partial_spartial_tlog Z_Lambda
=langle F_p F_qangle_{mu_Lambda}
-langle F_pangle_{mu_Lambda}langle F_qangle_{mu_Lambda}.
]
Proof: Z_s=Z_0 E F_p, Z_t=Z_0 E F_q and Z_st=Z_0 E(F_p F_q), so partial_{st}log Z=Z_st/Z-Z_s Z_t/Z². All expectations are of *one* selected mu_Lambda; an independent covariance source cannot replace it.

## Theorem C: cutoff-uniform but nondecaying bound

Popoviciu gives Var(F_p),Var(F_q)≤1 since both range over [0,2]. Cauchy–Schwarz yields
[
|partial_spartial_tlog Z_Lambda(0,0)|=|Cov_{mu_Lambda}(F_p,F_q)|le1.
]
This does **not** pay R320.P04/P05: no positive mass or dependence on physical distance follows.

## Negative control N01

On the two-point positive law with weights (1/2,1/2), take F=G=(0,2). Then Cov(F,G)=1, independent of any nominal separation assigned to two marks. Fixed C,m>0 cannot satisfy 1≤C exp(-m d) for all arbitrarily large d. This is an *abstract nonpromotion example*, not a pure Yang–Mills counterexample.

## Exact acceptance frontier

- **R443→R320:** identify actual continuous SU(N) Borel Haar, real matrix trace, selected CMP119 E/R/B/V Gibbs density and marked source on the same original lattice. Current Agda real/Haar authorities are conditional/postulated.
- **R320.P01/P02 restricted:** ordinary mathematical theorem now supplies finite differentiability and a common complex local source domain for uniformly bounded individual plaquette marks only. **Native Agda and full original mixed-J marked classes remain unproved.**
- **R320.P03–P05:** physically selected CMP116 differentiated rooted-shell exponential decay with cutoff/volume-uniform constants and distance units is OPEN.
- **R320.P06/R333:** same reconstructed Hilbert space, common physical Hamiltonian and spectrum, RP/OS through limits and strictly positive gap remain OPEN.
- **Verification:** `scripts/check_ym_r320_bounded_source_exact_reference.py` tests 25,000 random positive rational finite-state measures, exact mixed log coefficients, the sharp covariance bound and perfect-correlation negative controls. Arithmetic tests are not an analytic or Agda proof.

Provenance: standard Haar existence on compact groups, Wilson lattice action, dominated convergence, connected cumulants, Popoviciu and Cauchy–Schwarz. This module isolates a reusable source calculus boundary; it is **not** a Clay solution.