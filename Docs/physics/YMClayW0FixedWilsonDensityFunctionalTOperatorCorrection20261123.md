# YM W0 — one fixed Wilson/F19 conditional T, observables 1/F/G/FG (23 November 2026)

## Construction correction rather than duplicate machinery

The preceding W0 original F19 candidate `YMClayW0OriginalF19CandidateEquation171TExact.agda` instantiated an existing generic `CMP122Equation171TOperationSemantics` record **separately for each integrand**. Those individual finite identities reused the correct F19 arbitrary-integrand theorem, but the record representation could falsely suggest that each marked observable defines a physically different exponential density / Eq.(1.71) T. Worse, a spectator-marginal of a marked integrand is not generally the pure localized source exponential designated by the record's field `equation171ExponentialDensity`.

**Fix implemented in the existing module:** select one `sourceFixedWilsonDensity` (the already-built original physical sorted 1024-link SU(N) Wilson weight, 64 ordered pairs + 896 interacting spectators); expose one `sourceFixedWilsonT : FineTest -> SlowField -> Real` defined from the original fixed positive Wilson weight and existing F19 conditional-Haar fibre operator. Define `sourceFixedWilsonTTwoMarks` with the original source multiplication association and without factorizing the two fine marks. Wire `sourceKF` and `sourceKG` to the SAME single-observable T, and `sourceKFG` to its retained mixed insertion; `sourceK0` is the original unmarked fixed-weight mass. `originalF19UnmarkedEquation171` now selects only the physically unmarked Wilson integrand into the generic Eq171 source-carrier, with `sourceK0IsUnmarkedEq171 = refl`. All four original fine/F19 Haar equality terms remain present and use the existing *one* arbitrary-integrand F19 proof, not four different Wilson measures.

Geometric meaning, at original fixed 64-link W with the 896 spectator links H integrated inside:

[
T_W[h] = \int dH^{64}_{V}\, dH^{896}_{S}\, e^{-S_W(WV^{-1},V,S)}h(WV^{-1},V,S),
qquad K_0=T_W[1],;K_F=T_W[F],;K_G=T_W[G],;K_{FG}=T_W[FG].
]

The original global fine-mark covariance `KFG/K0-(KF/K0)(KG/K0)` remains in the same conditional fibre. The theorem does not pretend that F/G are coarse-only test functions. The actual original source selected SU(N) group multiplication and Haar assumptions are those of F19; no independent rational quadrature or new functional laws added.

The old generic `originalF19CandidateEquation171 integrand` is still a legitimate **interface-level scalar evaluator** but should **not** be cited as proof that the marked integrand is the literal CMP122 Eq.(1.71) exponential. The unmarked instance itself is also only a *candidate structural mass*; the actual source-localized exponential, proper Omega/Lambda/S domains, R-modified characteristic functions, FP/gauge fixing, determinant/Jacobian, active running beta and E/R/B/vacuum normalization still need actual original-source identification. Nat cutoff remains inert for this side-four single-cutoff candidate. The chosen coarse W is the original R445 64-link block carrier, not automatically the multiple source CMP119 scale domain B.

## Independent finite rational functional check

`scripts/check_ym_w0_fixed_density_functional_four_marks_20261123.py` uses a **single fixed nonfactorizing positive four-corner measure**, with weights (2,1,3,4) on (F,G)=(0,0),(0,2),(2,0),(2,2). The exact values are `K0=10, KF=14, KG=10, KFG=16`; covariance numerator `K0*KFG-KF*KG=20`, so it detects illegal `KFG=KF*KG/K0` normalization. Exact affine polynomial holds for all 9 rational (s,t) probes at -1/10,0,1/10 and positive four-column cone. This is an illustrative finite positive law, **not SU(N) Haar or a test of Bałaban's source itself**.

The independent local Fraction calculation passed 9/9 probes, plus cone and covariance checks. The committed checker has GitHub readback; exact byte-for-byte checkout execution was not done. The Agda code remains source-written, not kernel-accepted.

## Updated W0 max-cut

Reuse P10/P11 nested owner, `BalabanCubeEdgeDomains`, Gate4 collar, P3 constrained integral, CMP119 (2.18)-(2.22) ordered steps and Eq171 weighted-limit owners, and the original F19 arbitrary-integrand theorem. Only attach the **real** CMP119 source-local (T^{(j)}) and its intermediate conditioned domain histories to the original same-operator four-mark F19 source. Preserve `S_j` summation inside `T_k` and its genuine noncommutative Wilson weight and unique marks. The local Eq171 comparison must be a theorem, not a chosen record equality; W3 rooted-shell SI-rate and OS physical spectral gap remain unpaid.

Attribution: Wilson/Haar, Bałaban CMP119/122, existing DASHI original R445/F19/CMP119 and T authors.
