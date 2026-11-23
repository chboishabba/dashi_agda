# YM P0 — original Wilson affine W1/W3 bad-sector mixed jet and physical rate

22 November 2026. Original sources are already present; do not reconstruct a separate lattice Wilson measure, a new polymer gas, P06 animal enumeration, KP/FP or CMP116/119/122/W1/W3 compiler. This source cut responds to the older exponential-source bad-event note and selects the **existing rational two-source affine Wilson marking** instead. Source audit: BalabanLiteralTwoWilsonAffineSourceBoundExact, BalabanLiteralTwoWilsonAffineMarkedActivityExact, BalabanLiteralTwoWilsonSourceFirstKPDataExact, BalabanLiteralTwoWilsonSourceFirstNormalizedJetExact, BalabanLiteralTwoWilsonSourceFirstJetLocalizationExact, BalabanLiteralTwoWilsonCMP116ConnectingTailExact and YMClayD1OriginalFullWilsonSmallLargeFieldExact.

## 1. Actual original Wilson affine partition / event identity

Use the original finite SU(N) positive product-Haar Wilson Gibbs measure mu at any admissible cutoff and volume. F,G are bounded real **gauge-invariant closed Wilson words** with |F|,|G|<=1. B is a measurable original source bad event (not an independently sampled bad link); let A=B complement. Choose |s|,|t|<=r=9/100 as in the existing affine source. The true source deformation is

    M_st(U)=(1+s F(U))(1+t G(U))

with strict pointwise bound (1-r)^2<=M_st<=(1+r)^2. Define

    Z(s,t)=E_mu[M_st], Z_A(s,t)=E_mu[1_A M_st],
    Z_B(s,t)=E_mu[1_B M_st], p(s,t)=Z_B/Z.

For p(0,0)<1 the good-sector Z_A is strictly positive throughout the source square. All formulas below are for the same original Gibbs measure and original marks, with NO new KP activity.

**Exact W1 affine jet identity**, wherever Z_A>0:

    log Z - log Z_A = -log(1-p),
    d_s d_t(log Z - log Z_A)
      = p_st/(1-p)+p_s p_t/(1-p)^2.

At s=t=0, mixed derivatives of log Z and log Z_A are precisely Cov_mu(F,G) and Cov_{mu(.|A)}(F,G), respectively. This is exactly the normalized two-Wilson covariance jet wanted at the original source. At nonzero source, mixed log derivatives instead correlate the score observables F/(1+sF) and G/(1+tG): do NOT call these the unmodified F,G covariance.

The finite source remains positive, with p_st notation reserved here for mixed derivative only when explicitly written as d_s d_t p; otherwise p(s,t) means event probability.

## 2. Source-uniform bounds and exact origin covariance error

For the marked probability p(s,t),

    0<=p(s,t)<=min(1, [((1+r)/(1-r))^2] p(0,0))
              = min(1,11881/8281 * p(0,0)),
    |d_s p(s,t)|,|d_t p(s,t)| <= 2 p(s,t)/(1-r),
    |d_s d_t p(s,t)| <= 5 p(s,t)/(1-r)^2.

Proof: the log-scores of the affine source are H_s=F/(1+sF), H_t=G/(1+tG), |H_j|<=1/(1-r), and cross differentiation of log M is zero. Therefore d_s p=Cov(1_B,H_s), and d_s d_t p=E[1_B(H_s-E H_s)(H_t-E H_t)]-p Cov(H_s,H_t). Bound the first factor by 4p/(1-r)^2 and the second by p/(1-r)^2. This is finite compact-group probability calculus; no analytic polymer expansion is used.

When p(s,t)<1 let nu_st=mu_st(.|A), where mu_st has the original M_st weight. The full-versus-good *ordinary F,G covariance* bound from the previous note remains

    |Cov_mu_st(F,G)-Cov_nu_st(F,G)| <= 6 p(s,t)
                                   <= (6*11881/8281) p(0,0).

At the unmarked origin the exact affine log-jet remainder above equals Cov_mu(F,G)-Cov_nu(F,G) and is bounded by 6p(0,0). This is an actual original Wilson BAD-SECTOR error, not the assertion that the GOOD conditioned covariance equals Bałaban CMP116 small field.

## 3. CONDITIONAL physical rate for the existing microscopic bad-contour tail

Reuse original 19/20 November SU2 even-torus Wilson site-reflection/chessboard fixed-contour estimates, **only after native Wilson reflection/dissemination applicability is established**. Suppose the actual marked physical event B_{X,Y} is included in a union of rooted original bad-link animals with at least m=ceil(R/a) links, where R=d_phys(X,Y)>0 and a is the *actual positive fine link spacing in metres*. Assume at the selected beta(a) and all volumes an original uniform fixed-contour probability <=u(a)^n with 0<=q(a)=196u(a)<=q_*<1 (source-specific RP/chessboard application, not an inferred theorem), and at most M(a)<=C_root a^{-D} admissible roots for D>=1.

Existing degree-14/DFS animal count gives each rooted spanning event

    P(rooted bad animal of size >=m)
      <= u(a)*q(a)^(m-1)/(1-q(a))
      = q(a)^m/[196(1-q(a))].

Thus the all-root union has actual original-source bound

    p_00(B_XY) <= C_root/[196(1-q_*)] * a^(-D) * exp(-kappa R/a),

where kappa=-ln q_*>0. Fix an actual physical interval 0<a<=a0 with a0>0 and remote supports R>=R_min>0. Optimize x^D exp(-kappa R x/2) over x=1/a>0 at x=2D/(kappa R). This yields **the explicitly uniform BAD-EVENT physical rate**

    p_00(B_XY) <= A_bad exp(-m_bad R),

    A_bad = C_root/[196(1-q_*)] *
              [2D/(e*kappa*R_min)]^D,
    m_bad = kappa/(2*a0) > 0 [m^-1].

A_bad is dimensionless when C_root carries the natural [m]^D units; m_bad is SI inverse length. At marked sources the previous factor 11881/8281 bounds p(s,t), so the ordinary original full-versus-good covariance error is <=(6*11881/8281) A_bad exp(-m_bad R), if the source-defined event meets the assumptions. This constructs **explicit physical calibration from a CONDITIONAL MICROSCOPIC BAD-EVENT tail**. It neither derives the beta(a) trajectory nor proves that the original Wilson word support satisfies the assumed rooted animal event inclusion / polynomial root bound, and it is not the physical CMP116 marked CLUSTER estimate.

For D=4, q_*=1/4, a0=1/4, R_min=1 in chosen consistent length units, local SymPy checks 45 (a,R) pairs and analytically certifies the x^4 exponential optimizer; m_bad=ln(16) per length unit. Numerical values are illustrative conditional inputs, not the physical SU2 running-coupling data.

## 4. TRUE W1/W3 same-object negative control

The existing KP source applies affine factors to polymer activities. A global configuration Wilson mark F(U) is **not** automatically a product of independently attached polymer marks. Exact two-compatible-polymer counterexample:

    Z_original(s)=(1+a)(1+b)+s ab.

The source mark detects occupancy of *both* polymers but vanishes on the one-polymer configurations. Independently multiplying one-polymer factors instead gives

    Z_naive(s)=(1+a(1+s u))(1+b(1+s v)).

Matching the linear coefficients of a and b forces u=v=0; then the marked ab coefficient is zero, but Z_original has marked ab coefficient one. SymPy verifies the inconsistent exact linear equations. Also for SU2 quaternion i, t(i*i)=-1 while t(i)t(i)=0, so noncommutative Wilson holonomy traces cannot be naively factorized into independent trace marks. This is a *counterexample to a proposed formal shortcut*, not a counterexample to existing KP theory.

Therefore the physical W1 source payment must derive polymer activities/cluster functionals and their marked response from the SAME original Wilson partition, including cross-polymer/source insertion terms, in the precise existing source-first KP enumeration. SourceFirstNormalizedWilsonJetExpansion.normalizedPhysicalLogJetIsLiteralKPClusterJetSum is not automatic just because each local mark obeys the 6/5 radius bound. Its source-specific derivation is the remaining true interface.

## 5. Exact minimum small/large + W3 obligation

Let C_CMP116(F,G) be the existing selected small-field marked response on the source's actual analytic domain. For p_00(B_XY)<1:

    |Cov_original(F,G)|
    <= |C_CMP116(F,G)|
       + 6 p_00(B_XY)
       + |Cov_original(.|B_XY^c)(F,G)-C_CMP116(F,G)|.

This follows from the original affine jet and an ordinary triangle. A physical proof must estimate (i) selected CMP116 small-field source localization on the literal J directions, (ii) actual source GOOD-to-CMP116 response discrepancy, and (iii) same-original large-field marked event/cluster charge. The conditional BAD-EVENT rate above can pay (part of) (iii) **only once** the source's connecting event is genuinely the selected covariance remainder and its absolute marked cluster weights are dominated by that event. Without this, the existing W3 chargeSumBelowPhysicalRootedShell remains uninhabited. Do not silently set the discrepancy to zero.

Original E1 R4 nontrivial continuum/OS, one same-H full nonvacuum D2 spectral gap, N1 surviving observable and G1 all compact simple groups remain separate terminal mathematical obligations.

## Local acceptance / attribution

- scripts/check_ym_original_wilson_affine_bad_jet_w1_w3_20261122.py: **512/512** exact Q8 conditional configurations of original 1536 periodic L4 plaquette WORDS (17 affected), 25 marked affine rational settings and exact independent SymPy derivatives, log-jets and 6p bounds PASS. Committed Git blob verified against locally executed file. Discrete Q8 is NOT SU2 Haar integration.
- scripts/check_ym_original_wilson_bad_contour_si_rate_20261122.py: 45 conditional physical-grid pairs PASS, exact SymPy stationary-point optimizer. Committed Git blob verified against locally executed file. These are algebra/calibration regressions, not original-physical estimates.
- No pinned Agda 2.9 kernel, no CI, no claim of native SU2 full polymer/W3 or Clay YM completion.
- Primary prior art: Wilson lattice action and Haar; Osterwalder–Seiler/Menotti–Pelissetto Wilson RP; Fröhlich–Israel–Lieb–Simon/Biskup chessboard; Bałaban CMP116/119/122; Kotecký–Preiss and Fernández–Procacci marked polymer; original DASHI P06/Step-V, affine W1, physical W3 owners. This source adaptation and explicit conditional gap ledger does not supersede them.
