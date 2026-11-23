# YM P0 / W3 — exact normalized fifth exterior F19 four-moment calibration against CMP119/122

23 November 2026. **Original Wilson source first**, at the original L=4,d=2 periodic 4D SU(N) fine lattice with 1024 links, 1536 plaquettes, eight activated tube walls, transverse sections H0,H1,H2, and 1525 exterior spectators. This note advances the existing fifth-order cube result into a normalization-sensitive *necessary source-identity test* on the original physical F19 1/F/G/FG integration. **It does not instantiate the historically selected Bałaban CMP119 (2.18) admissible domain sequence or CMP122 (1.71) T^(j) operator and does not prove tau>0 W3.**

## Already-owned source: DO NOT duplicate

Current master contains these exact source-first owners:

- YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact.agda: original 64 ordered noncommutative pairs, 896 genuinely interacting spectators, four weighted fine 1/F/G/FG integral transport under the *same* actual Wilson weight, valid for arbitrary fine integrands.
- YMClayW0OriginalF19CandidateEquation171TExact.agda: a *finite original Haar* candidate inhabiting the generic Equation171 T semantic interface by the original F19 conditional fibre integral. It is **not** demonstrated to be the historical CMP122 localized constrained T.
- YMClayW0OriginalF19CandidateEq171FiniteT20261123.md: precise scope of that previously existing candidate.
- BalabanCMP119Equation218FactorizedFunctionalDensityExact.agda: actual fields for admissible domain sequences, disjoint components, ordered steps and residual; physical source-index extraction conditional.
- BalabanCMP119Equation171WeightedStepApproximationExact.agda: sourceStepIsEquation171Mass is **a field to be inhabited**, not an already-supplied identification.
- BalabanCMP122Equation171TOperationSemanticsExact.agda: local T mass is the *result of an integral*, not a renamed effective action.
- YMClayW0TPathGeometryRepair20261123.md: correct shared intermediate path state, not independently integrated T-step products.
- YMClayW0OriginalFineF19FourMomentCone20261123.md: positive four-column constraints, necessary but not sufficient for original-source identity.
- Docs/support/reference/balaban-source-extracts/cmp119-rg-lattice-gauge-i.txt, historical CMP119 pp.254–258: actual Omega/Lambda and internal S, background/gauge fixing, ordered T and R-modified step path.

**The next physical target is a selected-domain T-source equality, not another generic fibre integral or positivity adapter.**

## 1. Split the physical restoration source into section and exterior parameters

For common wall beta, define the actual original source (all original native Wilson plaquette words)

\[
d\mu_{\tau_s,\tau_e}\propto \exp\left(
\beta\sum_{q\in T}t_q+
\beta\tau_s\sum_{k=0}^{2}t_{H_k}+
\beta\tau_e\sum_{p\in E}t_p\right)\,dH^{1024},\quad |E|=1525.
\]

The two *globally unique* original fine marks used by W0 are **deficits**
\(F_d=1-t_F,\; G_d=1-t_G\), not functions of the 64 coarse blocks W alone. The identity
Cov(F_d,G_d)=Cov(t_F,t_G) is exact for every source measure.

At \(\tau_s=0\), write \(u=\tau_e\), and use the original Wilson weight plus marks *inside the same F19 integration* to define four unnormalized coefficients:

\[
A(u)=Z_0(u),\ B(u)=Z_{F_d}(u),\
C(u)=Z_{G_d}(u),\ D(u)=Z_{F_dG_d}(u).
\]

Then for the original **global** partition (after integrating over all coarse W and the original F19 fibres)

\[
\mathcal C(u)=\partial_s\partial_t\log[A+sB+tC+stD]_{s=t=0}
=D/A-BC/A^2.
\]

At u=0 the original wall-only transfer gives B0=C0=A0 and D0=A0(1+Gamma0), Gamma0=v_N m_N(beta)^8. No replacement conditional or coarse-only mark is permitted.

## 2. Extensive vacuum insertions at orders 2 and 3 — exact source check

Each of the 1525 exterior faces has at least three links outside the original wall+section support. Two distinct positive original plaquettes share at most one native link. At tau_s=tau_e=0, t_p has Haar mean zero, t_p² has mean v_N, and t_p³ has mean h_N *independently of the wall-weight source* via a private Haar link. Pairwise distinct exterior faces have enough private links to give zero mixed first-order products.

Consequently, for the genuine original Wilson source,

\[
\boxed{\frac{A(u)}{A_0}=1+\frac{1525}{2}\beta^2v_Nu^2+
\frac{1525}{6}\beta^3h_Nu^3+O(u^4).}
\]

For SU2, the second term is (1525/8)beta²u²; for SU3, it is (1525/36)beta²u² and the cubic term is (1525/648)beta³u³. These source-normalizer coefficients are extensive and are **not** connected W3 activity. Taking raw marked numerators without the same Z0 creates a spurious order-2 connected term.

## 3. Actual four-column fifth coefficient, including source normalization

Let A_n,B_n,C_n,D_n be ordinary Taylor coefficients in u of the four *global* original F19 moment integrals. Every source insertion containing <=4 exterior occurrences can be reduced by repeatedly integrating an independent Haar leaf. Thus, through n=4, each coefficient is a common scalar vacuum coefficient times its n=0 baseline: B_n=C_n=A_n and D_n=(1+Gamma0)A_n.

With the SAME globally integrated A,B,C,D, exact normalized algebra gives

\[
\boxed{[u^5]\mathcal C(u)=
\frac{D_5-B_5-C_5+(1-\Gamma_0)A_5}{A_0}.}
\]

Importantly, the correction proportional to A5 is **required**. A finite CMP119 T representation that matches the unnormalized FG column alone does not pay this normalized Wilson connected response.

The only fifth-order source-connected exterior supports are exactly 32 elementary native cube caps: 24 attach to individual active walls (3 each), 8 attach to H0,H1,H2 with multiplicities (3,2,3). For each five-face cube, continuous SU(N) fundamental Schur gluing gives integral_{five exterior faces} product t_p = v_N^4 t_q. Proper subsets have Haar leaves, so the connected seven-variable cumulant is v_N^4*kappa_mu0(t_F,t_G,t_q).

The fifth-order cube *excess columns* relative to a common vacuum factor are given below. Let P=beta^5 v_N^4, M=m_N(beta), M'=m_N'(beta), Gamma0=v_N M^8 and
U_F=v_N(3+2M^4+3M^8)=U_G (from the exact 3/2/3 native section attachment counts). After division by A0,

    delta A5 = P * (24 M)
    delta B5 = P * (24 M - U_F)
    delta C5 = P * (24 M - U_G)
    delta D5 = P * (24 M*(1+Gamma0) + 24 v_N M' M^7
                    - U_F - U_G + 8 h_N M^8).

Each raw column contains both source/vacuum and marked score terms. Their exact normalized combination is

\[
\boxed{\frac{\delta D_5-\delta B_5-\delta C_5+
(1-\Gamma_0)\delta A_5}{A_0}
=\beta^5v_N^4[24v_NM'M^7+8h_NM^8].}
\]

Here delta symbols represent *normalized by the common A0* source-relative cube additions (thus A0 is set to 1 in the displayed P expressions); the first displayed general four-column formula retains the original unnormalized A0 explicitly. Unknown common vacuum fifth-order contributions cancel identically. The same cancellation holds with arbitrary common vacuum terms through order four.

**Group calibration:** SU2 is (3/128) beta^5 M'M^7; SU3 is beta^5 M^7(M+18M')/1417176. Strictly positive for finite beta>0, SU(N), N>=2. Exactly 5! multiplies the Taylor coefficient to give the fifth restoration derivative's exterior part.

## 4. Genuine CMP119/122 Eq.(2.18)/(1.71) source-matching obligation

The existing *candidate* original-F19 entire fibre T already transports all four columns for arbitrary original fine integrands under the original SU(N) Haar/Fubini assumptions; it consequently transports these u-dependent column series as a logical specialization. **Do not count that as a physical source extraction of CMP119 T^(j).**

To certify the *historically selected* CMP119/122 source one must identify its actual Omega/Lambda/S histories (S summed WITHIN T), its conditioned intermediate link/background states, the correct disjoint components, ordered R-modified T operations, source original 896-interacting spectators, positive/complex FP/Jacobian/ghost/source action and E/R/B/V plus original vacuum normalization. After the actual source histories and disintegrations are fixed, compare the complete four global columns A_n,B_n,C_n,D_n, at least n=0..5, with their genuinely original F19 Wilson values. The necessary nontrivial new calibration is the **fifth connected identity above**, not merely low-order vacuum and four-column positivity.

A candidate that only multiplies all four Wilson baseline columns by a common vacuum generating function V(u), even when V reproduces the source second/third vacuum jets and all four moment cones, yields [u^5]C=0 and fails because the original value is strictly positive. A candidate that drops Z0 normalization produces a false u² signal. Neither negative control is an assertion that CMP119 itself makes either error.

The preferred physical proof output is a **selected source comparison** or explicit quantitative discrepancy, not an invented same-object record field. Convergence of conditional finite Haar quadratures alone cannot show selected CMP119 T^(j), E/R/B/V or termwise absolute W3. Complete original physical beta(a)->infinity uniform small/large-field absolute rooted-shell bounds and CMP116 decay remain separate obligations.

## 5. Independent local acceptance

Locally executed Python/SymPy 1.14 [checker](../../scripts/check_ym_original_w3_fifth_normalized_f19_calibration_20261123.py):
- Native 1536/1525 census; 76/1449 outside-link geometry; two distinct source faces share <=1 link.
- Exact 24+8 attachment/3-2-3 section multiplicities.
- Exact second/third vacuum coefficients and full symbolic fifth four-column cancellation including all first-score terms.
- Formal truncated-power-series equality for arbitrary common vacuum coefficients a2,a3,a4,a5 and normalized connected orders 1..4 vanishing.
- Independent exact SU2/SU3 substitutions and explicit wrong-normalization / missing-connected-channel negative controls.

Source checker committed and read back via connector; exact uploaded bytes are **not** independently executed after upload. Agda kernel/CI not run. The continuous SU(N) cube source identity is based on analytic Haar/Schur orthogonality rather than any finite Q8 replacement.

**Status: normalized original-Wilson/F19 fifth-order calibration PASS; historically selected CMP119/122 T-source identification OPEN; all-tau / UV cutoff uniform W3, CMP116, E1/D1/D2/N1/G1 OPEN.** Prior Wilson/Haar/Bałaban source attribution and DASHI original F19 owner precedence retained.
