# YM P0 / W3 — first nonzero exterior restoration activity, original Wilson L4/d2

23 November 2026. Source-first continuation of [W3 first two restoration jets](YMClayOriginalSUNW3FirstRestorationShellThirdMoment20261123.md) and [third-jet exterior cancellation](YMClayOriginalSUNW3ThirdRestorationExteriorLeaf20261123.md). No replacement measure, gauge group, physical clock, or F19 integration. **This is an exact finite Wilson Haar/character and native-support calculation; NOT the CMP119/122 constrained-renormalization operation, uniform W3, continuum mass gap, or Agda kernel result.**

## 1. Original connected-activity source

Work on the original periodic side-four four-dimensional native link complex with gauge group SU(N), N>=2, Haar product links, the actual eight active Wilson tube wall plaquettes T for the two genuine Euclidean-time-separated normalized spatial plaquette traces F=H0 and G=H2, and three transverse sections H0,H1,H2. Let t_p=ReTr(U_p)/N, b_q arbitrary finite wall couplings, m_N(b)=d/db log integral_G exp(b t(U))dH(U), v_N=Haar(t^2), and h_N=Haar(t^3). The reference measure mu_0 has only T activated. The interpolation activates every other original face with tau*beta and does **not** remove F/G/FG normalizations.

By the existing original tube calculation,

\[
C_0=\operatorname{Cov}_{\mu_0}(F,G)=v_N \prod_{q\in T}m_N(b_q).
\]

For the wall face q and section H_k the source variation gives, respectively,

\[
\kappa_{\mu_0}(F,G,t_q)=v_N m_N'(b_q)\prod_{r\in T\setminus\{q\}}m_N(b_r),\qquad
\kappa_{\mu_0}(F,G,H_k)=h_N\prod_{r\in T}m_N(b_r).
\]

Here m_N'(b)=Var_b(t)>0 at finite b.

## 2. Exhaustive original-source support search: exact first exterior order

Let B=T union {H0,H1,H2}. Its complement has precisely 1,525 genuine original positive plaquettes. Exactly 76 have three native links outside support(B), and 1,449 have four; no exterior face has fewer than three.

A rooted native link-to-face closure search starts with every exterior face adjacent to B and recursively covers any external link carried by exactly one currently selected face. It permits incidences >=2 (not just even-parity surfaces, so group epsilon-style 3-fold edge contraction is not ruled out by assumption). Exhaustively, there is NO such supported set of 1,2,3,4 DISTINCT exterior faces; the supported five-face sets are exactly 32, each one the five faces of a true elementary three-dimensional cube missing exactly one face q in B. The 1,024 original elementary cubes have B-intersection counts 990 (zero), 32 (one), 2 (six); no 2..5-face intersections.

Every strictly smaller distinct exterior set has a private link in at least one of its faces. That plaquette's holonomy is Haar independent of all other selected plaquette variables and the entire wall/mark source. Therefore **any connected cumulant with F,G involving <=4 restored exterior occurrences vanishes**, including repeated faces: if any face is repeated, at most four distinct exterior faces can occur in a five-insertion term, and a private-link plaquette makes that connected cumulant vanish. For order five, the only exterior support capable of a nonzero connected cumulant is five distinct plaquettes forming one of the 32 cubes.

This is a geometric and Haar-independence statement about derivatives at tau=0. The finite search is for the selected L4/d2 source; no unproved all-L claim is made.

## 3. Exact continuous SU(N) five-face conditional cube contraction

For one of the 32 cubes, q is the sole pre-existing wall-or-section face, and P_Q is the five new exterior faces. The four exterior upper-edge group variables remain independent Haar after gauge-fixing the four vertical internal edges. The cube's five normalized traces become four side factors t(U_j) and one opposite-cap trace t(U_1 U_2 U_3^{-1} U_4^{-1} U_q) (up to cyclic orientation and inversion). For normalized real fundamental characters, standard continuous SU(N) Schur orthogonality yields

\[
\int_{SU(N)} t(AU)t(U^{-1}B)\,dH(U) = v_N t(AB),
\quad v_2=\frac14,\quad v_{N>=3}=\frac1{2N^2}.
\]

Four successive group convolutions produce the pointwise identity

\[
\boxed{\int_{\text{8 external native cube links}}\prod_{p\in P_Q}t_p\,dH=v_N^4t_q.}
\]

All nonempty proper subsets of P_Q have a private Haar link, so their joint moments with arbitrary combinations of F,G vanish. Accordingly the full seven-variable connected cumulant satisfies

\[
\boxed{\kappa_{\mu_0}(F,G,(t_p)_{p\in P_Q})=v_N^4\kappa_{\mu_0}(F,G,t_q).}
\]

The Q8 subgroup provides a **separate exact finite-group regression**, NOT the continuous SU(N) proof: gauge-fixing the four vertical edges reduces the integral to 8^4 assignments, and exact rational enumeration checks each of the eight possible boundary holonomies. Result 8/8 PASS, coefficient 1/256 at N=2, consistent with continuous irreducible SU2 spin-1/2 Schur orthogonality.

## 4. Attachment multiplicities and fifth exterior Taylor coefficient

Of the 32 cube support sets, 24 attach to the eight activated walls, exactly three per wall. Eight attach to the sections, with H0/H1/H2 counts 3/2/3. Every other 5-insertion contribution containing an exterior face vanishes in the connected cumulant, including all multiplicity patterns. Distinct ordered insertions contribute 5! times the unordered cube sum.

Let C(tau)=Cov_{mu_tau}(F,G). Define [tau^5]C|_{contains-exterior} to mean ONLY the sum of terms of the actual original finite-source fifth Taylor coefficient containing at least one exterior restored face; this is NOT a new measure. At common wall and restored-face coupling beta,

\[
\boxed{
[\tau^5]C\big|_{\mathrm{exterior}} =
\beta^5 v_N^4\left[
24v_N m_N'(\beta)m_N(\beta)^7
+8h_N m_N(\beta)^8
\right].
}
\]

Equivalently the **exterior part**, not the entire derivative, of C^{(5)}(0) is 120 times the boxed expression. All exterior contributions to the first four derivatives vanish exactly.

For continuous SU2, with m_2(beta)=I_2(beta)/I_1(beta) and h_2=0,

\[
\boxed{[\tau^5]C|_{\mathrm{exterior},SU2} =
\frac{3\beta^5}{128}\,m_2'(\beta)m_2(\beta)^7.}
\]

For continuous SU3, v_3=1/18 and h_3=1/108,

\[
\boxed{[\tau^5]C|_{\mathrm{exterior},SU3} =
\frac{\beta^5 m_3(\beta)^7}{1417176}
\big(m_3(\beta)+18m_3'(\beta)\big).}
\]

For beta>0, m_N(beta)>0 and m_N'(beta)>0, so this FIRST exterior Taylor contribution is strictly positive in every SU(N), N>=2 (the positive wall term suffices). The **complete fifth derivative** ALSO contains 3^5 purely-sectional ordered terms, not computed here; positivity of the exterior component alone does not imply any full-tau monotonicity.

This is a significant source-specific advance beyond the initial zero exterior derivatives: a concrete nonzero connected activity and its continuous-character coefficient, but not an absolute polymer sum beyond fifth order.

## 5. Why the physical CMP119/122 / CMP116 proof is still open

The derived fifth-order coefficient is pointwise at tau=0, fixed bare beta and fixed finite source. It is **not bounded uniformly** in the physical weak-coupling beta(a)->infinity scaling. Indeed for SU2, m_2(beta)=1-3/(2beta)+O(beta^-2) and m_2'(beta)=3/(2beta^2)+O(beta^-3), so the SU2 coefficient behaves as (9/256)beta^3+lower orders. For SU3 the nonzero h3 term produces a beta^5 term in this fixed-order expansion. Such growing Taylor coefficients cannot be used as a tau-in-[0,1] absolute W3 bound.

Still required: the SAME actual full Wilson fine-to-blocked F19 original source identified with CMP119/122 chosen Omega/Lambda/S operation and FP/Jacobian/background E/R/B/V marked activities (or rigorously controlled discrepancy), a source-normalized positive/complex connected-activity expansion valid along 0<=tau<=1, large-field bounds, and cutoff-/volume-uniform absolute rooted-shell entropy leading to CMP116/W3 and one same-H interacting OS construction. E1/D1/D2/N1/G1 OPEN.

## 6. Evidence and provenance

- Exact local native-incidence search: 1525 exterior count and 76/1449 split; 32/32 five-face closures; 24 wall + 8 section distribution; zero no-private-link closures of size 1..4. Verified separately using two independent search criteria (outside-edge parity and no-degree-one).
- Exact local Q8 integral: all 8 group-boundary configurations PASS, expected v2^4=1/256.
- Local SymPy 1.14: fifth coefficient algebra, both continuous-group specializations and SU2 numerical positivity checks at beta=0.1,1,3,10 PASS. The continuous SU(N) argument is analytic Schur orthogonality, not approximated by Q8.
- Source checker: [check_ym_original_w3_fifth_exterior_cube_20261123.py](../../scripts/check_ym_original_w3_fifth_exterior_cube_20261123.py). Connector committed file subsequently read back; exact uploaded bytes not separately executed. No Agda 2.9 kernel or GitHub CI claimed.
- Reuse existing Wilson/Haar F19/W0 and CMP119/122/116 source owners; standard character orthogonality and Bałaban prior art retained. No parallel integration infrastructure.

**Next cut:** explicit CMP119/122 source reconciliation for the nonzero five-face coefficient, followed by proof of the full absolute rooted connected-activity envelope; do not continue accumulating finite jets as a surrogate.
