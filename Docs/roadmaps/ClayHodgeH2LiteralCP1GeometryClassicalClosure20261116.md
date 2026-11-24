# Clay Hodge H2 — literal CP¹ and CP¹×CP¹ rational Hodge cycle-class comparison

### Hodge P2 — genuine hyperplane primitive obstruction and reverse lift

Let X smooth projective complex dimension d, L rational ample very ample after positive integral rescale, 1<=p<=d/2. Choose smooth complete intersection i:Y->X of d-2p hyperplanes (Bertini; if d=2p take Y=X), dimension 2p. Weak Lefschetz successive restrictions give i^*:H^{2p}(X,Q)->H^{2p}(Y,Q) injective (last equal dimension), and H^{2p-2}(X)->H^{2p-2}(Y) iso. For primitive alpha, L_X^(d-2p+1)alpha=0, so for every beta in H^{2p-2}(X), integral_Y i^*alpha L_Y i^*beta = integral_X alpha L_X^(d-2p+1)beta=0. Poincare duality and iso imply L_Y i^*alpha=0, i.e. primitive maps to primitive; converse by the same pairing on X. Hodge type, rationality and original class preserved, not merely dimension. If a literal rational codim-p algebraic cycle Z_Y has class i^*alpha, then i_* Z_Y has class L_X^(d-2p)alpha by projection formula, codim d-p. Hard Lefschetz inverses recover alpha cohomologically, not automatically algebraically. Sufficient genuine reverse producer is algebraic cycle lift along inverse on these classes (e.g. algebraic inverse Lefschetz correspondence under standard conjecture B, or actual same-X cycle whose restriction equals i^*alpha). This is NOT inferred from HL or Hodge on Y. For d=2p, take separate smooth hyperplane j:Z->X, dim d-1. Weak Lefschetz H^{d-2}(X)->H^{d-2}(Z) iso, PD on Z and j_*j^*=L show ker(j^*:H^d(X)->H^d(Z))=ker L=primitive. In middle Hodge degree, Gysin image from H^{d-2}(Z) is L H^{d-2}(X), disjoint from primitive by HL. Thus a primitive nonzero target cannot be produced by this single hyperplane pushforward; not an obstruction to arbitrary cycles on X.

Actual selected source X=Gr(2,4), smooth hyperplane Q^3. Middle Schubert basis sigma2,sigma11, pairing I_2, h²=sigma2+sigma11; primitive r=sigma2-sigma11, intersection norm 2. Restriction to Q^3 in H^4 sends each sigma to the line class, as pairing with h_Y equals integral_X sigma h²=1; Gysin of h_Y gives h². Hence restriction row [1,1], primitive kernel (1,-1), known lower-degree image (1,1); signed primitive is actual difference of algebraic cycles although both restrict identically. Exact rational projector onto L H² is (1/2)[[1,1],[1,1]], complement reconstructs original cohomology. 9 exact rational matrix checks on this classical actual Schubert fixture, not native geometric comparison. No arbitrary-X lift from finite matrices. Existing HodgePrimitiveLefschetzClayReductionExact (d240391f0a0c1c6634bafe470b2d5882b2745606) and HodgePrimitiveAlgebraicResidualDecompositionExact (91e3977382cc1d1d9767b0754541183fe893db1c), known-cycle singular map -> HodgeAlgebraicCycleClayCoreExact. Exact P2/H3 unpaid: actual primitive algebraic lift in middle dimensions and genuine algebraic reverse lift for below-middle restriction (above-middle likewise inverse HL or original primitive assembly); no new assumption of standard conjecture B. P3 general X/p, P4 existing cycle addition and Lefschetz assembly, P5 native comparison open. Attribution classical Bertini, weak/hard Lefschetz, PD, projection formula and Schubert geometry; DASHI source-specific decomposition and boundary audit.


## 23 November 2026 — non-product Gr(2,4) all rational Schubert-cycle inverse

[Original six-lane geometry-first alpha ledger](ClaySixLaneAlphaOriginalEndsExactMissingLemmas20261123.md), [locally executed exact Schubert BIDI script](../../scripts/check_hodge_gr24_schubert_cycle_bidi_20261123.py), Git blob c437b482b547ae0a5773ee9a8f5931b89a2778c0 (byte-identical executed script). This expands the classical **selected H2** laboratory beyond P¹ products to the actual smooth projective fourfold X=Gr(2,4), Plücker Klein quadric Q⁴⊂P⁵, with six flag-defined algebraic Schubert varieties. Standard classical Schubert cellular theory identifies its true Chow and rational singular cohomology as Q[h,c]/(h³−2hc,h⁴−3h²c+c²), where h=c₁(S*), c=c₂(S*), and the six classes (1,h,h²−c,c,hc,c²) have codimensions (0,1,2,2,3,4).

**Geometry labels source-corrected**: sigma₂=h²−c is lines **through a fixed projective point**; sigma₁₁=c is lines **contained in a fixed projective plane**. The two middle classes have self-intersection one and mixed intersection zero; ∫h⁴=2, Hodge codimension ranks (1,1,2,1,1), and no off-diagonal cohomology by affine Schubert cells. The actual complementary Schubert pairing is unimodular (determinant 1, P²=I). For any rational Hodge class alpha in THIS X, coefficients a_lambda=∫alpha sigma_(lambda-complement) recover a unique **literal rational algebraic cycle** sum a_lambda[Omega_lambda]; 7,200 exact rational recovery cases PASS. This is the already established classical cellular/Schubert result, not a general Hodge proof.

**Native H2 Gr(2,4) OPEN**: construct true Plücker smooth projective variety and tautological bundle, six literal flag incidence schemes and Chow cycles, original cycle-to-singular/de Rham Hodge comparison, exact Pieri/Giambelli/duality and the inverse in the already-owned true RationalAlgebraicCycle carrier. Do not relabel the abstract P¹ weld as Gr(2,4). H1 native rational→complex Hodge transport and universal H3 for arbitrary noncellular smooth projective X remain OPEN. See standard Schubert reference https://www.math.uzh.ch/en/fileadmin/user/kresch/publikation/goe07.pdf .



## 23 November 2026 — complementary-pairing inverse and cycle reconstruction

[Geometry-forward BIDI/reverse-solve](ClayFourLaneGeometryForwardBidiReverseSolve20261123.md) strengthens the classical finite-product result: for `X_r=(CP¹)^r`, the rational complementary intersection pairing is a permutation matrix. For a class `alpha=sum_{|I|=p} a_I h_I`, recover each original coefficient **exactly** via `a_I=int(alpha h_(I^c))`, then return the genuine rational algebraic coordinate-cycle sum `sum_I a_I [coordinate_point_cycle_I]`. This explicit forward/reverse correspondence is classical Künneth/divisor geometry only, not a universal Hodge cycle-preimage or native `ProjectiveLineGenericCycleClassWeldExact` constructor. Exact rational script checks 900 reconstructed class vectors at `r=0..8`; [script](../../scripts/check_clay_geometry_reverse_20261123.py). General H1/H3 and Agda kernel acceptance OPEN.


## 23 November 2026 — selected all-r product-family extension (classical Künneth donor)

The documented literal CP¹ and CP¹×CP¹ H2 cases admit an elementary **all finite products** extension X_r=(CP¹)^r without constructing a generic smooth-projective H3 instance. Under established projective-space Hodge, singular/de Rham comparison, algebraic divisor cycle and Künneth theorems, H*(X_r,Q)=Q[h_1,...,h_r]/(h_i²); its binomial(r,p) squarefree monomials in degree 2p are all rational (p,p) classes and represent actual codimension-p coordinate products of point divisors. Complementary intersection pairing int(h_I h_J)=1 iff J=I^c, otherwise zero. Factor permutations preserve products and natural cycle classes. Thus the known Hodge conjecture holds classically for each chosen X_r at all codimensions; this does not address arbitrary varieties or count H2 again.

[Four-lane geometric proof and source boundary](ClayNonYMRHFourLaneGeometricMaxCut20261123.md); [exact regression](../../scripts/check_clay_four_lane_geometric_shortcuts_20261123.py): 5,504 exact cup/intersection/permutation cases at r=0..7. The finite tests do not prove the arbitrary-r geometric comparisons. The existing ProjectiveLineGenericCycleClassWeldExact remains conditional on supplied actual geometry, and HodgeAlgebraicCycleClayCoreExact still requires authentic rational algebraic cycles on general X. **H1/H3 universal, generic comparison and native kernel acceptance remain OPEN.**


**16 November 2026. H2 is CLASSICALLY MATHEMATICALLY CLOSED for the literal projective-line and product examples, under the established user-authorized classical/Python protocol. Native Agda kernel/geometric comparison remains OPEN. The universal Hodge conjecture H3 and general H1 source geometry remain OPEN.** This note pays the exact *special-case physical geometry* gate, not the general Hodge conjecture.

## Original owner audit and why old source was insufficient

Read at Agda Clay rollup branch \`chatgpt/clay-20261112-four-frontier-fail-closed\`:

- \`DASHI/Mathematics/AlgebraicGeometry/ProjectiveLineCycleClassExact.agda\` blob \`d3a2f922bd6bf3ac1ab01d6d23ae8537fb24f277\`. Defines \`P1RationalDivisorCycle\` and \`P1RationalH11Class\` as abstract coefficient records, \`p1CycleClass\` as identity on rational coefficients, proves \`p1CycleClassSurjective\`. Its own source warns that the literal singular/de Rham identification of a constructed smooth projective variety is **not supplied**.
- \`DASHI/Mathematics/AlgebraicGeometry/ProjectiveLineGenericCycleClassWeldExact.agda\` blob \`c84f5d923e5cb753c4a74b8cc9f142819a55ebd3\`. Defines \`ProjectiveLineGenericCycleClassWeld\` as a record with **supplied** \`cycleFromP1\`, \`h11FromGeneric\`, \`genericFromP1\`, \`h11RoundTrip\` and \`cycleClassCommutes\`. Proves \`genericP1WeldGivesHodgeAtOne\` **only given a weld**. Its canonical boundary correctly sets \`literalP1GeometryWeldPaid=false\`.
- \`DASHI/Mathematics/AlgebraicGeometry/HodgeRationalClassIntersectionExact.agda\` blob \`2e8654be05e948b872e58611a616faf3f3ecb193\` distinguishes the TRUE rational singular class intersection from an arbitrary (p,p) piece. Our H2 classical proof uses the exact rational intersection, not the older weaker carrier.
- \`DASHI/Mathematics/AlgebraicGeometry/HodgeAlgebraicCycleClayCoreExact.agda\` blob \`a70ab7e37a3b4dcfacaeae99d83a0ade8c4bf48d\` correctly demands a literal \`RationalAlgebraicCycle\` rather than an arbitrary \`Cycle\` carrier. Our geometric witnesses are literal closed algebraic points and products of points, not a stipulated identity map.

## Physical CP¹ geometry: real projective variety, not abstract Q

Let \(X=\mathbb P^1_{\mathbb C}\) with homogeneous coordinates \([Z_0:Z_1]\), its standard two affine algebraic charts and the usual holomorphic transition \(z\mapsto1/z\). This is an actual smooth projective complex curve, with its standard complex structure, projective embedding, compact Kähler structure and rational singular cohomology.

The standard CW decomposition \(X=\mathbb C\cup\{\infty\}\cong S^2\) has exactly one 0-cell and one 2-cell. The cellular boundary maps vanish, giving the **actual topological** groups
\[
H^0(X,\mathbb Q)=\mathbb Q,\quad H^1(X,\mathbb Q)=0,\quad H^2(X,\mathbb Q)=\mathbb Q.
\]
This is a computation of actual singular cohomology via the standard cellular-to-singular comparison theorem, not a record whose \`Carrier\` was arbitrarily chosen to be Q.

The complex structure makes the unique positive-degree Hodge component \(H^2(X,\mathbb C)=H^{1,1}(X)\), with \(H^{2,0}=H^{0,2}=0\). Thus
\[
H^2(X,\mathbb Q)\cap H^{1,1}(X)=H^2(X,\mathbb Q)=\mathbb Q h.
\]
The equality uses the actual rational singular class embedded in complex cohomology; it does NOT identify arbitrary complex (1,1) coefficients with rational classes.

For the **actual** Fubini–Study 2-form in the affine coordinate \(z\),
\[
\omega_{\mathrm{FS}}=\frac{i}{2\pi}\frac{dz\wedge d\bar z}{(1+|z|^2)^2},
\qquad
\int_X\omega_{\mathrm{FS}}=2\int_0^\infty\frac{r\,dr}{(1+r^2)^2}=1.
\]
The normalized class \(h=[\omega_{\mathrm{FS}}]\) is the integral generator \(c_1(\mathcal O_X(1))\), by the classical Chern–Weil/de Rham comparison theorem. The point divisor \(D=[1:0]\) is a genuine codimension-one algebraic cycle, and \(\mathcal O_X(D)\cong\mathcal O_X(1)\). The classical divisor-cycle/Chern-class identity gives
\[
\mathrm{cl}_{\mathbb Q}(D)=h\in H^2(X,\mathbb Q),
\qquad
\mathrm{cl}_{\mathrm{dR}}(D)=[\omega_{\mathrm{FS}}]\in H^{1,1}(X).
\]
These are classes of the **same literal geometric point** under the **actual** singular/de Rham comparison.

For EVERY rational Hodge class \(\alpha=a h\) with \(a\in\mathbb Q\), take the literal rational algebraic cycle \(Z=aD\). Then
\[
\mathrm{cl}_{\mathbb Q}(Z)=a\,\mathrm{cl}_{\mathbb Q}(D)=a h=\alpha,
\]
and its de Rham/Hodge class is \(a[\omega_{\mathrm{FS}}]\). This is the exact codimension-one rational Hodge cycle representative, including rational coefficients, not merely an abstract Q-surjectivity assumption.

## Physical product CP¹×CP¹ and exact naturality

Let \(Y=X\times X\) with actual algebraic projections \(\pi_1,\pi_2\). The Künneth theorem and the preceding *actual* cohomology give
\[
H^2(Y,\mathbb Q)=\mathbb Q h_1\oplus\mathbb Q h_2,\quad
h_i=\pi_i^*h,
\]
and
\[
H^*(Y,\mathbb Q)=\mathbb Q[h_1,h_2]/(h_1^2,h_2^2),
\qquad
\int_Y h_1h_2=1.
\]
The Hodge types of \(h_1,h_2\) are (1,1), so every rational degree-two class is an actual rational Hodge class.

The **literal algebraic divisors**
\[
D_1=\{[1:0]\}\times X,\qquad D_2=X\times\{[1:0]\}
\]
have exact rational cycle classes \(\mathrm{cl}_{\mathbb Q}(D_i)=\pi_i^*\mathrm{cl}_{\mathbb Q}(D)=h_i\) by the standard geometric naturality of cycle classes under flat pullback. Hence for arbitrary \(\alpha=a h_1+b h_2\in H^2(Y,\mathbb Q)\), the literal algebraic cycle \(aD_1+bD_2\) represents it.

In codimension two, \(D_1\cap D_2\) is the actual algebraic point \(([1:0],[1:0])\), and its rational cycle class is \(h_1h_2\), the generator of \(H^4(Y,\mathbb Q)=H^{2,2}(Y)\cap H^4(Y,\mathbb Q)\). Thus every rational top-degree Hodge class is represented by a rational multiple of a literal algebraic point. Codimension zero is represented by rational multiples of the fundamental variety cycle. This gives all codimensions for these **two specific varieties**, not for arbitrary projective varieties.

The diagonal \(\Delta\subset Y\) has class \(h_1+h_2\), as its intersection with either ruling is one. For any algebraic map \(g:X\to X\) of degree \(d\), \(g^*h=d h\), matching the pullback of point-divisor cycles. These naturality checks use the **true algebraic map** and its topological degree, not a chosen arbitrary map between Q-records.

## What is external classical background versus new source work?

**Standard classical theorems explicitly used:** the CW-to-singular cohomology comparison, projective-space Hodge decomposition and Kählerness, de Rham theorem, Chern–Weil first Chern class of O(1), algebraic divisor cycle-class compatibility, Künneth cup-product naturality, and intersection theory of the two rulings. They are *established mathematical results*, not newly proved in the repository. The finite exact SymPy/Fraction regression only checks normalization and algebraic arithmetic; it is NOT a substitute for these geometric theorems.

**Actual new gate payment under classical protocol:** explicitly instantiate the previously abstract P1 coefficient model with the actual smooth projective \(\mathbb P^1_{\mathbb C}\), its singular-to-de Rham comparison, its rational Hodge intersection, the genuine point-divisor class and \(\mathbb P^1\times\mathbb P^1\) naturality. This discharges the H2 mathematical target in its narrow literal special-case sense.

**Not paid:** Agda \`ProjectiveLineGenericCycleClassWeld\` field values on a constructed actual \`SmoothProjectiveComplexVariety\`; formal actual singular/de Rham comparison and cycle-class homomorphism; native Agda typechecking; full general H1 physical carrier construction for all varieties; H3 all-variety all-codimension algebraic representatives. In particular, the already-source-written \`genericP1WeldGivesHodgeAtOne\` cannot be called a native literal P1 proof until the weld is instantiated.

## Executed regression

Source: \`scripts/check_clay_h2_cp1_geometric_classical_20261116.py\`. Python/SymPy and exact rational Fraction regression:
- normalized physical Fubini–Study polar integral equals exactly 1;
- CP¹ CW rational Betti numbers \(1,0,1\), and CP¹×CP¹ Künneth Betti numbers \(1,0,2,0,1\), Euler characteristic 4;
- 361 rational codimension-one divisor/class correspondences;
- 343 codimension-two rational intersection/cup cases;
- 171 degree-pullback naturality cases.

The proof is the all-class classical geometric argument above; these tests are independent arithmetic diagnostics. The original H2 gate remains open in the NATIVE Agda trust subledger.

## Canonical portfolio after this round

Original historical A–F: **6/15 resolved, 9 open**. Expanded six-problem research decisions: **8/28 resolved, 20 open**, with **S4 and H2** the two subsequently classically closed new gates (on different rounds). All six original Clay prize endpoints: **0/6 proved**. H1/H3 remain OPEN. This selected Hodge example is a special case known classically and does not establish any unknown universal theorem.
