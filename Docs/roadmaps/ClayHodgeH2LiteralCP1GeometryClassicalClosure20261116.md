# Clay Hodge H2 — literal CP¹ and CP¹×CP¹ rational Hodge cycle-class comparison

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
