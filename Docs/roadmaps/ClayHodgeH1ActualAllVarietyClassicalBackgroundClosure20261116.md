# Hodge H1 — genuine all-variety rational Hodge/cycle-class background, classical closure and native type firewall

**16 November 2026. H1 CLASSICAL MATHEMATICAL BACKGROUND CLOSED, for every smooth projective complex variety and every codimension, by established Hodge/de Rham/algebraic-cycle theorems. NOT a new theorem, NOT an Agda/Lean kernel-checked construction, NOT H3 algebraic representability.** The original-source Agda carrier remains a *separate native implementation obligation*, especially its Q-versus-C type error documented below.

## Exact source inspection, no abstract-field substitution

Read original Agda sources at branch \`chatgpt/clay-20261112-four-frontier-fail-closed\`:
- \`DASHI/Mathematics/AlgebraicGeometry/HodgeDecompositionCycleClassExact.agda\` blob \`8057771f90cba5ea04536b3fd059e64ff99969bd\`.
- \`DASHI/Mathematics/AlgebraicGeometry/HodgeRationalClassIntersectionExact.agda\` blob \`2e8654be05e948b872e58611a616faf3f3ecb193\`.
- \`DASHI/Mathematics/AlgebraicGeometry/HodgeAlgebraicCycleClayCoreExact.agda\` blob \`a70ab7e37a3b4dcfacaeae99d83a0ade8c4bf48d\`.

The source is explicit that its \`SingularDeRhamComparison\`, \`HodgeDecomposition\`, \`RationalAlgebraicCycleClassBackground\` fields are *supplied*, not instantiated on arbitrary actual varieties. The classical proof below establishes the underlying mathematical background, not an inhabitant of those records.

**Additional source type error discovered this round:** \`HodgeDecompositionCycleClassExact.HodgePiece : Nat→Nat→RationalVectorSpace\` gives each (p,q) piece a **Q-vector space**, whereas the classical Hodge decomposition is a **C-linear** direct-sum decomposition of \(H^k(X,\mathbb C)\). In general \(H^{p,q}\) is not a Q-subspace preserved by Q-structure, and the exact rational Hodge condition is a *complexified* comparison of the Q-class to \(H^{p,p}\). Likewise \`deRhamCohomology : Nat→RationalVectorSpace\` is fine for rational de Rham cohomology, but \`injectPiece\` must target its complexification, not the rational carrier directly. Treating the old \`HodgePiece\` as literally equal to the geometric Hodge summand would falsely promote the type. A correct native repair needs a complex scalar carrier and explicit extension-of-scalars and comparison maps. This is not solved by the classical theorem.

## Classical mathematical theorem: real geometric objects for arbitrary X

Let \(X/\mathbb C\) be any **smooth projective** complex algebraic variety of complex dimension \(n\), and \(p\ge0\). Its complex analytic manifold \(X^{an}\) is compact Kähler (pull back the Fubini–Study form along an actual projective embedding). Thus the Kähler Hodge theorem gives the canonical C-linear decomposition
\[
H^k(X^{an},\mathbb C)=\bigoplus_{a+b=k} H^{a,b}(X),
\qquad \overline{H^{a,b}}=H^{b,a}.
\tag{Hodge}
\]
The actual singular rational cohomology is \(H^k(X^{an},\mathbb Q)\), with the canonical injection into \(H^k(X^{an},\mathbb C)\) induced by \(\mathbb Q\hookrightarrow\mathbb C\). Algebraic de Rham comparison identifies \(H^k_{\rm dR}(X/\mathbb C)\) with complex singular cohomology, and analytic de Rham comparison identifies the latter with smooth closed-form classes. **The complexification is indispensable**: do not replace the complex Hodge summand by an arbitrary rational vector space.

The genuine rational Hodge-class set is the **intersection on one actual complex cohomology object**
\[
\operatorname{Hdg}^p(X)_{\mathbb Q}
=\{\alpha\in H^{2p}(X^{an},\mathbb Q):
\alpha\otimes 1\in H^{p,p}(X)\}
=H^{2p}(X^{an},\mathbb Q)\cap H^{p,p}(X).
\tag{RH}
\]
For \(p>n\), these groups vanish. The old \`RationalHodgeClassExact\` is structurally intended to capture the rational source plus matching (p,p) component, but its native \`HodgePiece\` must be complex-linear for the identification to be literal.

Let \(Z^p(X)_{\mathbb Q}\) be the Q-vector space of **finite formal Q-linear combinations of integral closed algebraic subvarieties of codimension p** (the genuine rational algebraic cycles). For each integral \(V\subset X\) of codimension p, its fundamental class defines the actual rational singular cohomology class
\[
\mathrm{cl}_{\mathbb Q}(V)\in H^{2p}(X^{an},\mathbb Q),
\]
by the integral fundamental homology class and Poincaré duality on the oriented smooth compact ambient X; equivalently, the cycle-class construction of intersection theory. This construction does not require V to be smooth: singular algebraic subvarieties still have fundamental cycles. Extend \(\mathrm{cl}_{\mathbb Q}\) Q-linearly to \(Z^p(X)_{\mathbb Q}\). This is the genuine cycle-class homomorphism, not a \`Cycle : Nat→Set\` record with arbitrary maps.

**Hodge type of algebraic cycles** is an established theorem: the de Rham current of integration over a codimension-p complex algebraic subvariety is a closed current of bidegree (p,p), and under the Hodge/de Rham comparison its rational fundamental class lies in \(H^{p,p}(X)\). Equivalently, the algebraic cycle-class map factors through the exact rational intersection:
\[
\mathrm{cl}_{\mathbb Q}:
Z^p(X)_{\mathbb Q}\longrightarrow
\operatorname{Hdg}^p(X)_{\mathbb Q}
\hookrightarrow H^{2p}(X^{an},\mathbb Q).
\tag{Cycle}
\]
It preserves 0, addition and rational scalar multiplication by construction. This is valid for **every** smooth projective X and codimension p; it is not a selected CP¹ surrogate.

**Naturality:** under flat pullback, cycle classes commute with cohomological pullback; for proper maps, cycle-class pushforward commutes with Gysin pushforward. The usual projection formula and cup/intersection compatibility apply where the corresponding intersection products are defined. No claim that every cohomological class is algebraic follows.

**Crucial strict direction:** the classical theorem proves \(\operatorname{im}\mathrm{cl}_{\mathbb Q}\subseteq\operatorname{Hdg}^p(X)_{\mathbb Q}\). The Hodge conjecture H3 is the converse inclusion \(\operatorname{Hdg}^p(X)_{\mathbb Q}\subseteq\operatorname{im}\mathrm{cl}_{\mathbb Q}\), which is NOT known for general X and p. The proof does not use or assert that converse, nor does it invoke algebraicity of a Hard Lefschetz inverse.

## Proof input provenance and native debt

Established mathematical sources: Claire Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge University Press, DOI 10.1017/CBO9780511615344; Pierre Deligne, *The Hodge Conjecture*, Clay Mathematics Institute; Phillip Griffiths and Joseph Harris, *Principles of Algebraic Geometry*; William Fulton, *Intersection Theory*. The classical Hodge theorem, de Rham comparison, projective compact Kähler theorem, Poincaré duality, algebraic cycle-class construction and type-(p,p) theorem are used as named established results. This round does not newly prove them.

**Native open subgate H1-N:** Implement and kernel-check actual \`ComplexVectorSpace\` and \(\mathbb Q\to\mathbb C\) extension-of-scalars, genuine singular-to-complex-deRham comparison, geometric \`SmoothProjectiveComplexVariety\` construction, Hodge decomposition on the same complex cohomology object, and the actual algebraic-cycle map. Preserve old consumers by an explicit compatibility adapter rather than silently identifying a Q \`HodgePiece\` with a complex one. All these fields are still supplied in Agda, so \`native_kernel_acceptance=false\`. Do not edit ESD surfaces.

**Research gate H1 (classical background):** the mathematical object and cycle-class map are established for arbitrary smooth projective X by the classical theorems above. This meets the expanded portfolio's *classical mathematical background* protocol but not the stricter *native construction* protocol. The ledger must carry both statuses explicitly. H3 remains OPEN, because cycle-class **surjectivity** is exactly the unknown conjectural assertion.

## Exact executable finite diagnostic (not proof of the general theorem)

\`scripts/check_clay_h1_rational_complex_hodge_firewall_20261116.py\` checks:
1. Rational/complex base change on explicit Q matrices and conjugate-linear type split.
2. A non-real Hodge line is not a rational subspace (negative control against the original source type).
3. CP¹×CP¹ genuine algebraic cycle images are rational (1,1), while arbitrary complex (1,1) coefficients need not be rational.
4. Finite-dimensional image-in-target does NOT imply target-in-image (negative control against H3).

These examples are not the proof of H1; the general proof is the established classical Hodge and algebraic-cycle theory above.

**After this round: 10/28 classical/source research decisions resolved, 18 OPEN; historical A–F 6/15 unchanged; original Clay endpoints 0/6.**
