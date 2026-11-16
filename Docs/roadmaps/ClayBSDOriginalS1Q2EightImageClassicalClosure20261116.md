# BSD S1 — original E actual global/local H¹ and exhaustive Q₂ Kummer image: CLASSICAL closure

**16 November 2026. S1 CLASSICALLY CLOSED using established local elliptic-group and Kummer cohomology theorems, with exact eight original local-point witnesses. NATIVE AGDA/LEAN SAME-OBJECT REALIZATION STILL OPEN.** The selected curve is always \(E:y^2=x^3-x\), not an arbitrary \`GlobalCohomology\` record. This is a selected-curve classical descent computation, not the universal BSD theorem, and does not prove S3/S5/S6.

## Exact original source

\`DASHI/Mathematics/Arithmetic/EllipticRationalPlaceSelmerExact.agda\` (blob \`3a9c1ec65cdb987c644863f305bc5f9ca06fac6c\`) defines place-indexed *supplied* cohomology and Kummer image predicates; \`EllipticRationalPlaceTwoDescentProducerExact.agda\` (blob \`98a920f68832d71e6eb5a381170c057f5d18a059\`) has supplied \`archimedeanNecessary\` and \`dyadicNecessary\`; \`EllipticOriginalSelmerCohomologyExhaustionExact.agda\` (blob \`e8a2d7507a91502b7829da8120cb21eac5ca9c45\`) has supplied \`genuineSUnitSupport\` and \`globalCohomologicalSquareClassFaithful\`; \`EllipticSupportedSquareClassSieveExact.agda\` (blob \`2979b3c64909cf6a136bb7dd5bdd03f806a3de19\`) proves 16→8→4 *conditional* finite filtering.

The original **Lean** source \`chboishabba/dashi_lean4/Synthesis/MillenniumBSDCMQ2EightLocalPointWitnessesExact.lean\` (blob \`873cb3e1442feb7aa3999c41d0ae3b8e2c100e91\`) gives eight actual Q₂ points with rational x-coordinates 28,31,33,39,41,112,1/4,1/16 by Hensel square-root witnesses. The source explicitly says image exhaustiveness was open. The classical proof below pays that **mathematical** gap.

## The actual global H¹ and all localizations

The cubic discriminant is 64, and all 2-torsion points \(O,(0,0),(1,0),(-1,0)\) are rational. Consequently the **actual** finite Galois module \(E[2](\overline{\mathbb Q})\) is constant of rank two over F₂. Kummer theory for \(\mu_2\) (over fields of characteristic ≠2) and a basis of E[2] give
\[
H^1(\mathbb Q,E[2])\cong
(\mathbb Q^\times/\mathbb Q^{\times2})^2,\quad
H^1(\mathbb Q_v,E[2])\cong
(\mathbb Q_v^\times/\mathbb Q_v^{\times2})^2.
\]
These are genuine continuous Galois cohomology groups, not synthetic four-bit codes. Localization is induced by inclusion \(\mathbb Q\hookrightarrow\mathbb Q_v\) and commutes with both Kummer maps and these square-class identifications. For a non-2-torsion point \((x,y)\) the standard full-2-descent Kummer triple is
\[
([x],[x-1],[x+1])\in
(K^\times/K^{\times2})^3,\qquad
[x][x-1][x+1]=[y^2]=1.
\]
The triple identifies with two independent square-class coordinates, with a consistent basis choice; the 2-torsion points have standard separately defined branch values. **The triple is injective on \(E(K)/2E(K)\)** by the actual multiplication-by-two Kummer exact sequence. This injectivity is a standard theorem of full 2-descent, not a property postulated of four-bit projections.

At any odd prime p, E has good reduction since p∤64. The 2-Kummer image is unramified for p≠2 (standard good-reduction local Kummer theorem). Therefore the square-class coordinates of any global 2-Selmer class have even valuation at every odd p. Every such global rational square class is represented by one of \(\{\pm1,\pm2\}\); hence there are **16 supported ordered pairs**, exactly the source's finite code set. The two independent rational square-class coordinates are faithful: equal rational square classes imply equal original H¹ classes under the Kummer isomorphism, not just equal finite tags.

## Actual archimedean and dyadic point conditions

At the real place, for a nontorsion real point \(y^2=x(x-1)(x+1)>0\) forces \(-1<x<0\) or \(x>1\), hence sign(x)=sign(x−1). The separately defined torsion branch values satisfy the source's corresponding diagonal sign convention.

For any Q₂ point with x≠0,±1 and y≠0,
\[
2v_2(y)=v_2(x)+v_2(x^2-1).
\]
If \(v_2(x)>0\), then \(v_2(x^2-1)=0\) and v₂(x) is even. If \(v_2(x)<0\), then \(v_2(x^2-1)=2v_2(x)\) and 3v₂(x) is even, so v₂(x) is even. If v₂(x)=0 it is even. The 2-torsion branch classes are handled by the actual torsion Kummer dictionary, not by division by x=0. This is the real **point-level** local necessary condition behind the source's first-coordinate valuation parity.

## NEW decisive theorem: all eight Q₂ Kummer classes, no missing ninth

A standard theorem on local elliptic groups says, for an elliptic curve over a finite extension \(K/\mathbb Q_p\),
\[
|E(K)/mE(K)|=|m|_K^{-1}\,|E(K)[m]|
\]
for \(m\ne0\). In particular for \(K=\mathbb Q_2\), \(m=2\), this equals \(2\cdot|E(\mathbb Q_2)[2]|=8\). One proof uses the structure of the compact p-adic analytic group \(E(K)\): its open torsion-free subgroup has \(\mathbb Z_p\)-rank \([K:\mathbb Q_p]\), and the finite torsion quotient contributes exactly \(|E(K)[m]|\) to the multiplication-index. The local Kummer injection identifies the **actual** local image with \(E(\mathbb Q_2)/2E(\mathbb Q_2)\), hence it has **exactly eight elements**.

The eight existing original Lean points are all non-torsion, and their Q₂ square-class triples are:

| x | [x] | [x−1] | [x+1] |
|---|---|---|---|
| 28 | (0,7) | (0,3) | (0,5) |
| 31 | (0,7) | (1,7) | (1,1) |
| 33 | (0,1) | (1,1) | (1,1) |
| 39 | (0,7) | (1,3) | (1,5) |
| 41 | (0,1) | (1,5) | (1,5) |
| 112 | (0,7) | (0,7) | (0,1) |
| 1/4 | (0,1) | (0,5) | (0,5) |
| 1/16 | (0,1) | (0,1) | (0,1) |

Here (e,u) means 2-adic valuation parity e∈{0,1} and odd unit u mod 8∈{1,3,5,7}; it is the complete **actual** square-class classification of \(\mathbb Q_2^\times/\mathbb Q_2^{\times2}\), not an invented label. The eight triples are pairwise distinct, so their images under the genuine local Kummer map are distinct. Because the full image has **cardinality exactly eight**, these eight witnessed classes **exhaust the entire original local Kummer image**. This proves the previously missing upper bound; the eight-witness list alone had not proved it.

## Exact acceptance and limits

**S1 classical mathematical deliverables now established:** actual original global H¹ as rational square-class pairs; naturality of all actual local restrictions; actual good odd prime S-unit support; actual real and dyadic necessary filters; and **complete eight-class original Q₂ Kummer image**, with actual witness representatives and upper bound.

**What is NOT claimed:** Native Agda \`RationalPlaceTwoDescentData\` is still a record with supplied cohomology and predicates; native \`OriginalSelmerCohomologyRealization\` still has supplied faithful square-class and Kummer comparison fields. The Lean source has not been compiled here under its pinned toolchain. No kernel proof of local-group cardinality or of H¹ naturality has been constructed. Thus \`native_kernel_acceptance=false\`. S1's **classical** gate is closed under the same protocol as S2/S4/H1/H2, while the native source-to-actual bridge remains a distinct unpaid implementation obligation.

**S3 remains OPEN.** S1's eight local image elements are not the four global Selmer elements. To close S3, prove the global supported 16→8→4 elimination on the **same** pair-coordinate convention as the actual H¹ Kummer map and verify the original four torsion classes survive all places. The classical rank-zero theorem from Fermat descent is already established, but rank zero alone cannot imply Sha[2]=0.

**Classical sources:** J. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed. (multiplication-by-m Kummer, full two-descent and local elliptic groups); J. Milne, *Arithmetic Duality Theorems* (local Galois cohomology and Kummer image); standard local field square-class classification. The eight witnesses are original repository data. The finite exact regression below tests arithmetic only, not the cited general theorems.

**Expanded portfolio after S1: 11/28 resolved, 17 OPEN; historical A–F 6/15 unchanged; six original Clay endpoints 0/6.**
