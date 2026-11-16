# BSD S3 — original E actual Sel² exhaustion, Sha[2]=0 and Mordell–Weil rank zero: CLASSICAL closure

16 November 2026. **S3 classical selected-curve mathematics CLOSED. Native Agda/Lean SAME-OBJECT carrier and Stoll donor adapter NOT kernel-checked.** This is not universal BSD and does not prove full Sha triviality, odd-primary Sha, the strong BSD leading coefficient, or S5/S6.

## Original source and prerequisites

Original source audited at branch \`chatgpt/clay-20261112-four-frontier-fail-closed\`: \`DASHI/Mathematics/Arithmetic/EllipticOriginalSelmerCohomologyExhaustionExact.agda\` blob \`e8a2d7507a91502b7829da8120cb21eac5ca9c45\` provides the exact *conditional* theorem \`originalSelmerGlobalH1ExhaustedByActualTorsion\`, but its \`OriginalSelmerCohomologyRealization\` fields \`actualTorsionGlobalH1\`, \`originalTorsionAllLocalKummerConditions\`, \`genuineSUnitSupport\`, \`actualTorsionKummerCompatibility\` and \`globalCohomologicalSquareClassFaithful\` are **not** instantiated. \`DASHI/Mathematics/Arithmetic/EllipticSupportedSquareClassSieveExact.agda\` blob \`2979b3c64909cf6a136bb7dd5bdd03f806a3de19\` proves the 16→8→4 finite combinatorial elimination and literal rational torsion representative dictionary. The preceding S1 classical proof is \`Docs/roadmaps/ClayBSDOriginalS1Q2EightImageClassicalClosure20261116.md\`; S2 is \`Docs/roadmaps/ClayBSDOriginalS2ActualKummerShaClassicalClosure20261116.md\`. These establish **mathematical** actual Galois H¹/Kummer naturality and genuine Selmer–Sha exactness by standard classical theorems, NOT an Agda kernel instantiation.

## Actual original global H¹ and the 16 supported pairs

Let \(E/\mathbb Q:y^2=x(x-1)(x+1)\). All E[2] is rational; multiplication-by-two Kummer gives the genuine injective map
\[
\delta_{\mathbb Q}:E(\mathbb Q)/2E(\mathbb Q)\hookrightarrow H^1(\mathbb Q,E[2])
\cong (\mathbb Q^\times/\mathbb Q^{\times2})^2.
\]
Use the actual full 2-descent coordinates \(([x],[x-1])\) at nontorsion points and the usual root-derivative branch values at 2-torsion. All local restriction maps and local Kummer images are the genuine Galois-cohomological maps. For any \(s\in\operatorname{Sel}^{(2)}(E/\mathbb Q)\), good reduction of E at every odd p (discriminant 64, p∤2) implies its H¹ class is unramified at p. For the constant E[2] module, unramified local square classes have even p-adic valuation, hence the **global rational** pair is represented by \(a,b\in\{1,-1,2,-2\}\). There are 16 possible *faithful* global H¹ classes; no finite-code substitution is made.

## Actual real and Q₂ Kummer filters

At real nontorsion points, y²=x(x−1)(x+1)>0 gives x>1 or −1<x<0, so x and x−1 have equal signs. The torsion Kummer branch classes are O:(1,1), (0,0):(−1,−1), (1,0):(1,2), (−1,0):(−1,−2), and obey the same sign rule. Therefore any global Selmer class has sign(a)=sign(b), leaving eight pairs.

At Q₂, for any nontorsion point x≠0, \(2v_2(y)=v_2(x)+v_2(x^2-1)\). If v₂(x)>0 then v₂(x²−1)=0, if v₂(x)<0 then v₂(x²−1)=2v₂(x), and if v₂(x)=0 it is already even. Thus **v₂(x) is even** for every actual Q₂ point with x≠0. At x=±1 the x Kummer square class has even v₂; at x=0 the correct branch class is −1, again even. Consequently any actual Q₂ Kummer class has even v₂ in its first square-class coordinate. Of the eight global supported pairs with equal signs, exactly four have even v₂(a):
\[
(1,1),\quad (1,2),\quad (-1,-1),\quad(-1,-2).
\]
These are not merely four finite tags: since \(\mathbb Q^\times/\mathbb Q^{\times2}\) supported on {2,∞} has exactly these actual rational representatives, the equality is in genuine global H¹.

## Lower bound, all places and exact Selmer conclusion

The four pairs are the **actual Kummer images** of O,(1,0),(0,0),(−1,0), respectively, using the original curve and root-derivative branch values. All four belong to the genuine global Selmer group, because each comes from a global rational point and Kummer localization commutes with restriction at **every** place. They are pairwise distinct in \(H^1(\mathbb Q,E[2])\). The global upper bound is four, so
\[
\operatorname{Sel}^{(2)}(E/\mathbb Q)=\delta_{\mathbb Q}(E(\mathbb Q)[2]),
\quad |\operatorname{Sel}^{(2)}|=4,
\quad \dim_{\mathbb F_2}\operatorname{Sel}^{(2)}=2.
\]
The actual cohomological exact sequence from S2,
\[
0\to E(\mathbb Q)/2E(\mathbb Q)\to\operatorname{Sel}^{(2)}(E/\mathbb Q)\to\Sha(E/\mathbb Q)[2]\to0,
\]
and the known \(E(\mathbb Q)=E(\mathbb Q)[2]\) (proved below) imply \(\Sha(E/\mathbb Q)[2]=0\). Alternatively, the four distinct torsion images already fill Sel², so the Kummer injection and finite-generation argument show the quotient vanishes.

## Actual original Mordell–Weil rank, independently of BSD

For any rational nontorsion P=(x,y) with y≠0, the rational triple
\[
a=(x^2-1)/y,\quad b=2x/y,\quad c=(x^2+1)/y
\]
satisfies a²+b²=c² and ab/2=1. Taking absolute values gives a rational right triangle of area one. Fermat's classical infinite descent proves that no rational right triangle has square area. Therefore no such P exists. The only rational points are O and the three roots with y=0, so \(E(\mathbb Q)\cong(\mathbb Z/2)^2\) and **rank E(Q)=0**. This uses established Fermat infinite descent, not BSD analytic rank equality. Mordell–Weil finite generation is also a standard established theorem, but is not needed for this direct full-group classification.

## Native source and attribution firewall

**No Agda kernel check** for \`OriginalSelmerCohomologyRealization\` instantiated on actual Galois cohomology has been run; its fields remain supplied. **No Lean kernel check** of \`Integration/MillenniumBSDStollMordellWeilAdapter.lean\` was run and no version-pinned donor verification is claimed. The classical proof above establishes the **mathematical selected-curve theorem** directly; it does not certify the named Agda/Lean original endpoint declarations. Track \`S3-NATIVE\` as an unpaid implementation obligation, distinct from S3's classical mathematical decision. External established results: Silverman, *Arithmetic of Elliptic Curves* (full 2-descent, Kummer and good reduction); Milne, *Arithmetic Duality Theorems* (Selmer/Sha exactness); Fermat's infinite descent against square-area rational right triangles. Original Agda source receives attribution for its 16→8→4 finite sieve and exact target shape.

**S3 CLASSICAL mathematical closure; expanded 12/28 resolved, 16 OPEN; historical 6/15 unchanged; original six Clay universal endpoints 0/6.** S5 selected full leading coefficient and odd-primary Sha and S6 universal BSD remain OPEN. In particular **Sha[2]=0 does not prove Sha=0**.
