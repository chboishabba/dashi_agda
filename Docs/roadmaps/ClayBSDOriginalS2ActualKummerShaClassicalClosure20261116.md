# BSD S2 — classical actual cohomological Selmer–Mordell–Weil–Sha[2] exactness

## 23 November 2026 — selected E32 Tate degree-two descent and exact BIDI rank zero

**New selected-curve CLASSICAL arithmetic route, not a second proof of this S2 classical exact-sequence theorem:** [full six-lane alpha ledger](ClaySixLaneAlphaOriginalEndsExactMissingLemmas20261123.md), [byte-identically locally executed E32 isogeny regression](../../scripts/check_bsd_e32_original_2isogeny_bidi_20261123.py), Git blob d43aa30773b572551b749b5ac1b153be4c798ce5. The true original E:y²=x³−x (a=0,b=−1) has two-isogenous partner E':Y²=X³+4X (a'=0,b'=4). Exact forward/dual formulas and both generic compositions with [2], plus 11,616 independent original elliptic finite-field group-law checks, passed with exceptional O and (0,0) branches. These local receipts DO NOT supply an Agda elliptic group/continuous Galois-cohomology kernel theorem.

**Classical mathematical rank 0 is now explicitly reverse-solved via Tate's known two-isogeny theorem, independently of BSD.** Square-class alpha(O)=1, alpha(T=(0,0))=b, alpha(x,y)=x mod rational squares for x≠0. Prime-support valuations put E alpha inside {±1}, both realized. For E' b'=4 support gives {±1,±2}; real Y²=X(X²+4) disallows negative classes and the rational point (2,4) attains 2, while O attains 1. Thus image sizes 2 and 2, and published Tate equality 2^(rank+2)=2*2 gives rank E(Q)=0. Sources: https://www.cmi.ac.in/~siddhi/Rank.pdf §2, https://web.math.pmf.unizg.hr/~duje/pdf/section15-5.pdf §15.5. **This does not establish Sha[2]=0 or the refined BSD formula**; the S2 classical real H¹ exact sequence already belongs to this file and is not replaced by a squareclass argument.

**Native S1/S3 still OPEN:** define literal source E32/E' proper curves and group laws including all 2-torsion and O, source map kernels and both compositions, group-homomorphic Q×/Q×² alpha, valuation prime-support and real sign, actual Tate exact sequence and MW quotient; instantiate actual all-place cohomology/Selmer/Sha only in their original owners. Native Agda/Lean kernel NOT RUN. Selected arithmetic rank-0 **mathematical result** is classically settled; do not count the still-missing *native* S3 implementation as a second independent mathematical conjecture. Universal S6 remains OPEN.



**16 November 2026. S2 CLOSED CLASSICALLY as an established universal arithmetic theorem, not a new result and NOT native Agda/Lean kernel checked.** This discharges the *actual cohomological connecting morphism and classical Sha* mathematical gate for the original curve E:y²=x³−x, indeed for any elliptic curve over Q. It does not compute its Selmer group, prove rank zero, prove Sha finite or establish strong/universal BSD.

## Original-source audit and exact owner

The actual selected original is \`Elliptic.curveY2EqualsX3MinusX\`, \(E:y^2=x^3-x\), not an arbitrary abstract cokernel. Source owner \`DASHI/Mathematics/Arithmetic/EllipticTwoDescentRoadExact.agda\` blob \`e7dba5c64d705edd4bd1f4dbccb3e252f3a23a2f\` defines \`GlobalLocalTwoDescentCarrier\`, \`SelmerTwoElement\`, \`MordellWeilShaTwoExactness\`, but \`ShaTwo : Set\` and \`kernelEqualsKummerImage : Set\` are **supplied** fields, not a constructed classical Sha group or proved exactness. Its \`canonicalEllipticTwoDescentRoadBoundary\` correctly sets \`globalExactSequencePaid=false\`. \`DASHI/Mathematics/Arithmetic/BirchSwinnertonDyerBoundary.agda\` blob \`f8418e2c7f9db3f4b11554812a04040949e72619\` has a general \`ShortExactSequence\` record and separate BSD leading-coefficient boundary, not the actual H¹ construction. \`DASHI/Mathematics/Arithmetic/EllipticOriginalSelmerCohomologyExhaustionExact.agda\` blob \`e8a2d7507a91502b7829da8120cb21eac5ca9c45\` explicitly identifies additional original all-place S1/S3 hypotheses and does not claim a native actual Sha construction.

## Real Galois cohomology, not an abstract defined quotient

Take the original smooth elliptic curve \(E/\mathbb Q:y^2=x^3-x\), whose discriminant is \(64\ne0\). Its algebraic group \(E(\overline{\mathbb Q})\) and **actual Galois module** \(E[2](\overline{\mathbb Q})\) fit the genuine multiplication-by-two short exact sequence of discrete \(G_\mathbb Q\)-modules
\[
0\longrightarrow E[2](\overline{\mathbb Q})
 \longrightarrow E(\overline{\mathbb Q})
 \xrightarrow{[2]} E(\overline{\mathbb Q})\longrightarrow0.
\]
Surjectivity of [2] on algebraic closure follows because it is a finite surjective isogeny in characteristic zero. Standard continuous Galois cohomology yields the long exact sequence, in particular the **actual global Kummer exact sequence**
\[
0\to E(\mathbb Q)/2E(\mathbb Q)
\xrightarrow{\delta_\mathbb Q}H^1(\mathbb Q,E[2])
\xrightarrow{\iota_*}H^1(\mathbb Q,E)[2]\to0.
\tag{K_Q}
\]
Here \(\delta_\mathbb Q(P)\) is the cocycle \(\sigma\mapsto\sigma Q-Q\) for any \(Q\in E(\overline{\mathbb Q})\) with \(2Q=P\); independence of the chosen Q is equality of cohomology classes, not equality of cocycle representatives. The right-hand image is exactly the **actual 2-torsion** of \(H^1(\mathbb Q,E)\) by exactness at H¹ and multiplication by 2. In particular \(\ker\iota_*=\operatorname{im}\delta_\mathbb Q\) and \(\delta_\mathbb Q\) is injective on \(E(\mathbb Q)/2E(\mathbb Q)\).

For every place \(v\) of \(\mathbb Q\), including \(v=\infty\), the identical argument over \(\mathbb Q_v\) gives
\[
0\to E(\mathbb Q_v)/2E(\mathbb Q_v)
\xrightarrow{\delta_v}H^1(\mathbb Q_v,E[2])
\xrightarrow{\iota_{v,*}}H^1(\mathbb Q_v,E)[2]\to0.
\tag{K_v}
\]
Naturality of the long exact sequence under restriction \(G_{\mathbb Q_v}\hookrightarrow G_\mathbb Q\) (up to conjugacy, immaterial in cohomology) gives the actual commuting square
\[
\operatorname{res}_v\circ\delta_\mathbb Q
=\delta_v\circ(E(\mathbb Q)\to E(\mathbb Q_v)),
\quad
\operatorname{res}_v\circ\iota_*=\iota_{v,*}\circ\operatorname{res}_v.
\tag{N}
\]

Define **actual** 2-Selmer and classical Tate–Shafarevich groups by
\[
\mathrm{Sel}^{(2)}(E/\mathbb Q)
=\{\xi\in H^1(\mathbb Q,E[2]):
\forall v,\ \operatorname{res}_v(\xi)\in\operatorname{im}\delta_v\},
\]
\[
\Sha(E/\mathbb Q)
=\ker\!\left(H^1(\mathbb Q,E)\longrightarrow
\prod_v H^1(\mathbb Q_v,E)\right).
\]
The second definition uses the **actual E-valued H¹ and all completions**; it is NOT a cokernel manufactured from Selmer. Write \(\Sha(E)[2]\) for its true 2-torsion.

## Prove the exact sequence on the actual objects

1. **Left map lands in Selmer and is injective.** By (N), every global Kummer image satisfies every local Kummer condition. Injectivity is exactly (K_Q).
2. **The middle-to-right map is well-defined.** For \(\xi\in\mathrm{Sel}^{(2)}\), set \(\rho(\xi)=\iota_*(\xi)\in H^1(\mathbb Q,E)[2]\). By local Selmer membership and (K_v), \(\iota_{v,*}(\operatorname{res}_v\xi)=0\) for every v. By (N), every restriction of \(\rho(\xi)\) is zero, so \(\rho(\xi)\in\Sha(E)[2]\).
3. **Kernel equals the genuine global Kummer image.** If \(\rho(\xi)=0\), (K_Q) gives \(P\in E(\mathbb Q)\) with \(\xi=\delta_\mathbb Q(P)\). Conversely every such image maps to zero by (K_Q). No circular use of the Selmer quotient is involved.
4. **Surjectivity onto classical Sha[2].** Take \(a\in\Sha(E)[2]\subset H^1(\mathbb Q,E)[2]\). Global (K_Q) gives \(\xi\in H^1(\mathbb Q,E[2])\) with \(\iota_*\xi=a\). For every v, \(\iota_{v,*}(\operatorname{res}_v\xi)=\operatorname{res}_v(a)=0\). Local (K_v) forces \(\operatorname{res}_v\xi\in\operatorname{im}\delta_v\). Hence \(\xi\in\mathrm{Sel}^{(2)}\) and \(\rho(\xi)=a\).

Therefore the **actual classical** short exact sequence, for this original E and in fact every E/Q, is
\[
\boxed{0\longrightarrow E(\mathbb Q)/2E(\mathbb Q)
\overset{\delta_\mathbb Q}{\longrightarrow}\mathrm{Sel}^{(2)}(E/\mathbb Q)
\overset{\rho}{\longrightarrow}\Sha(E/\mathbb Q)[2]
\longrightarrow0.}
\]
This is a classical theorem (Kummer long exact sequence and local–global cohomology); the original contribution of this round is to replace the repo's supplied abstract \`ShaTwo\` record in the *classical research ledger* by this explicit actual-object derivation and exact owner/audit trail.

**Sources of classical inputs:** J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., DOI 10.1007/978-0-387-09494-6, standard descent/Kummer cohomology; J. W. S. Cassels, *Lectures on Elliptic Curves*; J. S. Milne, *Arithmetic Duality Theorems*, Selmer and Sha via Galois cohomology. These references are to established results, not claimed newly proved.

## Precise dependency and remaining frontier

The original selected curve has four rational 2-torsion points: O, (0,0), (1,0), (-1,0). This **does not determine** \(E(\mathbb Q)/2E(\mathbb Q)\), the Selmer group, rank or \(\Sha[2]\) without the actual all-place cohomological exhaustion and Mordell–Weil argument. For a finitely generated E(Q), \(\dim_{\mathbb F_2} E(\mathbb Q)/2E(\mathbb Q)=\operatorname{rank}E(\mathbb Q)+\dim_{\mathbb F_2}E(\mathbb Q)[2]\), but the rank is still an independent fact. S1 actual original local H¹ realization, S3 original selected all-place exhaustion/rank, S5 odd-primary Sha/full leading coefficient and S6 universal BSD all remain OPEN. S4 selected analytic L(E,1)>0 is independently classically closed, and cannot be promoted to rank zero via an unproved BSD rank conjecture.

**Native firewall:** No Agda/Lean implementation of continuous Galois H¹, the genuine E-valued Sha kernel, or this same-source exact sequence has been typechecked here. The source \`MordellWeilShaTwoExactness\` record remains supplied. Thus \`native_kernel_acceptance=false\`; this gate closes **only** under the preagreed classical mathematical protocol, and the actual native bridge remains a separate debt.

## Exact finite regression and negative controls

\`scripts/check_clay_s2_actual_kummer_sha_classical_20261116.py\` checks the original discriminant and four rational 2-torsion representatives, exact cocycle coboundary identities on a toy Galois module, and finite abelian-group exactness and local lifting controls. The **universal** theorem is proved by the preceding actual Galois cohomology argument, not by these finite examples. Negative controls reject (i) equating Sha to an arbitrary Selmer cokernel by definition, (ii) dropping the archimedean place, (iii) inferring Selmer size from four torsion points, and (iv) equating 2-primary information to all-primary Sha.

**Expanded six-problem ledger after S2: 9/28 decisions resolved, 19 open; historical A–F 6/15 unchanged; six original Clay prize endpoints 0/6.**
