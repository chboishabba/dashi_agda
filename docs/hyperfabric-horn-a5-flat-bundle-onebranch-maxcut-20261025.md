# Horn–Witten max-cut: finite A5 single-branch obstruction and smooth-flat exterior existence

**Date:** 2026-10-25, Brisbane. Continuation of [Agda #1249](https://github.com/chboishabba/dashi_agda/pull/1249) and [Lean #84](https://github.com/chboishabba/dashi_lean4/pull/84). Canonical original authors remain [Agda horn #1244](https://github.com/chboishabba/dashi_agda/pull/1244), [Agda neutrino/Wilson #1247](https://github.com/chboishabba/dashi_agda/pull/1247), and Hatcher (Example 2B.2). THIS IS NOT a new result about a physical neutrino experiment, 3D gravity, Witten's Monster CFT, or a Clay problem.

## Independent original primary mathematics

- **Hatcher**, [*Algebraic Topology*, Example 2B.2, pp. 170–172](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf): source-actual Alexander horned ball \(B\), open exterior \(X=\mathbb R^3\setminus B\), injective direct-limit group \(G=\pi_1(X)\) with meridians \(m_w=[m_{w0},m_{w1}]\). Hatcher proves nontriviality and perfectness. Hatcher does **not** give quantitative arclength bounds for an arbitrary later user-selected three-copy wild embedding.
- **Original Agda #1244**: source-produced a surjection \(q:G\to A_5\) for one horn factor by coherently selecting commutator antecedents, and a three-factor \(A_5^3\rtimes C_3\) quotient with faithful **c=0, 180-coordinate finite commutative VOA**. This is an actual nonabelian quotient, different from the pointed abelian fusion \(C_3\) of the Witten/Läcki–Zaugg \(SU(3)_1\) chiral theory. Crucially, \(G\to A_5\) can be nontrivial even though \(G\to C_3\) is necessarily trivial.
- **Classical icosahedral representation theory**: \(A_5\cong I\subset SO(3)\subset SU(3)\) has 60 elements (identity 1; 15 of order 2; 20 of order 3; 24 of order 5). In the faithful real three-dimensional rotation representation (complexified into SU3), the least nonidentity operator-norm gap is \(\kappa=2\sin(\pi/5)=\sqrt{(5-\sqrt5)/2}>1\). Original source, e.g. [icosahedral A5 representation](https://citeseerx.ist.psu.edu/document?doi=8fe0cba38589f5b749bd0575766d41c5e5aaea19&repid=rep1&type=pdf), not a new DASHI discovery.
- **Flat-bundle representation correspondence**: for any representation \(\rho:\pi_1(X)\to SU(3)\), the standard \((\widetilde X\times SU3)/\pi_1(X)\) produces a **smooth flat SU3 bundle with holonomy \(\rho\)** on the OPEN smooth exterior \(X\). See [Goldman–Millson 1988, representation/flat-connection correspondence](https://math.umd.edu/~wmg/PMIHES_1988__67__43_0.pdf) and [Cohen, *Bundles, Manifolds, and Homotopy*, §5](https://virtualmath1.stanford.edu/~ralph/bookR3.pdf). For a smooth three-manifold, SU3 is 2-connected, so a principal SU3 bundle admits a global smooth trivialization by standard obstruction theory; a global potential need NOT be uniformly bounded as one approaches the excluded wild set. This is EXISTENCE of a mathematical flat connection, not a physical realization with source energy, anomaly consistency, prescribed neutrino Wilson W, or an extension through the horned boundary.
- **Distinct Witten programme**: original Witten 1989 CS/WZW, Läcki/Zaugg 1989 \(SU2_4\subset SU3_1\) and three pointed chiral charges are CFT/quantum line-category objects, NOT the A5 matrices, Hatcher meridians, or the selected noncentral SU3 matrix \(W\) from sibling #1247.

## Mathematical ADVANCE 1: a single short marked branch rules out the chosen finite-image bounded realization

Fix \(g_w=\rho(m_w)\in H\) in any finite subgroup \(H\subset U(3)\), with \(g_\varnothing\ne I\).
If \(g_w=[g_{w0},g_{w1}]\ne I\), neither child can be \(I\). By induction **every descendant at every depth is nonidentity**.

Since \(H\) is finite, \(\kappa_H:=\min_{h\in H\setminus\{I\}}\|h-I\|_{op}>0\).
If \(\gamma_w\) is a **genuinely marked** loop for the Hatcher generator, with appropriately based/whiskered transport and length \(L_w\), and compatible unitary connection coefficient norm \(\le M\) along the LOCAL loop, then
\[
\kappa_H\le\|\mathrm{Hol}(\gamma_w)-I\|_{op}\le M L_w.
\]
The unitary whisker conjugacy preserves the norm. Consequently:

**ONE BRANCH, not uniform all leaves:** a sequence of correctly marked descendant loops \(\gamma_{w_n}\) with \(L_{w_n}\to0\) is incompatible with a uniform bound \(M<\infty\) and a nontrivial finite-image root. This is strictly stronger (FOR FINITE IMAGE ONLY) than the general SU3 half-distance-envelope test, which needs a complete depth with all leaves close to identity. It makes no claim about the separately selected W having finite-order/image.

For the source-compatible one-factor \(A5\) quotient and chosen icosahedral representation, \(\kappa_H=\sqrt{(5-\sqrt5)/2}>1\). The selected root in the existing A5 quotient has order 5 and is nonidentity. That mathematical representation can be realized on the open exterior by a smooth flat SU3 bundle; **if** truly shrinking marked loops exist, its connection cannot be uniformly bounded in the relevant Euclidean-compatible gauge as it approaches the horn set.

## Mathematical ADVANCE 2: local SOURCE-coordinate collar producer + explicit mark-failure control

At a straight tube segment with centerline and tubular radius \(r_w\), suppose a certified open annular collar of additional clearance \(c_w\) exists in the **actual complement**. The transverse loop at \(R_w=r_w+c_w/2\) is a genuine once-around-the-core loop in that LOCAL straight-tube complement, and has length \(2\pi R_w\). To apply the theorem globally, one STILL must prove the loop's homotopy marking equals the exact Hatcher generator in the full complement, including basepoint stems, all future-stage avoidance, and compatible gauge transport. The missing invariant is **arclength of marked generators**, not their printed stage/tube diameter alone.

The new executable tests a rational synthetic control family \(r_w=3^{-n}/10\), \(c_w=3^{-n}/20\), \(R_w=3^{-n}/8\), with \(2\pi R_w<11/(14\,3^n)\) using \(\pi<22/7\), and exactly \(2^n\) distinct collar centers at depth \(n\). It checks radial clearance and disjointness for all levels 0–7. For a hypothetical bounded source \(M=100\), depth four satisfies \(M L_{4}\le 1100/(14\cdot81)<1<\kappa_{A5}\); stage three fails that conservative threshold.

**DELIBERATE FAIL-CLOSED NEGATIVE CONTROL:** these cylinders are UNLINKED. Although their collars, clearances, arclengths and depth-indexed addresses pass exact arithmetic, they have not been proved to realize Hatcher's parent-as-child-commutator injection or a wild sphere. Hence they **do not** close the physical geometry gap. Hatcher's \(Z\)-block (open ball with two straight tubes deleted) provides a LOCAL marking proof in the source topological setting, but the source-specific three-copy chart/isotopy/collar metric and all-stage marking remain to be constructed.

## Mathematical ADVANCE 3: existing A5 representation DOES have a smooth FLAT bundle; boundedness is the real distinction

Let \(X=\mathbb R^3\setminus B\), where \(B\) is Hatcher's classic horned solid ball, and \(q:G\to A5\) be the independent #1244 quotient. Compose with icosahedral inclusion \(A5\to SU3\). Standard flat-bundle reconstruction gives a smooth flat connection on the resulting principal SU3 bundle over \(X\) with that nontrivial monodromy. Since \(X\) is a smooth open 3-manifold and \(SU3\) is 2-connected, the SU3 bundle is smoothly trivializable. Thus the question is **uniform regularity near the excluded wild set**, not abstract smooth-flat existence. Neither smoothness on an open exterior, flatness, nor vanishing bulk \(F^2\) curvature forces uniform coefficient bounds approaching its missing boundary.

A fully explicit NEGATIVE control on \(Y=\mathbb R^2\setminus\{0\}\) is
\[
A=(i/5)\,\operatorname{diag}(1,-1,0)\,d\theta,\qquad
d\theta=\frac{-y\,dx+x\,dy}{x^2+y^2}.
\]
It is smooth and FLAT on \(Y\); single winding circles of radius \(r\to0\) have length \(2\pi r\to0\) and FIXED order-five holonomy \(\mathrm{diag}(e^{2\pi i/5},e^{-2\pi i/5},1)\), with operator gap \(\kappa_{A5}\), while \(\|A\|_{op}=1/(5r)\to\infty\). This is ordinary punctured-plane \(\pi_1=\mathbb Z\), not the perfect horn group. It is a clean check that FLATNESS does not make the boundedness hypothesis dispensable.

## Exact implementation, genuinely executed GitHub blobs

- Agda #1249 [`scripts/check_horn_a5_single_branch_collar_cut.py`](https://github.com/chboishabba/dashi_agda/blob/chatgpt/hyperfabric-wave-spacetime-cut-20261024/scripts/check_horn_a5_single_branch_collar_cut.py): ALL 60 A5 permutations, exact group-order distribution, all 3600 commutator pairs, exact icosahedral gap squared, eight synthetic finite collar depths and the deliberate Hatcher-marking failure. **Executed locally**; file's local Git SHA-1 equals committed GitHub blob **`c3fe219759f2607118da75cefe2bfaf07bf01002`**.
- Agda #1249 [`scripts/check_horn_flat_puncture_escape.py`](https://github.com/chboishabba/dashi_agda/blob/chatgpt/hyperfabric-wave-spacetime-cut-20261024/scripts/check_horn_flat_puncture_escape.py): exact \(dA=0\), Hilbert operator gap squared \((5-\sqrt5)/2\), and seven shrinking-radius single-winding loop tests with \(\|A\|=1/(5r)\). **Executed locally**; local Git SHA-1 equals committed GitHub blob **`b15a80bc228f213f3918c2fd3509499034620f34`**.
- Lean #84 [`Integration/DASHITOE/HornFiniteImageOneBranchCut.lean`](https://github.com/chboishabba/dashi_lean4/blob/chatgpt/hyperfabric-toe-crossrepo-cut-20261024/Integration/DASHITOE/HornFiniteImageOneBranchCut.lean): source-written generic group theorem \(\forall w\ g_w\ne1\), parameterized one-short-leaf gap/transport contradiction, and rational stage-3/stage-4 collar coefficient checks. **Lean/Lake kernel NOT RUN**; no claim it certifies the ambient geometric horn connection or the external SU3 representation.

## Reordered phase acceptance

| Phase | Status |
|---|---|
| F0: Hatcher group / original quotient / literature provenance | SOURCE OWNERS CONFIRMED (Hatcher; #1244, #1247) |
| F1: A5 finite subgroup gap, 3600 commutators, one-branch theorem | **Mathematically discharged; exact Python**; Lean source-written |
| F2: actual marked shrinking *single branch* / source collar geometry | **OPEN**; synthetic unlinked control fails marking |
| F3: smooth flat SU3 bundle from q and standard representation | **POSITIVE existence by classical flat-bundle correspondence**, no local selected potential |
| F4: uniform bounded gauge regularity near actual wild compactum | **OPEN and conditionally incompatible with F2** |
| F5: other worker's independently chosen noncentral W, lepton spectrum/Hosotani | OPEN, not automatically finite A5 image |
| F6: Witten SU2_4→SU3_1 C3, Monster C27, original spatial hypervoxel | INDEPENDENT; no same-object physical functor |
| F7: physically calibrated gravity, anomaly, global energy, experiment, Clay | OPEN |

**Pareto next:** prove or disprove the Hatcher-word preserving all-level exterior straight-tube collar geometry with one convergent marked path of quantitative loop lengths; then choose the physical admissibility class for the flat bundle (uniformly bounded, boundary defect, L² connection/curvature, energy, etc.). Existing k4 conformal/VOA and the experimental synthetic Wilson interference remain independent.


## CRITICAL correction: arbitrary nonflat Wilson holonomies do NOT obey Hatcher π1 identities

The Hatcher relation `m_w=[m_w0,m_w1]` is a statement in the ABSTRACT
fundamental group. The replacement
`Hol_A(γ_w)=[Hol_A(γ_w0),Hol_A(γ_w1)]`
is valid for a **flat connection** (or a chosen explicit homotopy whose
non-Abelian Stokes curvature defect is established to vanish). For a
nonflat connection, Hol_A depends on GEOMETRIC loop representatives,
not just their homotopy classes. Therefore no general bounded
nonflat-holonomy no-go follows solely from Hatcher's π1 presentation.

**Executed same-source failure control:** new
`scripts/check_horn_curvature_homotopy_firewall.py`,
Git blob `4876fffbcc823aebf929c6b0bd6ef29b42591ece`, byte-exact
local execution PASS. On CONTRACTIBLE R², let
`A=i H (-y dx + x dy)/2`,
`H=diag(1,-1,0)`, with smooth bounded nonzero curvature
`F=i H dx^dy`. Two circles of radii 1/2 and 1/3
are both trivial elements of π1(R²) yet have
`Hol=diag(exp(iπ/4),exp(-iπ/4),1)` and
`diag(exp(iπ/9),exp(-iπ/9),1)`, which differ.
A nontrivial holonomy therefore is NOT a group
homomorphism from π1(R²) in this model.

**Strength of this current cut:** all A5 single-branch results
above explicitly use a TRUE group homomorphism
`ρ=q:G→A5→SO3→SU3`, and its standard flat-bundle realization.
They remain valid. To extend an analogous result to a physical
nonflat connection, introduce a SOURCE GEOMETRIC loop-homotopy
\(H_w\) and a quantitatively controlled curvature/surface
transport defect from nonabelian Stokes, and propagate its
accumulated error through the binary tree. Existing
`DASHI.Geometry.FlatFormalDiskHolonomySurface` on master
owns the **UNPAID** nonabelian-Stokes and transport-norm
analytical interfaces: no silent identification, no fictitious
zero-curvature residual.

This is an important conditional refinement to any older
draft text saying merely "bounded connection + Hatcher commutator
tower" without ALSO explicitly requiring flatness (or the exact
homotopy-defect certificate). It does not undermine the genuine
positive smooth-flat SU3 associated-bundle construction.


## Exact TOPOLOGICAL mark discriminator (added after synthetic-collar test)

The local synthetic straight-cylinder coordinate family now does more
than declare `markMissing`: for each parent word of depths 0..6
(\(1+2+4+8+16+32+64=127\) selected parent loops), the
parent transverse circle has planar winding vector **(1,0)**
around the two child tube cores at the next level, whereas the
supposed Hatcher commutator \([m_{w0},m_{w1}]\) has
abelianized winding vector **(0,0)**. The mismatch is checked from
EXACT rational centre/radius inequalities
`|c_parent-c_child0|=0<R_parent<|c_parent-c_child1|`.
Thus the synthetic straight-cylinder control **provably fails**
the original required Hatcher marking, despite passing all
collar clearance and short-length checks. This is a real
finite stage *topological* no-go for the control, not merely
a comment about the absence of linking. The actual Hatcher
two-tube replacement block must supply a different van Kampen
inclusion map that sends parent to a child commutator.

Updated script `check_horn_a5_single_branch_collar_cut.py`
was byte-exact locally executed and has matching committed
Git blob `e0e6b6cad6f3c5653c1097759facc12c76846ad2`.
Local exact checks cover all 60 A5 permutations, 3600 A5
commutator pairs, 8 selected local collar levels and these
127 source-marking rejection controls. Source original
A5 horn quotient remains owned by #1244.


## Strict cross-PR discriminatory NO-GO: selected W ≠ standard icosahedral A5 root

The other worker's ORIGINAL #1247 source character is
`Tr(W)=a+b ζ3`, where
`b=-19836986431118/181846007130841 ≠0`,
`ζ3=-1/2+i sqrt(3)/2`.
Thus `Im Tr(W)=b sqrt(3)/2 ≠0`; exact rational
squared imaginary component is
`295129523001269734919047443/33067970309429875820893367281 >0`.

Every matrix in the chosen **REAL** icosahedral
`A5<SO3<SU3` has REAL trace; conjugation
by SU3 cannot change it. Therefore the source-selected
W **cannot be SU3-conjugate to any matrix in this
chosen standard A5 subgroup**. The A5 quotient
and its one-short-branch no-go are legitimate
independently sourced alternatives, but cannot be
presented as the selected #1247 Wilson realization
or as a proof about its physical gauge field.
This does not rule out a non-finite-image SU3
representation or some separately sourced
different gauge/matter embedding.

The exact-source test was extended, executed locally
and byte SHA-matched to Git blob
`bce4f345d18912687bcf2d4a99d469376db39754`.
Lean #84 `HornWittenRegularityAndChargeCut.lean`
adds source-written `rootTraceZeta≠0`
and rational `3b²/4>0` theorem terms,
**kernel not run**.


## 2026-10-25 worker attribution correction: W infinite order ALREADY belongs to #1247

The strongest finite-image exclusion is NOT a new original #1249 discovery. Agda sibling #1247 already owns `NeutrinoExistingCPFiniteResidualNoGoExact.agda` and its exact Galois-trace certificate `442358853598/216225930001` in (2,3), with the standard algebraic-integer theorem stated as an external prerequisite. Original `NeutrinoHornedExteriorFifthPowerNoGoExact.agda` additionally owns the specific A5 fifth-power transfer. Our #1249 reproduces the exact rational certificate and adds the *independent* Q(zeta3) field norm `34895555697482945411132133124/33067970309429875820893367281` in (1,2). This second noninteger norm corroborates the original mathematical W-INFINITE-ORDER conclusion, ruling out ALL finite-image group representations of the selected W; it does not pretend to be first to that theorem.

The original Agda horn #1244 A5 quotient/c0 VOA remains a separate positive finite-image construction. A new complete 60/60 A5 inverse-conjugacy witness proves all unitary A5 characters real and also rejects the nonreal-trace W; this narrower result is strictly SUBSUMED by the original infinite-order no-go. Exact Agda #1249 scripts source-written and byte-for-byte locally executed, source hashes `b4a23effa02df27fe66c5e001f88f057cec3c8ea` and `4cb2aaf316ed28207d66a5f516c9d8bbbddeb30d`.

The correct positive compact-SU3 distinction: infinite order does NOT give a positive identity gap for all nontrivial powers. Standard two-eigenphase Dirichlet recurrence proves for all Q≥2 some m≤Q² with `||W^m-I||op≤4π/Q`; selected source W shows `||W^458-I||op≈0.04449169165` in a NUMERICAL regression (six Q values). Committed/equal blob `5de01046b58a8bd73fb9ac0681e9576b0a930619`. The finite A5 one-short-branch obstruction does NOT transfer to this W; the general full-depth commutator envelope remains conditional on FLAT source holonomy and true marked geometric lengths.

The Hatcher p171 source `Z` marking is once-punctured-torus boundary word `[a,b]`; the new exact finite free-group word test checks eight substitutions (2^n generators, 4^n nontrivial reduced word, zero abelianization), and rejects the original synthetic unlinked tube mark by its nonzero winding. Source executable blob `7a73fc6d68f55105de93ee416798f59127c03391` locally byte-tested. This is topological COMBINATORIAL marking, not a linked 3D Z-block coordinate/metric proof. Next actual producer remains a geometric marked meridian/collar with all-stage complement clearance, lengths and whisker compatibility, or a rigorous counterexample.

Canonical new source and stage roadmap:
`docs/hyperfabric-wilson-infinite-order-eisenstein-source-maxcut-20261025.md`.
Lean #84 `Integration/DASHITOE/HornWilsonInfiniteOrderEisensteinNormCut.lean` source-writes the distinct field-norm certificate, exact trace ranges and generic ambivalent-character lemma, with number-theory integrality as an explicitly identified standard external premise. **Lean/Lake kernel UNVERIFIED**. No observed lepton/TOE/Monster/Clay result.
