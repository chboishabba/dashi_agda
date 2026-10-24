# jFine 4+1+4, global S3, zeta, D4 and the TWO order-72 groups

**Date:** 2026-10-25 (Australia/Brisbane). **Primary source branch:** [dashi_agda IIT #1148](https://github.com/chboishabba/dashi_agda/pull/1148), open. **Cross-programme consumer:** [geometry/consciousness #1246](https://github.com/chboishabba/dashi_agda/pull/1246).

## Source archaeology / prior author rights

This is an audit and incremental mixed-character addition to **existing** source owners; do not reattribute older results to the new module:

- \`DASHI/Biology/JFinePhaseQuotientFieldExact.agda\` already constructs the source nine-trit phase field and the actual two-sided Fin19683 codec. Original general Fourier references cited there: **Audrey Terras**, *Fourier Analysis on Finite Groups and Applications* (1999), DOI 10.1017/CBO9780511626265; **Ingrid Daubechies**, *Ten Lectures on Wavelets* (1992), DOI 10.1137/1.9781611970104.
- \`IITJFineSelectedCrossPunctured79Exact\` already supplies the five-cross + four-corner split and the actual pointed/harmonic marker identification.
- \`IITJFineFourOneFourS3ZetaGaugeExact\` already constructs **four corners / centre / four edge sites** as a two-sided source-typed codec; additive centre-gauge reopening; global value-S3 = F3⋊C2; exact zeta-phase compatibility with original \`TriadicDepthOneCharacters\` and \`C3FourierConjugationExact\` sources; D4 site operations; source-reported D4×S3 Burnside 490.
- \`IITJFineS3RegularMonsterCharacterExact\` already constructs the C3 gauge orbit chart for the *original actual pointed source*: 10 marker choices × 3⁸ relative fields = 65610 free three-cycles, with three equal Fourier-sector multiplicities, plus a **character/multiplicity** comparison against \`Monster3BRegularC3BulkResidualFiftyThreeBidiExact\`. It does **not** provide a literal Monster intertwiner.
- \`IITJFineS3Heisenberg90x729CodecExact\` already provides the **actual source-typed** 90×729 chart for 65610 orbit labels, with original \`Monster3BHeisenbergMultiplicityExact\` 90=12+78 multiplicity source retained. It does **not** identify a Weyl/Heisenberg/Monster representation from cardinality.
- \`IITJFineD4EquivariantHeisenbergGaugeExact\` already builds opposite-edge half-sum/difference coordinates; note 1/2=2=-1 over F3 and opposite-edge differences are a *D4-stable label*. This is stronger than equating corner and edge four-tuples.
- \`PointedTernaryBulkExact\` owns the **moving D4 marker** on actual nine marked + unmarked sheets. A marked carrier under D4 is not ten inert copies of its fine component.
- \`OggSSPP2F4RecenteredTriXorS3Exact\` provides the recentered F3 local operations. Its name/other F4 sources are not authority for a new quantum or Monster claim.

**New audit owner:** \`DASHI/Biology/IITJFineD4S3MixedCharacterExact.agda\` and \`scripts/iit_jfine_d4_s3_mixed_character_audit.py\` provide a typed commuting-action bridge and a *numerically independently checked* full fifteen-sector complex character target, including the **actual moving marker**. No exact-head Agda compilation has been claimed.

## 4 + 1 + 4: the strongest spatial factorisation

In the original 3×3 source coordinate order:
\`\`\`
 corner(NW) edge(N)  corner(NE)
 edge(W)    CENTRE   edge(E)
 corner(SW) edge(S)  corner(SE)
\`\`\`

Thus \(\mathbb F_3^9\simeq\mathbb F_3^4\oplus\mathbb F_3\oplus\mathbb F_3^4\) and \(3^9=81\cdot3\cdot81=19683\). Unlike an arbitrary split, all three **subsets of positions** are invariant under source D4. The two four-dimensional modules are **not equivalent as D4 permutation modules**: the source vertical mirror fixes *two* edge positions but *zero* corner positions. An abstract F3-linear bijection of 81-state blocks alone does not intertwine the D4 action.

Better: use the centre \(c\) as a reference, making eight relative trits \(E-c,K-c\). Under the *global balanced-value* 3-cycle \(x↦x+1\) all relative trits stay unchanged, and only the centre moves. Under \(x↦-x\) the centre and all eight relative coordinates reverse. This is an **actual free C3 torsor chart** on the nine-trit fine sheet:

\[
\mathrm{Fine}\;\simeq\;\mathbb F_3^8\times\mathbb F_3,\qquad
19683=6561\cdot3.
\]

The original pointed source has 10×6561=65610 distinct C3-orbit labels. On *complex linearisation* its C3-permutation representation has multiplicities \(65610,65610,65610\) in the \(1,\zeta,\zeta^2\) sectors. For the nine-trit fine sheet alone those multiplicities are 6561 each.

## Exactly which S3?

1. **Global balanced-value S3**: \(\operatorname{AGL}(1,\mathbb F_3)=\mathbb F_3\rtimes\{\pm1\}\), six permutations \(x↦ax+b\) of the *three value symbols*, applied to all nine sheet positions. It COMMUTES with source D4.
2. **Spatial row/column S3**: independent \(S_3\) permutations of the *three row indices* and *three column indices*, plus transpose. This is \(S_3\wr C_2\) (automorphisms of the Hamming/rook graph H(2,3)), of order \(6\cdot6\cdot2=72\). It CONTAINS D4, but can move the distinguished centre; hence the 4+1+4 spatial split is **not stable under this full 72-group**. Original external source: S. M. Mirafzal & M. Ziaee, "A note on the automorphism group of the Hamming graph", *Trans. Combin.* 10(2) (2021), DOI 10.22108/toc.2021.127225.1817; more generally \(\operatorname{Aut}(H(d,q))\simeq S_q\wr S_d\).
3. **Earlier projective affine order-72**: \(\operatorname{AGL}(1,\mathbb F_9)=\mathbb F_9\rtimes\mathbb F_9^\times\), source in \`IITProjectiveF9Pointed80Exact\` and projective F9 audits. Although it ALSO has 72 elements, it is NOT the row/column wreath group. The affine F9 group has an order-8 element (multiplication by a primitive F9 unit); the row/column wreath group has orders only \(1,2,3,4,6\). No group isomorphism preserving their actions can exist.

**Independent exact finite results:**
- Combined D4(site) × S3(value) on all 19683 sheets: **490 orbits** (matching existing Burnside source). On the **196830 actual pointed/moving-marker states**: **4396 orbits** (NOT 10×490=4900).
- Combined spatial72(row/column) × S3(value): group order 432 and **84 orbits** on fine sheets. This is a different equivalence relation, not permission to identify it with \(\mathrm{AGL}(2,3)\), the F9-affine action, or an original j modular transformation.
- Spatial row/column 72 orders: exactly 1×order1, 21×order2, 8×order3, 18×order4, 24×order6.
- Mirror-fixed original sites: edge2, corners0. In the marked model the marker is transformed by the same D4, changing mixed characters nontrivially.

## Full mixed complex character targets

The character is the fixed-point count of \((g,h)\) on source states, where \(g\in D_4\), \(h\in S_3\) values. On a site-cycle of length \(L\), the number of value assignments is \(|\mathrm{Fix}(h^L)|\); multiply across site-cycles. For pointed sheets, multiply by \(1+\#\mathrm{FixSites}(g)\) to account for the unmarked marker plus fixed marked sites. Decompose against the 5 D4 and 3 S3 irreducible complex characters.

The labels A0,A1,A2,A3 denote the four one-dimensional D4 sectors (rotation/mirror eigen-signs \((+,+),(+,-),(-,+),(-,-)\)); E is its two-dimensional irrep.

| D4 irrep | Fine S3 (triv,sign,std) | Pointed S3 (triv,sign,std) |
|---|---|---|
| A0 | 490, 464, 954 | 4396, 4316, 8712 |
| A1 | 355, 356, 711 | 3856, 3884, 7740 |
| A2 | 418, 410, 828 | 4117, 4100, 8217 |
| A3 | 418, 410, 828 | 4117, 4100, 8217 |
| E  | 800, 820, 1620 | 8162, 8200, 16362 |

**Degree-weighted sums** (D4 E has dimension2, S3 std dimension2) recover **19683 and 196830 exactly**. Fine trivial-trivial count 490 is a Burnside orbit count; pointed trivial-trivial count is 4396. The unpointed and pointed tables are NOT simply related by multiplication by ten for D4, because markers move.

Restriction of the complex value-S3 to its C3 subgroup returns exactly the existing C3 Fourier multiplicities. Fine S3 irreps: \(3281\cdot1+3280\cdot\mathrm{sign}+6561\cdot\mathrm{standard}_2\); pointed: \(32810,32800,65610\). Under the subgroup C3, each standard 2D contains \(\zeta\) and \(\zeta^2\), and trivial+sign supply the invariant sector. Thus each pointed C3 phase has multiplicity 65610, consistent with the previously attributed Monster 3B **character count**. The existing Monster model has an additional 53-dimensional fixed-character residual, but NO original normalizer or literal Monster W equivariant action is identified.

## Zeta versus characteristic three

The exact Fourier phases \(\zeta\) and \(\zeta^2\) are **complex/cyclotomic** character values of C3. One must not diagonalise the global C3 permutation on an F3 carrier as though it had three distinct F3 eigenvalues:

\[
X^3-1=(X-1)^3\quad\text{over }\mathbb F_3.
\]

Therefore the representation is not generally semisimple in characteristic3; the complex-character decomposition is a statement about **linearising the finite permutation set over characteristic zero**. This is an essential boundary when importing TernaryGolay, Monster normalizer and putative quantum phase models.

## Priority, acceptance and physical boundaries

**Implemented new:** one source-typed Agda bridge proves four D4/value-S3 commuting relations, selected moving-marker relations, an actual row permutation counterexample that moves the centre, zeta-phase source reuses and 15 expected multiplicity numerals with dimension identities. The companion Python script proves numerical character integrality, positivity, total dimension, mirror fixed-sites, 72-group order spectrum and orbit counts. Both are integrated into the source IIT rollup and numeric verifier.

**Outstanding formal:** exact-head Agda compiler receipt; optionally kernel-reify the 48 fixed-point counts and character orthogonality using a source-specified complex/cyclotomic number ring if another programme actually consumes a normalizer-module comparison. The numerical tables alone are not a kernel-verified literal decomposition.

**High-value next physical test:** only if a real neural/AI/optical source supplies both a registered 3×3 map and controlled transformations, test D4 and value-S3 separate intervention equivariance, retained consumers and uncertainty. No observed consciousness, IIT Phi, exceptional Lie group, hidden physical axis, \(\mathbb F_{81}\) multiplication on both blocks, quantum coherence, or Monster representation is inferred from equal counts/spectral vocabulary.
