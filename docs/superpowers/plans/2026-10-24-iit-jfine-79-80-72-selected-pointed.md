# Exact JFine and pointed bulk: selected 5 + punctured 4, 72/79/80

**2026-10-24. Owner:** dashi_agda IIT PR #1148. The goal is **actual typed carrier isomorphism**, not arithmetic resemblance or an unsupported Monster action.

## Source and attribution ledger

1. Earlier DASHI JFinePhaseQuotientFieldExact proves a two-sided codec between the actual J fine frequency carrier (Fin 19683) and the actual ternary 9-position phase quotient field. BalancedTernaryHarmonicCarrierExact has nine ordinary channels and distinguished completionJ (10 channels).
2. Earlier PointedTernaryBulkExact has the literal 10-marker/9-trit pointed sheet (196830 states) and D4 quarter-turn/reflection operations. Its unmarked + nine marked multiplicity is not a Monster module theorem.
3. Earlier RiemannQuarticPuncturedKernel4EnumerationExact proves 80 distinct nonzero four-trit states; OggSSPP2PuncturedKernel2BidiExact separately carries eight nonzero two-trit states.
4. Earlier IIT 5-cube sources use a three-axis periodic additive \(\mathbb F_3\) lattice of 125 sites, rank120/kernel5, with a 5-slot cyclic lost profile and \(F^{80}=I-JP\) verified by finite 125-basis arithmetic.
5. This new DASHI bridge owns the *selected cross/corner codec, actual pointed-sheet conversion, and field81 numerical analysis*. Original McKay (1978), Conway–Norton (1979), Griess (1982), Borcherds (1992) own the classical moonshine discoveries. Their claims are not proved anew by the present combinatorics.

## Full two-sided identification, not cardinality alone

Take the actual 3×3 JFine sheet, with the five-site cross C,N,E,S,W and four corners NW,NE,SW,SE. Selection and joining are *functions on the original source Agda table*, with roundtrips:

\[
\mathbb F_3^9\;\cong\;\mathbb F_3^5\times\mathbb F_3^4,\qquad
19683=243\cdot81.
\]

DASHI Biology/IITJFineSelectedCrossPunctured79Exact.agda implements the literal split/join, composes it with the earlier two-sided Fin19683 codec, maps all ten original balanced harmonic coarse channels to PointedTernaryBulkExact's actual ten marker constructors, and explicitly converts Base.TriTruth ↔ Triadic.KernelTrit and PhaseFineTable9 ↔ DialecticalSheetSpiralExact.Sheet3. Therefore the *actual* original ElementaryHarmonicChannel ↔ *actual* PointedTernarySheet relation is exhibited by an explicit two-sided source-written codec, not just a newly named 196830-element copy.

\[
(9+1)\cdot3^9=10\cdot243\cdot81=196830.
\]

The **set** of cross sites is D4-stable under the source sheet rotation/reflection. The chosen five-site cyclic ordering C,N,E,S,W is *not* the original D4 action, and is not the original C3² phase translation action. A transported D4 action on the harmonic side is defined, but a C5 action on the 5-cube diagonal profile needs an additional registered intertwiner; |D4|=8 and |C3²|=9 are not divisible by 5.

## 79, 80 and 72 are structurally meaningful, but different

Equip the chosen four corner trits with the irreducible quartic polynomial \(X^4+X+2\) over \(\mathbb F_3\), obtaining \(K=\mathbb F_{81}\). Then K has 81 elements, \(K^\times\) has 80, every nonzero \(a^{80}=1\), and its inverse is \(a^{79}\). The original four-trit punctured carrier already has exactly 80 elements, now provided with a *chosen field multiplication*; a bare 80-element set did not previously supply that law.

Primitive fifth roots of unity are in F81, not F9 (5 divides 80, not 8). For the **same** 5-cube F3 three-axis operator the 125 Fourier eigenvalues are sums of three fifth roots. Independent local finite arithmetic enumerated their orders:

| Multiplicative order | Multiplicity |
|---|---:|
| zero eigenvalue | 5 |
| 8 | 12 |
| 16 | 12 |
| 40 | 48 |
| 80 | 48 |

This shows the retained 120-dimensional dynamics has *exact* period 80, with \(F^{79}\) the inverse of F on that retained subspace. It also explains the finite 125-basis identity \(F^{80}=I-JP\). The 79 here is *3^4−2, the inverse exponent in F81*. It is a prime integer but **not** one of the repository's fifteen Ogg/Monster supersingular primes (2,3,5,7,11,13,17,19,23,29,31,41,47,59,71).

The unique 9-element subfield \(K_9=\{x\in K:x^9=x\}\) has 8 nonzero elements. Its affine maps \(z\mapsto az+b\) (a nonzero; b arbitrary) form AGL(1,9), of order **9×8=72**. The historical punctured 2-trit set of eight and nine-state quotient are cardinally and structurally compatible with this chart, but their original **group actions are not automatically the affine action**. A C5 profile rotation cannot inject into AGL(1,9) because 5 does not divide 72. Conversely \(K^\times\) contains a C5 subgroup; its 80 nonzero elements break into 16 orbits of size 5.

## Where Monster identification stops

The exact numerical chain is

\[
3^9=19683,\quad 10\cdot3^9=196830,\quad
196830+53=196883,\quad 196883+1=196884.
\]

The first identification is now a *typed finite set isomorphism* with the original pointed carrier and explicitly transported D4 action. The latter two are number/dimension equalities in the pre-existing MonsterFilteredCarrierExact associated-graded candidate and JPlusOneScaleBridge. They do **not** provide an actual Monster action on the 196830-dimensional component, or a Monster-invariant 53-dimensional extension, irreducibility, modular j-invariant identity, physical magneto-optical dynamics, neural consciousness, or a quantum mechanism.

Source-written Agda theorem versus exact-head kernel run, finite Python result versus physical evidence, and derived D4 transport versus source-original action must remain distinct.

## Implementation and acceptance

New source: DASHI/Biology/IITJFineSelectedCrossPunctured79Exact.agda; new executable: scripts/iit_jfine_selected_punctured79_audit.py; imported into IITPhiIntegrationEverything.agda and scripts/iit_numeric_verification.py. The script is designed to exhaustively check the 19683-state 5+4 codec, finite multiplication/inversion, 72 affine transformations, fifth-root spectrum and known false identifications. The finite-field/spectrum computation was independently executed locally (80 nonzero inversions; five fifth roots; 9-element subfield; eigen orders as above). No exact-head run of the newly committed GitHub script or kernel compilation of the new Agda proofs is claimed.

Next cuts: (1) exact-head Agda kernel receipt for both pointed and JFine codecs; (2) kernel-checked four-trit F81 multiplication and fifth-root eigen decomposition, preferably by reuse of an existing finite-field owner; (3) direct actual 125-site shift/source spectral identification, preserving source matrix orientation; (4) registered group-action intertwiners, with negative order obstructions when appropriate; (5) source-specific neural/AI consumers without physical claim promotion.


## Existing F9 owner and constructive nonidentification (additional source archaeology)

The p=3/Ogg lane **already contains F9-shaped arithmetic structure** in OggSSPP3F9FrobeniusCandidateNoGoExact: F9 ≅ F3[α]/(α²+1) at the coordinate level, a Frobenius involution (a,b)↦(a,−b), six orbits on the full nine-point state, and an equivariant extension-coordinate quotient to a three-point/two-orbit target. OggSSPP3F9ExtensionQuotientSourceExact explicitly reserves the actual marked supersingular moduli identification as an **external uninhabited source gate**. This is source prior art for F9, not evidence that the new F81 field's unique nine-element subfield is *already identified* with the arithmetic p3 marked moduli object or with original C3² phase actions. A precise tower embedding into F81 needs a selected F9 basis/intertwiner matching the chosen quartic quotient.

A second negative-control result is now **source-written as an explicit witness**, not only group-order discussion: in IITJFineSelectedCrossPunctured79Exact, rotateFive has order five on the selected five profile labels and moves a centre-only nonzero profile, whereas the literal source PointedTernaryBulkExact D4 quarter rotation fixes its centre site. Therefore those specific actions cannot be equated. The selected five/corner nine-state codec remains a genuine two-sided carrier equivalence.

The D4 permutation action on the 196830-element pointed set can be **linearised** on the formal complex free vector space with that set as basis to obtain a 196830-dimensional D4 permutation representation. This is a legitimate *derived D4-module*, NOT a Monster action or Monster-invariant 53-dimensional complement. One should distinguish *196830 states* from a *196830-dimensional complex representation* until this linearisation is explicitly stated.

### Local independent finite receipt

An independent local script at /mnt/data/independent_jfine_79_check.py was executed, not just described. It exhaustively checked the chosen cross/corner roundtrip for all 19683 nine-trit states; independently checked the quartic's nonzero multiplication has no zero divisors, every nonzero inverse via x^79, F9-subfield size 9, 72 distinct affine maps and the eigenvalue-order distribution 0:5,8:12,16:12,40:48,80:48. Its JSON receipt is /mnt/data/independent_jfine_79_receipt.json. This is independent arithmetic verification **not** an execution of the exact GitHub script and **not** a kernel-checked Agda proof.
