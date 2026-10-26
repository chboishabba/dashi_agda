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


## Decisive further identification: projective 9+1 and punctured 72+8

The user observed **9×8=72**. The natural missing object is the projective line \(\mathbb P^1(\mathbb F_9)\), of **9 ordinary points plus the point at infinity**, with eight nonzero F9-scalars per projective line. Because \(\mathbb F_{81}\) is a degree-2 extension of F9, \(\mathbb F_{81}\) can be identified with the homogeneous coordinate vector space \(\mathbb F_9^2\) after choosing a basis \(1,\beta\). Thus:

\[
\mathbb F_{81}^\times / \mathbb F_9^\times
\cong \mathbb P^1(\mathbb F_9),\qquad
|\mathbb P^1(\mathbb F_9)|=9+1=10,
\]
\[
|\mathbb F_{81}^\times|=80=(9+1)\times8=9\times8+8=72+8.
\]

**Exact constructive finite witness:** using the same quartic F81 and the unique nine-element subfield \(F9=\{x:x^9=x\}\), choose \(\beta=X\notin F9\). Every vector \(z\in F81\) has unique \(z=a+\beta b\) with \(a,b\in F9\). For \(z\ne0\):
- if \(b=0\), project to \(\infty\), store nonzero scalar \(a\in F9^\times\);
- if \(b\ne0\), project to affine slope \(a/b\in F9\), store nonzero scalar \(b\).
- reconstruction is \(z=b(a/b+\beta)\), or \(z=a\cdot1\) at infinity.

This establishes an **exact 80-element two-sided trivialisation**, conditional only on the chosen basis/affine chart. The *projective quotient itself* is canonical given the F9 subfield, whereas its designation of infinity and chosen scalar representatives are not canonical without a chart. The finite independent Python audit confirmed ten lines, eight nonzero vectors per line, 72 affine and eight completion elements, with all 80 reconstruction roundtrips.

**Stronger old-source reuse:** the new Agda IITProjectiveF9Pointed80Exact constructs an actual two-sided isomorphism between the original Harmonic.CoarseChannel and **F9-shaped affine nine plus point infinity** using the already existing OggSSPP3F9FrobeniusCandidateNoGoExact.F9Point source carrier; completionJ goes *exactly* to its chart infinity. The actual older OggSSPP2PuncturedKernel2BidiExact eight-state carrier and actual punctured four-trit eighty-state carrier are both named in a typed Projective80Trivialisation obligation. The concrete 80-way section/retraction is **currently verified by finite arithmetic, not inhabited by an Agda field operation**. The original Ogg F9 source models a Frobenius action and does not prove external identification with supersingular moduli.

**Important correction to potential overclaim:** \(\mathbb P^1(F9)\) is not the modular function \(j\) or the modular curve itself; calling the distinguished finite projective point \(\infty\) a completion of the local harmonic chart does **not** make it the cusp of a classically sourced elliptic modular curve without a geometric moduli map. We have now proved a set-chart identification and given a complete finite projective quotient calculation, **not** a moonshine/Monster equivariant identification.

The observation 9×8=72 alone could also denote the distinct affine group AGL(1,9). There are now TWO independent, equally numbered 72-element structures:
1. nonzero homogeneous-coordinate vectors above the nine *affine projective points* (nine eight-element fibres);
2. affine bijections \(z\mapsto az+b\) of F9, with a∈F9×, b∈F9.

They have equal cardinality but **are not the same set/action by definition**; the first is 72 points in F81×, the second is 72 functions acting on F9. Neither number promotes a physical or Monster claim.

**Pre-existing projective-geometric proof donors:** ProjectiveLineHomogeneousPairExact, ProjectiveLineAffineChartsExact and ProjectiveLineAtlasHomogeneousWeldExact own general projective coordinate/overlap constructions over an abstract ComplexFieldPresentation. Our P1(F9) uses finite-field coordinate laws, so do not silently import a CP1/complex theorem as an F9 theorem; transport requires the specific field-presentation instance.

**Acceptance:** run scripts/iit_projective_f9_pointed80_audit.py and the aggregate numeric verifier at the exact PR head; compile IITProjectiveF9Pointed80Exact.agda with source-pinned Agda. Independent local arithmetic receipt is /mnt/data/independent_f9_projective_receipt.json. A genuine same-structure J to modular curve/Moonshine or physically measured system is still unproven.


## PGL2(F9): why the affine 72 is the infinity stabilizer, and why C5 appears

**The finite projective action has now also been independently computed on all ten actual chart points.** Its full fractional-linear symmetry group is

\[
|\operatorname{PGL}_2(\mathbb F_9)|
=\frac{(9^2-1)(9^2-9)}{9-1}
=\frac{80\cdot72}{8}
=\mathbf{720}.
\]

The stabilizer of projective infinity consists of the affine maps \(z\mapsto az+b\), hence has **72** elements, and its orbit has index \(720/72=\mathbf{10}\). Therefore
\[
\mathbb P^1(\mathbb F_9)
\cong
\operatorname{PGL}_2(\mathbb F_9)\big/
\operatorname{AGL}(1,9)
\]
as a transitive group-set. This is a **structural** reason for nine ordinary points plus one infinity, not just a cardinality fact.

There is a cyclic order-ten *Singer subgroup* coming from \(\mathbb F_{81}^{\times}/\mathbb F_9^{\times}\) acting regularly on the ten projective points. Its unique order-five subgroup acts as **two disjoint five-cycles** on the ten points. This is a natural new mathematical relationship to the five-slot lost diagonal profile; however the original D4-square action is not the Singer C5 action. The Singer order-five action **moves infinity** and therefore is not in the 72-element affine stabilizer. Thus \(5\nmid72\) is no contradiction: C5 is present in *PGL2(F9)* of order720, not in the infinity-fixing affine subgroup.

**Exact local group receipt:** an independent finite-field script enumerated all 720 distinct fractional-linear permutations of the ten projective points from F9 matrices, found 72 infinity-fixing permutations, an order-ten cycle, and two order-five cycles. The new IIT owner script is scripts/iit_pgl2_f9_720_audit.py; its aggregate numerical verification is wired but fresh exact-head GitHub script execution is not claimed. The independent JSON is /mnt/data/independent_f9_projective_group_receipt.json.

The older Hodge/complex projective owners ProjectiveLineHomogeneousPairExact, ProjectiveLineAffineChartsExact and ProjectiveLineAtlasHomogeneousWeldExact are **generic structural donors only**. The present F9 projective line is a finite-field object and is *not* the complex Riemann sphere or a physically measured Möbius field. Similar formal Möbius patterns in Ferrocell optics do not establish material/spacetime identity. This source/action distinction is essential under the attribution rules.


## 2026-10-24: field inverse and gap of three minus one

The exact relation is 79=81-(3-1)=3^4-2. The set F81 has 81 elements; puncturing zero leaves a multiplicative group of order 80. Finite-field Fermat then gives a^80=1 and a^79=a^(-1) for any nonzero a. The two units subtracted have **different roles**: remove zero, then reduce the exponent to obtain an inverse. No interpretation as two spatial degrees or a physically measured C3 symmetry is licensed by this arithmetic.

New Agda producer: DASHI/Biology/IITField81Inverse79ContractExact.agda provides an explicit conditional multiplicative law and the inverse79Left proof assuming a supplied nonzero Fermat80 certificate. It is imported into IITPhiIntegrationEverything. This proves the correct interface-level implication but does **not** construct the literal quartic multiplication or discharge Fermat80 in the Agda kernel. That concrete field proof remains an open obligation.

The primitive generator selection in scripts/iit_pgl2_f9_720_audit.py was strengthened to explicitly check multiplicative order 80 before using it to produce the Singer C10. The independent local F81 unit-inverse and projective checks remain valid as finite computational evidence, distinct from exact-head GitHub script execution or Agda compiler receipts.


## 2026-10-24 max-cut: 79, relative norm, and **concrete** Agda source codecs

### Refined arithmetic: 81-79 = 3-1 without confusing field elements and integers

Let K=F81=F3[X]/(X^4+X+2) with its **unique** subfield L=F9. For x≠0,

\[
x^{80}=1,\qquad x^{-1}=x^{79}=x^{81-2},
\quad 81-79=2=3-1.
\]

The equation with 3−1 is characteristic-three arithmetic coincidence; inversion in a general Fq has exponent q−2, *not* q−(p−1). The integer 81 maps to zero in characteristic 3 and **has no field reciprocal**; 79 is a power **exponent**, not the reciprocal of 81. Also 79≡−1(mod80), making inversion an involution. Its fixed nonzero elements are exactly +1 and −1; the C10 norm-one subgroup has two fixed points and four swapped pairs.

The true extension-field/Galois connection is:

\[
\operatorname{Frob}_{K/L}(x)=x^9,\quad
N_{K/L}(x)=x\,x^9=x^{10}\in L^\times,
\]
\[
x^{-1}=\frac{x^9}{N_{K/L}(x)};\qquad
N(y)=1\Longrightarrow y^9=y^{-1}.
\]

The **canonical projective group quotient** admits the stronger explicit norm-one identity
\[
K^\times/L^\times
\ \cong\ \ker(N_{K/L}) \cong C_{10},
\quad [x]\longmapsto x^{8}.
\]
Kernel of \(x\mapsto x^8\) is precisely \(L^\times\) (eight elements); image comprises all ten norm-one points, with exactly eight sources per image. The C5 subgroup has two five-cycles on the projective ten-point carrier. None of these facts implies an SSP p79 lane or Monster action.

### Same-original-quartic source arithmetic, not just abstract finite fields

A **specific registered tower basis has been independently verified** inside the **same** old DASHI quartic \(X^4+X+2\):
- \(\gamma=(0,1,2,2)\) in the original four-trit polynomial coefficient order, with \(\gamma^2=-1\) and \(\gamma^9=\gamma\), hence \(L=\mathbb F_3[\gamma]\cong F9\).
- \(\beta=(0,0,1,1)\), with \(\beta^2=1+\gamma\), which is nonsquare in L; hence \(K=L[\beta]\).
- Literal two-sided coefficient conversion:
\[
(a_0+a_1\gamma)+(b_0+b_1\gamma)\beta
\longleftrightarrow
(c_0,c_1,c_2,c_3)
=(a_0,\ a_1+b_1,\ -a_1+b_0+b_1,\ -a_1+b_0-b_1).
\]
The inverse is
\[
(a_0,a_1,b_0,b_1)
=(c_0,\ c_1+c_2-c_3,\ c_1+c_3,\ c_3-c_2).
\]
All expressions are over F3. **Independent exact local executable** \`/mnt/data/f81_f9_tower_same_object_audit.py\` checked a bijection on all 81 elements, **6561** pairs of additions and **6561** pairs of multiplications, plus Frobenius9 conjugation and norm10.

### New in-kernel-candidate implementations, with accurate authority statuses

The earlier typed \`Projective80Trivialisation\` and \`PuncturedF81PowerLaws\` records were not sufficient for a concrete source-level proof. This round implements more:

1. **DASHI/Biology/IITF81F9ConcreteQuarticTowerExact.agda**: explicit F3 addition/multiplication, actual original Ogg F9-shaped coordinates, concrete quadratic-tower multiplication, actual \`TriadicPAdicCodec.Kernel4\` forward/backward basis transformations, transported quartic addition and multiplication. It adds **exhaustive closed Agda proof cases** for all 81 two-sided carrier maps, all 81 Frobenius9 and norm10 statements, and all 80 punctured-state Fermat80, inverse79, norm-one quotient, inversion involution and Frobenius/inverse identities. This is stronger than numerical cardinalities: source original carrier is the actual PuncturedKernel4.
2. **DASHI/Biology/IITProjectiveF9Punctured80ConcreteExact.agda**: **constructive 80-case** forward/backward lookup from literal \`RiemannQuarticTriadicCodecKernelBridgeExact.PuncturedKernel4\` to original \`IITProjectiveF9Pointed80Exact.ProjectiveF9Chart × OggSSPP2PuncturedKernel2BidiExact.PuncturedKernel2\`; two-sided proofs enumerated, and the previously uninhabited **\`Projective80Trivialisation\` record is now inhabited as Agda source**. Lookup tables derive from the same tower basis/division; no equal-cardinality shortcut.
3. **DASHI/Biology/IITF81F9NormInverseBridgeExact.agda**: reusable algebraic theorems for inverse79 and Frobenius9 inversion on norm-one, now a conditional abstraction over the original PuncturedKernel4 type. Not a competing field. The concrete companion above provides the exact source-level finite computations, although the abstract closed-under-multiplication record still requires a separate kernel transport instance.
4. **scripts/iit_f81_f9_norm_inversion_audit.py** and **scripts/iit_f81_f9_quadratic_tower_audit.py**: source-faithful finite arithmetic; wired into \`scripts/iit_numeric_verification.py\`; the original selected/punctured, 5cube, P1(F9) and PGL2(F9) audits remain reused.
5. **Integration:** all new Agda files imported by \`IITPhiIntegrationEverything.agda\`. No parallel reimplementation of the 2×2 XOR model, raw 125-node rank, original JFine source codec, Ogg p3 Frobenius, or historic Monster modules.

### Independent local receipts / exact-head admission

- /mnt/data/f81_f9_norm_inversion_receipt.json: 81 field elements, 80 units; norm-one 10, F9 scalar fibres 8, both fixed inversion units ±1; 80 same-object quotient cases; C5 two orbits.
- /mnt/data/f81_f9_tower_same_object_receipt.json: source quartic↔F9 tower bijection on 81 elements and **13,122** individual binary operation comparisons (6561 additions plus 6561 multiplications); Frobenius and norm.
- A separate local check matched the **actual source** 80 punctured Kernel4 field vectors with chosen F9 projective quotient slopes and nonzero scalars, all 80 forward/backward pairs.

**REMAINING BLOCKER**: the environment lacks the pinned Agda compiler/stdlib checkout, and GitHub access here is through the connector (container cannot clone). Thus **source-written exhaustive Agda equations are not yet a recorded Agda kernel pass**, and newly committed GitHub Python scripts have not received an exact-head checkout run. Never claim these as proven/CI-green solely from their code or independent local Python results. Importantly, there is now no *conceptual need* to invent another field carrier to unblock that check: the explicit source code and exhaustive test cases are committed.

**Acceptance commands when compiler is present:**
\`\`\`sh
python3 scripts/iit_f81_f9_norm_inversion_audit.py
python3 scripts/iit_f81_f9_quadratic_tower_audit.py
python3 scripts/iit_numeric_verification.py
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Biology/IITF81F9ConcreteQuarticTowerExact.agda
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Biology/IITProjectiveF9Punctured80ConcreteExact.agda
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/EverythingIITPhiIntegrationMaxCut.agda
\`\`\`

**Next Pareto cut after the exact compiler receipt:** transport the verified **concrete quartic** operations and proofs of nonzero-product closure into the abstract \`PuncturedF81PowerLaws\` and the source-specific projective norm-one intertwiner. Full Monster module, actual modular j-cusp, neural/AI source traces, quantum observables and IIT Φ remain independent requirements, not consequences of the 79 arithmetic.


## 2026-10-24: two FOUR-trit shells plus one distinguished centre (S3/zeta)

New [source and experiment roadmap](./2026-10-24-iit-jfine-4-1-4-s3-zeta-gauge.md). The old cross5/corners4 is now complemented with the D4-site-stable split **corners4 + centre1 + edges4**. It is NOT five + four with an unexplained extra dimension: \(3^9=81\times3\times81\), and using the centre as a balanced-ternary gauge makes 3^8=6561 relative configurations with a free uniform-translation C3 orbit of three full configurations each. All 19683 source sheets and 118098 affine S3 equivariance equations were checked in independent local Python. A direct source-written Agda two-sided codec and source-recentered S3 laws now live in IITJFineFourOneFourS3ZetaGaugeExact.

The source-typed regular C3 extension uses the **literal existing 10×FineFrequency pointed harmonic carrier**, not a copied 196830-element Fin. IITJFineS3RegularMonsterCharacterExact makes (coarse marker, eight relative trits, centre) its same-C3-set chart. It yields 65610 free C3 orbits. The complex linearised S3 action has pointed multiplicities (trivial 32810, sign 32800, 2D standard 65610), and its C3 restriction has phase multiplicities 65610 each. This character therefore matches **the existing Monster3BRegularC3BulkResidualFiftyThreeBidiExact character** \(W|C3=53·1+65610·Reg(C3)\), at its regular bulk level. It does NOT supply a canonical intertwinining into the literal Monster W nor the full normalizer action. A point/value reflection in our pointed action has trace 10; this is now a concrete experimental/formal action-discriminator for the normalizer comparison.

An important new firewall: F81 has characteristic three and its nonzero group order80, so it contains **no nontrivial cubic roots of unity**. The zeta sector decomposition is over C/Q(zeta3) after complex linearization, not inside F81. Original Ogg F4 zeta and characteristic-zero Monster zeta are distinct fields linked only by an explicitly sourced C3 chart. D4 edge-vs-corner permutation modules remain inequivalent (vertical mirror fixes 2 edges, 0 corners). Preserve original 79 inverse-exponent field and projective 72/720 proofs as a *different algebraic lane*.

The prior Agda IITF81F9ConcreteQuarticTowerExact and IITProjectiveF9Punctured80ConcreteExact **have since been added to this branch**, containing explicit closed finite proof cases for source-actual field arithmetic and projective 80-way roundtrip. Their presence supersedes earlier roadmap prose saying only a conditional interface was available, though fresh exact-head kernel receipts and any further coherence/normalizer bridges still require verification.


## 2026-10-25: Two four-trit shells + centre; mixed S3/zeta maximum cut

The user asked whether the same original 19683-state JFine could be represented as **\(3^4 \times 3 \times 3^4\)** with two four-trit blocks and one distinguished centre, and how this interacts with S3/balanced ternary/zeta. The answer is affirmative, with the stronger D4/S3 and character obligations now implemented. **Full source and result owner:** [\`2026-10-25-iit-jfine-4-1-4-s3-zeta-mixed-characters.md\`](./2026-10-25-iit-jfine-4-1-4-s3-zeta-mixed-characters.md).

The earlier \`IITJFineFourOneFourS3ZetaGaugeExact\` / \`IITJFineS3RegularMonsterCharacterExact\` / \`IITJFineS3Heisenberg90x729CodecExact\` / \`IITJFineD4EquivariantHeisenbergGaugeExact\` sources had **already** made the principal 4+1+4 codec, centred C3-gauge action, zeta/\(65610\) regular C3 multiplicities, and 90×729 chart. No duplicate implementation was introduced for them.

The new \`IITJFineD4S3MixedCharacterExact\` and companion Python audit establish the independent **D4(site) × S3(global ternary values)** comparisons: fine sheet 490 orbits; *actual moving-marker* pointed 196830 carrier 4396 orbits (not 4900), full fifteen complex-irrep multiplicities. The full **spatial row/column** \(S_3\wr C_2\) (order 72) instead changes the centre and has 84 combined value-S3 fine-sheet orbits. This spatial order72 is **not** the earlier F9-affine order72, which has an element of order8 absent in the row/column group. A 4+1+4 decomposition is D4-stable and global-value-S3-compatible but **not** stable under the entire spatial row/column72. Neither four-trit shell is a canonical copy of the other as a D4 module; mirror-fixed edge/corner sites are 2 versus 0.

Reminder: complex \(\zeta,\zeta^2\) diagonalisation is distinct from nonsemisimple characteristic3 linear algebra. New source-level commuting proofs and numbers still need exact-head Agda kernel verification and source-specific experimental intervention before any Monster/physical/phenomenal claim.
