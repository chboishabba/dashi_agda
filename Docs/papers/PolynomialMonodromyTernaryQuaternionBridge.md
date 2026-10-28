# Polynomial monodromy: balanced ternary, C3, quaternion and 720 degrees

## Source and provenance
User-supplied **2swap polynomial-roots / Abel--Ruffini video transcript**, especially 9:39--25:24. It is an educational presentation, not a mathematical authority. Original mathematical authors: Abel (1824, general quintic radical impossibility), Galois (1830--1832, solvability by radicals via group structure), Riemann (1851, branched surfaces), Hamilton (1843, quaternions). Modern group references: Dixon and Mortimer, Permutation Groups (1996), DOI 10.1007/978-1-4612-0731-3; Serre, Linear Representations of Finite Groups (1977), DOI 10.1007/978-1-4684-9458-7. Modern context: https://www.dpmms.cam.ac.uk/~pmhw/Galois.pdf and https://classes.golem.ph.utexas.edu/category/2013/06/g2_and_the_rolling_ball.html.

**Attribution:** earlier DASHI S3, C3, balanced ternary, quaternion, Ibrahim Pareto/snowball, and Monster 3B results retain their independent owners. The current contribution consists only of these explicitly constructed compositions. No Moonshine matching or other analogy is promoted into same-object proof.

## Reuse-first owner table

| Existing owner | Consumed theorem/structure | Distinction |
|---|---|---|
| DASHI.Foundations.TernaryEndomorphismConjugacyExact | Six reversible ternary maps and seven 27-endomorphism orbit shapes | Not six unrelated labels |
| DASHI.Foundations.TernaryPermutationS3LawsExact | Exact nonabelian S3 multiplication, swaps, and cycles | S3 is not cyclic C6 |
| DASHI.Foundations.TernaryPermutationCyclicSubgroupsExact | C3 rotation subgroup with exact embedding | C3 misses swaps |
| DASHI.Foundations.HexTruthS3CarrierBridgeExact | Six-state chart and proved failure to preserve the alternate hex group law | Cardinality is not isomorphism |
| DASHI.ComputerScience.BalancedTernaryC2C3DihedralCodecBridgeExact | Classical C2 antipode and C3 cycle | C2 is not C3 |
| DASHI.Algebra.Trit, DASHI.Codec.BalancedTritBitFibre | -/0/+ signed trits | Not a 5-state alphabet |
| DASHI.Biology.NonaryCompletionPhaseQuotientExact | Existing five-mode carrier | Not quintic roots |
| DASHI.Algebra.FiniteQuaternionDoubleCover | Exact Q8 -> V4 sign-forgetting cover | Not full Spin3 -> SO3 |
| DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact | Rational quaternion multiplication/conjugation/norm | No smooth topology |
| DASHI.Moonshine.OggSSPP2BinaryTetrahedralRigidificationQuotientExact | 2T -> A4 central-sign quotient, order-3/order-6 refinement | No same-object Monster inference |
| DASHI.Core.C3OrbitVerticalDynamicsExact; DASHI.Topology.HelicalWeaveMappingTorusExact | Projection return distinct from fine provenance | Round coordinate can advance |
| Draft PR #1407 (2026-10-28) | 3x3x3 27-cube; 13/27 and 5/9 symmetry | No implied polynomial Galois result |
| Draft PR #1408 (2026-10-28) | Signed SSP, prime sieve and information-loss | No implied prime theorem |

## Constructed finite bridge

1. **ABC six permutations:** the two adjacent root swaps generate the preexisting S3. Their permutation images satisfy the three-strand braid relation. Their commutator gives the nontrivial 3-cycle; C3 is an actual proper subgroup. In the braid group a generator and inverse are different paths even though both map to the same S3 transposition.
2. **Projected return:** the abstract LabelledCoefficientState retains an unchanged coefficient descriptor while its root ordering changes. This demonstrates the finite information-loss pattern. It does **not** supply a continuous coefficient path or actual analytic polynomial monodromy.
3. **3^5 versus 5^3:** five balanced-trit coordinates have arithmetic size 243. Three positions in the existing five-mode carrier have arithmetic size 125; these counts are different. For an illustrative monic quintic, five coefficients each restricted to {-1,0,1} yield 243 *different coefficient strings*. Selecting three of its five root labels with replacement yields 125 ordered triples; without replacement yields 5x4x3 = 60. None is a natural bijection, quintic radical formula or complete Galois group.
4. **C3 / quaternion:** q=(1+i+j+k)/2 is a unit rational quaternion. Conjugation by q gives i->j->k->i. This exactly intertwines the existing permRotate action on the ABC labels. q^3=-1, q^6=+1. The associated 3D rotation is 120 degrees; three steps are **360 degrees spatially** but leave spin lift -1; six steps make a **720-degree lifted return**. This is a literal finite rational witness, not a proof of the smooth covering/homotopy theorem. Q8 itself has no half-coordinate element q.
5. **Abel--Ruffini boundary:** S3 is solvable via S3 > C3 > 1. The generic quintic has S5, whose commutator subgroup A5 is perfect nonabelian simple; therefore its general radical formula cannot exist. Some **specific** quintics are solvable by radicals. The video phrase "no algebraic formula for a quintic" must be interpreted as no general formula by radicals, not that algebraic roots cease to exist.

## Ordered max-cut proof obligations

- M0. Type-check the new Agda owner and all three TOE import roots at the actual branch head; source-written is not kernel-verified.
- M1. Formalise discriminant-complement coefficient space and branched root covering, including polynomial roots with multiplicities separately.
- M2. Construct B3 braid words, inverse words and braid relation; construct the quotient B3 -> S3 and exhibit a nontrivial pure braid.
- M3. Exhibit concrete coefficient loops realizing both adjacent transpositions and verify analytic continuation/path lifting.
- M4. Prove S3 derived series and radical cubic resolvent structure without identifying this finite test with all polynomial cubics.
- M5. Prove S4 > A4 > V4 > 1 solvability and quartic radical resolvents.
- M6. Construct S5, A5, their exact derived subgroups and non-solvability (A5 perfect), without postulates.
- M7. Formalise the characteristic-zero Galois solvability/radicals equivalence and the generic S5 quintic, distinguishing solvable special quintics.
- M8. Provide explicit carrier enumerations and lengths before asserting a fully formal no-bijection theorem between the 243 and 125 vectors.
- M9. Upgrade rational q identities to continuous Spin(3)=SU(2) -> SO(3), kernel {+/-1}, lift of loops and noncontractible 360-degree path.
- M10. Show why the exact positive-axis i,j,k permutation action of S3 cannot come from only proper rotations without an orientation correction, even though its C3 part does.
- M11. Define and verify an actual transport to C3 provenance/helical fabrics, rather than matching group orders.
- M12. Wire source/proof/execution/kernel statuses through existing Pareto/snowball/Ibrahim receipts. Preserve original author ownership.

## Evidence restrictions

This new Agda source is **written but not Agda-kernel-verified**. Do not call it a completed proof until the pinned Agda check succeeds. Do not claim a continuous Spin cover, general Galois theorem, polynomial path-lifting theorem, arbitrary-radical impossibility theorem, or Monster object identification. No new postulates, allow-unsolved-metas, TERMINATING or NO_POSITIVITY_CHECK; no ESD modifications. Independent exact-Fraction checks, when executed, are computational evidence only; they are not Agda kernel receipts.


## Transcript-complete obligation ledger — 45 enumerated subjects (28 October 2026)

The identifiers V01–V45 track the full video; their order follows the 45-concept extraction in the prior discussion. The time ranges are approximate because several subjects overlap in the narration. **Status P means finite-source constructed or existing-owner reuse, NOT Agda kernel verification.** The underlying transcript does not mention our quaternion, 3^5 / 5^3, Monster, or 27-cube extensions.

| ID | Approximate timestamp | Video concept | Formal receiver / deliverable | Status |
|---|---|---|---|---|
| V01 | 00:00–01:18 | Polynomial coefficients and zeros | finite exact polynomial evaluation + root predicates | P |
| V02 | 01:18–02:11 | Complex-plane domain colouring | observation map, argument/modulus need analytic charts | I |
| V03 | 02:11–04:25 | N→Z→Q→R→C extensions | source-typed field-extension hierarchy | I |
| V04 | 03:57–04:25 | i and -i solve x²+1=0 | rational-complex exact conjugate witnesses | P |
| V05 | 04:25–04:57 | Algebraic closure of C | FTA receipt / no self-contained proof yet | O |
| V06 | 04:57–05:17 | Degree n yields n roots counted with multiplicity | root-multiset theorem interface | O |
| V07 | 05:17–05:57 | Double roots and local order | multiplicity and winding interface | O |
| V08 | 05:57–06:15 | n+1 coefficients for degree ≤n | finite coefficient-vector representation | P |
| V09 | 06:15–07:12 | ±1 coefficient configurations | finite alphabet cardinality; exact examples | P |
| V10 | 07:12–08:51 | Point-cloud complexity and dragon-curve resemblance | non-promotion of fractal identity | B |
| V11 | 08:51–09:39 | Linear equation solution | field inverse requires a≠0 | I |
| V12 | 09:39–10:26 | Ordered coefficients vs unordered roots | Vieta symmetric invariance finite exact | P |
| V13 | 10:26–11:10 | No global continuous distinguished-root selection | continuous-section obstruction interface | O |
| V14 | 11:10–12:19 | Discontinuous branch choice | two-sheet finite branch model | P |
| V15 | 12:19–13:11 | Real coefficient conjugate root pairing | complex conjugation exact polynomial examples | P |
| V16 | 13:11–13:41 | Movable branch cuts | branch cut bookkeeping interface | I |
| V17 | 13:41–14:32 | Riemann surface two-sheet gluing | covering / ramification interface | O |
| V18 | 14:32–15:02 | Continuous multi-root relation | unordered multiset transport | I |
| V19 | 15:02–15:54 | Square-root loop swaps two roots | finite C2 root-label monodromy image | P |
| V20 | 15:54–16:18 | Cubic needs more than only square roots | S3 derived obstruction conditional criterion | I |
| V21 | 16:18–16:50 | Cube-root three sheets and C3 cycle | C3 embedding reused | P |
| V22 | 16:50–17:08 | C3 cannot make a transposition | S3/C3 proper subgroup proof reused | P |
| V23 | 17:08–17:51 | Two adjacent root swaps | S3 generators and braid-image words | P |
| V24 | 17:51–18:49 | Commute / undo loops; nontrivial commutator | S3 commutator exact | P |
| V25 | 18:49–19:24 | One radical has abelian monodromy | cyclic monodromy and derived-triviality | P |
| V26 | 19:24–20:22 | Nested skewed radicals / shifted branch points | algebraic tower interface; analytic branch geometry open | O |
| V27 | 20:22–20:28 | Cardano cubic radical construction | specific radical formula + field hypotheses | O |
| V28 | 20:28–20:59 | Nested commutators for quartics | S4/A4/V4 derived chain interface | I |
| V29 | 20:59–21:28 | Older radical machine loses deeper action | finite tower derived-length bound interface | I |
| V30 | 21:28–21:55 | Further nested radicals can extend finite solvable depth | tower recursion interface | I |
| V31 | 21:55–22:17 | Single transposition S2 trivial commutator | S2 table and derived identity | P |
| V32 | 22:17–22:33 | Three-root derived series terminates | S3→C3→1 finite exact | P |
| V33 | 22:33–22:57 | Four-root derived series terminates | S4→A4→V4→1 finite check/interface | I |
| V34 | 22:57–23:17 | Five-root two overlapping 3-cycles | literal S5 permutation witnesses A,B | P |
| V35 | 23:17–23:59 | Double commutator recovers generators | A,B finite exact witness | P |
| V36 | 23:59–24:19 | Arbitrarily nested nontrivial commutators | recurrence on A/B commutator identity | I |
| V37 | 24:19–24:55 | Radical towers have finite solvable derived length | conditional derived-length theorem | I |
| V38 | 24:55–25:23 | A5 perfect, S5 non-solvable | finite group proof obligation, not inferred only from two cycles | O |
| V39 | 25:23–25:30 | General quintic no radical formula | Galois criterion with char0 and generic S5 hypotheses | O |
| V40 | 25:30–25:32 | Higher generic degrees similarly obstructed | Sn n≥5 subgroup/inheritance obligation | O |
| V41 | 25:32–25:52 | Zeros of ±1 polynomial families | finite root atlas numeric exact/symbolic checks | I |
| V42 | 25:52–26:17 | Interactive coefficient/root dragging | parameterised coefficient family and tracked labels | I |
| V43 | 26:17–26:30 | Three legal coefficient symbols instead of two | base-3 length-(n+1) count | P |
| V44 | 26:30–26:57 | Demo app / sponsor claims | no mathematical theorem; recorded source provenance | B |
| V45 | cross-cut | Balanced-ternary 3^5 versus five-valued 5^3 | different carriers 243 versus 125; no canonical bijection | P |

**Status key:** **P** new/existing finite source theorem or executable exact witness (Agda kernel still pending); **I** formal interface, finite model, or conditional mathematics; full theorem not discharged; **O** analytic / algebraic global theorem genuinely open in this PR; **B** boundary: descriptive claim, not promoted to a theorem.

### Separate mathematical prerequisites and falsification gates

| ID | Required lemma or construction | Mathematical completion criterion |
|---|---|---|
| A01 | Symmetric polynomial / Vieta | Product coefficients invariant under S_n action on roots, not under arbitrary coefficient permutation |
| A02 | Discriminant complement | Distinct-root coefficient space, discriminant nonzero condition |
| A03 | Ordered/unordered configurations | Quotient by S_n with genuine covering and lift |
| A04 | Fundamental groups and braid groups | B_n as π1 of unordered configuration, P_n kernel of permutation map |
| A05 | Monodromy action | Characterise π1 induced root permutation, with concrete coefficient loops |
| A06 | Branched coverings | Separate singular discriminant fibres and ordinary unbranched parameter space |
| A07 | Derived series of S2/S3/S4 | Exact subgroup and commutator equalities, including solvable termination |
| A08 | Alternating A5 perfection | Prove normal closure of 3-cycles yields A5, or complete finite group enumeration |
| A09 | Galois radical criterion | Characteristic-zero Galois extension, roots of unity, splitting field, both directions |
| A10 | General degree-5 Galois group | Generic independent coefficient indeterminates over appropriate base field have S5 |
| A11 | Continuous Spin3 topology | SU2/SO3 covering, path homotopy, 360-degree nonreturn and 720-degree return |
| A12 | Punctured-loop winding | Winding number relates branch sheets; no claim from colour plot alone |
| A13 | Source/scope provenance | Never promote toy finite action, coefficient-count identity, or Monster fingerprint into a global theorem |
| A14 | Cross-repo ownership | Keep primary mathematicians, existing Agda owner, new bridge source code, executed regression, kernel receipt separate |

### Numerology / cross-pollination — maps with controlled receivers

| Candidate link | Exact transport / finite fact | Promotion gate |
|---|---|---|
| 3^3 = 27 | All ternary self-maps on a 3-point set are 3^3; S3 consists of exactly six reversible ones | The 27 synthesis cells (x,y,z) are a *different* 27-state carrier; use a typed chart, not identity |
| 3^5 = 243 | Five independently chosen signed-trit coefficients of a monic quintic | Not five arbitrary complex roots; coefficient vectors and root multisets have different objects |
| 5^3 = 125 | Three independently chosen values from existing five-mode carrier | This is with replacement; ordered triples of distinct roots would be 5·4·3 = 60 |
| S3=6=C3⋊C2 | Cycle generator r, reflection s with srs=r^-1; use preexisting dihedral bridge | S3 is not the cyclic group C6 or Base369's hexXor |
| 27 orbits | S3 acts by simultaneous relabelling on the 27 unary ternary maps; existing source classifies into seven conjugacy shapes | Cannot identify seven shapes with seven irreducible representations |
| 3 steps / 6 steps | q=(1+i+j+k)/2: q³=-1, q⁶=1 and conjugation cycles i,j,k | Three 120° spatial steps vs six lifted steps; not six root permutations = 720° |
| Q8 -> V4, 2T -> A4 | Existing kernel ±1 and signed lift fibres | Q8 has no 3-cycle q; 2T is a separate proved/typed source, not same-object Monster 3B |
| braid word vs permutation | σ_i and σ_i^-1 both map to same transposition; σ_i² has trivial permutation image but nonzero exponent | Braid history is not reconstructed from S3 endpoint |
| 3-adic / p-adic addresses | Reuse signed ternary codecs and hypervoxel transport to represent finite ordered root labels | Does not imply complex analytic continuation or number-theoretic prime theorems |
| Fourier C3 / 369 | Reuse existing character and convolution owners on finite C3/27 carriers | Do not equate complex root winding to finite Fourier phase by numerical coincidence |
| Pareto / snowball / Ibrahim | Max-cut by independent lemmas and provenance-preserving reindexing | Link only witnessed exact maps; preserve Ibrahim historical/Monster 3B owners |

### Recent PR audit and source roots

- [#1414](https://github.com/chboishabba/dashi_agda/pull/1414): the canonical current **draft** for this topic, extended here.
- [#1407](https://github.com/chboishabba/dashi_agda/pull/1407): C3 / 27 / 729 / Hermitian Fourier submodels; only source-linked reuse, no branch-only import silently absorbed.
- [#1408](https://github.com/chboishabba/dashi_agda/pull/1408): finite sieve and signed SSP, with explicit candidate-vs-global no-go.
- [#1406](https://github.com/chboishabba/dashi_agda/pull/1406): non-Archimedean spectral finite models; no complex-monodromy theorem implied.
- [#1396](https://github.com/chboishabba/dashi_agda/pull/1396): evidence non-promotion aggregation; reuse same guard style.
- Ramond (2022), *The Abel–Ruffini Theorem: Complex but Not Complicated*, DOI 10.1080/00029890.2022.2010494.
- D. Kohli (2023), *An Introduction to Galois Theory and the Abel–Ruffini Theorem*: https://math.uchicago.edu/~may/REU2023/REUPapers/Kohli.pdf.
- Source discussion of braid monodromy: https://edocs.tib.eu/files/e01dh06/52066552X.pdf.
- Binary tetrahedral quaternion chart, David Stone, Stony Brook: https://www.math.stonybrook.edu/~tony/bintet/quat-rep.html.
- Lean AI formalization leaderboard states an Abel–Ruffini benchmark target, not a verified imported DASHI theorem: https://lean-lang.org/eval/problems/abel_ruffini/.

### Max-cut execution order / stop rule

P0: existing owner search, provenance and negative gates; P1: finite S2/S3/C3 algebra + quintic overlapping 3-cycles; P2: finite Vieta and branch covering models; P3: braid-word crossings and pure-braid exponent separator; P4: typed 3^5/5^3/27/S3 and quaternion transport; P5: genuine S4/S5 finite group proof by full enumerations; P6: complex discriminant complement and covering path lifting; P7: field-theoretic solvability by radicals and generic S5; P8: Spin3 homotopy and fibre topology; P9: TOE regression, source receipts, kernel validation. Stop at the first *unpaid external theorem dependency* and record its exact input/output type; do not create an alleged proof using a synthetic certificate or analogy.


## 2026-10-28 continuation: source-written owner inventory and independent exact audit

### Executed scope

All 45 video subjects have exact names in \`DASHI.Foundations.PolynomialVideo45ConceptContractsExact\`. This is a COMPLETE COVERAGE INDEX, not 45 kernel-verified proofs.

**New individual mathematical owner files on the current PR branch:**
- \`PolynomialVietaRootSymmetryExact.agda\`: generic rational cubic Vieta factor expansion, all six S3 root permutations preserve its three elementary symmetric coefficients, evaluation invariance, three zero witnesses and the exact ±i complex example.
- \`PolynomialTwoSheetMonodromyExact.agda\`: C2 deck generator, two-sheet swap, order-two action, coarse return and contradiction for monodromy-invariant sheet selection. The global *continuous* section theorem remains explicitly separate.
- \`PolynomialBraidPermutationImageExact.agda\`: word action under \`B3 -> S3\` generators, Yang–Baxter permutation relation, nonempty σ₀² with identity permutation image, all 36 S3 commutators even, and 9 C3 commutators trivial. Reuses the textile braid rewrite owner.
- \`QuinticOverlappingThreeCyclesExact.agda\`: actual A=(012), B=(234) with a one-point overlap; pointwise inverse checks and the **two literal double-commutator identities** recovering A and B. This is the video's central 5-root finite witness.
- \`Polynomial369TrialecticTransportExact.agda\`: \`LevelTwoCode\` and \`SynthesisChoice27\` are a literal pair-carrier identity, with two-sided chart, S3 conjugation action laws, retained triangular synthesis cell, distinct first-two-slot action and existing quaternion C3/hypervoxel axis action.
- \`QuinticPermutationTripleOrientationAtlasExact.agda\`: explicit **120-case** bijection \`Permutation5 ≃ DistinctTriple5 × Orientation2\`; 60 unique ordered distinct triples; 60 even-parity permutation codes; action of every permutation on the five labels; inverse and first-three-coordinate correctness proofs by constructor reduction. This is much stronger than a same-number coincidence. It does not yet formalise all S5/A5 group-operation laws.
- \`PolynomialNumerologyArithmeticAtlasExact.agda\`: 3^3=27, 3^5=243=9×27, 3^6=729=3×243, 5^3=125=5×25, difference 118, 5P3=60, 5!=120=60×2, even-permutation count 60, parity vs Q8 sign two-sided *carrier* chart with explicit semantic separation.
- \`PolynomialGlobalRadicalTopologyContractsExact.agda\`: explicit **uninstantiated** field, discriminant-cover, analytic-monodromy, radical-solvability, generic-S5 quintic and continuous-Spin theorem contracts. A conditional general-quintic contradiction is proved given all actual inputs.
- \`PolynomialIbrahimParetoSnowballMaxCutExact.agda\`: formal proof-level firewall with direct retained original Ibrahim recognition boundary and exact negative-promotion adapters. Neither this new proof nor its source rights belong to the original Ibrahim Monster 3B claims.
- \`PolynomialMonodromyTernaryQuaternionBridgeExact.agda\`: pre-existing PR #1414 finite S3/C3 and rational quaternion generator.

The eleven new owners plus the original finite bridge are attached through \`EverythingTOESymmetryResolved369\`, \`Unifier\`, and \`Unified/Everything\`. No protected ESD file was edited.

### Independent exact Python audit (EXECUTED, not Agda)

An independent local exact-integer/Fraction calculation was executed with these results:

| Calculation | Exact observed result |
|---|---|
| Derived series S2 | 2 → 1 |
| Derived series S3 | 6 → 3 → 1 |
| Derived series S4 | 24 → 12 → 4 → 1 |
| Derived series S5 | 120 → 60 → 60 (stable) |
| Subgroup generated by the two overlapping 3-cycles | 60 elements, derived subgroup also 60 |
| Explicit nested commutators | recover A and B exactly as permutations of five labels |
| S3 conjugation orbit sizes on all 27 ternary maps | 1, 2, 3, 3, 6, 6, 6 |
| All 5-permutations / ordered distinct triples / parity | 120 ↔ 60×2, with exactly 60 even completions |
| Cubic Vieta sample-grid tests | 625 exact evaluations, all six root orders per sample preserved |
| Quaternion q=(1+i+j+k)/2 | unit norm, q³=-1, q⁶=1, i→j→k→i |
| Alphabet families | 3^5=243, 5^3=125; distinct three-root choices=60 |

The source committed to \`scripts/check_polynomial_video_complete_maxcut.py\` implements materially equivalent calculations, but **the committed GitHub blob was not executed inside a checked-out repository**. Do not call this a successful exact-head CI receipt.

### The new 60-state cross-pollination is mathematical, not just numerical

For five labelled roots, each *ordered injective triple* \`(a,b,c)\` leaves two unused labels. Those labels can be appended in two orders, producing two permutations of five. Exactly one completion is even (because swapping the last two positions reverses parity). Thus the set of **even permutations** is in bijection with ordered injective triples. More strongly, the natural A5 action on that 60-element triple set is free and transitive: stabilising three individual labels forces an even permutation to fix the remaining two as well, and any target triple can be reached by adjusting the last-two order to even parity. The explicit 120/60 atlas is **source-written**; a formal Agda group-action proof of regularity still needs group operation/closure and stabiliser lemmas (P5). This is NOT the same as three arbitrary five-valued digits (125 combinations with replacement).

Compare to our other two-state refinements: quaternion central \`±1\`, binary completion phase, and orientation parity all have two elements, but are separate carrier meanings. Their two-element charts are not identifications of physical spin, field Galois sign, binary tetrahedral inertia, or Monster 3B.

### Remaining irreducible proof debt and evidence cut

- **Agda:** type-check all new source modules and three TOE roots at the exact branch HEAD. All source theorem proofs remain **kernel-pending**.
- **Group theory:** derive general A5 perfection and simplicity by formal group operation, 3-cycle generation, all necessary conjugations; finite Python agrees but not Agda-verified. Likewise S4 quartic derived subgroup equalities need first-class Agda proof.
- **Topology:** construct an actual complex polynomial coefficient discriminant complement; prove unordered-root covering, π1/B_n, loop lifting, and square/cube-root branch structures. A finite swap model does not supply continuity.
- **Field theory:** splitting fields, Galois groups, radical-tower criteria in both directions, generic S5 group, special solvable quintic exceptions.
- **Spin:** continuous SU2→SO3 covering and path homotopy; exact rational q remains a discrete 720-degree witness.
- **Historical / provenance:** never reassign Abel/Galois/Riemann/Hamilton, original Ibrahim, earlier DASHI source proof owners, source-authored PR code, executed Python checks or Agda kernel status; never infer same-object Monster 3B from counts, symmetric character fingerprints or synthetic receipts.


### C3/Fourier/trialectic receiver (additional exact owner)

\`DASHI.Foundations.PolynomialC3FourierTrialecticChartExact\` consumes \`TriadicDepthOneCharacters\`, \`C3FourierConjugationExact\`, \`C3CubeFourier27Exact\`, and the existing three-coordinate \`SynthesisChoice27\`. It provides a genuine C3 phase-group isomorphism (all nine multiplication cases), reuses the symbolic Fourier conjugate-row proof \`chi1 ↔ chi2\`, constructs a lossless two-sided \`SynthesisChoice27 ↔ Cube3\` chart, and retains the original cube-character homomorphism. This is a finite C3/C3³ character transport only; it is **not** analytic continuation of polynomial roots, an actual complex Riemann-surface Fourier transformation, or an independently established Monster 3B representation. The module is imported into all three canonical TOE roots; its newly authored source remains kernel-pending.

A further external prior-art confirmation is the American Mathematical Society account of the Artin braid-group exact sequence \`1 → P_n → B_n → S_n → 1\`, https://doi.org/10.1090/noti2452, and the source about exponent-sum \`B_n → ℤ\` (which distinguishes σ₀² from the identity), https://stoimenov.net/stoimeno/homepage/papers/burex2.pdf. Those are mathematical source authorities, not proof terms automatically imported into Agda.

**Execution update:** The independent exact replay also checked \`Permutation5 ↔ DistinctTriple5 × Orientation2\` as a bijection over all 120 permutations, verified 60 even permutations and 60 distinct triples, and found exactly one even completion per triple. The committed script includes this 120-case replay, but an execution from that exact GitHub blob is not recorded.


## 2026-10-28 attached Alexander–Hatcher steelman + Gamma/9999! + Pickover/Spin cut

**Attachment provenance:** the newly supplied 613-line file *The full formalism of our current steelman* is a user's research synthesis, NOT an Agda source, independent kernel receipt or proof of the geometric wild embedding. It discusses Alexander's classical wild ball, Hatcher's Example 2B.2, the three-factor limit group, perfectness, \(C_3\) outer automorphisms, binary icosahedral \(2I\) gauge holonomy, and a Pickover phase. The attachment does **not** contain verbatim evidence of the separate video's phrase “theta is the factorial function”; treat that as an interpretation to resolve using notation evidence, not a transcript-verified historical quote.

### Critical notation and original-phase target

- The standard analytic extension of factorial is **Euler's \(\Gamma\)**, with capital Gamma notation attributed to Legendre: \(\Gamma(n+1)=n!\). In particular \(\Gamma(10000)=9999!\), not \(\Gamma(9999)=9999!\).
- The symbol **\(\theta\)** ordinarily denotes an **angle** in \(z=e^{i\theta}\), or, in a different context, a Jacobi theta function. Neither is *definitionally* the factorial function. A source may make a private substitution \(\theta:=n!\) or \(\theta:=99^{n!}\), but that is an expression assigned to an angle, not an identity between \(\theta\) and \(\Gamma\).
- NIST primary reference on notation: https://dlmf.nist.gov/5.1, Gamma integral and residues: https://dlmf.nist.gov/5.2, Jacobi theta functions: https://dlmf.nist.gov/20.2.
- **Exact intended object:** \(E=9999!=\Gamma(10000)\), \(M=99^E\). This is not \((99^{9999})!\), \(99^{\Gamma(9999)}\), superfactorial or a power tower.
- **Actual hard real analytic target:** \(\operatorname{sgn}(\sin M)=\operatorname{sgn}(\Im e^{iM})\), in **radians**. Equivalently \( (-1)^{\lfloor M/\pi\rfloor}\) for this nonzero integer \(M\) (not an integer multiple of \(\pi\)). No exact terminal real interval or parity certificate has been constructed.
- **Different solved degree-angle target:** \(\operatorname{sgn}(\sin(M\pi/180))=+\), since \(M\bmod 360=81\) and \(81^\circ\in(0^\circ,180^\circ)\). Degree reduction is NOT reduction modulo the real period \(2\pi\) for radian \(M\).

### Concrete exact independent Python replay

With Python's exact integer factorial and modular exponentiation, the locally executed independent replay found:

| Exact item | Result |
|---|---|
| \(\mathrm{bit\_length}(9999!)\) | 118445 |
| \(v_2(9999!)\) | 9991 |
| \(v_3(9999!)\) | 4996 |
| \(v_5(9999!)\) | 2495 |
| \(v_{11}(9999!)\) | 998 |
| \(v_{101}(9999!)\) | 99 |
| \(99^{9999!}\bmod 9\) | 0 |
| \(99^{9999!}\bmod 11\) | 0 |
| \(99^{9999!}\bmod 101\) | 1 |
| \(99^{9999!}\bmod 360\) | 81 |
| \(99^{9999!}\bmod 9999\) | 4950 |
| CRT idempotent | \(4950^2\equiv4950\pmod{9999}\) |
| \(S_5\), \(A_5\), ordered injective triples × parity | \(120\), \(60\), \(60\times2\) |
| Two overlapping 3-cycles | generate all 60 of \(A_5\); 60-element commutator subgroup |

The committed script \`scripts/check_polynomial_pickover_gamma_horned_maxcut.py\` contains the corresponding finite replay but was not executed from its exact GitHub blob. The independent in-session replay **passed**. The analytic \(\operatorname{sgn}\sin(99^{9999!})\) is NOT among its outputs.

### Explicit reusable mathematical proof terms

- \`PolynomialPickoverFactorialGammaDegreeExact.agda\`: reuses the standard-library factorial \`Data.Nat.Base._!\`, proves the successor recurrence and the **conditional** Gamma-at-successor contract for \(\Gamma(10000)\); proves the exact \(99^2\bmod360=81\) and residue-toggle statements; gives an inductive TWO-STATE positive-even-degree exponent automaton. This does not by itself prove the full \(\mathbb Z/360\mathbb Z\) modular exponent congruence for every \(n\), which is separately replayed in Python for the target integer. The radian sign is explicitly unproved.
- \`PolynomialHornedPerfectGroupObserverExact.agda\`: proves an exact universal **commutator-factorisation ⇒ commutator-killing observer is trivial** theorem. The source gives a finite list of pairs for *each* group element, and the target observer preserves products. This is the reusable algebraic fact connecting perfect \(A_5\), the perfect binary icosahedral \(2I\), and the abstract three-factor horned-source limit. Their actual groups and origin proofs remain distinct. Every group element need only be a PRODUCT of commutators; do not assert commutator width one for the horned limit group without its own witness.
- \`PolynomialHornedSpinSignNonDescentExact.agda\`: reuses existing exact \(Q_8\to V_4\) quotient, proves that \(+1\) and \(-1\) have the same projective image but are distinct, and proves **NO universal signed-quaternion reconstruction** from the sign-forgetting projection. Do not identify this \(Q_8\) witness with \(2I\to A_5\); the latter is a separate stronger donor in PR #1244.
- All three owners are imported and named exported through the three canonical TOE root aggregates. This is source-written, **Agda kernel pending**.

### Dated donor / prior-art ownership: source-first reuse, not branch-copy

| Independent source owner | Established material | This PR's valid receiver | Non-promotion |
|---|---|---|---|
| [#1244 Alexander horned C3](https://github.com/chboishabba/dashi_agda/pull/1244), draft | Three-sector binary-horn tree, commuting \(C_3\) refinement, conditional perfect group and outer action, finite \(2I\) quotient and central-sign non-descent | Universal commutator-observer proof + shared \(C_3\) and rational quaternion labels | No source-group = actual geometric exterior identification until H1–H5 and compact-exhaustion geometry are paid |
| [#1260 Eisenstein/Pickover](https://github.com/chboishabba/dashi_agda/pull/1260), draft | Exact factorial CRT, \(3^4\times3^5\) Eisenstein quotient, \(4950\) idempotent, Machin small-phase signs, catastrophic interval-width cost | Gamma index contract and comparison of **degree** vs **radian** phase | Finite CRT quotient and ultrametric observer do not furnish the terminal \(\operatorname{sgn}\sin M\) |
| [#1407 369/27 Fourier](https://github.com/chboishabba/dashi_agda/pull/1407), draft | C3/Fourier finite 27×729 and 13/27,5/9 structure | Existing \(C_3^3\) Fourier/trialectic chart | Not a polynomial path-lift theorem or a Monster same-object identity |
| Existing \`FiniteQuaternionDoubleCover\` on master | Actual \(Q_8\to V_4\) double-cover | Exact universal no-reconstruction proof | No \(2I\) quotient identified with this group |
| Existing \`TernaryEndomorphismConjugacyExact\` | 27 endomorphisms, S3 orbits | 27↔27 trialectic carrier identity and seven orbit sizes | A 27-cell synthesis is not an Alexander horn binary branch or a new Galois quintic |
| Existing \`IbrahimMonster3BRecognitionRouteParetoExact\` | Ibrahim independent Monster 3B/source-control and Pareto gates | Retained existing-owner receipt and no-promotion theorem | No matching order, trace or phase authorises object equality |

**Critical 120-vs-120 check:** \(S_5\) and \(2I=SL_2(\mathbb F_5)\) both have **120 elements**, but they are **not isomorphic as groups**. \(S_5\) has a nontrivial sign homomorphism \(S_5\to C_2\), whereas \(2I\) is perfect. Also \(Z(S_5)=1\) whereas \(Z(2I)=\{\pm1\}\). The projective quotient \(2I/\{\pm1\}\cong A_5\) has **60**, matching the ordered-injective triple count with an ACTUAL finite chart on the \(A_5\)-label carrier, not proof that a source quintic polynomial, horn exterior, or Monster module realises that quotient. The exact group-level donor lives in PR #1244.

**Critical end-space count:** the actual horn sector address set at finite depth \(n\) has \(3\cdot2^n\) sectors/branches; it is NOT \(3^n\), \(3^5\) or \(5^3\). The 3-sector root labels can be charted to \(C_3\), but the internal Cantor/horn refinement is binary. The clopen ultrametric end topology is intrinsic, and does not prove the ambient Alexander wild embedding.

**Critical holonomy readout:** chosen two-dimensional spin-channel halftrace is \(-1\), while the normalised trace of \(\operatorname{diag}(-I_2,I_2,I_2)\) in the full six-dimensional three-channel actor is \(1/3\). Neither equals the unknown \(\sin M\) or determines its sign.

### Remaining cut, in Pareto priority

1. **P0** Real analytic terminal signed phase of \(e^{i99^{9999!}}\), with independently verified rational \(\pi\)-phase interval and end-to-end certificate cost. PR #1260 is original producer; this PR does not duplicate it.
2. **P1** Exact-head Agda type check of all new files and three TOE roots. No new postulates, no unsafe options; the source is not a kernel receipt.
3. **P2** Braid/group formalisation: complete \(A_5\) perfection and \(S_5\) derived series in first-class Agda; do not promote group-order matching alone.
4. **P3** In PR #1244, pay real relative-collar geometry, selected actual wild satellites, van Kampen basing paths and same-object \(\pi_1(E)\) identification. The abstract perfect direct-limit presentation is not the same theorem.
5. **P4** Projective \(2I\to A_5\) quotient source homomorphism/representation and binary-horn generator compatibility; retain exact first-channel vs six-channel normalisation.
6. **P5** Exact \(\theta\) angle-unit separation, \(\Gamma\) analytic recurrence, Bishop analytic continuation and Lie/spin global topology; do not call a conditional Gamma record the classical proof.
7. **P6** Preserve numerology boundary across \(3\cdot2^n\), \(3^3\), \(3^4\cdot3^5=3^9\), \(3^5\), \(5^3\), \(5P3\), \(|S_5|\), \(|2I|\) and the \(C_3^3\) Fourier cube.

**Scope:** attachment is supporting context; no device, synthetic-gauge experiment, Riemann surface, wild embedded complement identification, Monster same-object proof, or terminal Pickover radian sign was established by this continuation.


### Important PREFIX !9999 versus source POSTFIX 9999! (derangement max-cut)

**Distinct operation:** prefix !n denotes the subfactorial/derangement count D_n, whereas the user's attached steelman writes 99^(9999!) with a POSTFIX factorial. The user's new message writes !9999 with prefix notation; both must be retained as distinct exact targets until the source is clarified, and neither radian sine sign may be guessed. Derangements originate in de Montmort and Euler; Whitworth proposed the name subfactorial. Historical references: https://mathworld.wolfram.com/Subfactorial.html ; https://mathworld.wolfram.com/Derangement.html ; https://doi.org/10.1080/0020739X.2026.2701739. Gamma factorial (Euler/Legendre) and theta angle are separate again.

Mathematical definitions:
  n! = Gamma(n+1) = product(k=1,...,n) k;
  !n = D_n = n! * sum(k=0,...,n) ((-1)^k/k!);
  D_0=1, D_1=0, D_n=(n-1)(D_(n-1)+D_(n-2)).

The asymptotic !n~n!/e is NOT a real-phase approximation after exponentiating 99 to these two different huge exponents.

| Distinct object | Exact count | Typed interpretation |
|---|---:|---|
| 3! | 6 | All six S3/ABC permutations |
| !3 | 2 | Exactly the two nonidentity C3 rotations; all swaps fix one label |
| 5! | 120 | Full S5 root-label permutations |
| !5 | 44 | Fixed-point-free 5-root permutations |
| !5 in A5 | 24 | Even derangements |
| !5 outside A5 | 20 | Odd derangements |
| A5 | 60 | All even permutations; not just derangements |
| 5P3 | 60 | Ordered injective triples / exact A5 finite-set chart |
| 5^3 | 125 | Triples with repeated choices permitted |
| Gamma(10000) | 9999! | Ordinary factorial, not !9999 |

**Exact independent local Python replay** (not a radian-phase certificate):

| Exponent E in 99^E | Bit length E | E mod 100 | 99^E mod 101 | 99^E mod 9999 | 99^E mod 360 |
|---|---:|---:|---:|---:|---:|
| 9999! | 118445 | 0 | 1 | 4950 | 81 |
| !9999 | 118444 | 86 | 23 | 3861 | 81 |

The same degree-angle residue 81 does NOT imply the same radian sine sign. The two terminal radian-phase signs remain unresolved. The original Pickover study in draft PR #1260 is the **postfix factorial** target.

**New source-written Agda module:** DASHI.Foundations.PolynomialSubfactorialDerangementS3S5Exact. It defines subfactorial by its classical recurrence; constructs D3=2 and D5=44; proves C3's two nontrivial S3 rotations fix no point; exhibits fixed points for identity/transpositions; evaluates a 120-case quintic atlas filter into 44 derangements with exact 24+20 even/odd counts. All three canonical TOE import roots now link the exact named bridge. This source remains **Agda-kernel pending**.

The committed scripts/check_polynomial_pickover_gamma_horned_maxcut.py now computes both factorial and subfactorial CRT targets, and audits the 44=24+20 split. An independent materially equivalent in-session Python replay passed; exact GitHub script-blob execution was not recorded.

**Proof cut:** retain the standard two-step recurrence and derive the full inclusion-exclusion factorial/subfactorial formula in Agda; run exact-head typechecking of 120-constructor filtering; formalize genuine S5/A5 parity group laws without interpreting two equal counts as an isomorphism; require independent REAL certificates for each separately typed radians-phase target; preserve Ibrahim/Monster source ownership and wild-geometry non-promotion.


## 2026-10-28 native ternary end-address and typed theta follow-up

The user clarified that the desired balanced-ternary replacement of
the Alexander horned-space notation is the **INFINITE END-ADDRESS
SPACE ITSELF**, not a ternary-valued observer over its original
binary stream:

```text
K2 = C3_sector × Bit^N
K3 = C3_sector × Trit^N   (full -/0/+ in every chronological digit).
```

Parent horned PR #1244 now owns
`AlexanderHornedNativeBalancedTernaryEndTowerExact.agda`
using original `RecursiveFibreTower.FibreTower` and
`InverseLimitPoint`, finite prefix projections,
an actually coherent infinite-zero end family,
external C3 and distinct internal balanced-trit
C3, the sign-reflection S3 conjugation equation,
and a tetration config-table receiver.
No cross-branch import is attempted here.
The external sector C3 and internal root/digit S3
are mathematically different typed actions; #1414
continues to own the ORIGINAL polynomial root
label monodromy and quaternion 120°/720° lift.

The complete prefix code `-→0,0→10,+→11`
from stacked #1254 gives a homeomorphism of
ABSTRACT Cantor end spaces K3 and K2, even
C3-sector-equivariantly, but not a metric isometry,
a fair Bernoulli measure equivalence, a
2-adic=3-adic additive group identity,
a same-depth binary-tree map, or a wild
3D linked-handlebody embedding. The native
ternary cylinders have `3·3^n` cells at
depth n; at n=2 this is 27 sites, whose
full trit-label configuration table has
`3^27 = 3↑↑3` entries. The existing
`DASHI.Cognition.RecursiveFibreTower` owns
that TETRATION FUNCTION-SPACE recurrence.
The native geometric 3-child wild-horn
supplier remains separate from the original
Hatcher binary source and the new abstract
`[a,b][b,c]` ternary word tower.

**Exact theta / prefix notation (not a quotation claim):**
The attached user steelman specifies POSTFIX
`9999!` and its actual real-angle phase
`θ_F=99^(9999!)`, while #1414's
`PolynomialSubfactorialDerangementS3S5Exact`
already independently models PREFIX
`!9999`, the derangement number, and the
alternative angle `θ_D=99^(!9999)`.
The new `ThetaIndex` and
`thetaAngleRadians` in this PR's EXISTING
Gamma/factorial owner are a local definition
of these angle expressions, NOT a proof
that standard mathematical theta denotes
factorial. Standard Gamma satisfies
`Γ(10000)=9999!`. No exact video transcript
sentence specifying theta as a factorial
function has been recovered; do not present
it as a sourced assertion.

The exact local CRT discriminator is
`θ_F mod 9999=4950` and
`θ_D mod 9999=3861`; both happen
to be `81 mod 360`. The existing
`check_polynomial_pickover_gamma_horned_maxcut.py`
now defines and checks `sub_residues` BEFORE
printing them (fixing a NameError). Both
terminal radian sine signs remain unproved.
The original #1260 Pickover objective is
`θ_F`, not `θ_D`, pending source-level
verification otherwise.

These additions neither establish an
analytic polynomial monodromy path, a
new Galois quintic result, an actual
horn exterior group homotopy, an
Ibrahim Monster 3B same-object representation,
nor a proof of RH. Original author attribution
and distinct source/code/test/kernel status
are unchanged.


## 2026-10-28 attached native end-fibre local action max-cut — linked to original #1244 owner

Two new user-supplied research notes clarified the native end space K3=C3×{-1,0,+1}^N, the different original binary Hatcher address space K2=C3×{0,1}^N, and the interpretation of the 3^27 function space as the **actual group of independent local phase rotations** on 27 cells. This is not merely a count and does not make Hatcher's meridians ternary. The existing #1244 source NativeTernaryFibreActionExact had already proved pullback injectivity and evaluation; the new source is committed to THAT owner branch, without cloning the group into this independently based PR.

New #1244 theorem modules, source-written on alexander-horned-c3-equivariant-20261024:

1. DASHI/Mathematics/Topology/AlexanderHornedNativeTernarySemidirectActionExact.agda: inverse-pullback external sector C3 action on Map(K3_n,C3), composition, pointwise semidirect group laws including inverse and identities, faithful pullback, semidirect refinement multiplication/field action naturality.
2. DASHI/Mathematics/Topology/AlexanderHornedTernaryFibreDerivedCutExact.agda: explicit depth-zero noncommuting local-gauge/sector pair, abelian local gauge kernel and abelian sector quotient, documented metabelian derived boundary.
3. DASHI/Mathematics/Topology/AlexanderHornedNativeTernaryTrialectic27ChartExact.agda: literal two-sided **bijection** of native 27 address cells and the prior trialectic SynthesisChoice27; different external-sector and internal-digit C3 actions; exact pointwise field-group-law transport on the 27 chart.
4. DASHI/Mathematics/Topology/AlexanderHornedNativeTernaryS3LocalValuesExact.agda: local S3^X value permutations using the existing S3 source owner, local-vs-global reflection negative control, and true C3→S3 cyclic subgroup homomorphism on local fibre values. S3^X is solvable and not an A5, 2I or generic-quintic Galois source.

New exact regression owner #1244: scripts/alexander_horned_native_ternary_local_fibre_actor.py. Its private-branch source was committed and inspected, but the exact blob was not executed from GitHub in this environment. INDEPENDENT local Python checked depth 0–3 action/refinement squares and enumerated all 81 semidirect elements at depth zero, finding nine commutator translations, second derived trivial, and genuine noncommutation.

Key mathematics: put k=3^n. Then

  |K3_n|=3k; A_n=Map(K3_n,C3)≅C3^(3k);
  H_n=A_n ⋊ C3 has order 3^(3k+1);
  H_n'≅C3^(2k), H_n''=1;
  H_n^ab≅C3^(k+1).

At depth two, |A_2|=3^27=7,625,597,484,987; |H_2|=3^28=22,876,792,454,961; |H_2'|=3^18=387,420,489; |H_2^ab|=3^10=59,049. The derived subgroup is the sum-zero augmentation kernel on EACH three-sector orbit. The pointwise group-law adapter is source-written, and the full derived/cokernel Agda group-object theorem remains outstanding; the equation is mathematically standard and computationally checked at depth zero.

**Strong non-promotion:** nontrivial perfect G_A, perfect A5, and perfect 2I admit only TRIVIAL homomorphisms into solvable H_n, and likewise into any local-S3-valued field group extended by the external finite C3. Therefore these finite phase-fibre actors are NOT a replacement for the perfectly nonabelian Hatcher source or its 2I holonomy. The actual orbifold group (G_A*G_A*G_A) ⋊ C3 is a separate construction with a non-solvable/perfect source normal subgroup, not isomorphic to H_n. An actual source-group action on a richer non-solvable fibre is an additional independent representation theorem.

**Polynomials and numerology:** C3 sector rotations and C3 local-value translations are different commuting/semidirect roles. The six ABC label permutations S3 and the full local independent S3^27 extensions have independent group meanings; no analytic braid loop follows. The 27 native sector/digit addresses have a chosen invertible chart to the triple trialectic carrier, but this is not an identity of an actual polynomial coefficient fibre or wild-space embedding. The equality 3^27=tetration(3,3) is for the local FUNCTION SPACE on 27 cells, whereas 3·3^n counts addresses; the original Hatcher binary tower has 3·2^n geometric meridians. The attached 13/27 and 5/9 antipodal fixed-orbit counts are for specific involutions with non-intertwining orbit structures, not proofs of same-object group actions.

**Prior sources:** Alexander (1924), Hatcher AT 2B.2, classical finite wreath/semidirect products, C3/S3 groups and prior DASHI original authors; independent #1244, #1254, #1407, #1414, #1260 and Ibrahim/Monster 3B retain their separate ownership and exact-head proof tiers. External mathematical reference for the permutational wreath product H^S ⋊ G: https://agda-algebras.universalalgebra.org/Classical/Structures/Group/Wreath/ . All operations here are SOURCE-WRITTEN, Agda kernel NOT run; no newly claimed wild geometry, quintic Abel–Ruffini, RH, physical experiment or original Pickover sin sign.

**Next irreducible cut:** the quotient/direct-limit group A_loc and compact-clopen proof C_loc(K3,C3), the full Agda augmentation-derived subgroup theorem, and source-to-geometric same-object relative-collar identification in #1244. Do not write a second competing 27/end-space kernel or import unmerged #1244 modules into #1414.


## 2026-10-28 qualified new local-gauge interface from #1244 (no same-object weld)

A subsequent #1244 continuation now extends the *previously source-owned* native ternary `K3=C3_sector×Trit^N` tower with the actual local phase field group `G_n=Map(C3×Trit^n,C3_phase)` and external sector permutation. The existing #1244 `AlexanderHornedNativeTernaryFibreActionExact.agda` is the canonical local group/pullback owner; its **additive** `AlexanderHornedNativeTernaryLocalPhaseActionExact.agda` source-writes semidirect `G_n⋊C3_sector` with pointwise associativity/inverses and equivariant refinement, a cylinder setoid on the original inverse limit, and an invariant-observation no-go. See [#1244](https://github.com/chboishabba/dashi_agda/pull/1244) and `Docs/topology/AlexanderHornedNativeTernaryLocalPhaseFibreMaxCut20261028.md` *in that separate branch*. No unmerged source is silently imported into this PR.

At depth two `|X2|=27`, `|G2|=3^27`, `|G2⋊C3|=3^28`. These are exact abstract finite group cardinalities, **not** counts of physical horns, Riemann/Monster states or eigenmodes. The original #1414 polynomial root **monodromy S3/C3** is an independently owned action on roots; the original quaternion u³=-1/u⁶=1 is a separate central double-cover result. Neither is now claimed to act on the #1244 local gauge bundle without a concrete typed equivariant homomorphism. For the earlier #1275 Zipf observation, only global label relabelling preserves complete Heaps trajectories; a local address-dependent gauge can change them. This is a valid NO-GO crosswalk, not a merged probability or Spin model.

Independent exact local oracle passed 81³ semidirect associativity cases and higher-depth checks; exact-head Agda still unverified. No change in the previously unsettled 9999! versus !9999 radian sine sign or wild geometric collar. Prior #1414 original mathematical author/source, #1244 proof owner, and Ibrahim Monster 3B ownership preserved.


### 2026-10-28 source-owner correction: canonical LocalPhaseAction and gauge-invariant observable no-go

On the current PR #1244 native end branch, the earlier original AlexanderHornedNativeTernaryFibreActionExact AND the subsequently surfaced AlexanderHornedNativeTernaryLocalPhaseActionExact already own the C3-valued end field group, sector-twisted semidirect multiplication, inverse, group laws, refinement compatibility, cylinder setoid congruence, and invariant-observer theorem. The new NativeTernarySemidirectActionExact adapter was subsequently refactored to import those exact original proof owners and retain only a missing *field action of the already-defined semidirect group*, its group multiplication/action coherence, and faithful refinement. This removes an inadvertent duplicate of the source group implementation.

The LocalPhaseAction owner proves a second decisive obstruction independent of the perfect-to-metabelian group-homomorphism no-go: because the local C3 gauge acts freely and transitively on the set of phase fields, every pointwise-extensional observable invariant under ALL independent local gauges is constant. Wilson traces are NOT obtained from such a bare phase-field observable; they require a separate connection/edge transport and properly based loop data. This keeps the classical #1244 finite 2I nonabelian holonomy experiment coherent without claiming it is implied by arbitrary local C3 or S3 field translations.

The *actual* branch-end import graph is Original NativeTernaryFibreActionExact -> canonical NativeTernaryLocalPhaseActionExact -> semidirect FIELD-action adapter -> derived/no-go adapter, alongside NativeTernaryTrialectic27ChartExact and NativeTernaryS3LocalValuesExact. #1414 links to this branch-level theorem owner by exact reference rather than importing unmerged source. All Agda proof-status caveats, Hatcher geometry and gamma/Pickover separation remain.


## 2026-10-28 additional Artin/Hatcher/27-orbit/3^5-to-5^3 convergence

**A new actual braid-source lemma:** PolynomialBraidFullTwistSevenWitnessExact.agda reuses the original PR #1414 braid-word-to-S3 image. It defines an explicit C7 residue evaluator for BOTH Artin crossings and their inverses, proves the B3 Yang–Baxter relation and each inverse cancellation respects the evaluator, and proves:

  image_S3((sigma0 sigma1)^3)=1,
  exponent_mod7((sigma0 sigma1)^3)=6 != 0.

This is strictly stronger than showing a braid word is syntactically nonempty. It proves a genuinely presentation-compatible finite witness of nontrivial braid history with trivial final root permutation. Original source credit: Emil Artin's B3 presentation, Joan Birman (1974), Kassel–Turaev (2008), Jenny Wilson's primary braid lecture notes: https://dept.math.lsa.umich.edu/~jchw/RTG-Braids.pdf. Full-twist centrality/generator-of-the-centre is NOT re-proved by this C7 source; it belongs to classical B3 prior art. Nor does the integer winding observer establish a continuous polynomial coefficient path or an SU2 covering.

**The most productive new 243-vs-125 cross-pollination is in the original #1244 owner, NOT reimplemented here:** The existing native ternary end, 27-cell trialectic chart, and five-orbit quotient already construct 5 orbits of the sign-reversed two-trit carrier and thus the real group Map(FiveOrbit,C3) with 3^5=243 elements. The new original-owner extension defines a distinct set Map(C3_sector,FiveOrbit) with 5^3=125 elements. It constructs the evaluation composition between these two different functional spaces, proves every chosen triple-phase readout is realizable, and proves no universal recovery of a five-orbit field from only the selected three-orbit observation. This is a mathematically genuine difference in domain/codomain, NOT a 243↔125 equality or C5 group identification. See: https://github.com/chboishabba/dashi_agda/blob/alexander-horned-c3-equivariant-20261024/DASHI/Mathematics/Topology/AlexanderHornedDepthTwoFiveOrbitFibreExact.agda.

**Further original-owner #1244 results:**
1. S3 derived-series concrete instance in AlexanderHornedS3DerivedMonodromyNoGoExact: any Hatcher-compatible *recursive meridian* assignment into S3 must be trivial because S3 -> C3 -> 1; generic polynomial root monodromy has a different source group and is NOT thereby killed.
2. On the same 27-cell carrier two distinct involutions have 1 vs 3 fixed points (13 pairs vs 12 pairs), and AlexanderHornedTernaryTwentySevenInvolutionNoGoExact proves no equivariant injection from internal-only to all-coordinate reflection.
3. AlexanderHornedSectorDihedralS3EndExact extends external horn-sector C3 to ALL six ABC/S3 permutations with projection-equivariance and reflection conjugating the 3-cycle to its inverse; this is intrinsic label symmetry, not guaranteed ambient wild embedding.
4. Canonical existing 27/trialectic chart was extended with a two-sided native gauge ↔ third-level predicate-table map; 3^27=3↑↑3 now has an actual pointwise carrier equivalence rather than only a count.
5. Original local S3 source now proves all 54 pairwise-equality invariance cases for GLOBAL diagonal relabelling and a LOCAL reflection counterexample for the first two Heaps labels. Original #1275 statistics/Heaps and #1407 13-in-27 proof owners are preserved.

**Refinement distinctions:** real Hatcher wild geometry 3*2^n binary meridians; native ternary end-space 3*3^n address cells; depthwise local field count 3^(3^(n+1)); recursive predicate iteration at next tower level 3^(3^27). These have explicit typed bridges or stated independent roles. Full twist group B3, SU2 lift sign and source outer C3 are not one common action merely because their projections return.

**Verification:** independently executed finite Python PASS for 6->3->1, 14-vs-15 involution orbit split, Heaps witness, nonempty full-twist endpoint identity with exponent mod7=6, 3^27 and binary-vs-ternary counts. The added Agda source remains source-written / KERNEL-PENDING. No exact-head Agda, CI or geometric wild-exterior proof. No source-owner copy of draft-branch code into this PR and no ESD edits. The new accepted positive work is on the correctly owned #1244 branch; the full-twist receiver is on #1414.


## 2026-10-28 focus correction: actual polynomial discriminant, not another wave/fibre owner

Current donor inspection: #1244 already owns 27-cell/five-orbit local field group, 243-versus-125 evaluation and the C3² invisible kernel; #1405 already owns T15/T16 homogeneous/heterogeneous wave equivariance, and the #1244 five-orbit wave consumer; #1407 already owns the 13/27, 5/9 and Fourier orbit lanes. Their implementations are **not duplicated** on polynomial PR #1414.

**New polynomial owner:** `DASHI.Foundations.PolynomialVandermondeDiscriminantExact.agda`, directly reusing `PolynomialVietaRootSymmetryExact.ThreeRoots`, the existing six `TriPermutation` constructors and the rational ring tactic. Source-written exact lemmas:
- `vandermondeTransformsByParity`: the alternating product `V=(a-b)(a-c)(b-c)` is preserved by the THREE even/C3 permutations and negated by the THREE odd transpositions; six explicit source cases.
- `discriminantInvariant`: `V²` is invariant under all six root-label permutations; six explicit source cases.
- `discriminantDependsOnlyOnVietaCoefficients`: with `s1=a+b+c`, `s2=ab+bc+ac`, `s3=abc`, prove `V²=s1²s2²-4s2³-4s1³s3-27s3²+18s1s2s3`. This is the actual ALGEBRAIC bridge from ordered-root labels to an invariant in coefficient space.
- Three collision implications: a=b, a=c, b=c imply `V²=0`.
- All new names are attached to the three canonical TOE root aggregates; no protected ESD edits.

This is the real missing polynomial-source link behind the video's branch-point/discriminant discussion. It is **not yet** the complex discriminant-complement covering, converse nonzero/disjoint-root proof, analytic path-lift, monodromy or global radical criterion.

**Independent exact verification actually executed:** integer/Fraction polynomial calculations on all 343 triples `(a,b,c) in [-3,3]^3` passed the coefficient-discriminant identity; 2058 six-permutation checks passed `V²` invariance. This tests the source mathematics, but **is NOT execution of the committed code or Agda kernel type-check**.

**Attribution:** classical Vieta (1591), Vandermonde/Lagrange (18th-century alternating polynomial), discriminant theory and Galois/Abel; repository ownership stays with the earlier S3 and cubic Vieta modules, while this PR owns only the new specific compositional proof source. No original Ibrahim Monster 3B or other PR proof ownership is transferred. The explicit sign-character link is structural, unlike equal numerology counts.

**Next maximal dependency:** establish a genuine algebraic `Δ=0 ⇔ roots collide` over a field with no zero divisors, then construct a specific complex coefficient discriminant complement and ordered-root cover with loop transport. Existing #1244/#1405 end-fibre/wave and #1407 Fourier owners are separate and should be consumed only if a typed actual operator or monodromy intertwiner exists. CI is not required; source remains Agda-kernel pending.


## 2026-10-28 source-qualified S3 orbit transport (not a spin-weld)

A newly source-written sibling [#1244](https://github.com/chboishabba/dashi_agda/pull/1244) `AlexanderHornedS3WordSignOrbitTransportExact.agda` formally witnesses the actual relation of **two quotient sets**: global S3 relabel orbits of named length-(n+1) ternary words, and C2 simultaneous sign-orbits on n relative ternary coordinates. It fixes the first symbol as an anchor, subtracts it modulo 3 to remove the translation-C3 normal subgroup, and shows the residual involution is sign reflection; conversely a relative sign relation constructs an explicit affine S3 action. It explains the shared Stirling/Burnside ranks `1,2,5,14,41,122,365,...` (not merely 41=41). The existing #1414 **polynomial analytic root monodromy** and original quaternion double-cover remain distinct objects: an action on named ternary labels is neither a continuous braid path nor an identified physical spinor bundle. No code copied from #1244; kernel not checked; previous factorial/subfactorial terminal signs and Ibrahim Monster 3B remain independently unresolved.
