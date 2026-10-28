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

The ten new owners plus the original finite bridge are attached through \`EverythingTOESymmetryResolved369\`, \`Unifier\`, and \`Unified/Everything\`. No protected ESD file was edited.

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
