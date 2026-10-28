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
