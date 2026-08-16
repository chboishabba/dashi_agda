# Blue-Team NTT Prior / Observation / Search Geometry — Round 17

This tranche continues the defensive MLWE/ML-KEM programme at the point where generic candidate-fibre machinery is no longer the main obstacle. The live questions are concrete: conditional list size under actual FIPS coordinates, reconciliation/separator complexity, transition/update geometry of exact verification, sufficient-state/readout capacity, average success under the exact CBD product prior, and the value of concrete implementation observations after acquisition cost.

No ML-KEM break or security proof is claimed.

## Source / threat-model provenance

Primary cryptographic source throughout the source-faithful ML-KEM lane:

- National Institute of Standards and Technology, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, FIPS 203 (2024), DOI `10.6028/NIST.FIPS.203`.

Finite-field uncertainty source used by the harmonic support lane:

- Martino Borello and Patrick Solé, *The uncertainty principle over finite fields*, *Discrete Mathematics* 345 (2022) 112670, DOI `10.1016/j.disc.2021.112670`.

Defensive side-channel context for why joint NTT observations must be treated as an implementation-level threat surface, not as an abstract curiosity:

- Mike Hamburg, Julius Hermelink, Robert Primas, Simona Samardjiska, Thomas Schamberger, Silvan Streit, Emanuele Strieder and Christine van Vredendaal, *Chosen Ciphertext k-Trace Attacks on Masked CCA2 Secure Kyber*, IACR TCHES 2021(4), 88–113, DOI `10.46586/tches.v2021.i4.88-113`.
- Estuardo Alpirez Bock, Gustavo Banegas, Chris Brzuska, Łukasz Chmielewski, Kirthivaasan Puniamurthy and Milan Šorf, *Breaking DPA-Protected Kyber via the Pair-Pointwise Multiplication*, ACNS 2024, LNCS 14584, 101–130, DOI `10.1007/978-3-031-54773-7_5`.

Those side-channel papers motivate the threat model only; their attack algorithms are not imported as proof assumptions.

## New strongest finite result: complete m=8 raw pair profiles

`MLKEMNTTActualCBD2EightCoefficientLeakageResolutionExact` now records the complete `5^8 = 390625` CBD2 raw-signature profiles pinned by `scripts/crypto_ntt_cbd_block_reconciliation_probe.py` for three actual FIPS residue pairs:

| residues | candidates | distinct images | unordered collision pairs | conditional mass | mean list size | max fibre |
|---|---:|---:|---:|---:|---:|---:|
| `(0,1)` | 390625 | 271441 | 151632 | 693889 | 693889 / 390625 ≈ 1.77636 | 4 |
| `(0,2)` | 390625 | 369865 | 20805 | 432235 | 432235 / 390625 ≈ 1.10652 | 3 |
| `(0,3)` | 390625 | 390625 | 0 | 390625 | 1 | 1 |

The Agda module checks the exact arithmetic identity

`conditionalMass = candidates + 2 * collisionPairs`

for all three profiles. It also keeps the crucial semantic boundary kernel-visible: raw-signature injectivity does **not** imply injectivity of the actual physical observation after coarsening. A tiny exact counterexample shows an injective raw signature followed by a constant observation channel.

Thus the blue-team interpretation is:

> `(0,3)` is a high-sensitivity raw joint observation on this conditioned eight-coefficient carrier and should be treated as a priority implementation-audit surface if a real leakage channel preserves enough of that pair.

It is **not** a theorem that a trace exposes those raw residues, not a full-polynomial/key recovery theorem, and not a runtime claim.

## Opposite-residue structure

`MLKEMOppositeResidueParityDecompositionExact` proves the exact ring identity behind the special opposite FIPS pairs

`gamma_1 = -gamma_0` and `gamma_3 = -gamma_2`.

For an eight-coefficient polynomial evaluated at `a` and `-a`, sum and difference isolate the even- and odd-exponent sectors.

`MLKEMOppositeResidueParityFibreFactorisationExact` strengthens this to a fibre theorem: whenever doubling is injective, equality of the two opposite-residue observations is equivalent to equality of both parity sectors. The theorem is now stated explicitly as a **defensive joint-leakage structural result**. The seeded Python controls remain computational prioritisation evidence, not an implementation claim.

## Earlier source-faithful CBD2 local-list results

`MLKEMNTTActualCBD2ScalarCollisionExact` proves that two distinct CBD2-supported source triples collide on the first constant NTT scalar. The multipliers at source degrees 0, 8 and 12 are `1`, `296`, and `2319`, and both `(-1,-1,+1)` and `(+2,0,-2)` map to scalar value `2022`.

`MLKEMNTTActualCBD2SliceCouplingExact` independently shows a two-coefficient FIPS-constant slice whose transported joint support is non-Cartesian.

`MLKEMNTTActualCBD2TwoScalarRefinementExact` uses a second actual scalar at residue `i=2`, where the relevant weights are `1`, `296`, `1010`; the old colliding pair separates.

`MLKEMNTTActualCBD2FullTripleListProfileExact` exhausts all `5^3 = 125` triples on source degrees 0, 8 and 12. The first scalar has exactly 16 unordered collision pairs. The joint pair of actual scalars has zero unordered collision pairs on the complete slice.

`MLKEMNTTActualCBD2ConditionalListMassExact` converts those collision counts into exact finite conditional-list mass. With `N=125` candidates and `P` unordered collision pairs, total list mass is `N + 2P`; therefore the one-scalar and two-scalar masses are `157` and `125` respectively.

These are local finite/dataflow results, not a global recovery theorem.

## FIPS NTT dataflow and locality tradeoff

`MLKEMNTTDataflowCouplingExact` follows FIPS 203 Algorithm 9 and BaseCaseMultiply. One scalar secret NTT component depends on a 128-coefficient parity class; one quadratic secret residue pair spans all 256 coefficients of its source polynomial. BaseCaseMultiply recouples the two local components before the public equation is checked.

`MLKEMCandidateMoveFanoutExact` turns that dependency around: a one-coefficient source move is potentially visible across `256*k` public-residual scalar coordinates.

`MLKEMLocalityAreaInvariantExact` exposes the endpoint representation-geometry identity:

- coefficient-local: prior support `1`, public fanout `256*k`;
- scalar-NTT-local: prior support `128`, public fanout `2*k`.

`MLKEMButterflyStageLocalityInvariantExact` strengthens this across every canonical FIPS Algorithm-9 stage: source-support widths `1,2,4,8,16,32,64,128` pair with remaining scalar fanouts `128,64,32,16,8,4,2,1`, so the structural locality area remains exactly `256*k` — 512, 768 and 1024 for the approved parameter sets.

## Harmonic uncertainty to exact update-resource obstruction

The uncertainty lane is now much more than an endpoint locality slogan.

`MLKEMNTTSingularBudgetUncertaintyExact` packages the support statement

`128 <= sourceSupport * (survivingSupport + singularBudget)`.

`MLKEMUncertaintyTransitionCostBridgeExact` identifies the exact missing same-object premise needed to turn surviving support into a primitive verifier/update cost: surviving output residues must be covered by the concrete update work.

`MLKEMProtectedLabelUncertaintyEdgeExact` moves that statement onto actual protected-label search edges.

`MLKEMExactResidualTouchLowerBoundExact` supplies a concrete operational resource for one important verifier class: if an exact residual array is explicitly materialised, subtracting a nonzero delta changes that residual cell, so every changed residual cell must be touched. This yields

`128 <= sourceSupport * (touches + singularBudget)`.

`MLKEMResidualTouchPathLowerBoundExact` sums the per-step obstruction over a traversal rather than identifying one edge with total runtime.

The result is a genuine representation/update-resource tradeoff for exact materialised residual verification, but still not a generic wall-clock lower bound: lazy/compressed/symbolic states require their own sufficient-state/readout theorem.

## Sufficient state, transcript capacity and average success

That second seam is now explicit too.

`MLKEMProtectedLabelReadoutFactorisationExact` and `MLKEMFiniteStateTranscriptCapacityExact` formalise exact protected-label recovery through maintained state plus readout/query transcript. If a protected label is exactly decodable from that pair, the protected-label carrier injects into `StateCode × TranscriptCode`.

`MLKEMBoundedCellTranscriptCapacityExact` then gives the finite numerical capacity

`stateAlphabet^stateCells * transcriptAlphabet^transcriptDepth`.

`MLKEMUpdateCapacityDichotomyExact` composes this with the harmonic/update obstruction. A concrete architecture is therefore constrained simultaneously by update locality and distinguishability capacity. NIST/FIPS and Borello–Solé provenance are attached directly to this composition module.

`MLKEMFIPS203ProtectedSecretCapacityExact` and `MLKEMFIPS203UpdateCapacityResourceExact` move the carrier counts onto the FIPS parameter sets.

`MLKEMFinitePriorSuccessMassExact` separates support cardinality from prior mass.

`MLKEMFIPS203CBDPriorSuccessBoundExact` uses the exact `SamplePolyCBD_eta` product-prior multiplicities. For one coefficient the raw-bit multiplicities are:

- `eta=2`: `1,4,6,4,1`, total 16, maximum 6;
- `eta=3`: `1,6,15,20,15,6,1`, total 64, maximum 20.

Hence the maximum complete-secret raw-bit multiplicities are `20^512`, `6^768`, `6^1024` under the explicit independent uniform CBD input-block model.

`MLKEMFIPS203AverageSuccessResourceExact` composes the update obstruction with this prior-mass bound. It now carries direct NIST and Borello–Solé provenance and yields two separate constraints:

- update locality: `128 <= sourceSupport * (touches + singularBudget)`;
- average-success numerator: `successWeight <= stateTranscriptCapacity * maxSecretPointWeight`.

This is an average-success resource tradeoff under the stated CBD product prior. It is not a proof that deterministic SHAKE output is information-theoretically independent and not a generic complexity lower bound.

## Conditioned BaseCase equations and ambiguity

`MLKEMBaseCaseConditionedResidualExact` proves that conditioning `s0` leaves

`c0 - a0*s0 = a1*s1*gamma + e0`

and

`c1 - a1*s0 = a0*s1 + e1`.

`ConditionedResidualAmbiguityRegressionExact` and `ConditionalMateAmbiguityExact` show that simplification does not imply a unique remaining mate. `ConditionalReconciliationSearchExact` remains the positive seam: if a real conditional-mate theorem exists, one outer candidate can construct a global witness without Cartesian pairing.

## List-decoding language

`FiniteMLWEListDecodingGeometryExact` recasts the existing 2×2 Z/5 MLWE lab as a finite list-decoding problem `L(t,tau) = {s' : Score(t-A*s') <= tau}`. The exact score vector is `2,0,0,2`; thresholds 0 and 1 give list size 2, while threshold 2 gives list size 4.

The CBD2 profile modules are the source-faithful counterparts: they track exact fibres/list mass for actual FIPS coordinates while keeping “small list”, “injective raw signature”, “physical leakage”, and “cheap recovery” logically separate.

## Search transition geometry and mixed-radix Gray traversal

`ProtectedLabelSearchGeometryExact` upgrades a candidate fibre into a system with admissible search edges, a machine representation, edge/update cost, reconciliation cost, and observation-induced geometry changes.

`GrayPathTransitionOptimalExact` and `SearchGraphEmbeddingDistortionExact` separate equal-rate encodings by transition geometry. `FiniteMLWETransitionGeometryExact` and `IncrementalResidualTraversalExact` carry that distinction into the finite MLWE lab.

`CBD2MixedRadixGrayTraversalExact` uses the five-value CBD2 coefficient alphabet. For a two-coefficient 25-state carrier, row-major traversal costs 40 while boustrophedon/mixed-radix Gray traversal costs 24. Candidate cardinality is unchanged.

## Observation value and separator geometry

`ObservationSeparatorGeometryExact` shows that observation value need not track candidate-count reduction: one finite observation removes one candidate but collapses separator work from 80 to 12 after acquisition cost.

`ObservationAcquisitionCostExact` compares `recovery-before` against `observation-cost + recovery-after`, so strict candidate shrink is not sufficient for attack progress.

`AttackerObservationLanguageRefinementExact` gives the quotient-theoretic version: enlarging the admitted observation language can only refine attacker observational equivalence, and a newly admitted coordinate matters only with an explicit same-base-observation split witness.

The new m=8 leakage-resolution theorem adds the converse implementation boundary: a mathematically rich **raw** signature can be collapsed by the physical observation channel. Therefore raw residue-pair sensitivity is a prioritisation signal for blue-team measurement and mitigation, not itself evidence of a leak.

## Representation-security minimax

`RepresentationSecurityGameExact` packages the cross-pollination between computational geometry and physical observation geometry. Its finite minimax regression makes the faster representation worse under one side observation, so transition-optimal and leakage-optimal representations are not identified.

`RepresentationLeakageGeometryExact` keeps the physical side-channel claim boundary explicit: different Hamming movement can define a different observation surface without implying that smaller movement is universally safer.

## Rate / guessing / recovery remain different coordinates

`CryptoRepresentationParetoExact` retains rate, transition cost, reopening cost and observation cost separately. `AdaptiveCandidateResidualWidthExact`, `ConditionalResidualRateExact`, and `FiniteGuessingProbabilityExact` keep fibre-local residual width, finite expected rate, guessing improvement, and computational recovery improvement distinct.

The hierarchy remains strict:

`rate reduction != guessing improvement != candidate shrink != raw-signature injectivity != physical leakage != search-cost improvement != total runtime`.

## Frontier after the m=8 tranche

The shortest remaining mathematical targets are now:

1. provide a compact Agda certificate/proof for semantic injectivity of the actual `(0,3)` eight-coefficient raw signature, rather than replaying a 390625-point Python enumeration in the kernel;
2. replace raw-signature sensitivity with concrete **coarsened observation** profiles for defensive channels such as Hamming weight/distance, timing buckets or masked-share observables, and prove exactly which distinctions survive;
3. continue the conditioned BaseCase experiment with random controls and identify whether opposite-residue parity factorisation changes the real conditional-mate/reconciliation complexity rather than only raw fibre count;
4. instantiate the harmonic/update certificate on the actual FIPS local public matrices, including the full-rank/singular producer rather than leaving `singularBudget` abstract;
5. instantiate the sufficient-state/readout capacity theorem for a concrete verifier architecture, so the current update-locality plus average-success tradeoff becomes source-and-architecture complete;
6. keep observation acquisition cost and representation minimax in the final theorem so that a defensive mitigation is valued by the geometry of the **actual admitted observation**, not by raw candidate-count slogans.

The working thesis is:

`protected-label quotient + source-faithful prior + harmonic/support geometry + exact update resource + sufficient state/transcript + admitted observation channel + algorithm-relative recovery cost`.

No GitHub Actions or CodeRabbit run is required by this tranche. `scripts/check_crypto_ntt_prior_observation_round17.sh` fail-closes the source surface, re-runs the Python finite regressions when Python is available, and invokes the Round-17 aggregate only when Agda is locally available. No kernel-clean claim is made without an observed typecheck.
