# Clay P0 — ramified correspondence, geometric complexity and SAT endpoint

2026-11-24. Shared Agda/Lean mathematical work and roadmap. This is an extension of [Agda #1548](https://github.com/chboishabba/dashi_agda/pull/1548) and [Lean #119](https://github.com/chboishabba/dashi_lean4/pull/119), not a competing programme. Independently based on master/main; no divergent donor merges. P0 = solve original Boolean P vs NP. Endpoint mathematics before certification. F2 resource-closing self-quotation is one sufficient route, not a necessary condition for F3 universal failure. N1–N3 polynomial semantic coverage is the enabling priority; N4–N5 universal obstruction in parallel. New lemmas below are mathematical derivations in this markdown, not kernel declarations. No separation claimed.

## 1. Reconciliation: we already have ramified and GCT machinery

Inspected current default-branch source (blob IDs below); historical branch items are explicitly marked. Search index for Lean returned no matches, so use known file paths and PR heads rather than infer absence.

| Producer / source owner | Actual supplied result or boundary | Existing or intended consumer |
|---|---|---|
| Agda DASHI/Mathematics/Complexity/CookLevinCircuitGCTBoundary.agda (f3963789f8b3) | invariantInequalitySeparatesWitnessedOrbits; gctObstructionSeparatesWitnessedOrbits; classicalAndAlgebraicProblemsAreDistinct; OrbitClosureGCTBoundary fields remain obligations | DirectSATLowerBoundExact imports BooleanFormula and Satisfiable; orbit separation is not circuit exclusion |
| DASHI/Biology/SignedMultiplicityObstructionExact.agda (9d8106190b0e) | deltaSwap, orientationSwap, twistedAntiSymmetry, same presence of 1 and 2 yet nonzero signed defect; explicitly cites GCT occurrence and multiplicity literature | SignedMultiplicityYinYangBridgeExact, SignedWreathReachabilityBridgeExact, SSPJProfiniteOrthogonalComplexityRound8Validation (indexed consumers); proposed LGC4–5 |
| DASHI/Mathematics/Complexity/PNotEqualsNPCircuitCarrierNoGoExact.agda (e5ce9c3432e9) | candidateHasZeroSizeAbstractCircuitFamily, candidateAbstractCircuitEvaluatesExactly, candidateAbstractCircuitSizeIsZero: arbitrary functions in old carrier cost zero | must use concrete DAG instead |
| PNotEqualsNPConcreteBooleanCircuitDAGExact.agda (56e111d36b37, same directory) | ConcreteBooleanCircuit, WireRef, Gate, evaluateCircuit, circuitSize, ConcreteCircuitFamily; acyclic gates with actual structural size | shared compiler, quotient circuit; machine-to-circuit coverage not asserted in owner |
| PNotEqualsNPConcreteCircuitSharedCompilerExact.agda (d7814ccc089b) | circuitGateCountBelowSharedConstraintNodeCount; sharedConstraintFamilyCannotSelfEncodeSuperlinearMember | SharedSemantics; no free same-size quotation |
| PNotEqualsNPConcreteCircuitSharedSemanticsExact.agda (763a8a53a3ed) | sharedAcceptanceExact: circuit acceptance exists iff shared acceptance formula satisfiable; canonical gate realization | restriction quotient circuit and SAT encoding, not SAT decision in P |
| PNotEqualsNPRestrictionQuotientCircuitExact.agda (bccbcf901e77) | quotientCircuitGateCount = (rootVariables+1)*stateCount; zero-input output; owner's last comment requires DP equality | DP semantics and same-object resource-closing quotation; not a uniform SAT decider by itself |
| DASHI/Core/QueryFactorisationSufficiency.agda (98c592232292) | FactorsThrough, StaticSufficient; sufficiency not world coverage | LGC2/5; reuse dependent query family rather than duplicate |
| DASHI/Core/ResidualFibreLowerBoundExact.agda (b0fc9a0c998d) | exactResidualInjectiveOnEveryFibre, distinctFutureClassesForceDistinctResiduals | finite cardinality and width consumers, not arbitrary runtime |
| DASHI/ComputerScience/FibreProgramComplexityExact.agda (275abb34923b) | separate description, execution, storage, representation, trace and residual coordinates; transitionConsumer and path cost | N1c and U3 target cost selection |
| DASHI/Moonshine/OggSSPSmallCharacteristicSOTAInertiaRRRefinementExact.agda (a8edafd3648a) | preferredWeightCannotDetermineTameCharacterDenominator: equal preferred p2 weights, different character denominator; NF.witnessRulesOutEveryFlatFactorisation; wild local data still required | actual reusable non-descent mechanism; LGC4/5 candidate, not universal cost theorem |
| DASHI/Analysis/RHGRHDirichletCubicHeckeLocalCorrespondenceExact.agda (2d82566d2de5) | quadratic conductor 3, CM order conductor 1; same-prime split/inert observations of Lean #69, not global analytic Hecke character | TOEArithmeticCMRealizationExact; keep conductor/infinity type/bad local factors separate |
| DASHI/Physics/QFT/SeibergWittenLanglandsReceiptSurface.agda (5b0f6970be45) | targets and postulated abstract types; missingLanglandsBridgeConstruction, empty promotion token | TOE target only, not a constructed Langlands equivalence |
| Lean Integration/ScopedVerifierConsumerSufficiency.lean (1afa1425acb4) | factorizedConsumersEqual, collisionBlocksFactorization, adequateRefinementMustSeparate (actual native source proof bodies) | native Lean LGC2/5; no fresh native circuit/SAT theorem inspected |
| Agda PNotEqualsNPDirectSATLowerBoundExact.agda (0838b3252b3f) | PolynomialSATDeciderCandidate, SATDecisionFailure, candidateIsAnchoredOrAlreadyFails; universalDecisionFailureGivesSATLowerBoundProducer (existing roadmap/source) | PNotEqualsNPClayCoreExact.SATLowerBoundProducer and literal endpoint on standard cost model |

Default-branch arithmetic ramification is also indexed in SSP15CMModSevenExact (p=7), OggSSPP2GaussianCMRamifiedEmbeddingSourceExact (p=2), OggSSPSmallCharacteristicWildDifferentNoGoExact, DuncanSwisherDworkPublishedFirstPoleSharpnessExact and OggSSPSmallCharacteristicBadLevelInertiaLocalizedFourthTermCutsetExact. These are not interchangeable with ramified geometric Langlands.

Historical [Agda #585](https://github.com/chboishabba/dashi_agda/pull/585) head 2cb821df4989 and merged integration [#596](https://github.com/chboishabba/dashi_agda/pull/596) head d5342a6e23b6: inspected PR bodies and changed paths. #585 carries RamifiedLocalValuationSharpnessExact, DuncanSwisherDworkRamifiedA1SharpnessExact, DuncanSwisherLegendreRamificationDepthExact; P11JacquetLanglandsRepresentationStandardAuthorityExact, P11JacquetLanglandsFixedSpaceResolutionExact, P11JacquetLanglandsCoordinateNonCanonicityExact, P11JacquetLanglandsSectionIndependenceExact, CasselmanUnramifiedPGL2FixedVectorTowerExact, P11Level44TwoAdicFixedSpaceIntersectionExact. #596 includes DASHI/Core/SectionIndependentConsumerExact. PR reports same unramified local pi_2 with distinct dimension-3 fixed spaces and dimension-2 intersection, noncanonical alignments; JL at published authority interface, not arbitrary ramified equivalence. Section-independence iff coarse factorization under coverage is directly relevant. These are PR-reported results; inspect historical bodies before source import, no default-branch presence or fresh kernel receipt assumed. The p>3 Dwork valuation comparison is at named Hensel/published boundaries, p=2,3 wild residual open.

Ramified literature ingress: Agda Docs/roadmaps/OpenAIMathCorpusCrosswalk20261114/corpus_manuscripts_source_index_20261101.json (f93e2b24f995) explicitly indexes "Temperedness at ramified places for globally generic exceptional groups" (2026-10-05), "Rationality of the Canonical Unramified Arthur Filtration" (2026-09-24), "The Restricted Geometric Langlands Equivalence in Positive Characteristic" (2026-09-24) and "Global quantum geometric Langlands at irrational level" (2026-10-04). This is manuscript index, not an established ramified correspondence or native proof. [Lean #78](https://github.com/chboishabba/dashi_lean4/pull/78) merged, pins openai/math at 1581d4cbdd69a0faf34b2089614fe2a814316a6a; [Agda #1212](https://github.com/chboishabba/dashi_agda/pull/1212) unmerged provenance mirror. Find the precise theorem, ramification hypotheses, conductor/local data and catalogue/solution declaration in that pin before import; never assume one exists. No need to solve general ramified Langlands to solve PNP.

## 2. Mathematical work LGC1a–LGC3a: explicit polynomial geometric graph encoding

Use the existing concrete bounded-fanin Boolean DAG, n input bits, s gates in topological order, output wire o. Over any field K, define a *sparse system* with variables x_i and z_j, one equation x_i^2-x_i=0 per input and one gate equation z_j-f_j(u,v)=0 per gate. Each u,v is an input or an earlier gate. f=0/1 for constants, 1-u for NOT, uv for AND, u+v-uv for OR. Repeated gate references use the same variable, not copies of the subcircuit. Include output equation only for the acceptance locus, z_o=1 (or x_o=1 if input wire).

**LGC1a unique lift / LGC2a exact projection — proof.** In a field the roots of X(X-1) are exactly 0 and 1, including characteristic two. For fixed Boolean x, induction on topological order gives a unique value z_j=f_j(u,v), itself Boolean by the truth table. Conversely any solution must have those values, by the same induction. Hence projection onto x is a bijection on the graph locus and its inverse is gate evaluation. With output equation, projection identifies precisely the accepted input subset. No solving SAT or enumeration of all x is used to construct the sparse description. The accepting *existence* query is not an efficient evaluation of arbitrary SAT.

**LGC3a resource and sharing — proof.** At most n+s+1 equations of degree <=2, O(n+s) monomial occurrences with coefficients in {0,1,-1}; binary wire labels cost O(log(n+s+2)) each. Thus sparse encoded length O((n+s+1)log(n+s+2)); a single topological pass emits the constraints with O((n+s+1)polylog(n+s+2)) bit work on a standard efficient representation; even sequential tape copying gives a polynomial bound. Evaluate graph coordinates in s Boolean gate steps plus input/output/address handling, polynomial bit overhead, no huge integer arithmetic. Concatenating DAGs with fresh auxiliary names and identifying producer-output wires with consumer-input wires composes the unique lifts. Renaming internal wires transports the graph isomorphically. This is a costed *presentation* construction, not a polynomial decoder for arbitrary geometric presentations nor a functor on an unspecified category. The graph projection includes the input; its injectivity does not imply computational ease of arbitrary consumer queries.

**LGC1b standard machine coverage — classical construction.** For fixed deterministic finite single-tape TM D and time cap t, encode each of O(n+t+1) possible visited cells by constant-width bits for symbol and possible head/state marker, initialize from input, apply the fixed finite radius-one transition table simultaneously at each of t layers. The local function on constant-width input has a constant gate implementation (finite truth-table DNF). Make accepting/rejecting halts absorbing, and OR accepting head/state markers at final layer. Induction on t gives exact configuration simulation and output; no head outside the chosen window can be reached. Total gates O_D((t+1)(n+t+1)); description construction polynomial in n,t, using indexed wires, and sparse geometric encoding above preserves that bound up to logs. Standard multitape-to-single-tape polynomial simulation can precede this construction, or a fixed multitape transition compiler may be proved separately. For polynomial D, set t=c(n+1)^k; this gives a polynomial-size circuit family and sparse geometric presentation of its output graph. Invalid formula handling carried by D. This is the usual classical simulation instantiated to the existing DAG target in mathematical form; native code/weld to canonical CodedStandardHaltingPolynomialDeciderExact remains unpaid. A uniform construction is obtained given D,c,k, but no effective discovery of correct clocks required. Unlike self-quotation, t is an external time bound for a fixed D; no size feedback contradiction invoked.

**LGC1c quotient-ring variant.** In K[x_1,...,x_n]/(x_i^2-x_i), the gate recurrences compute the Boolean function as a ring element. Evaluation at Boolean points identifies this ring with K^(2^n): the delta polynomials product_i (x_i if a_i=1 else 1-x_i) form the evaluation basis. They span since reduction gives at most 2^n square-free monomials and their evaluations are independent. The DAG representation has s shared operations, but explicitly expanding this canonical normal form may take exponential space/time. No equality of costs with ordinary algebraic circuit complexity for an unreduced polynomial follows; do not conflate Boolean quotient equality, polynomial identity, or orbit closure. The sparse system is a better F2 donor than the expanded tensor.

## 3. Mathematical work LGC4a–LGC5a: local-to-global transport and negative controls

**Ramification-style refinement (not arithmetic ramification).** Let h:X->O be the coarse observer, r:X->R an extra indexed local datum, and c:X->C a consumer. If c=g(h,r), any pair with h(x)=h(y) and c(x)!=c(y) must satisfy r(x)!=r(y), by substitution. For a finite fibre h^-1(o), pick one representative of each distinct c value (or joint query row); their r values are injective. This is the existing FactorsThrough/ResidualFibre theorem pattern, applied to local graph/representation observations. If the refined observable has b bits, at most 2^b distinctions. If c is already a function of h, no extra information is necessary. No implication of global coverage or runtime from this width fact. Use the actual inertia counterexample and JL section-independence as donors, not labels alone.

**Multiplicity and extension negative control.** Over F2, take C2 generated by g. Compare two 2-dimensional modules with generator actions I and J=[[1,1],[0,1]]. Both satisfy g^2=I and have two trivial composition factors (line span e1 and quotient). Their occurrence and composition multiplicities coincide, yet rank(g-I) is 0 versus 1, so they are not isomorphic. Fixed-space dimensions are 2 versus 1. This exact small example demonstrates why modular/inertia extensions can matter beyond signed multiplicity. In characteristic zero finite group representations are semisimple; do not export the nonsemisimple example there. In either setting an isomorphism invariant must be related to *all* admissible low-cost computations, not just two modules.

**Rank lower bound with valid scope.** For finite x,y, if F(x,y)=g(h(x),y) and h has at most K values, its communication matrix has at most K distinct rows and rank_Kfield <= K. A deterministic communication protocol with b communicated bits yields at most 2^b monochromatic transcript rectangles (pad to depth b); matrix is sum of at most 2^b rank-one rectangle indicators weighted by the output bit, so rank <=2^b. Thus log2(rank) lower-bounds communication on this split. For equality of m-bit strings the matrix is I_(2^m), rank 2^m in every field. Yet equality has O(m) Boolean gates (XNOR each pair, AND the results). A rank or residual multiplicity exponential in m therefore does not prove superpolynomial gate size: its logarithm is only m, and the high-rank family has an explicit small DAG. This is an adversarial control for universal F3.

**Charging requirement.** For a finite paid event set E of one execution, suppose obligations j have weights w_j and nonnegative allocations a_(j,e) with sum_e a_(j,e)>=w_j and sum_j a_(j,e)<=cost(e). Summing proves sum_j w_j <= total cost. The arithmetic is already supplied by #1548/#119 R4; finding valid weights and allocation for arbitrary DAGs or machine traces is still U2/U3. Multiple cuts may reuse the same gate; do not multiply per-cut multiplicities by depth or sum separate executions. Gate products multiply communication-rank upper bounds, so exponential ranks can arise cheaply. Full input/output graph, identity observer and output observer are additional negative controls; cost of producing output must be counted. Existence of a polynomial sparse graph description is not existence of an efficient procedure for a geometric hard predicate.

**Local regression.** Executed local SymPy exact checks: 48 truth-table/unique-root checks for NOT/AND/OR at all Boolean input pairs in characteristics 2,3,5,7; 8 equality-matrix exact rank checks for m=1..8; 56/56 passed. This is finite regression supporting formulas, not universal proof authority; the proofs above are independent of regression. No GitHub CI invoked.

## 4. Exact remaining lemmas / phases / deliverables

Use n-bit SAT decision function SAT_n on a fixed canonical encoding, including invalid inputs consistently. If defining a geometric image of bounded circuits, fix a common ambient space (padding/coordinates accounted for) and identify the semantic SAT graph independent of its circuit presentation. Otherwise comparing a circuit syntactic object with a truth function is ill-typed. One may use the *set* of graphs admitting sparse size<=s, or a precisely defined closure of that set; closure separation is stronger. An invariant under one orbit is not a separator for the union of all small circuits.

| ID / phase | Exact deliverable and consumer | State after this work |
|---|---|---|
| LGC0 / A | Recover exact ramified sources, local types, authority; attach #585/#596, #78 corpus and GCT owners without duplicate ontology | audit above; historical body/global correspondence not required |
| LGC1 / A N1 | fixed D, all inputs, exact canonical start/halting simulation and cost p_D(n,t), then concrete DAG -> sparse polynomial graph | LGC1a/b/c mathematical construction supplied; native model/bit-code weld open |
| LGC2 / A N2 | graph projection unique lift, preserve accepted output; same-object representation alignment and query factorization | LGC2a proof supplied; native adapter to SharedSemantics, FactorsThrough, Lean sufficiency |
| LGC3 / A N1c/R5 | polynomial encoded size, generation work, share wire identities, compositional graph semantics; bound actual target cost not proof-log size | LGC3a proof supplied; implement syntax/bit encoding or reuse if found; no inverse general geometry algorithm required |
| LGC4 / B R1–R3 | choose concrete semantic ambient object V_n and complexity filtration E_(n,s) with all gate-size<=s functions represented. Local/refined invariants well-defined under admissible alignments, include bad sectors and extensions only where required | exact finite nonfactorization and multiplicity donors exist; common ambient + filtration/invariant construction open |
| LGC5 / C N4 U2–U4 | prove for ALL size-s circuits or all fixed polynomial machines that a semantic obstruction has bound B(s,n); account for arbitrary shared gates, all splits, bypasses and alternative encodings; or construct vanishing invariant on entire E_(n,s) | rank/width and double-counting scope proved; universal charging/closure theorem open |
| LGC6 / D N5 A2 | for each k,c>=1 arbitrarily large n, explicit SAT_n graph violates LGC5 for s=c(n+1)^k; if using uniform route choose fixed D first and find failure/actual superpoly time; no assumed NP-hard invariant oracle | open controlling endpoint, not an interface weld alone |
| LGC7 / E N6 | use LGC1 and LGC5/6 to exclude standard polynomial SAT deciders and feed DirectSATLowerBoundExact.universalDecisionFailureGivesSATLowerBoundProducer then ClayCore; native Lean same theorem | classical transport below; unconditional producer and native weld open |

**Transport proof.** If a correct uniform polynomial SAT decider D existed, LGC1b would yield circuits of size c'(n+1)^k' for fixed constants. LGC1a maps those circuits into the admissible geometric filtration. A strict separator for SAT_n from that entire filtration at arbitrarily large n would contradict membership. Consequently SAT notin P, and because SAT in NP, P != NP. If the separation covers all nonuniform circuits, it proves the stronger NP not subset P/poly (SAT NP-completeness gives the usual reductions). The circuit route does not require behavioural self-reference or full Karp-21 closure. For the constructive Agda consumer, separate a classical negation argument from construction of a concrete failure witness; a search needs a termination proof or explicit classical principle. No assertion of such an inhabitant here.

## 5. Other P0 source owners and consumer dependencies

- [Agda #1040](https://github.com/chboishabba/dashi_agda/pull/1040) (aa40c276b7a3): anchored SAT collision iff decision error, identity factorization and lossless codecs no-go. [#1129](https://github.com/chboishabba/dashi_agda/pull/1129) (730ec95ce044): CodedStandardCanonicalInputExact, CodedStandardHaltingPolynomialDeciderExact, CodedStandardHaltingPolynomialCostModelExact, actual-halting bridge, phase size |Q|(T+1), rules T|R|, quotation size no-gos, Kleene behavioural route; recover before duplicate machine compiler.
- [Agda #1006](https://github.com/chboishabba/dashi_agda/pull/1006) (fc930b20d844, unmerged): PolynomialFactorisationCostExact, PolynomialClassicalObserverExact, MillenniumResidualDescentClassifierExact.UniformObserverNonDescent, RSAQuantumShorPvsNPCrossPollinationExact. Factoring witness vs classical/quantum cost distinction; not NP-completeness. No wholesale divergent merge.
- [Agda #123](https://github.com/chboishabba/dashi_agda/pull/123) (7ac328ee76f3, merged): VerifiedFractranCrankPipeline, CompilerSimulation, CostVector, MDLVector, bounded noCheaperEquivalentInsideSearch. JMD retains original FRACTRAN/MDL architecture attribution; DASHI owns its typed adapters. Not global lower bound. [#1334](https://github.com/chboishabba/dashi_agda/pull/1334) contextual FRACTRAN consumer normalization (search result); exponent bit costs and first-enabled rule search paid.
- [Agda #1474](https://github.com/chboishabba/dashi_agda/pull/1474), [#1502](https://github.com/chboishabba/dashi_agda/pull/1502), [#1445](https://github.com/chboishabba/dashi_agda/pull/1445): Karp-21 original binary codec, signed graph, Cook–Levin convergence; use SAT encoder and verifier only as needed.
- [Agda #1291](https://github.com/chboishabba/dashi_agda/pull/1291) (d8f05ff5fc68): Relate369HyperfabricPantsTOEExact consumes typed pants/gluing, J-invariant sheaf descent, PNFHyperfabric369; EverythingTOESymmetryResolved369, Unifier and Unified.Everything are consumers, not new theorem producers. Indexed cube compatible reductions do not imply arbitrary DAG completeness. Monster 3B restriction/intertwiner sources (indexed scripts monster_3b_normalizer_restriction.g, monster_3b_actual_kernel_structure.g, monster_3b_inertia_phase_resolution.g and monster_3b_suzuki_all_conductors_export.g) are finite representation candidates; recover exact PR/native modules before an invariant is asserted. No fixed finite group decomposition alone establishes asymptotic SAT lower bound.
- [Agda #1546](https://github.com/chboishabba/dashi_agda/pull/1546) fast pi sharing/bit-cost/liveness control; [#1483](https://github.com/chboishabba/dashi_agda/pull/1483), [#1484](https://github.com/chboishabba/dashi_agda/pull/1484), [#1491](https://github.com/chboishabba/dashi_agda/pull/1491), [#1494](https://github.com/chboishabba/dashi_agda/pull/1494), [#1495](https://github.com/chboishabba/dashi_agda/pull/1495) typed proof DAG/corpus identity, shared nodes, provenance and actual stream costs; PNF logical calculus owner DASHI/Reasoning/PredicateNormalFormLogicalCalculusExact.agda. These links and #1546 are inherited from directly read #1548/#119, not newly audited source bodies. Distinguish proof-DAG size from algorithm execution.
- [Lean #117](https://github.com/chboishabba/dashi_lean4/pull/117) (022e45ef3461): actual upstream pequalnp gitlink b3787c5889d7039ad509e5cb7306613325b70f49, separate toolchain; L_meta_1397 restricted-NOT projective-plane line OR and L030 query-local partial-MCSP as scoped benchmarks, not universal. [Lean #118](https://github.com/chboishabba/dashi_lean4/pull/118) (9edb5100e3fa) R1–R5/U2–U4/A2. Lean MillenniumExternal/TerminalCensus.lean reports Agda-owned PNP per #119, not a native proof. Reuse native Integration/ScopedVerifierConsumerSufficiency first.
- [ITIR #73](https://github.com/chboishabba/ITIR-suite/pull/73), [zkSEC #1](https://github.com/chboishabba/zkSEC/pull/1), zkperf observed trace/cost, DA51/PNF source identity: inherited #1548 references, not independently reaudited. Use source/occurrence IDs and measured windows only; verification cost is not search cost.
- [Agda #1548](https://github.com/chboishabba/dashi_agda/pull/1548) (01b532644899), [Lean #119](https://github.com/chboishabba/dashi_lean4/pull/119) (e4ea5e6449de) exact same existing roadmap blob 88690cd04eb: authoritative phase numbering N1–N6. [Agda #1499](https://github.com/chboishabba/dashi_agda/pull/1499) coordinator; #1444/#1536 YM separate, no new Clay prerequisite.

## 6. Prior art and hard barriers

- Gaitsgory/Raskin, [geometric Langlands I](https://arxiv.org/abs/2405.03599), [V](https://arxiv.org/abs/2409.09856): characteristic-zero geometric functor and multiplicity one, not polynomial-time Boolean compilation or arbitrary ramification.
- Mulmuley/Sohoni GCT I DOI 10.1137/S009753970038715X; [Bläser/Ikenmeyer survey](https://www.theoryofcomputing.org/articles/gs010/). Algebraic complexity is a distinct target. Need a concrete Boolean bridge; no unsupported VP/VNP equivalence with Clay.
- [Bürgisser/Ikenmeyer/Panova](https://arxiv.org/abs/1604.06431), DOI 10.1090/jams/908: occurrence obstructions fail for intended permanent/determinant orbit-closure lower bounds in their regime. Not a no-go for every multiplicity/extension invariant. [Dörfler/Ikenmeyer/Panova](https://doi.org/10.1137/19M1287638) multiplicity stronger than occurrence; not permanent/determinant separation proof.
- [Ikenmeyer/Mulmuley/Walter](https://arxiv.org/abs/1507.02955) positivity of Kronecker coefficients NP-hard. Useful concrete reduction donor: recover actual encoding, partition sizes, coefficient decision predicate and reduction direction; hardness of computing an invariant does not lower-bound SAT unless an independent lower bound for that target is shown. Do not infer NP-completeness or polynomial verifier automatically.
- Any claimed universal invariant needs explicit checks against relativization, natural-proofs (constructivity/largeness/usefulness under cryptographic assumptions), and algebrization barriers where applicable. These are constraints, not proofs of impossibility for this project.

## 7. Next consolidated mathematical tranche

A/B: attach standard canonical machine to concrete DAG and sparse polynomial graph using the proved induction and polynomial envelope; attach same-object semantics to existing shared compiler and native Lean factorization. No need to build a parallel geometric Langlands category. C/D in parallel: select an invariant on semantic graphs with a universal gate-change or trace-charging bound; reject candidates on equality, parity, duplicated gates, shared subcircuits, zero-cost extensional abstract carrier, identity observer, and modular extension controls. Prove a hard family with a gap exceeding every polynomial *in charged cost*, not merely in rank/cardinality, then close LGC7/N6. Only after an endpoint derivation seek full independent kernel certification. If local geometry cannot constrain unrestricted computations, retain it as a scoped donor and pursue direct standard-machine lower bound in parallel. No promotion from finite experiments, published authority, provenance or shared nomenclature.

## 8. LGC-R1–R7 — genuine ramified Langlands continuation (2026-11-24)

Stay on the Langlands owner, not a second generic G6 search. The other P0 worker's actual #1548 head 70c6529a83c2841c5b07c517aad1efa9f6bc0723 (roadmap blob 0d71c3b1f398479afcf9c3c43b6503ca59e5e93a, inspected tail) and Lean #119 head 6b2e96c63c9c4fb404177c7710ca1688d06f837a supply G1–G5: Boolean algebra A=F2^X, X={0,1}^n, affine V0, product flags V'=V+span(ab), exact multiplicative complexity MC, exterior residual and bounded-potential transport. Use as input, not duplicate. LGC5/LGC6 and G6 remain open. Below are new mathematical derivations and negative controls specifically for arithmetic Langlands. No native prover or global separation claimed.

### R1. The existing gate graph is split étale, not ramified

Strengthen LGC1a over Z, not only fields. In the integral graph ring, successively eliminate z_j using the monic linear relation z_j-f_j(earlier)=0. This gives an isomorphism with Z[x_1,...,x_n]/(x_i^2-x_i). The factors x_i and x_i-1 generate the unit ideal, so CRT inductively identifies the ring with product_{a in X} Z. Explicit orthogonal idempotents e_a=product_i(x_i if a_i=1 else 1-x_i) sum to 1 and give the evaluation isomorphism. The acceptance equation selects the factors with output one (including empty product ring if no input accepted). Hence the scheme is finite split étale over Spec Z; all Galois actions on geometric points are trivial, and this remains so in residue characteristic two. The presentation may be short while the split product is exponentially large. Intrinsic inertia, conductor and ramification of this graph cannot distinguish circuit complexity. This exact theorem rules out a naive LGC4 identification with wild geometry. To get real ramification one must introduce a genuine arithmetic cover/local system, not rename gate graph fibres.

### R2. A genuine GL(1) ramified gate representation

Use K=Q_2, L=K(i), pi=1+i. The polynomial T^2-2T+2 of pi is Eisenstein at 2, so L/K is totally ramified of degree two. pi^2=2i, hence 2=-i*pi^2 with unit -i. In the normalization v_L(pi)=1, v_L(2)=2. This is the exact factorization consumed by historical RamifiedLocalValuationSharpnessExact; not a purported inference of a factorization from a ramification label. The local quadratic character chi of K^* associated by local reciprocity to L/K is the Hilbert-symbol character chi(u)=(-1,u)_2. For u=2^r v, v an odd unit, chi(u)=(-1)^((v-1)/2) (parity of odd-unit residue modulo 4; chi(2)=1 since 2=N(1+i)). Thus chi is trivial on 1+4Z_2, nontrivial on 1+2Z_2, conductor exponent 2. On the Weil side use the corresponding quadratic character via GL1 local Langlands (local class field theory). Global donor is the quadratic character of Q(i)/Q, equivalently the primitive Dirichlet character modulo 4, odd at infinity. Keep the smooth character of Q_2^* distinct from the Dirichlet character extended by zero on even integers.

For each actual Boolean value a in F2 let rho_a=chi^a. Tensor product realizes XOR: rho_a tensor rho_b=rho_(a+b). Tensor with chi realizes NOT. The Hilbert pairing realizes AND exactly:
    (-1^a,-1^b)_2 = (-1)^(ab),
where the arguments mean (-1)^a and (-1)^b. In particular rho_(ab)=chi raised to (1-symbol)/2. For the odd-unit formula only (-1,-1)_2=-1 is nontrivial. Independent elementary nonnorm proof: x^2+y^2=-1 over Q_2 is impossible, since if either coordinate has negative valuation, scaling by the smallest common denominator and reducing modulo 4 yields a primitive sum of squares equal to 0 mod 4, impossible; integral coordinates have squares 0 or 1 mod 4, never sum to 3. All other sign pairs are split. This is a real local reciprocity/quaternion operation, not the tensor product of two characters (which is XOR). In cohomological language it is the Kummer cup product valued in Br(K)[2], then the explicit two-element re-encoding; no claim it is a tensor functor. At odd primes the Hilbert symbols of these two units are 1, while the real Hilbert symbol is also (-1)^(ab). Global reciprocity product is therefore 1, even on an AND output of 1: multiplying all places erases the nontrivial local bit. Retain labelled places.

The representation of a fixed input's computation is built with one local sign/character label per gate, with constant bit cost per gate at this fixed field. This is an actual GL1 arithmetic encoding of operations, but the family over all x can be exponentially large and computing its aggregate invariants is not free. It does not prove general geometric Langlands nor a cost equivalence of arbitrary automorphic operations.

### R3. Attach to existing P11 Jacquet–Langlands on the same local component

Reopened historical files at #585 head 2cb821df49890b51605d1b990ee0b497e490b88c, actual source bodies:
- DASHI/Algebra/RamifiedLocalValuationSharpnessExact.agda blob 833c9a5592ecf1a1664be34dae11032627359aea, ramifiedSharpCoefficientValuation, unitDepthOneBranchPowerDepth.
- DASHI/Core/SectionIndependentConsumerExact.agda blob f68f75b46abdd0e073b02eeab24c1fc66b7e63e4, factorizationImpliesSectionIndependence, sectionIndependenceImpliesFactorization under SectionFamilyCoversFine.
- DASHI/Moonshine/P11JacquetLanglandsRepresentationStandardAuthorityExact.agda blob 4ebb8197b03cb9cf84198aa2cceef77063b7c821, p11QuaternionLocalAtTwoUnramified, p11BrandtA2IsMinusTwo, imported same local component at 2; not a global equality of representations of different groups.
- DASHI/Moonshine/P11JacquetLanglandsSectionIndependenceExact.agda blob cb2e01ec0333d1099f870193b85476c62fed115e, transportedU2DependenceDetectedByGenericCriterion and satakeResidualSectionIndependent. Distinct coordinate alignments have same Satake residual but different transported operator. #596 is historical integration owner. These source bodies are inspected, not fresh kernel authority.
- Default-branch search found EllipticRationalKummerOpenExact and EllipticRationalTwoTorsionKummerExact plus BSD local valuation parity scripts, but no exact-name HilbertSymbol/LocalReciprocity/ArtinConductor search hits; this is index-limited, not a claim of absence. Elliptic Kummer maps and multiplicative squareclass Kummer here are different typed objects.

Let R be the rank-two Frobenius-semisimple unramified Weil–Deligne parameter of the existing common local pi_2 (N=0), in the weight-two arithmetic normalization with Frobenius polynomial P(T)=1+2T+2T^2 from a_2=-2, det=2. At the representation-level authority boundary, define R_a=R tensor chi^a. LLC twisting compatibility attaches pi_2 tensor (chi^a composed with det) on GL2. Since R is unramified, inertia acts trivially before twisting and by the nontrivial scalar quadratic character after twisting. Consequently:
    a=0: dim R_a^I=2, Artin conductor exponent 0, inverse Euler factor P(T);
    a=1: dim R_a^I=0, Artin conductor exponent 4, inverse Euler factor 1.
Proof of conductor: split R over an algebraic closure into two unramified Weil characters (Frobenius semisimple); twisting either by chi has conductor exponent 2, and Artin conductor is additive. Alternatively the lower ramification groups for L/K are G0=G1=C2, G2=1 (sigma(pi)-pi=-2i, valuation 2; O_L=Z_2[pi]); each nontrivial group contributes codimension 2 in the twisted rank-two representation. The unramified parameter has N=0 and twisting preserves it. No canonical marked U2 coordinate action is claimed; use parameter-level invariants only. No assertion of a new global modularity proof, global level calculation or fixed-space isomorphism. This is a genuinely ramified local twist of the exact previously unramified JL lane.

### R4. Unlabelled Langlands profiles fail completely as universal hardness invariants

For any Boolean function f on X, let w(f)=#{x:f(x)=1}, N=|X|. Form the finite direct sum of global quadratic Galois characters
    M_f = direct_sum_(x in X) chi_global^f(x)
        = 1^(N-w(f)) direct_sum chi_global^w(f).
This is a characteristic-zero representation; its associated local Weil parameters are sums of the corresponding local characters, not an assertion that a reducible direct sum is a cuspidal GL_N representation. At every place the entire unlabelled isomorphism class depends only on N,w. At 2, inertia dimension N-w, Artin conductor exponent 2w, inverse Euler factor (1-T)^(N-w) (trivial Frobenius on unramified summands). For the P11-twisted variant direct_sum R_f(x), the same claims hold with dimension 2(N-w), conductor 4w, factor P(T)^(N-w). At the global character level the Artin L-function is zeta(s)^(N-w) L(s,chi_-4)^w, initially Re(s)>1, extending where the factors do. This is an identity of representation-theoretic factors, not a computational way to determine w. All multiplicities, inertia filtration, local factors and any invariant of the unlabelled representation factor through weight. The previous signed multiplicity and section-independence producers apply exactly: reordering input summands leaves the packet unchanged but may change f.

**Bounded-increment no-go:** a single AND x1*x2 at n>=2 produces weight 2^(n-2) from the zero function, so the raw conductor changes by 2^(n-1) (GL1) or 2^n (P11 rank-two variant). Counting conductor as one unit per ramified place/fibre does not charge actual nonlinear operations. Normalizing by N instead gives a bounded scalar, not superpolynomial goal growth.

**Balanced masking theorem (unrestricted circuits):** put F(x,z)=f(x)+z in F2. Then MC(F)=MC(f): add XOR at zero multiplicative cost for upper bound, and set z=0 for lower bound, as restrictions cannot increase multiplicative complexity. Yet w(F)=2^n independent of f, so M_F and every local/global unlabelled representation datum are identical to those of the easy affine output z. More generally for any fixed k>=0, append k+1 mask variables and put F_k(x,z)=f(x)+sum_(j=0)^k z_j. For EVERY restriction of at most k coordinate positions, at least one mask variable remains free; flipping that variable pairs inputs with opposite output. Each restricted representation has exactly equal trivial and ramified multiplicities, same as easy parity of the mask variables. This proves equality of *all labelled coordinate-restriction profiles of order <=k*, at every place and for the P11 twist, including full inertia filtration, conductors, Euler factors, and all invariant consumers of these packets. MC equality again follows by restriction all z=0. If k grows polynomially with original n, new width remains polynomial, so a superpolynomial MC family stays superpolynomial in padded width (with the conventional family parameter or subsequence). The theorem applies to SAT as well, but gives no proof its MC is high.

For an unconditional impossibility of using these profiles as a complete complexity proxy, count circuits with m ANDs and free affine gates: at stage j each AND uses two affine-linear combinations of at most n+1+j currently available generators; output uses another affine combination. At most 2^[2m(n+1)+m(m-1)+n+m+1] functions realizable with exactly m slots (pad redundant ANDs to cover <=m). For any fixed polynomial m(n) exponent is polynomial in n, smaller than 2^n for large n; some functions have MC>m. Choose a sequence exceeding every fixed polynomial by the same counting with e.g. m=2^(floor(n/3)). Their masked profiles coincide exactly with affine functions. This is a no-go for any claimed *general* superpolynomial lower-bound measure that depends only on these profiles and is bounded polynomially on easy circuits; it does not exclude an encoding-specific SAT predicate or all Langlands-derived invariants. Recovering the fully input-labelled representation determines f pointwise, but entails potentially exponential data and still has no global gate-cost theorem. Seek a richer efficiently describable relation rather than a higher unlabelled moment.

### R5. Exact bridge to the other worker's dual alternating geometry, with joint-charge obstruction

Identify A=F2^X with functions on Boolean points. Each linear functional ell is a weight vector lambda_x over F2. For V containing 1 and ell in V^perp, define
    H_ell(a,b) = product_(x in X) [ ((-1)^a(x),(-1)^b(x))_2 ]^lambda_x
               = (-1)^ell(ab).
Thus the worker's alternating form omega_ell(a,b)=ell(ab) on V/<1> is exactly the exponent of a product of genuine local Hilbert symbols. Bilinearity follows from multiplication and linearity, diagonal vanishes since a^2=a and ell(a)=0, and adding constants is invisible because ell(V)=0. The pairing is weighted and place-labelled; global all-place reciprocity would erase it. For a productive p=ab outside V, V'^perp = V^perp intersect {ell:ell(p)=0}. Evaluation at p is a nonzero linear functional on V^perp (extend basis V by p); its kernel has codimension one. Therefore a single gate simultaneously kills exactly half of the annihilators, namely 2^(dim A-dim V-1), including many nonzero forms. Cannot sum independent Hilbert obstructions as independent paid operations. Counting all killed witnesses, even using higher ramification labels, is not a universal charge. Log of annihilator size decreases exactly one, independent of target f, and reaching any subspace containing f alone only forces one extra dimension. Retain joint residual correlations and decomposable-plane constraints. This bridge is a pointwise class-field-theoretic realization of G3; not a solution of G6.

### R6. Local exact execution, actually run this continuation (no CI)

Re-executed previous reported gate/rank regression in the local runtime: 48/48 gate equations with unique root at characteristics 2,3,5,7, 8/8 identity-matrix ranks (SymPy DomainMatrix, Q, dimensions 2^1 through 2^8). These reproduce the earlier document's reported figures; execution evidence in this continuation, not retroactive proof of an earlier run. New exact checks: 16/16 Hilbert sign vs primitive conic residue checks mod 4,8,16,32; 5/5 Gaussian odd norm image checks mod 4..64; 4/4 integral idempotent evaluation matrices n=1..4; 7,424/7,424 masked local profile comparisons for every 3-input truth table and k=0,1,2, over every coordinate subset size <=k and all its assignments; explicit n=3 affine annihilator has 16 elements, x1*x2 discharges exactly 8. These finite checks do not certify local class field theory, analytic L-functions or arbitrary circuit lower bounds. Proofs above establish the general elementary consequences independently.

Reproduction (Python/SymPy, no external data):
```python
from itertools import product, combinations
import sympy as S
from sympy.polys.matrices import DomainMatrix
gate = rank = hilbert = mask = 0
for p in (2,3,5,7):
    for a,b in product(range(2), repeat=2):
        for z in (1-a,a*b,a+b-a*b):
            assert [v for v in range(p) if (v-z)%p==0] == [z]
            gate += 1
for m in range(1,9):
    assert DomainMatrix.eye((2**m,2**m),S.QQ).rank()==2**m
    rank += 1
for k in range(2,6):
    q=2**k
    for a,b in product(range(2), repeat=2):
        u,v=(-1)**a,(-1)**b
        symbol=(-1)**(((u-1)//2)*((v-1)//2))
        soluble=any((u*x*x+v*y*y-z*z)%q==0 and (x%2 or y%2 or z%2)
                    for x,y,z in product(range(q),repeat=3))
        assert symbol==(-1)**(a*b) and soluble==(symbol==1)
        hilbert+=1
t=S.symbols('t')
assert S.discriminant(t*t+2*t+2,t)==-4
for q in (4,8,16,32,64):
    norms={(a*a+b*b)%q for a,b in product(range(q),repeat=2) if (a*a+b*b)%2}
    assert norms=={a for a in range(q) if a%4==1}
for n in range(1,5):
    X=list(product(range(2),repeat=n))
    E=S.Matrix([[S.prod(xi if ai else 1-xi for xi,ai in zip(x,a))
                 for a in X] for x in X])
    assert E==S.eye(2**n)
for k in (0,1,2):
    n=3+k+1
    X=list(product(range(2),repeat=n))
    subsets=[I for j in range(k+1) for I in combinations(range(n),j)]
    for f in range(256):
        ys=[((f>>sum(x[i]<<i for i in range(3)))&1)^(sum(x[3:])%2) for x in X]
        for I in subsets:
            counts={a:[0,0] for a in product(range(2),repeat=len(I))}
            for x,y in zip(X,ys):
                counts[tuple(x[i] for i in I)][y]+=1
            assert all(c==[2**(n-len(I)-1)]*2 for c in counts.values())
            mask+=1
X=list(product(range(2),repeat=3))
V=[sum((((i&1)^sum(((i>>(j+1))&1)*x[j] for j in range(3)))%2)<<k
       for k,x in enumerate(X)) for i in range(16)]
p=sum((x[0]*x[1])<<k for k,x in enumerate(X))
L=[l for l in range(256) if all((l&v).bit_count()%2==0 for v in V)]
assert len(L)==16 and sum((l&p).bit_count()%2 for l in L)==8
assert (gate,rank,hilbert,mask)==(48,8,16,7424)
```

### R7. Exact remaining Langlands-only proof obligations and consumers

| Lemma | Status and next mathematical deliverable |
|---|---|
| R1/LGC4a | Integral split-étale theorem derived; retire naive graph inertia as complexity measure. |
| R2/LGC4b | Genuine ramified GL1 sign character/Hilbert gate transport derived using standard class field theory; native valuation and source-specific character adapters open. |
| R3/LGC4c | Same P11 local rank-two twist conductor/Euler factor derived at explicit LLC authority boundary; attach historical p11 unramified parameter and conductor adapter. |
| R4/LGC5a | Unlabelled and bounded-order coordinate local-profile no-go proved; never promote raw conductor, multiplicity, Euler factors or their global products to universal cost. |
| R5/G3 | Weighted local Hilbert-symbol realization and exact joint annihilator update proved; no independent private-gate charges. |
| R7a/LGC4d | Construct a *label-aware, compositional* local system/Weil representation or cohomological object whose arithmetic data is sensitive to cross-coordinate dependencies and well-defined under admissible section/representation changes. Charge any n-dependent labels, local systems and coefficient encodings. Must defeat R4 masking; no brute-force exponential truth-table materialization as a purported efficient compiler. |
| R7b/LGC5 | Prove a noncircular invariant on that object with a uniform bound under EVERY legal product extension (or every actual machine transition), including simultaneous discharge, shared gates and arbitrary XOR; explicitly derive how local correspondence and gluing transport that bound. R5 rules out naive cardinality. |
| R7c/LGC6 | On canonical SAT family, prove any goal object forces superpolynomial accumulated charged progress, for all fixed polynomial budgets. No conclusion from hard arbitrary functions, ramified extension existence, prime counts or analogies with BSD/RH. |
| LGC7/N6 | Existing DirectSATLowerBoundExact conditional endpoint plus standard-machine coverage. No new endpoint inhabitant. |

Priority R7a/b/c in one mathematical tranche, not new certification infrastructure. Candidate next target is a section-independent but relation-sensitive *labelled* character packet with an explicit universal edge-cost theorem; local/global Langlands equivalence alone does not bound the cost of obtaining the packet. If no such theorem, retain this lane as a mathematically scoped donor; other worker owns general multiplicative-complexity route. No requirement to solve RH, BSD or YM first.

Source attribution: classical local reciprocity and quadratic Hilbert pairing: Kiran Kedlaya, https://kskedlaya.org/cft/sec_localrecip.html ; Romyar Sharifi, https://www.math.ucla.edu/~sharifi/notes/algnum-ch09.html ; John Voight, *Quaternion Algebras*, DOI 10.1007/978-3-030-56694-4, local and global Hilbert symbols (https://link.springer.com/chapter/10.1007/978-3-030-56694-4_12 and _14); Ralf Schmidt, *Some remarks on local newforms for GL(2)*, https://math.unt.edu/~schmidt/papers/gl2.pdf ; LLC parameter/conductor compatibility https://doi.org/10.1017/S1474748024000227 ; LLC twisting https://masaooi.github.io/LLC.pdf. These are standard theorem authorities, not claimed reproofs of LLC. DASHI owns only the gate-encoding, profile no-go and crosswalk synthesis here; preserve JMD attribution and other worker's G1–G5 ownership. P11 arithmetic normalization distinct from unitary automorphic normalization; inverse Euler factor at a ramified twist is 1 in either convention. No source of a universal lower bound is imported by citation.

## 9. R8–R13: Monster-inspired cocycle correction, labelled ramified descent and a universal scoped charge (24 Nov 2026)

Stay on the Langlands owner (#1549/#120); #1545 is a donor, not a new workstream. Live #1545 head e7cca5d6c88fcd363ce33f0d1db41ea24e8af4e7; actual canonical Docs/roadmaps/Monster3BEndpointFirstConstruction20261123.md blob 257b17cea5b60a81f52f8db07a006fb46e8af686 inspected. It distinguishes character-level 12+78 (already supplied by IbrahimMonster3BPhaseResolvedCharacterTwelveSeventyEightWeldExact) from actual original complex Hom operators and simultaneous extraspecial lift (open). Actual DASHI/Moonshine/Monster3BNormalizerCocycleCancellationExact.agda blob f3dec4ac1e0e9eb6f51f52f667f0ff28413fe35b, compensatedTensorActionIsHonestOnPureTensors, is C3-specific and must not be silently reused as a C2/mu4 theorem. Related indexed owners Monster3BFiniteHeisenbergCocycleExact, Monster3BFiniteHeisenbergAssociativityExact, Monster3BFiniteHeisenbergCentralExtensionExact; exact source paths need inspection before native adapter. The mathematical inspiration is cocycle correction plus actual Hom reconstruction, not 729 or 90 as a complexity invariant. Other PNP worker current #1548 049e4ed2d9f75648624064d785b699eca3204ef3 / #119 b35f249b3b21ad2de0b3c222140ff100e5c6e84b; retain their G1–G6 ownership.

### R8. Actual labelled relative character lines and gluing

Let X=F2^n, W=W_Q2, chi the ramified order-two Weil character of R2. For f:X->F2 define L_f(x)=C with W acting by chi^f(x). This is a family of actual rank-one Weil representations on the discrete labelled base. Pointwise GL1 LLC gives the corresponding family of local characters; P11 twist R tensor L_f is available as in R3. The carrier is compactly *presented* by a given Boolean circuit and fixed character, with no exponential packet materialized by the compiler. The all-x semantic family is a mathematical object, not a polynomial algorithm to evaluate arbitrary f.

For an arrow x->x+h of the translation groupoid define D_f(x,h)=Hom_C(L_f(x),L_f(x+h)) with the conjugation W action. It is a line with character chi^{Delta_h f(x)}, Delta_h f(x)=f(x+h)+f(x). The Hom is over C, NOT Hom_W: the latter is zero when the characters differ. Composition of linear maps gives canonical W-equivariant tensor isomorphisms
    D_f(x+h,k) tensor D_f(x,h) -> D_f(x,h+k).
Associativity follows from composition, identity from End of the source line. In character labels Delta_{h+k} f(x)=Delta_h f(x)+Delta_k f(x+h). This is a multiplicative line system on arrows; do not pretend the original L_f has equivariant isomorphisms along every translation. The relative system is a coboundary, has trivial cycle character, and is not a new nontrivial H^1 class. Its labelled edge data, however, recover f up to a constant: if D_f and D_g agree as characters on all coordinate edges, then Delta_ei(f+g)=0 for every i, so f+g is constant by connectedness. One anchored value determines the original function. Arbitrary changes of fibre basis cancel in composition; if using explicit local intertwiners in place of characters, retain section provenance where no equivariant map exists. This is the precise SectionIndependentConsumerExact / P11JacquetLanglandsSectionIndependenceExact donor application, not a claim of a new arithmetic Langlands equivalence on X.

Composition in the circuit presentation: XOR tensor, NOT twist, AND the pointwise R2 Hilbert-symbol cup operation and re-encoding (not an ordinary tensor functor). The derivative of a product obeys the exact Boolean identity
    Delta_h(ab)=a Delta_h b + b Delta_h a + Delta_h a Delta_h b.
This preserves all correlations and shared inputs. A derivative family with variable h has circuit construction by two evaluations f(x), f(x+h) and XOR; at most 2m AND for original m, plus polynomial affine work. Relative characters and P11 twists follow pointwise. Thus the R7a label-aware presentation/gluing sublemma is supplied mathematically. The full R7a endpoint still needs a noncircular arithmetic object/invariant on that presentation whose cost bound can be strong enough for SAT; reading the whole labelled packet or finding its minimal circuit is not a paid shortcut.

### R9. Characteristic-two Heisenberg correction: fourth roots, not 1/2

Fix a computational subspace V containing 1 and a functional ell in V^perp. U=V/<1>. R5 supplies the alternating pairing B(u,v)=ell(uv), exactly the exponent of the weighted product of local Hilbert symbols. Important: (-1)^B itself is a *symmetric* cocycle, has trivial commutator, and is a coboundary. It is not the Heisenberg cocycle. Indeed with coordinates u_i, q_0(u)=sum_{i<j} B_ij u_i u_j (mod 2) satisfies q_0(u+v)-q_0(u)-q_0(v)=B(u,v). A nontrivial Heisenberg commutator requires a one-sided cocycle.

Choose an ordered basis and C strictly upper triangular with C+C^t=B. Define H_C=U x Z/4 with law
    (u,t)(v,s)=(u+v,t+s+2 u^t C v mod 4).
Bilinearity proves associativity; commutator is (0,2B(u,v)). The central generator acts by i in the chosen complex central character; this is a finite group derived from the arithmetic Hilbert pairing, NOT the actual Galois group of Q2 or a new local LLC construction for H_C.

For an isometry A of B, E=A^t C A-C over F2 is symmetric. Unlike the Monster F3 donor, one cannot divide by 2. Define
    Q_E(u)=sum_i E_ii u_i + 2 sum_{i<j} E_ij u_i u_j mod 4.
Coordinates here are Boolean representatives 0,1. Using u_i xor v_i=u_i+v_i-2u_i v_i over Z proves
    Q_E(u+v)-Q_E(u)-Q_E(v)=2 u^t E v mod 4.
Consequently (u,t)->(Au,t+Q_E(u)) is an automorphism of H_C, fixing the central generator; adding 2 times a linear functional gives the other lifts. The same formula compares different choices of C with equal alternating part (the symmetric difference). Diagonal terms really matter: over mu2, the diagonal of a polarization vanishes, so if E has nonzero diagonal no mu2-valued correction exists. Passing to mu4 repairs it exactly, with no odd-characteristic formula smuggled in. Individual lifts do not necessarily compose: their defects are additive characters U->Z/4, hence in 2U^*. A simultaneous isometry-group lift would require splitting this group extension; not automatically supplied or needed for the line-system charge.

For rank B=2r and radical dimension d-2r, the complex twisted group algebra with central action i has 2^(d-2r) simple blocks each M_(2^r)(C). Proof: symplectic basis plus radical; for each hyperbolic pair use Pauli shift and sign, anticommuting, spanning M2; distinct pairs commute. Radical generators commute with everything, and may be rescaled by i to square to identity. Their 2^(d-2r) characters give the blocks. This is finite Stone–von Neumann/Morita structure, not evidence of circuit cost. A specific honest source module M in a fixed irreducible central sector has the canonical evaluation H tensor Hom_(H_C)(H,M)->M; by semisimplicity and Schur it is an isomorphism (restrict to the isotypic summand when not all of M is isotypic). If an actual normalizer action T_g and projective factor K_g with cocycle alpha exist on that sector, L_g(phi)=T_g phi K_g^-1 on the Hom factor satisfies L_g L_h=alpha(g,h)^-1 L_(gh). Tensor evaluation gives the genuine action; scalar gauge cancels. This is the exact characteristic-two counterpart of #1545's Hom mechanism, with no invented multiplicity module or source action. Nothing here supplies an honest source action of all computational transformations on one fixed U; V and ell can change with gates.

### R10. Universal Langlands charge from joint translation stabilizers

Use R8 relative characters, not just their unlabelled direct sum. For V containing the affine functions define
    S(V)={h in X : Delta_h v is constant in x for every v in V}.
Equivalently all relative character lines for each v along h have one fixed inertia type over all x. S(V) is a subspace: Delta_(h+k) v(x)=Delta_h v(x)+Delta_k v(x+h), and constants add. For any h in S(V), alpha(h)=Delta_h a and beta(h)=Delta_h b are linear functionals on S(V) when a,b in V. For p=ab, the R8 derivative formula shows that every h in ker alpha intersect ker beta (inside S(V)) has Delta_h p=0. Hence for V'=V+span(p),
    ker alpha intersect ker beta <= S(V') <= S(V).
Thus codim_X S(V') - codim_X S(V) <= 2 for every legal AND extension, regardless of shared gates, XOR, alternative path or choice of affine coordinates. Initial affine V0 has S(V0)=X. If f is in final V_m, S(V_m)<=S(f), where S(f) is defined with just f. Telescoping:
    MC(f) >= ceil((n-dim S(f))/2).
This is a real universal gate-progress bound, expressed in arithmetic relative inertia labels. It is the KNOWN linear-structure dimension lower bound (see NIST/PMC below), not a novel asymptotic lower bound. It is sharp for f(x,y)=x dot y on 2r bits (all nonzero translations give nonconstant derivative, MC=r). The potential codim S(V)/2 is at most n/2, so R7b is paid only for this scoped linear invariant, not the superpolynomial endpoint.

There is an exact nonlinear-core factorization, analogous to the Monster Hom separation but at the function level. For S=S(f), h->Delta_h f is a linear functional on S. Extend it to a linear l on X. Then f+l is constant on S-cosets, hence factors uniquely through X/S. Conversely, any f=l+g(q(x)) for a linear quotient q implies ker q <= S(f). Consequently codim S(f) is exactly the smallest linear quotient dimension in such a factorization (not the least number of nonlinear gates). For a whole V choose the affine correction for each basis function and extend linearly. The quotient is canonical; a splitting/choice of linear l is not, consistent with section independence. This is a concrete FactorsThrough consumer and exact backsolve: arbitrary m nonlinear operations imply a nonlinear core of at most 2m linear dimensions, but once m>=n/2 the bound is exhausted.

### R11. Stronger no-go: even ALL labelled translation-pair Langlands profiles conceal arbitrary MC

The earlier R4 masking defeats bounded-order coordinate restrictions. Now use all translations, not just coordinate axes. For x,y in F2^r and arbitrary g:F2^r->F2, let
    b_g(x,y)=x dot y + g(y).
This is the classical Maiorana–McFarland bent family (identity permutation case). For every shift (u,v), compute the sign autocorrelation
    C_g(u,v)=sum_(x,y) (-1)^[x dot v + u dot y + u dot v + g(y)+g(y+v)].
If v !=0 the sum over x vanishes. If v=0 and u!=0 the sum over y vanishes. If both zero it is 2^(2r). Thus the autocorrelation profile is identical for every g. The signed Walsh transform is
    W_b(a,b)=2^r (-1)^[g(a)+b dot a],
so even the entire labelled absolute Walsh spectrum agrees. Weight alone can differ, so append one extra parity mask z:
    F_g(x,y,z)=x dot y+g(y)+z.
Now weight is exactly 2^(2r), independent of g; for each shift (u,v,w), C_F=2(-1)^w C_g(u,v). The labelled absolute Walsh spectrum is also independent of g: 2^(r+1) for mask frequency 1 and 0 for frequency 0. Since both marginals at any shift are balanced, the four joint sign counts (++/--,+-/-+) are (N+C_F)/4 and (N-C_F)/4 respectively, N=2^(2r+1). Therefore *every labelled shift's complete unlabelled pair-character packet*, including both joint output labels, tensor product, local GL1 Artin data and P11-twisted data, agrees with the easy quadratic-plus-affine case g=0. The relative line family from R8 is not the same as this aggregated packet: retaining the actual basepoint x,y,z preserves information; summing over basepoints loses it. No claim about all higher-order correlations or full labelled Weil lines.

Restrict x=z=0 to recover g, so MC(F_g)>=MC(g). Conversely MC(F_g)<=r+MC(g). There exist g with superpolynomial MC by the standard circuit counting bound already in R4; g=0 has MC=r by R10. For F_g every shift with (u,v)!=0 gives balanced (nonconstant) derivative; the z-axis consists of constant derivatives, so S(F_g)=span(e_z) and R10 returns the same r for every g. The easy and arbitrarily hard families share exact pair-packet, all labelled absolute Walsh magnitudes, full translation stabilizer and total conductor. Thus even these joint arithmetic/spectral invariants cannot alone deliver an invariant with a superpolynomial universal separation on the masked hard family. This does not prove the canonical SAT family is hard or disprove every possible Langlands-derived invariant. To transport to SAT use an explicit SAT reduction and resource accounting; no such lower bound is claimed. Phase-sensitive signed Fourier data or all basepoint-labelled arrows recover information but still require a noncircular universal progress theorem.

### R12. Local exact checks (executed in this continuation)

Local Python/SymPy exact integer/GF2 arithmetic, no CI. 21,840/21,840 polarizations over 5 deterministic symmetric matrices at each d=2,4,6 and all pairs of Boolean vectors; 32,768/32,768 complete shifted pair profiles (all 256 g on 3 bits, every shift on 7 bits), independent direct counting against integer Walsh autocorrelation; 7,424/7,424 joint stabilizer gate-step checks on all pairs of elements in the affine space and its 7 distinct one-AND extensions on 3 bits (8 spaces). Total 62,032 finite checks; proofs above are independent. No fresh Agda/Lean kernel run. Reproduction:
```python
from itertools import product
from random import Random
from collections import Counter
import sympy as S
rng=Random(1549)
c=0
for d in (2,4,6):
    for t in range(5):
        M=S.Matrix(d,d,lambda i,j:rng.randrange(2))
        E=(M+M.T).applyfunc(lambda v:v%2)
        for i in range(d): E[i,i]=rng.randrange(2)
        X=list(product(range(2),repeat=d))
        def q(x):
            return (sum(int(E[i,i])*x[i] for i in range(d))
                    +2*sum(int(E[i,j])*x[i]*x[j] for i in range(d)
                           for j in range(i+1,d)))%4
        for x in X:
            for y in X:
                z=tuple(a^b for a,b in zip(x,y))
                assert (q(z)-q(x)-q(y))%4==2*(sum(x[i]*int(E[i,j])*y[j]
                       for i in range(d) for j in range(d))%2)
                c+=1
assert c==21840
def fwht(a):
    a=a[:]; h=1
    while h<len(a):
        for i in range(0,len(a),2*h):
            for j in range(i,i+h):
                a[j],a[j+h]=a[j]+a[j+h],a[j]-a[j+h]
        h*=2
    return a
r=3; N=1<<(2*r+1); m=(1<<r)-1
ref=None; count=0
for g in range(256):
    s=[(-1)**(((x&m)&((x>>r)&m)).bit_count()%2
              ^ ((g>>((x>>r)&m))&1) ^ (x>>(2*r))) for x in range(N)]
    W=fwht(s); C=[z//N for z in fwht([v*v for v in W])]
    assert sum(s)==0
    if ref is None: ref=C
    assert C==ref
    for h in range(N):
        counts=Counter((s[x],s[x^h]) for x in range(N))
        assert sum(counts.values())==N
        assert counts[1,1]==counts[-1,-1]==(N+C[h])//4
        assert counts[1,-1]==counts[-1,1]==(N-C[h])//4
        count+=1
assert count==32768
n=3; N=1<<n; allmask=(1<<N)-1
base={sum(((i&1)^(((i>>1)&x).bit_count()%2))<<x
          for x in range(N)) for i in range(1<<(n+1))}
def constant_derivative(v,h):
    return sum((((v>>x)^(v>>(x^h)))&1)<<x
               for x in range(N)) in (0,allmask)
def stab(V):
    return {h for h in range(N) if all(constant_derivative(v,h) for v in V)}
Vs={frozenset(base)}|{frozenset(base|{u^(a&b) for u in base})
                      for a in base for b in base}
count=0
for V in Vs:
    old=stab(V)
    for a in V:
        for b in V:
            new={h for h in old if constant_derivative(a&b,h)}
            assert len(old)<=4*len(new)
            count+=1
assert len(Vs)==8 and count==7424
```

### R13. Revised endpoint roadmap / exact remaining lemmas / ownership

| ID / phase | Mathematical deliverable | Producers -> consumers / boundary |
|---|---|---|
| R8 / LGC4d / A | labelled character family, relative Hom lines, gluing, reconstruction up to anchor, polynomial circuit presentation | R2/R3, historical SectionIndependentConsumerExact and P11JacquetLanglandsSectionIndependenceExact -> R9/R10; derived, native weld open |
| R9 / B | characteristic-two mu4 cocycle polarization and individual lifts, radical/isotypic blocks, reciprocal Hom cocycles | #1545 C3 donor, R5 Hilbert exponent -> actual relative representation; derived mathematical formulas, no simultaneous group lift claim; do not duplicate Monster endpoint |
| R10 / LGC5-scoped / B-C | joint translation stabilizer codim progress <=2, canonical quotient/factorization | R8, FactorsThrough, ResidualFibreLowerBoundExact, existing G1-G4 -> linear lower bound; derived and known prior art; cannot grow beyond n |
| R11 / C | all-shift pair-character plus absolute spectral profile collision with arbitrary MC | R4, Maiorana–McFarland -> invariant selection; general theorem supplied |
| R7a' / LGC4d / C | choose a phase-sensitive or higher relational arithmetic consumer beyond R11, with well-defined same-object transport under admissible section changes; do not merely choose entire truth table as complexity measure | R8/R9, signed multiplicity, P11/JL, #1291 indexed gluing; open as cost-sensitive consumer |
| R7b' / LGC5 / C | derive universal bounded charge for that specific consumer for all legal AND extensions, arbitrary sharing, joint discharge; bound may not saturate at polynomial in n by construction | R5/R10, #1548/#119 G6, fast pi and #123 charge controls; open |
| R7c / LGC6 / D | independent superpolynomial SAT goal separation for same consumer, all polynomial budgets | canonical SAT, #1040/#1129/#1474, standard machine compiler; open |
| LGC7/N6 / E | original standard cost-model endpoint, conditional consumer | DirectSATLowerBoundExact and ClayCore; no unconditional inhabitant; native weld after mathematical endpoint |

Next combined R7a'/b'/c mathematical tranche: use phase-sensitive local pairings or multi-arrow gluing, test actual dependence on signs (not only conductor), and seek a bounded global charging theorem that survives easy quadratic bent packets and arbitrary g. R9 explains exactly how projective gauge can cancel rather than impose computational cost; do not count the number/dimension of complementary Hom modules or the number of cocycle conditions as paid primitives. A full simultaneous lift may carry a genuine cohomological obstruction but requires a specified source group/action and proof of connection to *all* low-cost algorithms; no such source action is inferred from this construction. Do not repeat local tests as a gate to endpoint mathematics; use #1548/#119 for general G6. Remain on Langlands, no RH/BSD/YM/Monster prerequisite.

Prior art and attribution: rank/codimension bound is Theorem 2 in *Boolean Functions with Multiplicative Complexity 3 and 4*, https://pmc.ncbi.nlm.nih.gov/articles/PMC7918276/ and https://www.nist.gov/publications/boolean-functions-multiplicative-complexity-3-and-4 (not a new DASHI lower bound). Maiorana–McFarland/Walsh formulas are classical bent-function theory; see e.g. https://drops.dagstuhl.de/storage/00lipics/lipics-vol362-itcs2026/html/LIPIcs.ITCS.2026.72/LIPIcs.ITCS.2026.72.html for a modern use (its query-complexity bound is not a circuit bound). Local reciprocity is R2 standard authority. R8–R11 arithmetic representation crosswalk, exact mu4 adaptation and profile-based negative-control synthesis are DASHI working mathematics, no priority claim over existing representation or Boolean function theory. Preserve JMD/DASHI split from #123 and Monster source-specific character attribution.

## 10. R14–R20 — F2/F3 source bridge, cubic ramification and selector-SAT (2026-11-24)

User directed reuse of existing F2/F3 bridge, stay on Langlands. Attached continuation and selector geometry are the basis; other worker owns G13a–e and G12a–c. Live #1548 head 9cd7ebdc7459ed956f77281642ce62754f8483e2 and #119 ca3364ab5eb500b976b16f55a8cad3dadf3246d5 match the supplied selector-SAT handoff. Langlands work extends #1549/#120; not a Monster, RH, BSD or YM detour.

### R14. Actual default-branch F2/F3 donors inspected

- DASHI/ComputerScience/BinaryBalancedTernarySubcarrierExact.agda, blob c9ade4f43191c2790f62230c805e95d29e2e36e6: embedBit false=sspNegOne, true=sspPosOne, binaryTernaryRoundTrip, centreIsUnusedByBinaryEmbedding, binaryEmbeddingPreservesBooleanComplementAsAntipode, binaryTernaryStreamRoundTrip, binaryInBalancedTernaryRepresentation. This is exact antipodal subcarrier, not additive field map.
- DASHI/Codec/BalancedTritBitFibre.agda, 9fa72fc85938f78aa64cc53443a06ada3824280a: encodeFibre/decodeFibre and inverse laws, supportBit, OptionalSignBit, encode-commutes-involution, wordBitCost-support-plus-sign. Zero has no sign bit, nonzero sign retained.
- DASHI/Interop/CodecCarrierFibreBridge.agda, a11a165afb47e32129eea923cc4e14f4d189436c: sspToFibre/fibreToSSP inverse, signToPolarity and flip compatibility.
- DASHI/Foundations/Base369BinaryTernaryRefinement.agda, 6345afd94fda8b8b5a45f635bf3fba6486c1998d: Resolution23, independent binaryDepth/ternaryDepth, binary-ternary-refinement-commutes, circlePhaseRefinementDiamond (3->6/9->18).
- DASHI/Arithmetic/SixWheelCRTExact.agda, 7f5648752595f796f16c7e6de68a557f77366fd0: r6CRT23RoundTrip, crt23R6RoundTrip, survivor residues (1,1),(1,2). Actual mixed-prime residue chart, not merely cardinality.
- DASHI/Mathematics/Topology/AlexanderHornedMixedPrimeCRTWeldExact.agda, af2baed60578bcf481b874e20ed8d40507b7724c: explicit mixed address system, ternaryBinaryTwoBitRoundTrip and binaryPairUnusedCode; distinguishes inverse-system sets from ring transport.
- DASHI/ComputerScience/ShorStandardBinaryTernaryStoredProgramComputerExact.agda, 5d4df6e47176d71a68f1c9ea3983fe85ef107d9b: rebuildBinaryState/rebuildTernaryState, same decoded order15/order21 executions; finite concrete source, not universal machine-cost theorem.
- DASHI/Foundations/TernaryGolay/BinaryTernaryMacWilliamsUnification.agda, ea6e20fc9fe3ecb91c64e1943d6c5e29071c9984: common q-ary distribution/coefficients, general theorem and binary octad boundary explicitly separate. Do not infer arbitrary code equivalence from it.
- DASHI/Computation/SSSPBinaryTernarySymmetryRefinementBidiExact.agda, 556b91905ac69913ccbd7f763eed30c554accb23: explicit refinement and symmetry distinction. Source bodies inspected at master; no new kernel run.

### R15. Gate transport preserving the actual antipodal convention

Use e(b)=2b-1 in F3 (false=-1,true=+1), not the opposite sign convention of the earlier Hilbert phase (-1)^b=-e(b). On the nonzero antipodal carrier, with s=e(a),t=e(b):
    e(NOT a)=-s;
    e(a XOR b)=-st;
    e(a AND b)=(s+t+st-1)/2 in F3.
Derive the last equation from a=(s+1)/2,b=(t+1)/2 and 2ab-1. All outputs stay in the nonzero fibre. A ternary arithmetic implementation of a Boolean DAG uses O(1) fixed-field operations per Boolean gate and preserves sharing. In reverse, use the existing support/sign fibre with a canonical zero code and fixed finite lookup Boolean circuits per F3 operation; each fixed-field primitive has constant Boolean gate count, so total gate size polynomially equivalent. This does NOT preserve free-XOR multiplicative complexity at unit cost: XOR maps to signed multiplication in F3. No unital ring homomorphism F2->F3 exists (1+1=0 would map to 2=0). No common field containing both as subfields. Mixed prime lanes are paired typed charts, not a shared linear vector space. R9 mu4 cocycle still needs fourth roots: C3 phase does not repair order-two diagonal defects. This explicit sign preservation closes the transport sublemma, not a cost shortcut.

### R16. Genuine cubic local Langlands lane at 3

Let K=Q3(zeta), zeta primitive cube root, pi=1-zeta. pi^2-3pi+3=0 is Eisenstein, so pi uniformizer, v_K(3)=2. Let L=K(theta), theta^3=pi. Eisenstein over K gives degree 3, totally ramified, theta uniformizer; K contains mu3, so L/K is cyclic Galois. For sigma(theta)=zeta theta and either nonidentity automorphism:
    v_L(sigma(theta)-theta)=v_L(zeta-1)+v_L(theta)=3+1=4.
Since O_L=O_K[theta] (Eisenstein uniformizer generates integral ring here), this gives lower ramification groups G0=G1=G2=G3=C3, G4=1; one break 3, also upper break 3 for this cyclic group. For either nontrivial one-dimensional character the Artin conductor exponent over K is 4 (each nontrivial group contributes one). Local reciprocity gives eta:K^*->mu3 with kernel N_(L/K)(L^*), conductor exponent 4, thus nontrivial on 1+pi^3 O_K and trivial on 1+pi^4 O_K. Choose u in 1+pi^3 O_K with eta(u)=zeta (if primitive inverse, square it). This is an existence and finite constant-field choice from the conductor theorem, not an explicitly evaluated cubic Hilbert symbol on a guessed unit. GL1 LLC gives the corresponding Weil character; eta is distinct from the earlier quadratic chi over Q2. The character may be written as a norm-residue/Hilbert symbol with convention fixed by eta; in particular eta(u^j)=zeta^j. The sign -1 itself is a cube, so do not naively copy the Q2 Hilbert sign pairing at 3.

The actual ternary carrier t in {-1,0,+1} maps to eta^t; inversion swaps the nonzero phases and fixes zero. For the repository's binary antipodal subcarrier, use eta^{e(b)}, NOT eta^b unless explicitly converting the index. Character support via trivial/nontrivial recovers the support bit, and distinction eta versus eta^-1 recovers sign. Conductors alone cannot distinguish the two signs: both exponent 4. Thus the full ramified character, not its conductor, is the typed codec consumer. Character tensor exponent addition is F3 addition, not F2 XOR on the antipodal subset. The paired binary and ternary chart can be read as local parameters at two different base fields, without asserting an LLC equivalence across characteristics. It is a genuine GL1 local arithmetic representation, not a proof of new global Langlands.

If an unramified rank-d parameter at K is used, twisting by eta^t gives conductor 0 for t=0 and 4d for t!=0, and invariant dimension d or 0 respectively, by splitting into unramified Weil characters over C. Do not call that parameter the prior P11 at 2; no base change to 3 or global compatibility is assumed. For global arithmetic provenance K is the completion of Q(zeta3) at its prime over 3 and L is the completion of Q(zeta3, cube root(1-zeta3)); local calculation suffices.

### R17. Selector-SAT as exact local norm descent, not a free deterministic section

Use other worker's actual fixed NP-complete selector family. Variables m; N_m=2m+4 binom(m,2)+8 binom(m,3); selectors s_C for each non-tautological width<=3 clause; for a Boolean assignment x, q_C(x)=1 iff C falsified. Their exact geometry F_m(s)=1 iff exists x with s_C q_C(x)=0 for every C. Each q_C is a product of at most 3 false-literal bits. Represent Boolean auxiliary gate values on the repo antipodal fibre using R15. The forbidden-bit p_C=s_C q_C(x) is 0/1 (decode from antipodal convention first). Define local character eta^{p_C}, or equivalently norm obligation
    u^{p_C} in N_(L/K)(L^*).
This holds iff p_C=0 since eta(u)=zeta. Similarly at Q2 use a fixed element with chi=-1 (e.g. -1 under R2) and the quadratic norm condition. The exact same Boolean existential relation can be expressed in either arithmetic lane and jointly:
    F_m(s)=1 iff exists x such that for every C eta(u^{s_C q_C(x)})=1
           iff exists x such that for every C u^{s_C q_C(x)} is a norm.
For a satisfying witness every norm equation has explicit solution 1, since p_C=0; for a violated constraint no local solution. No unresolved local-field search, no enormous field elements: u fixed once, exponents bounded. O(N_m) small indexed obligations and constant-size gate records, with the x existential coordinates explicit. If using norm polynomials with coordinate variables for L/K, N(z0+z1 theta+z2 theta^2)=z0^3+pi z1^3+pi^2 z2^3-3pi z0 z1 z2; obtained by multiplying the three conjugates (standard cubic norm identity). It equals u^p with p=0/1 so RHS 1+(u-1)p; enforce p Boolean. This is an existential presentation over K with Boolean witness restrictions and fixed field parameters. Do not infer arbitrary local field quantifier elimination is cheap or yields a polynomial circuit. The number of norm equations is not a lower bound on decision operations. Multiplying all phase conditions into one character loses violations: 3 nontrivial eta factors cancel, and 6 violations cancel in both 2- and 3-lanes. Keep indexed labels and simultaneous constraints, as in R8/other worker's joint intersection geometry. A valid SAT decider need not produce a witness; however standard SAT self-reduction can turn a polynomial selector decider into a polynomial witness extractor by adding unit clauses one at a time. At each of m stages test one extension using the same fixed N_m encoding; if a satisfiable input, at least one polarity preserves satisfiability, and accumulated units select one assignment. Thus a polynomial-time or polynomial-size circuit decider yields a polynomially costed deterministic section of the norm relation on satisfiable inputs (and a rejection marker otherwise). Conversely a polynomially costed section plus verifier decides SAT. This is a precise decision/search transport, not a theorem that a section cannot exist. Noncanonical choices cannot be charged as independent obligations.

### R18. Unconditional linear lower bound on the actual selector target

Use R10 relative ramified translation stabilizer, now on the concrete target rather than arbitrary functions:
    S(F_m)={h in F2^N_m : Delta_h F_m constant}.
Every selector coordinate is essential: for C choose an assignment falsifying it, select exactly m unit clauses forcing that assignment. This configuration is satisfiable, but adding C (not among those units) makes it unsatisfiable. F_m is decreasing under inclusion. If h!=0 and Delta_h F_m=0 identically, fix all coordinates outside supp(h). Then the all-zero and all-one choices on supp(h) have equal output, hence monotonicity forces every intermediate choice to have equal output. Thus every coordinate in supp(h) would be inessential, contradiction.
If Delta_h F_m=1 identically, for m>=2 choose two disjoint unsatisfiable selector cores A={positive and negative units of variable 1}, B={positive and negative units of variable 2}. Choose s with all A entries 1 and all B entries of s+h equal 1 (possible because A and B disjoint). Then F_m(s)=F_m(s+h)=0, contradiction. Hence S(F_m)={0} for m>=2. For m=1, F_1=1+s_+s_- and direct check yields S=0 too.
By R10 every arbitrary shared AND circuit computing the actual selector SAT function has
    MC(F_m)>=ceil(N_m/2).
For m=2 N=8 bound 4; m=3 N=26 bound 13; m=4 N=64 bound 32. (N_3=6+12+8=26.) This strengthens the other worker's unit-clause restriction bound 2m-1 at sufficiently large m. It is a direct application of the known linear-structure lower bound, not a novel general circuit lower bound nor superpolynomial growth. The relative GL1 inertia line at each translated selector input supplies the same obstruction; moving to eta phases does not multiply the lower bound. The invariant saturates at N_m, so no LGC6 promotion.

### R19. Joint 2/3 arithmetic count boundary

For a fixed selector s, let W(s)=number of satisfying assignments (0<=W<=2^m). Exact arithmetic detection of W=0 is equivalent to SAT rejection. The fixed residue mod 6 cannot detect it: m=3, a single width-two clause leaves 6 satisfying assignments, indistinguishable from 0 mod2 and mod3. This is an actual selector-instance negative control, not random counts.
Choose a,b with 2^a 3^b>2^m. CRT implies W=0 iff W mod2^a=W mod3^b=0, because W is in the unique residue interval. Bit lengths O(m), and one can choose a,b=O(m); this is a true mixed-prime arithmetic observer (extends SixWheelCRTExact to coprime powers), not an efficient algorithm for obtaining W's residues. For a fixed x the conjunction of local conditions is a product of character projectors (1+eta^p+eta^(2p))/3, and similarly quadratic (1+chi^p)/2 with the appropriate evaluated phase. The product equals the Boolean witness indicator. Summing over all x gives W. This exact orthogonality formula permits Fourier/representation manipulations, but naive sum is exponential; divisions occur in characteristic zero, not in F3 or F2. Computing W mod prime powers may itself be difficult. Do not substitute residue sizes or character-packet dimensions for execution costs. No result on MOD_m P or #P completeness needed or claimed here.
A genuine next phase-sensitive target: a structured norm/character representation of the selector relation with a deterministic *charged* section/projection invariant that survives arbitrary gate sharing. Existing exact joint flat intersections supply incidence data but R11 and G13e prohibit charging all witnesses or regions independently. Seek an actual universal incremental bound sensitive to the width-two/three interactions, not another proof of local solvability.

### R20. Local execution and roadmap

Actually ran local Python/SymPy this continuation, script:
```python
from itertools import product, combinations
from sympy import symbols, expand, resultant
enc=lambda b:2*b-1
dec=lambda t:(t+1)//2
c=0
for a,b in product(range(2),repeat=2):
    s,t=enc(a),enc(b)
    assert (-s*t-enc(a^b))%3==0
    assert (2*(s+t+s*t-1)-enc(a&b))%3==0
    assert (-s-enc(1-a))%3==0
    assert dec(s)==a
    c+=4
for t,u in product((-1,0,1),repeat=2):
    assert (t+u)%3==(t%3+u%3)%3
    assert (t*u)%3==((t%3)*(u%3))%3
    c+=2
z,T=symbols('z T')
assert expand(resultant(z*z+z+1,T**3-1+z,z))==T**6-3*T**3+3
def clauses(m):
    return [(I,p) for k in range(1,min(3,m)+1)
            for I in combinations(range(m),k) for p in product(range(2),repeat=k)]
for m in (1,2):
    C=clauses(m); N=len(C); xs=list(product(range(2),repeat=m))
    fals=[sum(1<<j for j,(I,p) in enumerate(C)
              if tuple(x[i] for i in I)==p) for x in xs]
    f=[int(any(s&z==0 for z in fals)) for s in range(1<<N)]
    stab=[h for h in range(1<<N)
          if len({f[s]^f[s^h] for s in range(1<<N)})==1]
    assert stab==[0]
    assert all(any(f[s]!=f[s^(1<<i)] for s in range(1<<N)) for i in range(N))
w=0
for m in range(1,6):
    C=clauses(m)
    for j,(I,p) in enumerate(C):
        x=[0]*m
        for i,b in zip(I,p): x[i]=b
        units=[k for k,(J,q) in enumerate(C) if len(J)==1 and q[0]!=x[J[0]]]
        assert j not in units
        def sat(S):
            return any(all(tuple(y[i] for i in C[k][0])!=C[k][1] for k in S)
                       for y in product(range(2),repeat=m))
        assert sat(units) and not sat(units+[j]); w+=1
crt=0
for m in range(1,9):
    a=b=0
    while 2**a*3**b<=2**m:
        if a<=b:a+=1
        else:b+=1
    for k in range(2**m+1):
        assert (k%(2**a)==0 and k%(3**b)==0)==(k==0);crt+=1
assert (c,w,crt)==(34,230,518)
```
Counts: 34 finite gate/fibre arithmetic comparisons; one resultant identity; 260 translation candidates exhaustively checked (m=1,2), 10 coordinate essentiality checks in those truth tables; 230 forced-assignment witnesses across m=1..5; 518 CRT zero-test count comparisons. No local-field oracle evaluation, no numeric u chosen, no kernel/CI; general ramification proof at standard LCF authority boundary. No tests for unclaimed asymptotic statements.

| ID / phase | Exact deliverable | Producer -> consumer / status |
|---|---|---|
| R14 / A | F2/F3 and support/sign source reconciliation | actual master blobs above -> R15/16; inspected |
| R15 / A | antipodal gate translation + polynomial total gate transport both ways, no free-XOR MC equivalence | BinaryBalancedTernarySubcarrierExact, BalancedTritBitFibre, existing concrete DAG -> R17; derived |
| R16 / B | cubic Kummer local field, conductor 4, eta/eta^-1 sign-sensitive character fibre | R2, RamifiedLocalValuationSharpnessExact, local reciprocity, Base369 refinement -> R17; mathematical construction supplied at standard theorem authority; native adapter/explicit unit optional |
| R17 / B | selector existential local norm relation and polynomial decision/section equivalence | G13c/d #1548/#119, R15/16, original SAT reduction #1040/#1129/#1474 -> R7a'/b'; derived |
| R18 / C | S(F_m)=0 and MC>=ceil(N_m/2) | R8/R10, G13c selector target -> known linear lower bound, derived; no asymptotic promotion |
| R19 / C | exact CRT residue zero detection and fixed-mod6 collision on actual selector instances | SixWheelCRTExact, G13 selector incidence -> charge control; derived |
| R7a'/LGC4d / C | phase-sensitive relation consumer beyond R11/R19 and existential presentation, canonical up to valid section choice | R8/R9/R16/R17, P11 section independence, indexed hyperfabric #1291; open |
| R7b'/LGC5 / C | universal serial-safe resource bound for that consumer across all circuits (or direct uniform machines), not capped linearly/polynomially by definition | R5/R10/R18, G12a/G6, #123 charge; open |
| R7c/LGC6 / D | same invariant strict superpolynomial separation on selector SAT or canonical SAT, with polynomial reduction transport | G12b/c, R17, #1040/#1129/#1474; open |
| N6/LGC7 / E | literal Clay endpoint | conditional consumer; not inhabited |

Attribution: classical Kummer theory, local class field theory and Artin conductor filtration formula (standard authorities already recorded R2/R3; use only explicit theorem boundaries); classical SAT decision-to-search self-reduction; known linear structure MC bound R10; elementary CRT. DASHI crosswalk uses actual binary/ternary owners and local arithmetic; preserve JMD FRACTRAN/MDL attribution. No claims of field isomorphism, new LLC theorem, or P≠NP. Endpoint mathematics next, not repeat certification.

## 11. R21–R27 — constructor correction, zero mediator, six faces and ramified branch descent (24 Nov 2026)

User correction: "unused centre" is only correct for the strict binary embedding's image, NOT the ternary mediator or zero-residual geometry. This section supersedes any reading in R14–R20 that identifies those notions. Stay on Langlands; attached other-worker G14/G15 is a donor. Live #1548 ca442a027f3deca9e8d108adf207c750050dabc3, #1291 d8f05ff5fc68da3c918d50c67f00edecc1e62648, #1549 a715df92ff97af33ae373ff266022ec0848fa1e4, #120 3d59da16938b355ff039d79eaac7d1fe7d6da742. #1291 is divergent source donor, not merged master authority. No unrelated programme edits.

### R21. Inspect actual constructors and six-square owners (not names/cardinalities)

Fetched from #1291 head above: Base369.agda d3bed50a4baafd274a30ef0b1fab8301f7016c4a (tri-low, tri-mid, tri-high; indices 0,1,2; triXor identity tri-low); DASHI/Foundations/SSPTritCarrier.agda 633ac129a3d17154ec2c73305022af60cfb97fa2 (sspNegOne, sspZero, sspPosOne, explicit neutral classifier and toTriTruth/fromTriTruth); DASHI/Algebra/TritTriTruthBridge.agda d428679741681a762d11190016a668cde695a2e5 (toTriTruth neg=low, zer=mid, pos=high, toFrom/fromTo, rotTrit-equivariant-to, reflection not triXor hom at neg); DASHI/Foundations/Base369TriTruthField.agda 83c6d6c8cd4819b92cfb8d1c27eb8652f103d31d (triZero=tri-low, triOne=tri-mid, triNeg fixes low, triAdd=triXor); DASHI/Foundations/Base369MobiusTransport.agda 2d0cc4ab403cd464ac1b052bdd4fb67d8c9491a6 (hex shift +3 flips orientation preserves triadic phase).
DASHI/Foundations/BalancedTernaryAntipodalResidualCodecExact.agda 2a5069418e25572f04941591dbc83334862c012d: OrientationResidual27 centre27=unit, noncentral classes Orientation2=direct/counter, encode27/decode27 exact. 27=1+2*13, centre included, no fictitious sign on centre; coarse quotient loses information only if residual discarded.
DASHI/Codec/TriadicMaskSignFactorization.agda db62f5518adc7fd3815c56ead5e20a8071db4b5a: FactorizedTrit inactive | active Sign; inactive decodes zer, not missing observation.
DASHI/Core/GovernedIndexedResidualCubeExact.agda 42b70ebb7376813076934f2245ce6011b76f10c8: eight typed vertices A B C D E F H I, 12 actual maps, Faces Rxy0/Rxz0/Ryz0/Rxy1/Rxz1/Ryz1, ExactFaces distinct from ResidualFaces, xyz-zyx and five other endpoint comparisons. Residual alone does not imply equality.
DASHI/Codec/IndexedCubeMaskSignInstanceExact.agda 7a948ba3700bfd43c50fa08de3e4ee8bf2895a95: x partitions WITH suffix, y rotates, z encodes; codecExactFaces uses partitionRotation, partitionCodec, codecRotation, splitCodecRotation; terminalReopen decodes joins to original rotated state. Exact faces have unit extra defect because suffix/sign remain in carriers, not because erased. IndexedCubeMarkedAffine9Exact uses explicit balanced add3/mul3 (zer identity/absorber) and recharted six face witnesses; chart marks material.
Fetched from master: DASHI/Foundations/Base369Ternary27HypervoxelFabricGeometryExact.agda eabb5876f391abc285d042a789ab4a29fc6b82b0: actual origin=(sspZero,sspZero,sspZero), TritGridStep negToZero/zeroToNeg/zeroToPos/posToZero, noDirectNegToPos/noDirectPosToNeg, six outer Face6; DASHI/Moonshine/Base369PeriodicTernaryTorusPathRestrictionBidiExact.agda a7bb055c139503da711157e897bf17b695130452: pathStepToCyclic, cyclicWrapIsNotPathStep, same nine-coordinate carrier different adjacency. This is the actual mediator, not the raw cyclic code or unrelated Lacan comparison role. The #1291 living roadmap blob a40721dde3fa561f82abe80c5312363e18aee158 explicitly warns against shifted residue path and preserves zero, winding, residual, source and physical time. H07 native ambient overlap and analytic operator faces still open; no import of physical authority.

### R22. Balanced vs field chart — repair the actual commuting operations

For t in {-1,0,+1}, SSP and Trit constructors agree under their bijection; Base369 chart j(t)=t+1 mod3. Therefore balanced zer maps tri-mid, NOT the field triZero=tri-low. The transported BALANCED field operations in raw index coordinates are:
    j(t+u)=j(t)+j(u)-1 mod3,
    j(tu)=(j(t)-1)(j(u)-1)+1 mod3,
    j(-t)=2-j(t) mod3.
The existing triXor instead adds raw indices and has identity low; the balanced reflection is not raw triNeg (indeed source has reflection-not-xor-hom). Do not reinterpret existing source operations. The correct Langlands character chart rho_bal(t)=eta^t, rho_index(j)=eta^(j-1), commutes with toTriTruth and balanced inversion. It sends the mediator to the trivial representation (an actual one-dimensional line, not the zero vector space), endpoints to inverse nontrivial characters. On raw triXor use eta^j if a homomorphism is desired; that is a DISTINCT choice with different unit and neutral semantics. In the balanced chart tensor composition has translated index j+j'-1. No unital ring map F2->F3 or equivalence of local fields asserted.

For the original P3 path -1->0->+1, each successive relative cubic character is eta, product eta^2. Direct periodic +1 to -1 wrap is allowed only in C3 graph. Integer displacement -2 and +1 have the same cubic phase; likewise +2 and -1. Retaining ordered path/incidence and integer lift/winding distinguishes direct cyclic wrap from actual two-step mediated edge. The involution t->-t preserves P3 and fixes its middle. Cyclic translation does not preserve P3 adjacency; use transported graph if changing chart. The character is a representation of phase, not an intrinsic graph-length lower bound. This is the zero-aware path/periodic distinction from existing source.

### R23. Relative ramified lines with zero residual — exact binary pair and branch mediator

For two binary values a,b, use the INTEGER signed difference d=b-a in {-1,0,+1}, rather than XOR alone or the antipodal endpoint embedding. Map d into the SSP balanced constructor, then cubic local character eta^d. Binary relative character is chi^(d mod2). The support is d!=0, sign of nonzero d determines direction, and d=0 is a real equal-value state. The exact lossless pair codec is:
    d=-1: (a,b)=(1,0), unique;
    d= 0: (a,b)=(0,0) OR (1,1), retain a bit;
    d=+1: (a,b)=(0,1), unique.
This is a dependent residual on the ZERO fibre of the DIFFERENCE map, distinct from OrientationResidual27 (unit at centre, sign on noncentral antipodal classes) and FactorizedTrit (no sign at zero). The latter codecs remain exact on their carriers. Here the extra bit is common endpoint VALUE, not a fake orientation at zero. Algebraically pair ~= Sigma d Residual(d), Residual(0)=Bool, Residual(+/-1)=unit, 4=1+2+1. Recovery b=a+d with legal a, or piecewise decoding. If both endpoint values are known, cubic relative line over W_K is Hom_C(eta^a,eta^b), and is eta^d. This uses 0/1 exponent for Boolean *value* lines, NOT antipodal exponent e(b); if using eta^{e(b)} relative exponent is 2d=-d mod3, so invert orientation or use the typed chart conversion. Never mix the two.

For actual selector SAT let a,b be truth of whether prefix assignment extended by next bit 0 or 1 admits any full satisfying witness (R17 local norm relation). Then d=-1 = left-only, d=+1 = right-only, d=0 = both viable OR neither viable. Both have trivial relative character and norm residue, different parent truth. Keep the common viability bit r when d=0. Parent OR is |d|+(1-|d|)r (r=0 by convention on nonzero d); equivalently a+b-ab. This gives an exact three-way mediator and dependent reconstruction of the two-branch feasibility state. A polynomial-cost selector decider yields these branch bits by unit self-reduction; a polynomial section yields decider. The character alone cannot provide them. Examples on one-variable selector: no selected clauses -> both viable; contradictory units -> neither; one selected unit -> one branch. These are actual selector instances, not invented hard inputs. Thus the zero residual is critical to arithmetic descent. Cannot independently pay for each branch or count zeros as solved; computing joint feasibility bits is the target. Source-specific zero mediator may be unresolved/neutral in partial assignment chart; it is not a third Boolean witness. The two-branch feasible set must be retained until actual descent resolves it.

### R24. Six genuine commuting squares on signed ramified edge transport

Take actual output f on a 3-dimensional Boolean selector subcube (three distinct flips, all other selectors fixed). Vertices x in {0,1}^3 with output f(x) in {0,1}. Directed edge e_i(x)=f(x+ei)-f(x) for x_i=0. Along edge use transport (anchor a, signed d) -> a+d; edge character eta^d and chi^(d mod2), with admissibility a+d in {0,1}. For each of six oriented square faces (three pairs of axes, two values of remaining axis):
    e_i(x)+e_j(x+ei)=e_j(x)+e_i(x+ej)=f(x+ei+ej)-f(x).
This is exact integer equality, hence equality of the relative cubic and quadratic line compositions, compatible with the R22 codec and R23 anchor residual. It gives six source-square witnesses of the shape of GovernedIndexedResidualCubeExact, NOT a native Agda instantiation yet. Six permutations of axis order all recover same final output from same anchor. Conversely, for arbitrary signed edge labels, all six integer face identities imply path independence by adjacent swaps, and uniquely reconstruct all eight vertex values from anchor by sums; to be a Boolean-labelled cube additionally require all recovered values in {0,1}. Conversely these conditions suffice. Merely equal characters modulo3 (or even modulo6) do not imply arbitrary integer lifts glue without bounds. These six faces are binary selector source cube faces (eight vertices); distinguish original P3^3 six OUTER faces (27 sites); no assertion they are identical cell complexes. Codec cube x=partition, y=rotate, z=encode is a THIRD diagram whose actual six proofs are reused as proof shape, not replaced by selector axis flips. For a native weld use these typed distinctions and attach original suffix/anchor to each vertex; no residual-free promotion.

Important admissibility calculation: at a common source vertex, three signed first differences all lie in {0,+1} when f(x)=0 or {0,-1} when f(x)=1. Their union has 2^3+2^3-1=15 possible triples (12 mixed-sign triples inadmissible), not 27. All-zero gradient has two common-source output possibilities. With anchor 16 possible local source stars. On all eight cube vertices there are 256 Boolean labellings and exactly 255 distinct full edge gradients (two constant labellings coincide, all others determine anchor since some nonzero edge specifies endpoints). This is the actual joint source-admissibility restriction; do NOT populate entire F3^3, count 27 as independent computational directions, or erase common-source identity. Original ternary 27 geometry is valid on its own typed carrier, but binary derivative image is a proper governed subset. This is the same reason source-specific overlaps matter in #1291 H07.

### R25. Higher signed residuals and exact prime-power repair, attached to G14/G15

At order r>=1 the signed integer mixed derivative along r distinct Boolean flip axes is an alternating sum of 2^r output values; absolute bound 2^(r-1). First differences are actual trits, higher differences need NOT be trits. Example r=4, f=indicator(Hamming weight=2), signed derivative at 0 is +6. Both binary parity and cubic phase are trivial, although integer residual is nonzero. Thus even the paired 2/3 phase chart cannot replace higher signed residuals. For order r choose coprime powers M=2^a*3^b>2^r; signed CRT reconstruction in [-2^(r-1),2^(r-1)] is unique. This is arithmetic transport of the signed jet with O(r) bits per coordinate, not free computation or a cost bound. For first differences the cubic phase determines d exactly and parity is its support; for higher derivatives carry/residual is essential. The relevant producer is SixWheelCRTExact plus R19, with proper integer signed reconstruction.

Attached other worker G14 full-degree proof (orbit parity) improves R18 lower bound to MC(F_m)>=N_m-1, using known degree bound. Both width-two and width-three have full degree and exponential boundary jet rank yet 2-SAT polynomial. Adopt their result as source donor, not our new proof. On their maximal assignment flat and orders within admitted isolation radius, Boolean mixed derivatives are products of q_C(x); integer signed derivatives are (-1)^r times those products (local restriction of monotone decreasing flat indicator). Thus cubic signed jet line is eta^{(-1)^r product q_C(x)}, and trivial on zero derivative; branch anchor/jet lift distinguishes cases as above. Their exponential rank is explicitly not an unrestricted resource lower bound. Preserve incidence and phase signs, but do not count every nonzero derivative or 27 pattern as a separate paid gate. Width-three-specific universal arithmetic descent obstruction still open.

### R26. Actual local finite execution (no CI or native kernel)

Executed local Python exact integer tests, with SymPy available (no symbolic theorem certification claimed). 9 shifted chart pair comparisons, 8 signed endpoint triples, 1536/1536 integer square identities (256 binary cube labellings x6 faces), 1536/1536 monotone endpoint paths, 255 gradient patterns and 15 common-source patterns exactly, 518 signed CRT reconstruction comparisons at r=1..8, explicit order-four +6 collision. Reproduction:
```python
from itertools import product, permutations, combinations
T=(-1,0,1)
j=lambda t:(t+1)%3
bal=lambda r:((r+1)%3)-1
for a,b in product(T,repeat=2):
    assert j(bal(a+b))==(j(a)+j(b)-1)%3
    assert j(-a)==(2-j(a))%3
    assert j(bal(a*b))==((j(a)-1)*(j(b)-1)+1)%3
for a,b,c in product(range(2),repeat=3):
    assert b-a+c-b==c-a and (b-a)%2==(a^b)
    assert ((b-a)%3==0)==(a==b) and a+(b-a)==b
vertices=list(product(range(2),repeat=3)); faces=paths=0
gradients=set(); base_grad=set()
for f in product(range(2),repeat=8):
    F=dict(zip(vertices,f))
    def step(x,i): return tuple(v+(j==i) for j,v in enumerate(x))
    E={(x,i):F[step(x,i)]-F[x] for x in vertices for i in range(3) if x[i]==0}
    gradients.add(tuple(E.values()))
    base_grad.add(tuple(E[((0,0,0),i)] for i in range(3)))
    for i,j in combinations(range(3),2):
        k=3-i-j
        for b in range(2):
            x=tuple(b if t==k else 0 for t in range(3))
            assert E[x,i]+E[step(x,i),j]==E[x,j]+E[step(x,j),i]
            faces+=1
    for p in permutations(range(3)):
        x=(0,0,0);y=F[x]
        for i in p:y+=E[x,i];x=step(x,i)
        assert y==F[x];paths+=1
assert (faces,paths,len(gradients),len(base_grad))==(1536,1536,255,15)
v=list(product(range(2),repeat=4))
assert sum((-1)**(4-sum(x))*int(sum(x)==2) for x in v)==6
n=0
for r in range(1,9):
    B=2**(r-1);a=b=0
    while 2**a*3**b<=2*B:
        if a<=b:a+=1
        else:b+=1
    M=2**a*3**b
    for x in range(-B,B+1):
        y=(x%(2**a)*3**b*pow(3**b,-1,2**a)+x%(3**b)*2**a*pow(2**a,-1,3**b))%M
        if y>M//2:y-=M
        assert y==x;n+=1
assert n==518
```
NOTE: variable j in loop shadows chart function after chart comparisons; no later chart invocation. Actual output matched all counts. No local field evaluation or CI. General proofs above are independent of finite run.

### R27. Corrected phases, deliverables and original consumers

| Gate / phase | Exact deliverable | Status / producers -> consumers |
|---|---|---|
| R21 / A | constructor and original six-face source reconciliation | inspected; SSPTritCarrier, TritTriTruthBridge, Base369TriTruthField, codec cube, #1291 -> R22–24 |
| R22 / A | balanced-index shifted character chart, nonwrapping/periodic distinction | derived; source chart and P3/C3 restriction -> R23 |
| R23 / B | signed binary difference dependent zero residual, norm/branch feasibility codec | derived; R16 eta, R17 selector norm, FactorsThrough and residual codec (distinct typed fibre) -> R24/R7a' |
| R24 / B | all six selector face laws plus converse admissibility and anchor reconstruction | derived; H05 exact face shape, R23 -> labelled joint arithmetic data; native instantiation open, no H07 ambient promotion |
| R25 / C | higher signed jet CRT carry, G14/G15 crosswalk | derived / other-worker results credited; N_m-1 bound still linear; 2SAT negative control |
| R7a' / LGC4d / C | joint mediator-aware norm descent consumer of actual width-three family that preserves viable/dead zero residuals and overlaps | exact representation/branch gluing supplied; cost-sensitive invariant open |
| R7b' / LGC5 / C | universal serial-safe bound for THAT consumer under all shared nonlinear extensions or actual machine transitions | OPEN; no independent branch/jet count, retain both parallel and serial chords G13 |
| R7c / LGC6 / D | strict superpolynomial separation on actual selector SAT | OPEN; must distinguish 2SAT from 3SAT despite same full-degree/jet-rank phenomena |
| LGC7/N6 / E | Clay endpoint transport via standard cost model | existing conditional consumer, no unconditional theorem |

Next mathematical tranche: investigate mediator-aware joint feasibility across clause overlaps (not repeat constructor tests). Show which *source-specific* relations enforce nonlocal choices even after arbitrary earlier computational sharing, and prove a valid global charge or find a counterexample. The exact signed edge gluing and branch residual transport do not solve witness selection. Stay on arithmetic Langlands/norm descent and coordinate with #1548/#119 on G12; no Monster/RH/YM prerequisite. Attribution: original DASHI constructors, #1291 H05, JMD source boundary as in earlier sections; standard character theory and integer CRT; no priority claim for elementary difference codec/cube facts.

## 12. R28–R35 — nonabelian ramified descent, signed mediator gluing and monotone representation lower bound (2026-11-24)

Stay on Langlands. Both current user attachments read from actual mounted files. Adopt the other worker's G16–G19 as scoped donors: median/pairwise hull and no existential 2-CNF for a 3-clause, monotone selector projection and superpolynomial lower bound, complete propagation obstruction, nonmonotone shortcut no-go. Live #1548 a33655646b928536a02578623cc81b491d53d28d and #119 ae18da2457eb01d7585347b7f6c39f13c2b9683c agree with supplied handoff. #1549 679397137e12cfb48174eb41d205354a97e00a03 / #120 fa917cfc5c58cc6f40e3f1168ee80b935b56cc01 / #1291 d8f05ff5fc68da3c918d50c67f00edecc1e62648. No changes to other worker's branches. G16 applies to Boolean bijunctive relations, not arbitrary binary encodings; the full inhabited ternary witness including neutral selection is essential. R21–R27 zero/residual distinction retained.

### R28. Actual reused C2/C3/S3 and descent source owners

Inspected master source bodies:
- DASHI/ComputerScience/BalancedTernaryC2C3DihedralCodecBridgeExact.agda ae1704bb5e880c46c97f1e2db3566fcf020087f6: antipodeOrderTwo, cycleOrderThree, antipodeConjugatesCycleToInverse, binaryPresentationIntertwinesAntipode, binarySupportForgetsOnlyOrientation, qutritPresentationIntertwinesCycle.
- DASHI/Foundations/TernaryPermutationS3LawsExact.agda baeed264a0a4811f3cad463f101eb6c27f7928b6: literal permutation multiplication, applyComposition, nonCommutativeWitness.
- DASHI/Foundations/PolynomialC3S3ReflectionParityFourierExact.agda 9a7a180555dad4a042b2978d576a66814b5fc15c: evenAverage, oddHalfDifference, reconstructPositive/Negative, decodeAfterEncodeAt, exact 11=7+4 chart over F3. The existing chart is reflection diagonalization, not C3 averaging in characteristic 3.
- DASHI/Foundations/PolynomialC3S3ReflectionParityLinearExact.agda e888873013b05d0122c5f7ecb8b41d649f1bcae9: evenAverageAdditive, oddHalfDifferenceAdditive, decodeAdditiveAt.
- Docs/papers/PolynomialMonodromyTernaryQuaternionBridge.md ca5a81f465a54bcdf4f791871c9b9e2e5b1559dc: distinct finite permutations, cyclic subgroups, signed codec, monodromy authorities; do not promote finite monodromy to arbitrary field/Galois proof.
- scripts/check_polynomial_c3_s3_reynolds_character_exact.py ade7974a862e2cbffb85572f1c1ec5419d7402b2; scripts/check_polynomial_s3_c2_reflection_fourier_20261029.py 824caee0b79c9b5c50c76d52ae1620d337fb8381: rational C3/S3 averaging, reflection parity source checks; no new execution of those scripts.
- DASHI/Mathematics/Complexity/SATDecisionToWitnessSelfReductionExact.agda a0371c7d8243f7c22c57f7255ab79c63baf7d4b5: recoverWitness conditional on exact decision oracle and satisfiableSplits. R17/G15 decision-search reuse.
- DASHI/Mathematics/Complexity/Karp21CliqueSetPackingExact.agda ddffdd6e4276c263f3e96be129598c502005a3b2: cliqueToPacking/packingToClique semantic equivalence, not alone an executable polynomial encoding.
- DASHI/Analysis/RHGRHDirichletCubicHeckeLocalCorrespondenceExact.agda 2d82566d2de56baa789aad3b6b027ed7721ebf26: separates quadratic conductor/discriminant from cubic local factors; does not construct global Groessencharacter. We do not reopen RH or equate these cubic characters.

### R29. A genuinely nonabelian local extension; correction of descent scope of R16

R16 used K=Q3(zeta), pi=1-zeta, L=K(cuberoot pi). Valid cyclic cubic extension of K, but NOT Galois over F=Q3. For conjugation tau(zeta)=zeta^-1, tau(pi)/pi=1+zeta=-zeta^2. If Kummer lines [tau(pi)] and [pi] agree in K*/K*^3, valuation mod 3 forces the same power (not power 2), and -zeta^2 would be a cube. This would give a primitive ninth root in K, impossible: Phi_9(X+1) is Eisenstein of degree 6 over F. Thus do not assert eta from R16 is conjugate-self-dual or that its induction has S3 image. R16 arithmetic stays valid over K; new source-selected character eta' below replaces it for THIS nonabelian descent only.

Take M=K(theta), theta^3=3. v_K(3)=2, so 3 is not a cube. M/K cyclic cubic and totally ramified (valuation of theta is 2/3 relative to K). M is splitting field over F of X^3-3; degree 6, with sigma(theta)=zeta theta fixing K, tau(theta)=theta and tau(zeta)=zeta^-1. Thus sigma^3=tau^2=1 and tau sigma tau=sigma^-1, actual S3. This realizes the existing dihedral donor on a genuine arithmetic Galois group. Uniformizer w=theta^2/pi has normalized M-valuation 4-3=1; w^3=zeta*pi=zeta-zeta^2 and w^6=-3. The polynomial X^6+3 is Eisenstein over F, so O_M=O_F[w]. For sigma and sigma^2, v_M(sigma(w)-w)=v_M(zeta^2-1)+1=4. For any reflection, the ratio g(w)/w reduces to -1 modulo w (tau(w)/w=-zeta), so difference valuation 1. Lower filtration G0=S3, G1=G2=G3=C3, G4=1. Over K the cubic character eta' has conductor exponent 4; tau exchanges eta' and eta'^-1. Via local reciprocity eta' is a character of K* with norm kernel N_(M/K)M*. Choose fixed unit u' with eta'(u')=zeta. R17 norm relation can use this new character/extension without changing Boolean semantics. New norm polynomial is a^3+3b^3+9c^3-9abc, not the pi-radicand norm. No numerical u' claimed.

### R30. Actual GL2 parameter with a genuine fixed mediator and signed descent failure

Let U=Ind_(W_K)^(W_F) eta' be the irreducible standard 2D representation of the actual S3 quotient (N=0). Restriction U|W_K=eta' direct_sum eta'^-1; induction of the inverse yields the same U. Let epsilon be the quadratic sign character of S3/C3. Artin formula a_F(rho)=sum_i [G_i:G_0] in the denominator times codim rho^(G_i) gives a_F(epsilon)=1 and a_F(U)=2+3*(1/2)*2=5. Hence standard rank-two LLC attaches U to a genuine irreducible supercuspidal GL2(F) representation of conductor exponent 5; Euler factor 1. Trivial induced parameter Ind 1=1 direct_sum epsilon has conductor 1 and inverse Euler factor 1-T. This is standard LLC authority, not a new LLC theorem; operations below on Weil parameters do not mean tensor products of automorphic GL2 representations within the same group.

Three-state module P=1 direct_sum U is the permutation representation on three roots. Restriction to W_K splits into one line per cubic character t=-1,0,+1. Mark sigma and its eigenlines using E_t=(1/3)sum_{j=0}^2 zeta^(-tj) rho(sigma)^j; E_t E_s=delta_(t,s) E_t, sum E_t=I, tau E_t tau^-1=E_-t. Coefficients characteristic zero, NOT averaging in F3. The true trivial line E_0 P is inhabited rank one; in spatial root-label basis it is span(1,1,1) and E_0=J/3, not the spatial basis vector labelled 0. The balanced spatial mediator is fixed under reflection, not under the full cycle. Fourier zero and spatial zero must be distinguished and transported by the actual Fourier chart, retaining the label. Reflection preserves the P3 path; full S3 action on roots does not preserve nonwrapping incidence. Do not infer graph equivalence.

For a literal truth mask (a_-,a_0,a_+) in {0,1}^3, define actual endomorphism A=sum a_t E_t. This is W_K-equivariant, but W_F-equivariant iff a_-=a_+, by Schur on 1+U or direct conjugation. Therefore full unmarked descent cannot distinguish arbitrary asymmetric clause-witness masks. This is a precise source-specific obstruction to forgetting the orientation; it does not obstruct every algorithm. Define e=(a_++a_-)/2, o=(a_+-a_-)/2. Then
    A_even=a_0 E_0+e(E_++E_-),
    A_odd=o(E_+-E_-),
    A=A_even+A_odd.
The odd line in End(P) transforms by epsilon under W_F conjugation, so the orientation residual is an actual sign subrepresentation (conductor 1), not an invented bit. Even mask e and mediator a_0, with signed odd o, reconstruct exactly. Even quotient has 2*3=6 classes; endpoint count 1 carries one binary orientation residual, count 0 or 2 has unit residual. Total 8 masks. This matches the existing reflection parity chart's proof shape, with different coefficient field, actual three-state module, and actual ramified action. On a fixed clause use G16 witness t=-1,0,+1 with l_t(x)=1 requirement; a_t=l_t(x), or a_t=1 if clause absent. Mediator t=0 is the actual middle literal, not missing witness or always-satisfied constraint. Existential projection is trace(A)>0. Under simultaneous reflection of literal labels and module, transport A covariantly. If source labels fixed, cannot simply claim descended A is equivariant. Marked fibres and shared overlap from R23/R24 must be retained.

### R31. Exact odd-residual gluing and shortcut on a shared witness

For masks A,B on the SAME marked witness line system, common feasible witness count is
    Tr(AB)=a_0 b_0+2(e_A e_B+o_A o_B).
Discarding odd residual and multiplying averaged masks yields a wrong answer, e.g. both masks allow + only versus one allows + only and other - only: same even data but intersection counts 1 and 0. This is an actual failure of FactorsThrough for independent reflection quotients on a shared witness. It is not an assertion all local clause selectors share one witness; original clause witness variables are distinct, original assignment variables can be shared. Preserve which variable/coordinate each factor refers to.

The precise reconstruction/gluing law is
    (e,o)*(f,p)=(ef+op, ep+of);
    a_0 multiplies independently.
This is the ordinary coordinatewise product in the original two endpoints under the even/odd chart. The odd-odd term is essential: epsilon tensor epsilon=1. For k masks on one witness, product has 2^(k-1) formal even-parity terms if expanded, yet two even/odd accumulators and one mediator scalar compute the same result in O(k) fixed-size operations (or simply multiply original three diagonal entries). Hence number of odd terms is NOT paid cost. This is an explicit nonmonotone/signed arithmetic shortcut on the actual local residual structure. No global SAT algorithm follows; different witness variables coupled by constraints require actual indexed contraction/selection, not this single shared-witness product. G16 median obstruction supplies the failure of existential Boolean 2CNF, not a lower bound on arbitrary signed network contractions. R24 six-face gluing remains valid with ordered marked endpoints; recharting alone cannot remove an actual overlap failure.

### R32. Superpolynomial lower bound in a defined positive representation calculus

Verify external theorem separately: Cavalar–Kumar–Rossman, *Monotone Circuit Lower Bounds from Robust Sunflowers*, DOI 10.1007/s00453-022-01000-3, https://pmc.ncbi.nlm.nih.gov/articles/PMC9705498/ and https://arxiv.org/abs/2012.03883, n^Omega(k) for k<=n^(1/3-o(1)). Other worker G17 uses monotone projection CLIQUE_(n,k) -> selector absence G_(M,3), M=O(kn), N=Theta(M^3); k=floor(n^1/4) gives 2^Omega(N^(1/15) log N) on projected lengths. This is a valid restricted-model transport (standard result plus supplied explicit projection), not a new proof of CKR.

Define a concrete characteristic-zero positive Weil representation DAG model: fixed finite quotient groups (e.g. C2, C3, S3 and their fixed products) and a fixed finite list of their irreducible types; input absence bit t_C represented by either zero object or a fixed actual representation (monotone inclusion), fixed constants; operations direct sum, tensor product, dual, fixed induction/restriction, fixed isotypic projection, invariant space, and dimensions of equivariant Hom between actual semisimple reps, using the multiplicity signature. All these operations have nonnegative integer structure coefficients (Hom dimension bilinear dot product); no arbitrary kernel/cokernel of a varying map, subtraction of virtual characters, phase comparison, arbitrary Fourier coordinate gates, data-dependent type search, or external SAT oracle. Output nonzero multiplicity/support test. More generally any fixed-arity operation whose output multiplicities are explicitly nonnegative polynomial combinations of input multiplicities, with charged structure coefficients/monomial occurrences, fits. Support sigma(a)=1 iff a>0 satisfies sigma(a+b)=sigma(a) OR sigma(b), sigma(ab)=sigma(a) AND sigma(b). Thus every such representation DAG translates to a monotone Boolean DAG of O(size) when type tables fixed (or O(total charged monomial occurrences) for explicitly growing types), preserving all fan-out and sharing. Proof for S3 tensor: (a tensor b)_k=sum_(i,j) N_ij^k a_i b_j, hence support is OR over fixed N_ij^k>0 of support(a_i) AND support(b_j). S3 fusion U tensor U=1 direct_sum epsilon direct_sum U, epsilon tensor U=U. Ind/restriction matrices are nonnegative. Character-valued signs of traces are not multiplicity signs: the proof is in actual multiplicity semiring.

Therefore positive fixed-type representation computation of G_(M,3) requires
    size >= 2^Omega(N^(1/15) log N).
This is an actual superpolynomial lower bound in the defined representation resource model, via G17 and support transport. If using symbolic giant groups/types, arbitrary representations with implicit exponential support, or arbitrary maps, separately prove and charge coverage; theorem does not cover them. A fortiori nonnegative arithmetic DAG that computes exact witness count W(t) (or any nonnegative value nonzero iff selector SAT) requires that many operations. The local norm relation admits positive witness-count presentation: for a fixed assignment x form tensor product over clauses of 1 when x satisfies C, and t_C copies of 1 otherwise; take direct sum over all x. Dimension W(t), actual trivial representation. Can alternatively mark local ternary literal-witness masks, whose nonzero intersection enforces the relation; do not charge each summand independently without the support simulation theorem. This expression has exponential witness enumeration; lower bound says no polynomial positive DAG compression in this model. Width-two monotone Boolean reachability admits polynomial support DAG by G17; AND/OR use tensor/direct sum on trivial types, interpreting output only by support. This upper is in symbolic support-operation cost, not a claim polynomial explicit dimensions or bit sizes. No lower bound for unrestricted arithmetic circuits or all Langlands constructions.

### R33. Exact nonmonotone escape within actual equivariant linear algebra

It is not enough to demand actual representations, exact intertwiners, honest diagrams or zero-aware residuals: a genuine equivariant cokernel already realizes NOT with constant cost. Represent bit b by the marked subspace B_b=b*C inside the fixed trivial Weil line C. Then C/B_b has dimension 1-b. Both inclusion and quotient are actual equivariant maps; no virtual representations or negative-dimensional objects. Preserve ambient basis and use canonical coordinate quotient (zero or C). AND is tensor product of the marked subspaces inside C tensor C=C; NOT is the quotient just described, OR by De Morgan. Every standard Boolean circuit lifts gate-by-gate to bounded-dimension, polynomially costed actual equivariant operations (copy/reference fan-out allowed). Conversely the restricted Boolean-valued tensor/quotient gate fragment decodes to the original Boolean circuit; this is not a reverse compiler for arbitrary rank/kernel computations on succinct huge representations. Hence exact genuine Galois/Langlands-compatible representation computations need NOT be monotone even when all objects and maps honest. Example B_0->C has cokernel C, B_1->C has cokernel 0. A positive support gate cannot reproduce that reversal. A fixed-type circuit with positive-support gates can use arbitrary internal phase conventions but cannot evade R32 as long as every output support factors through input supports monotonically and cheaply. If such factorization fails, keep the extra residual, with actual charged operations. This establishes a sharp restricted frontier: positive compression obstructed, actual equivariant quotient escape available, proving all efficient unrestricted paths fail still G12a/R7b' open. Do NOT claim number of NOT/quotient operations must itself be superpolynomial, or that forbidding signs on input suffices. The target is joint cost in the actual unrestricted source, not requiring nonmonotone computation to behave monotonically.

### R34. Actual local exact execution and standard theorem authority

Executed local Python/SymPy in current turn, no CI or native kernel. Algebraic cyclotomic identities including shifted Phi9, permutation relations, 36 group products, 9 character projector products, 6 reflection/eigen equations, 8 literal masks (6 even classes), 729 pairs of nonnegative multiplicity triples (sum and fusion support transport), explicit shared witness collision, 4096 four-mask exact even/odd products, 4 Boolean quotient/AND/OR input pairs. These tests check finite algebra, not local field oracle evaluations or general CKR/LLC theorems. General proofs above independent of finite results. Reproduction (compact equivalent checks):
```python
from itertools import product
from fractions import Fraction as F
import sympy as S
from sympy import Matrix, eye, zeros
z,w=S.symbols('z w')
red=lambda p:S.rem(S.expand(p),z*z+z+1,z)
for p in [(1-z)**2+3*z,(z*(1-z))**2+3,
          (z*(1-z))*(1-z)**3-9,(1-z)*(1+z)-(1-z*z)]:
    assert red(p)==0
assert S.expand(S.cyclotomic_poly(9,z).subs(z,w+1))==w**6+6*w**5+15*w**4+21*w**3+18*w**2+9*w+3
T=range(3); P=lambda f:Matrix(3,3,lambda i,j:int(i==f(j)))
R=P(lambda j:(j+1)%3); J=P(lambda j:(-j)%3)
assert R**3==eye(3) and J**2==eye(3) and J*R*J==R**2
G=[R**i*J**j for i,j in product(T,range(2))]
assert len({tuple(g) for g in G})==6
assert all(a*b in G for a,b in product(G,repeat=2))
E=[sum((z**((-k*i)%3)*R**i for i in T),zeros(3))/3 for k in T]
rm=lambda m:m.applyfunc(red)
for i,j in product(T,repeat=2):
    assert rm(E[i]*E[j]-(E[i] if i==j else zeros(3)))==zeros(3)
assert rm(sum(E,zeros(3))-eye(3))==zeros(3)
for i in T:
    assert rm(J*E[i]*J-E[-i%3])==zeros(3)
    assert rm(R*E[i]-z**i*E[i])==zeros(3)
assert E[0]==S.ones(3)/3 and E[0]!=S.diag(1,0,0)
masks=list(product(range(2),repeat=3)); classes=set()
for a,b,c in masks:
    A=rm(a*E[0]+b*E[1]+c*E[2]); even=rm((A+J*A*J)/2); odd=rm((A-J*A*J)/2)
    assert rm(even+odd-A)==zeros(3)
    assert (rm(J*A*J-A)==zeros(3))==(b==c)
    assert rm(even-a*E[0]-F(b+c,2)*(E[1]+E[2]))==zeros(3)
    assert rm(odd-F(b-c,2)*(E[1]-E[2]))==zeros(3)
    classes.add((a,b+c))
assert len(classes)==6
p=(0,1,0);q=(0,0,1)
assert (p[0],p[1]+p[2])==(q[0],q[1]+q[2])
assert any(a*b for a,b in zip(p,p)) and not any(a*b for a,b in zip(p,q))
chars=[(1,1,1),(1,-1,1),(2,0,-1)]; weights=(1,3,2)
Fus=[[[sum(weights[t]*chars[i][t]*chars[j][t]*chars[k][t] for t in T)//6 for k in T] for j in T] for i in T]
assert Fus[2][2]==[1,1,1] and Fus[1][2]==[0,0,1]
vs=list(product(range(3),repeat=3))
for a,b in product(vs,repeat=2):
    out=[sum(a[i]*b[j]*Fus[i][j][k] for i,j in product(T,repeat=2)) for k in T]
    supp=[any(a[i]>0 and b[j]>0 and Fus[i][j][k]>0 for i,j in product(T,repeat=2)) for k in T]
    assert [x>0 for x in out]==supp
    assert [x+y>0 for x,y in zip(a,b)]==[x>0 or y>0 for x,y in zip(a,b)]
for a,b in product(range(2),repeat=2):
    assert a*b==int(a and b) and 1-a==int(not a) and 1-(1-a)*(1-b)==int(a or b)
for ms in product(masks,repeat=4):
    c,e,o=1,F(1),F(0); direct=[1,1,1]
    for a,b,d in ms:
        u,v=F(b+d,2),F(b-d,2)
        c,e,o=c*a,e*u+o*v,e*v+o*u
        direct=[x*y for x,y in zip(direct,(a,b,d))]
        assert (c,e+o,e-o)==tuple(direct)
    assert c+2*e==sum(direct)
```
Sources: Serre, *Local Fields*, Artin conductor filtration (LMFDB https://www.lmfdb.org/knowledge/show/artin.conductor); standard GL2 LLC irreducible Weil parameter/supercuspidal and conductor compatibility https://docs.magma-maths.org/ModularArithmeticGeometry/RepresentationsOfLocalFields/introduction.html ; CKR DOI above. Local Kummer and group/representation formulas are standard theory with explicit elementary derivations here. Preserve original DASHI finite-source owners, JMD attribution and other worker G16–G19. No claim of priority for local S3 example, Reynolds decomposition, support semiring, or basic quotient gate.

### R35. Exact remaining P0 roadmap / producers -> consumers

| Gate / phase | Deliverable | Status |
|---|---|---|
| R28 / A | Source C2/C3/S3, reflection Fourier, witness and Karp reconciliation | inspected; source owners above -> R29–33 |
| R29 / B | Actual S3 local Galois extension and correct R16 descent boundary, conductor filtration | derived; R16, ramification donor, dihedral source -> R30 |
| R30 / B | GL2 standard parameter, marked mediator, even/odd descent and conductor | derived at standard LLC authority; #585/#596 section independence, reflection parity -> R31 |
| R31 / B–C | Signed joint mask reconstruction, exact O(k) shared-witness gluing | derived; R23/R24, G16 -> R7a'; negative control on independent sign charges |
| R32 / C | Positive representation support simulation and superpoly selector lower bound | derived restricted theorem via G17/CKR; fixed type/explicit coefficient cost, arbitrary shared DAG |
| R33 / C | Actual bounded-dimension equivariant quotient Boolean compiler | derived; all gates, shared source, no free general rank; no generic monotone transport |
| R7a' / LGC4d / C | Source-marked arithmetic relation sensitive to width-three joint constraints beyond positive support | local descent and signed gluing supplied; global cost-sensitive consumer still open |
| R7b' / LGC5 / C | Universal charged global invariant or obstruction under signed/quotient shortcuts AND arbitrary nonlinear reuse, not just positive support | OPEN P0, connect R31–33 to G12a/N4 on original DAGs |
| R7c / LGC6 / D | Superpolynomial separation of same unrestricted invariant on actual selector 3-SAT | OPEN P0; G17 only restricted, G12b/c/N5 |
| LGC7/N6 / E | Original Clay endpoint via standard cost model | conditional source consumer, no unconditional producer |

Next consolidated mathematical target: determine what extra global constraints of the actual selector norm network force charged progress even with the R33 quotient gates and R31 shared signed contraction. Do not try to prove arbitrary honest representation transport is monotone, or charge every independent mask/character/cocycle term. R32 supplies a precise monotone baseline, R33 a mandatory unrestricted escape. No generic certification programme or other Millennium prerequisite.

## 13. R36–R42 — same-object selector projectors, weight-section gluing and logarithmic quotient escape (2026-11-24)

Stay on Langlands. User supplied Monster #1545 direct source character-idempotent/Hom construction and attachments of R28–35 plus G20–21 (inhabited zero, masked dual rails, negative-evidence orbit covering). Actual live heads: #1545 197b0d5f92dd7418b63918507e2a104bccbb6886; #1548 e8afe2cba4e36e2d1a698105b195d4783b3a2422 / #119 05642355ac3e043aa472f5e072933e3647aa0062; #1549 3289f1851895ed4845d2a2c835f3f2b551b2541f / #120 7e52e18442b4c5de267b50f81eb6a7b27dbc8aed. Keep G20–21 ownership there, no Monster edits. Source donor inspected: Docs/roadmaps/Monster3BEndpointFirstConstruction20261123.md blob 7f97a0f5a473c9171c87870f17a1f8cc4b20808c, M3B-L11S explicitly conditional on R_actual source character/word attachment; E_17496/E_113724 commute with phase projectors, Hom ranks 12/78, actual basis/word matrices remain open. Do not infer source identity from dimension. Additional master donors inspected: DASHI/Moonshine/Monster3BFiniteWeightProjectorExact.agda 11f3d7bce9da7654b013d61ef30df4a62f0b0657 (weightProjectorCoefficientIdempotent and translatedProjectorCoefficient; finite model, original sector attachment separate); DASHI/Core/QueryFactorisationSufficiency.agda 98c592232292bbb6c5f0df047c8df3fd42be30d3 and ConsumerFibreRepairExact.agda 5bab8f89861559c14f3877acd5e11424b21a6a6d (refinementRepairSeparatesWitness, factorizationRepairSeparatesWitness, necessary separation not global sufficiency). Existing R28 source parity and R21 six-face donors retained.

### R36. Actual source-selected projector and Hom construction

Take X=F2^m, D=C^X with named basis |x>. Fixed actual Weil representation P=1+U from R30 (W_F acts on P and trivially on D); W=D tensor P. For each clause C, q_C(x)=1 iff x falsifies C; define Q_C diagonal with entries q_C(x). For absent-selector t (1=absent), let
    Pi_t=product_C (I-(1-t_C)Q_C).
These are commuting orthogonal idempotents on the original D, so Pi_t diagonal with entry 1 iff x satisfies selected clauses. W_t=im(Pi_t tensor I_P) is an actual W_F-submodule. If W(t)=number of satisfying x, W_t=1^{W(t)} direct_sum U^{W(t)}. Actual central character idempotents of S3 acting on P commute with Pi_t tensor I_P; Hom_WF(1,W_t) and Hom_WF(U,W_t) have dimension W(t), canonically reconstruct via evaluation, no separate unknown representation matrices. The same holds after restriction and cubic phase projection: each phase space has dimension W(t), including inhabited trivial mode when satisfiable. The norm criterion R17 produces the same clause factor because eta'(u'^p_C)=1 iff p_C=0. This is same-object arithmetic submodule, not new global Langlands theorem. The assignment labels are external multiplicity coordinates, not independent local Galois automorphisms. R36 is a succinct product presentation with exponentially dimensional semantic carrier; computing rank/trace is not a free primitive. Unlike Monster where source character multiplicities supplied, the multiplicity W(t) is precisely the unknown #SAT output. No inference of its value from generic central idempotents.

### R37. Exact same-object Fourier compression and noncommuting source attachment

Use actual assignment translation group X acting regularly on D (separate from W_F). Its Fourier rank-one projectors E_h=v_h v_h^*/|X| where v_h(x)=(-1)^(h dot x), h in X. Then for every h,
    Tr(Pi_t E_h)=W(t)/|X|,
    (Pi_t E_h Pi_t)^2=(W(t)/|X|) Pi_t E_h Pi_t.
For W(t)>0 compressed operator has rank one with sole nonzero eigenvalue W(t)/|X|. For empty fibre it vanishes. Thus a *single* original Fourier mode detects SAT by nonzero compression; no need to examine exponentially many phases individually. For normalized v, p=W(t)/|X|, Pi v has squared norm p. Decompose v=Pi v+(I-Pi)v. The commutator is off-diagonal rank <=2, has operator norm sqrt(p(1-p)), Hilbert-Schmidt norm squared 2p(1-p). Therefore for 0<W(t)<|X| no individual E_h commutes with Pi_t. Centrality in the assignment group algebra does NOT imply centrality in the larger algebra containing arbitrary clause projectors. By contrast actual S3 central idempotents on P commute with Pi_t, exactly as their typed factor requires. Same-object proof requires this distinction; cannot transfer Monster commuting assumption across different acting groups. Off-diagonal Fourier matrix entries are Walsh coefficients of satisfying indicator divided by |X|. Phase-labelled full matrix retains all assignment information, but materializing it is exponentially expensive; even one diagonal is normalized #SAT and requires charged computation. Neither small output rank nor rank of commutator is a complexity separator.

More source covariance: translations h of assignment cube permute clause polarities, hence t -> h.t and Q_C -> Q_(h.C); T_h Pi_t T_h^-1=Pi_(h.t). At a fixed t only its stabilizer H acts on satisfying subspace. H acts freely on assignment labels, so as H-module im Pi_t is W(t)/|H| copies of regular H (including zero if unsat). Across orbit X.t, direct sum of those subspaces is Ind_H^X im Pi_t, hence W(t)/|H| copies of regular X. Unmarked equivariant character on orbit contains no additional dependence beyond count and orbit stabilizer. Keep selector and assignment coordinates; covariance is not fixed-input invariance. R37 gives exact obstruction to unmarked spectral shortcut, not a lower bound.

### R38. Logarithmic number of genuine equivariant quotients suffices for arbitrary circuits

G21 supplies an almost-every-minterm conditional lower bound on distinct negative literal evidence in accepting traces (NOT gate count is different). R33 realizes NOT by quotient of the fixed trivial line. Stronger universal negative control: all N negative input rails can be generated using at most r=ceil(log2(N+1)) genuine bounded-dimension quotient gates and polynomial positive circuit size. This is the known Markov–Fischer inversion phenomenon; explicit elementary weight-chart derivation below, not a new general circuit theorem. Sources: Jukna et al. *On the minimum number of negations leading to super-polynomial savings*, https://eccc.weizmann.ac.il/eccc-reports/2001/TR01-058/index.html ; *On the Complexity of Negation-Limited Boolean Networks*, https://epubs.siam.org/doi/abs/10.1137/S0097539794275136 ; Fischer inverters have stronger size bounds than the simple O(N^3) here.

For t in {0,1}^N let w=sum t_i and monotone thresholds T_k(t)=[w>=k]. Compute all thresholds with fan-in-two AND/OR recurrence T_(j,k)=T_(j-1,k) OR (t_j AND T_(j-1,k-1)), T_(j,0)=1, T_(0,k>0)=0. Cost O(N^2). Compute thresholds T_k^(-i) excluding i, separately O(N^3) all i. Read binary weight bits from most significant j=r-1 to 0. If previous bits encode prefix p (length r-j-1), its indicator A_p is AND of previously computed positive/negative bit rails (empty prefix=1). Then
    b_j=OR_p (A_p AND T_(p*2^(j+1)+2^j)).
Thresholds above N are constant 0. Each b_j uses only positive gates and existing rails. One quotient generates 1-b_j; reuse all rails. At the actual prefix exactly one A_p=1, so b_j is correct. Total r quotient gates, O(N log N) extra prefix logic (or share prefixes for O(N)), no other NOTs. Now exact-weight indicators Z_k=[w=k] obtained as AND of chosen weight-bit rails, and
    1-t_i=OR_(k=0..N) (Z_k AND T_k^(-i)).
Proof: on actual weight k, sum_(j!=i)t_j=k-t_i, so >=k iff t_i=0. All remaining gates positive, O(N^3) bound. Convert arbitrary Boolean circuit of size s to dual-rail monotone logic on t_i,1-t_i with O(s) gates, then plug this inverter. Realize all positive gates on Boolean-valued trivial Weil lines (AND tensor; OR support of direct sum, saturated to one bit via a charged constant-size Boolean OR operation). More precise model: OR as sum followed by fixed support-to-bit operation on dimensions 0,1,2, which is positive on support, not claimed additive multiplicity map; alternatively ordinary subspace sum inside same marked line, B_a+B_b. Both are explicit constant-cost actual marked subspace operations. Quotients only for r weight bits. Thus any polynomial Boolean circuit admits a polynomial-size honest marked representation circuit with at most logarithmically many nonmonotone quotient gates. No promise for arbitrary implicit rank operations. Theorem forbids any attempted universal proof that superpolynomially many quotients are required, independent of other gate cost. Nor does it give a polynomial SAT circuit: starts with one if available.

### R39. Weight projectors on the actual input and the sharp cross-slice obstruction

Let b=sum_(j=1..3) binom(m,j), N=N_m. All selector minterms P_x=Z_x have weight b (one absent falsified polarity for each variable subset). Consequently G=G_(m,3) is zero on weights <b, and its entire monotone upward closure is determined by values on the weight-b slice. This is the original input selector carrier, not the assignment D of R36. Weight idempotents are diagonal functions of the Hamming-weight operator, not S3 central character idempotents unless an appropriate action is separately specified.

For any dual-rail monotone DAG D(t,u) with D(t,1-t)=G(t), define
    L_b(t)=D(t,(T_b^(-i)(t))_i).
L_b is monotone, size O(s+N^3). On weight exactly b it equals G, since T_b^(-i)=1-t_i. On weight <b all these negative rails vanish, so L_b<=G=0. On weight >b it may be unsound: whenever weight >=b+1, every negative rail equals 1, so L_b=D(t,1). Explicit actual selector counterexample: for m>=2 take all clauses absent except contradictory unit pair on one variable. Weight N-2 >= b+1, G=0. Modify a correct dual-rail circuit by OR with t_i AND u_i for some absent coordinate i (on consistent rails this term identically zero). Then L_b accepts this unsat input. This is a counterexample to universal slice-to-global soundness, not proof every circuit has that defect.

There is an exact converse relevant to cost: ANY monotone H that agrees with G on all weight-b inputs and is sound (H<=G) on higher inputs must equal G globally if sound on lower inputs too. Indeed every positive t contains some minterm of weight b, so H(t)=1 by monotonicity. Even lower soundness follows for G if every lower input extends to a weight-b negative input, but do not assume this; require H<=G globally. Hence R32/G17 superpolynomial lower bound applies to sound monotone extension of the weight-b trace, not just exact computation ON that slice. Conditional on polynomial unrestricted SAT, L_b gives a polynomial monotone circuit correct on every minterm and all smaller weights, yet no polynomial globally sound extension. This is a sharp global gluing obstruction, with explicit marked weight projector Z_b isolating the slice; Z_b is not a monotone gate. It does not assert that an arbitrary nonmonotone circuit must pay separately for every slice or overlap. The G21 mask underapproximations are globally sound precisely because their rails correspond to an actual smaller input; the weight-slice shortcut loses that property on larger weights. Next resource question: charge genuine correlations of these inconsistent-rail evaluations, not number of quotient gates or negative literals, preserving arbitrary sharing. The above shows even an O(log N)-bit weight residual can unlock all negative rails, so pure residual cardinality bound cannot suffice.

### R40. Executed local Python/SymPy (no CI/native prover)

Actually ran exact local script, 18,434 coordinate inverter checks across every input n=1..10, 18,434 slice checks at actual weight, 1,032 exact rational selector Fourier projector/commutator comparisons across every selector m=1,2 (4 and 256 inputs respectively). The inverter checks evaluate prefix threshold logic semantically, not a native circuit compiler/size benchmark. Proof and size recurrence above independent. Reproduction:
```python
from itertools import product,combinations
import sympy as S
checks=slices=comm=0
for n in range(1,11):
    r=n.bit_length()
    for t in product((0,1),repeat=n):
        w=sum(t); pref=0
        for j in reversed(range(r)):
            bit=int(any(pref==p and w>=p*2**(j+1)+2**j
                        for p in range(2**(r-j-1))))
            pref=2*pref+bit
        assert pref==w
        for i,x in enumerate(t):
            neg=int(any(pref==k and w-x>=k for k in range(n+1)))
            assert neg==1-x;checks+=1
            assert int(w-x>=w)==1-x;slices+=1
for m in (1,2):
    X=list(product((0,1),repeat=m));n=len(X)
    C=[(I,p) for k in range(1,m+1)
       for I in combinations(range(m),k) for p in product((0,1),repeat=k)]
    Q=[S.diag(*[int(tuple(x[i] for i in I)==p) for x in X]) for I,p in C]
    I=S.eye(n);E=[]
    for h in X:
        v=S.Matrix([(-1)**sum(a*b for a,b in zip(x,h)) for x in X])
        E.append(v*v.T/n)
    for t in product((0,1),repeat=len(C)):
        P=I
        for z,q in zip(t,Q):P=P*(I-(1-z)*q)
        W=sum(all(z or tuple(x[i] for i in inds)!=p
                  for z,(inds,p) in zip(t,C)) for x in X)
        assert P*P==P and S.trace(P)==W
        for e in E:
            assert S.trace(P*e)==S.Rational(W,n)
            assert (P*e*P)**2==S.Rational(W,n)*(P*e*P)
            assert S.trace((P*e-e*P).T*(P*e-e*P))==2*S.Rational(W,n)*(1-S.Rational(W,n))
            comm+=1
assert (checks,slices,comm)==(18434,18434,1032)
```
No actual local field oracle evaluations or kernel proof. Standard character theory/projector/Hom and Markov–Fischer prior art explicit; new DASHI crosswalk source-specific selector norm module and weight-slice boundary, not priority claims. Retain JMD/Monster/G16–21 attribution.

### R41. P0 proof obligations, not additional certification rounds

| Gate / phase | Deliverable | Source -> consumer / status |
|---|---|---|
| R36 / B | Actual selector norm projector on fixed Weil module, central/phase/Hom same-object subspaces | R17/R30, #1545 L11S method, R28 -> derived; unknown multiplicities are W(t), not free |
| R37 / B-C | Fourier rank-one compression, commutator formula and orbit covariance | R8, #1545 weight projector, original selector translation -> derived; no lower bound from ranks |
| R38 / C | Polynomial shared inverter with logarithmic genuine quotient gates | R33, G20–21, Markov–Fischer -> derived explicit compiler; no quotient-count superpoly |
| R39 / C | exact minterm-weight slice monotone transport and global sound-extension obstruction | R32/G17, G21 orbit masks -> derived; conditional cheap slice vs hard globally sound extension |
| R40 | local exact regression | executed, not native certification |
| R7a' / LGC4d / C | genuine correlation-dependent arithmetic consumer sensitive to width-three overlap and globally sound across slices | R36–39, R23/R24, G21, FactorsThrough -> open cost-sensitive choice |
| R7b' / LGC5 / C | universal serial-safe resource bound under all shared Boolean/quotient operations, not just number of negative rails/quotients, rank, coefficient count or dimensions | G12a/N4, R38/39 and #123 charge discipline -> OPEN P0 |
| R7c / LGC6 / D | same invariant superpolynomial lower bound on selector-SAT or original uniform machine | G12b/c/N5 -> OPEN P0 |
| LGC7/N6 / E | literal Clay endpoint transport | conditional source consumer, no unconditional inhabitant |

### R42. Next combined mathematical tranche

Target the compatibility of the actual marked slice projector, signed rail correlations and globally sound selector norm descent. R39 isolates the missing global extension: minterm-weight computations are not sufficient unless correct on supersets. Seek a universal resource argument for genuinely consumer-relevant correlation/overlap handling across slices, or a precise counterexample, with actual all-circuit coverage. Do not propose another source character census, local ramification calculation, quotient-count bound, or per-minterm charge as the endpoint. R38 proves quotient count alone is too weak and G21 provides conditional widespread trace-width constraint; they are compatible because a few shared quotient outputs can generate many negative rails. Native weld only after mathematical progress. Continue Langlands, no Monster endpoint prerequisite or changes to #1545/#1548/#119.

## 14. R43–R49 — dense-scope ramified fibre compression and thin-band upward closure (2026-11-24)

User directed stay on Langlands, using G22–27 (attachments and supplied G25–27) as inspiration. Read both mounted attachments. Live other-worker #1548 ead847b32e6a2e10666f209ff6305c222e5de38c and #119 8a8f77430e62a12a77111a12ae6c19aaecf59f3f, matching roadmap blob 790854f6eb326974377356c840c10d38945bf1c8. Existing Langlands heads #1549 464691089a12257aee5a0374f36dc293aa04c7fe and #120 9c181a9fd0efe4101ccfdf96805b005c7af1c67e; matching blob 71f8d6eef6ec3693f6db8d98c9968b252d5d4d7d. No changes to other worker's branches. Actual inspected master donors: DASHI/Mathematics/Complexity/PNotEqualsNPRestrictionQuotientCircuitSemanticsExact.agda 393fe5a7ad26ac00c3076768ee3b9f0091c1305c, quotientCircuitComputesDP/rootDecision; PNotEqualsNPRestrictionQuotientSATAuthorityExact.agda 05977a2ed2b6d89c4769fbe5c0763fc3f95ab93d, quotientSATAuthorityExact (conditional exact finite-state restriction, no state bound); BooleanFormulaSATSelfReductionExact.agda 5991b2b90cf03be35769ca5ef6d8b47622aab24f, restrictionEvaluation, liftFalse/liftTrue; DASHI/Core/ConsumerFibreRepairExact.agda 5bab8f89861559c14f3877acd5e11424b21a6a6d, necessary collision separation not general sufficient cost. Reuse R16/29 local norm, R23 zero-residual, R24 governed cube, R36–37 actual projectors, G23 actual assignment fibre, G27 exact minterm recognizer. No native certification or new infrastructure phase.

### R43. Dense-scope residual bound (strictly wider than G27 minterm slice)

Let B_m = all nonempty variable subsets I of size <=3; b(m)=|B_m|, N_m=sum_I 2^|I|. A_I(t)={p:t_(I,p)=1} is the allowed polarity set in the absent-clause selector. SAT iff an assignment x satisfies x|I in A_I for all I. If some A_I is empty reject. Otherwise k=|t|-b(m)=sum_I (|A_I|-1)>=0. A singleton scope means |A_I|=1 (not necessarily |I|=1), and forces every variable in its unique pattern. If two such scopes force different values of the same variable, reject. Let F be the variables fixed by any singleton scope, with consistent fixed values c, and R=complement F, r=|R|. Every scope meeting R must contain >=2 allowed patterns, hence pays >=1 unit of k. Exact combinatorial bound
    b(m)-b(m-r) <= k.
Each variable occurs in d_m=1+(m-1)+binom(m-1,2) scopes, each scope counts at most three of the r incidences, so
    r*d_m <= 3k.
In particular k<d_m implies r=0 (one unresolved variable alone is incident to d_m scopes). This does not assert every nonzero excess creates a genuinely free variable; r is a conservative residual count, further propagation can reduce it. N_m=Theta(m^3), d_m=Theta(m^2). This exploits the dense original selector geometry, not the density of a general sparse CNF representation. G27's b+1 counterexample is detected by the stronger singleton-SCOPE overlap checks.

### R44. Same-object ramified restriction and exact charged algorithm

With the actual R36 assignment carrier D=C^(F2^m) and ramified P=1+U, retain the embedding J:C^(F2^R)->D, J|y>=|c union y>. J*J=I, JJ*=E_c the original coordinate-fibre projector. Every singleton-scope constraint is diagonal and forces its pattern, hence Pi_t E_c=Pi_t=E_c Pi_t. For an individual falsifying pattern C=(I,p), J*Q_C J=0 if any p_i disagrees with c on I intersect F, otherwise it is the falsification projector for p|_(I intersect R) (identity when I intersect R is empty). This is the exact G23 fibre-mask transport on actual assignment projectors. Equivalently the R29 local norm factors u'^(s_C q_C(x)) restrict to the same norm test on the residual scope, or a constant; the full character and original source labels can be retained in provenance. No new local field or character identification is needed.

For each residual scope L subset R, |L|<=3, define B_L as intersection over original I with I intersect R=L of the allowed patterns restricted after checking c. Include L=empty; B_empty is either {()} or empty, not a discarded zero mode. Missing residual scopes mean unrestricted, whereas empty B_L means impossible. Then the compressed projector Pi_R is the product of original restricted diagonal conditions; aggregation by L is literal intersection, retaining a source I for each rejected pattern. Exact identities:
    J* Pi_t J = Pi_R; J Pi_R J* = Pi_t;
    im(Pi_t tensor I_P) ~= im(Pi_R tensor I_P)
as actual Weil representations, by J tensor I_P; all central S3 and marked C3 phase projectors commute with J since they act on P. Both Hom dimensions and W(t)=Tr Pi_R are unchanged. R37 normalized Fourier compression on residual D_R has eigenvalue W(t)/2^r, not the original W(t)/2^m; record this normalization. This is a genuine same-object submodule compression, not just matching dimensions. It preserves exact witness recovery y -> c union y; conflicting singleton scopes give empty fibre rather than a fabricated c. R24 face gluing requires same marked c and compatible restrictions; independent charts with inconsistent fixed assignments must not be identified.

Construction scans each original scope at most eight patterns, records fixed c and checks consistency, intersects <=8-bit residual masks. O(N_m) fixed-word operations plus polynomial indexing/bit-cost overhead; residual scope count <=b(r)+1. Enumerate 2^r residual assignments, evaluate all residual scopes, sum exact count using O(r+1)-bit integers. Time poly(N_m)+(r+1)^O(1) 2^r, with explicit original-witness reconstruction and memory poly(N_m) if streaming. In particular bound poly(N_m)*2^{O(k/m^2)} for m>=2; when k=O(m^2 log m), polynomial time (constant in O fixed), including exact count. For k<d_m, at most one assignment, recover or reject in one scan plus original validation. No free rank operation, implicit exponentially wide matrix, or independent charge per original assignment used. This is a positive algorithm on a promised band, not all-input polynomial SAT.

### R45. Wider positive/monotone band via bounded actual obstruction cores

Define H_l(t) as conjunction over all collections of at most l distinct original scopes of the proposition that some jointly consistent selection of one available pattern per scope exists. For each collection, enumerate <=8^l pattern choices with consistent shared variable labels, OR the corresponding AND of selector bits. H_l is monotone; G<=H_l globally. Size O(l*8^l*(b(m)+1)^l), fixed l polynomial; operations are positive marked-line support operations (AND tensor, OR sum/support), within R32. This is joint overlap, not independent per-scope projections; no need to decide whether a scope is singleton inside H_l.

If unsat due empty scope or inconsistent unique patterns there is a 1- or 2-scope obstruction. Otherwise R44 fixes c. For each of 2^r assignments y of R, choose an original scope whose allowed relation rejects c union y. For each chosen original scope, attach at most 3 singleton scopes that force its variables in F. The resulting collection is jointly unsatisfiable: any assignment satisfying it must agree with c on the fixed coordinates used, and every possible residual y has one selected blocking scope. Thus there exists a core of <=4*2^r scopes. Alternatively, for each forbidden residual pattern (L,p), choose one original scope that excludes it on c, and add forcing scopes for its fixed variables. There are at most 1+N_r such patterns, counting the empty pattern; same contradiction. Therefore one may take
    l(r)=4 min(2^r,1+N_r).
For k bounded by C*m^2 with fixed C, r bounded, so some fixed l gives a polynomial-size positive representation/monotone support circuit exact on ALL such inputs (including below b, where an empty scope forces rejection). Specifically H_4 is exact whenever |t|<b+d_m. This is an unconditional wider monotone tractable band, not conditional on a hypothetical SAT circuit as R39. Upper bound H_l may be much larger than nonmonotone algorithm when r grows; no claim polynomial monotone size for k=O(m^2 log m).

Sharp order for fixed l>=4: choose l+1 unresolved variables, all remaining variables fixed to zero. All scopes allow every pattern consistent with those fixed coordinates, except pair scopes forming a cycle on the unresolved variables. Set l edges equality and the closing edge disequality. Full conjunction inconsistent, but any l-scope collection omits some edge and is satisfiable; the omitted-edge claim follows from a path of binary equalities/disequalities. All original scopes nonempty, all scopes meeting R have >=2 patterns. Excess k=sum_I(2^|I intersect R|-1)-2(l+1) <=7(l+1)d_m, also >=d_m. Thus H_l can fail at Theta(m^2) excess for any fixed l>=4; no uniform finite overlap width works across all selectors. This is a width-two parity-cycle constraint embedded in full width-three selector carrier, not a general unrestricted lower bound. It is a counterexample to that specific local checker, not to all possible algorithms.

### R46. BIDI: thin-band padding preserves the original hard problem

Take arbitrary selector on q original variables, embed into m>=q variables. For scopes I contained in the q variables, copy every input coordinate unchanged. For every other I, set the available pattern bits to constants admitting exactly assignments with all added-variable coordinates 0; no further constraints on the original variables. Original assignment and padded witness are in bijection x -> (x,0^(m-q)), including empty solution relation. At projector level J_pad* Pi_padded J_pad=Pi_original, Pi_padded=J_pad Pi_original J_pad*, same actual P and Hom dimensions. The embedding is a monotone projection, not an existential reduction with hidden preprocessing. All added coordinates fixed by singleton scopes; any original empty scope remains empty, hence promise is upper bound only (weights below b allowed). Excess satisfies
    |t_padded|-b(m) <= 7[b(m)-b(m-q)] <= 7 q d_m.
For fixed epsilon>0 choose polynomial m in q with q<=m^(3 epsilon) (if epsilon>=1/3 take m=q or larger). Then padded instances lie in |t|<=b(m)+O(N_m^(2/3+epsilon)). This is an NP-hard promise family, with explicit uniform polynomial reduction and exact #witness preservation. For a two-sided band b<=|t|, detect empty original scopes in polynomial preprocessing and map to a known no-instance at b+1 as G27; that variant is no longer a pure monotone projection, so do NOT use it for monotone lower bounds. Combined with R44, polynomial-time exact algorithm up to O(N^(2/3) log N), and NP-hardness for every fixed power increase N^(2/3+epsilon), without assuming P!=NP. The gap between these scales remains.

Monotone / limited-negation transport uses the upper-bound-only band. Choose m=ceil(q^a), fixed a>max(1,1/(3epsilon)), so input length N_m=Theta(q^(3a)). G22 CKR lower bound on q-variable source yields exp(Omega(q^(1/4) log q)) for delta=1/12, i.e. exp(Omega(N_m^(1/(12a)) log N_m)) along hard subsequences, even for circuits only required correct on this promised band. R32 fixed-type positive rep model inherits bound. G25 Amano–Maruoka CLIQUE bound also preserves genuine negation gates under this projection; loglog of graph n vs padded N differs by O(1), so excluded polynomial size at <=(1/6)log2 log2 N-O(1) NOTs along its appropriate (different) hard sequence. References verified in current turn: https://epubs.siam.org/doi/10.1137/S0097539701396959 (Amano–Maruoka); https://pmc.ncbi.nlm.nih.gov/articles/PMC9705498/ (CKR). Apply to R32 positive support gates plus R33 canonical Boolean-valued marked-line quotient (one NOT), charged constant-cost support operations. Arbitrary higher-dimensional variable-map cokernel/rank is not one Boolean NOT, and not covered absent its own compiler. R38/G26 logarithmic shared inversion remains valid, so this is a limited nonmonotone theorem, not unrestricted. G24 transversal/different mismatch independence is not a count of paid gates. Do not infer global SAT cost from input density, actual r, or exponential dimension.

### R47. Local execution and reproduction

Actual local Python/SymPy: all 260 selector inputs m=1,2; 118 consistent nonempty fibre cases with exact matrix equalities J*J=I, J*Pi J=Pi_R, J Pi_R J*=Pi, normalized residual Fourier trace; 162 unsat cores across those inputs. 600 deterministic random planted/partially constrained inputs m=3..8, 340 consistent nonempty fibre cases, 286 unsat core checks. 1040 padding witness-count and excess-bound comparisons (all 260 inputs, each padded to m=3..6). Five cycle witnesses (m,l)=(5,4),(6,4),(6,5),(7,6),(8,7) with k=95,130,179,301,468; each omitted-edge conjunction satisfiable. No CI/native prover or field oracle. Reproducible core of actual checker (complete small exhaustive and padding/cycle fixtures; random generator below):
```python
from itertools import product,combinations
from math import comb
from random import Random
import sympy as S
def scopes(m):return [I for j in range(1,min(3,m)+1) for I in combinations(range(m),j)]
def patterns(I):return list(product((0,1),repeat=len(I)))
def nbits(m):return sum(2**len(I) for I in scopes(m))
def solve(m,A):
    Ilist=scopes(m);X=list(product((0,1),repeat=m))
    masks={I:sum(1<<j for j,x in enumerate(X) if tuple(x[i] for i in I) in A[I]) for I in Ilist}
    full=(1<<len(X))-1;actual=full
    for v in masks.values():actual &= v
    if any(not A[I] for I in Ilist):return actual,None,[next(I for I in Ilist if not A[I])],masks
    fixed={};src={}
    for I in Ilist:
        if len(A[I])==1:
            for i,v in zip(I,next(iter(A[I]))):
                if i in fixed and fixed[i]!=v:return actual,None,[src[i],I],masks
                fixed[i]=v;src[i]=I
    R=tuple(i for i in range(m) if i not in fixed);r=len(R);k=sum(len(A[I])-1 for I in Ilist);d=1+(m-1)+comb(m-1,2)
    assert len(Ilist)-len(scopes(m-r))<=k and r*d<=3*k
    B={};prov={}
    for I in Ilist:
        J=tuple(i for i in I if i in R)
        allowed={tuple(p[j] for j,i in enumerate(I) if i in R) for p in A[I] if all(i not in fixed or p[j]==fixed[i] for j,i in enumerate(I))}
        if J not in B:B[J]=set(patterns(J))
        B[J]&=allowed
        for p in patterns(J):
            if p not in allowed:prov[J,p]=I
    restored=0;fibre=[];good=[];failed=[]
    for y in patterns(R):
        D=dict(fixed);D.update(zip(R,y));x=tuple(D[i] for i in range(m));idx=X.index(x);fibre.append(idx)
        bad=next(((J,tuple(D[i] for i in J)) for J in B if tuple(D[i] for i in J) not in B[J]),None)
        good.append(int(bad is None))
        if bad is None:restored|=1<<idx
        else:failed.append(prov[bad])
    assert restored==actual
    core=[]
    if not actual:
        selected=set(failed) if len(failed)<=len(prov) else set(prov.values())
        core=set(selected)
        for I in selected:core.update(src[i] for i in I if i in fixed)
        assert len(core)<=4*min(2**r,1+nbits(r))
        z=full
        for I in core:z&=masks[I]
        assert z==0
    if m<=2:
        J=S.zeros(len(X),len(fibre))
        for a,b in enumerate(fibre):J[b,a]=1
        P=S.diag(*[actual>>i&1 for i in range(len(X))]);Bmat=S.diag(*good)
        assert J.T*J==S.eye(len(fibre)) and J.T*P*J==Bmat and J*Bmat*J.T==P
        assert S.trace(Bmat)==actual.bit_count()
        v=S.ones(len(fibre),1);E=v*v.T/len(fibre)
        assert S.trace(Bmat*E)==S.Rational(actual.bit_count(),len(fibre))
    return actual,r,core,masks
def all_inputs(m):
    I=scopes(m);C=[(i,p) for i in I for p in patterns(i)]
    for t in range(1<<len(C)):
        A={i:set() for i in I}
        for j,(i,p) in enumerate(C):
            if t>>j&1:A[i].add(p)
        yield A
def pad(A,r,m):
    return {I:A[I] if all(i<r for i in I) else {p for p in patterns(I) if all(i<r or p[j]==0 for j,i in enumerate(I))} for I in scopes(m)}
def cycle(m,l):
    R=set(range(l+1));B={I:{p for p in patterns(I) if all(i in R or p[j]==0 for j,i in enumerate(I))} for I in scopes(m)}
    for i in range(l):B[i,i+1]={(0,0),(1,1)}
    B[0,l]={(0,1),(1,0)}
    return B
def check_core(m,core,ms):
    if core:
        z=(1<<(2**m))-1
        for I in core:z&=ms[I]
        assert not z
for m in (1,2):
    for A in all_inputs(m):
        a,r,c,ms=solve(m,A);check_core(m,c,ms)
rng=Random(20261124)
for m in range(3,9):
    for q in range(100):
        x=tuple(rng.randrange(2) for _ in range(m));R=set(rng.sample(range(m),rng.randrange(m+1)));A={}
        for I in scopes(m):
            candidates=[p for p in patterns(I) if all(i in R or p[j]==x[i] for j,i in enumerate(I))]
            a={p for p in candidates if rng.random()<.65}
            if q%3==0:a.add(tuple(x[i] for i in I))
            if not a:a.add(rng.choice(candidates))
            A[I]=a
        a,r,c,ms=solve(m,A);check_core(m,c,ms)
for r in (1,2):
    for A in all_inputs(r):
        a,*_=solve(r,A)
        for m in range(3,7):
            B=pad(A,r,m);b,*_=solve(m,B)
            assert a.bit_count()==b.bit_count()
            assert sum(len(s) for s in B.values())-len(scopes(m))<=7*(len(scopes(m))-len(scopes(m-r)))
for m,l in [(5,4),(6,4),(6,5),(7,6),(8,7)]:
    A=cycle(m,l);a,r,core,ms=solve(m,A);assert not a and r==l+1
    for omit in [(i,i+1) for i in range(l)]+[(0,l)]:
        z=(1<<(2**m))-1
        for I,mask in ms.items():
            if I!=omit:z&=mask
        assert z
    k=sum(len(s)-1 for s in A.values());d=1+(m-1)+comb(m-1,2)
    assert d<=k<=7*(l+1)*d
```

### R48. Updated P0 ledger, producers and consumers

| Gate / phase | Exact deliverable | Status |
|---|---|---|
| R43 / B | dense-scope residual bound | G23/G27 original scope incidence -> derived |
| R44 / B-C | original ramified norm/projector fibre compression, exact count and witness with explicit FPT cost | R29/R36/R37, restriction-quotient semantic and SAT authority, R23 zero fibre -> derived |
| R45 / C | bounded joint obstruction core and exact positive support on wider near-minterm band | R32, G16/G27, source scope overlap -> derived; parity-cycle control |
| R46 / C-D | reverse monotone padded projection, NP-hard thin band and restricted superpoly transport | G22/G25, R33, R44 -> derived |
| R47 | exact local checks | executed, not kernel certification |
| R7a' / LGC4d / C | actual global overlap consumer and charged compression beyond bounded residual | R44 gives an exact conditional parameter algorithm, R46 shows dense padding cannot alone shrink arbitrary original hard core |
| R7b' / LGC5 / C | universal serial-safe cost across arbitrary shared signed/quotient computation, or a direct uniform lower bound | OPEN P0; use R46 promised source if helpful, not independent rank/trace/quotient count |
| R7c / LGC6 / D | superpolynomial unrestricted separation on same actual selector/padded source | OPEN P0; G25 limited negations and G26 logarithmic ceiling distinct |
| LGC7/N6 / E | literal Clay endpoint via existing standard machine coverage/consumer | conditional, not inhabited |

### R49. Next endpoint-first tranche

Use R44 as a concrete solved compression, not a new generic certification project. Need either a lower bound on every polynomial unrestricted algorithm for actual thin-band residual instances (sufficient by R46), or a costed normalization preserving G24/G25 constraints beyond shared logarithmic inversion; do not assume high r forces independent work or claim local character count is a lower bound. For a positive alternative investigate actual residual scope interaction structure and whether arbitrary nonlinear operations can compress rank nonvanishing; the reverse projection shows any generally efficient method on the hard band solves original SAT. Retain width-two negative controls, marked incidence, dependent zeros and all original labels. No unrelated Monster/YM/RH work. Standard CSP restriction, finite-dimensional projector and prior lower-bound authority credited; original DASHI/JMD owners and other worker G22–27 retained. No claim P!=NP.

## 15. R50–R56 — single central sandwich, actual exterior-power Weil module and Fourier coefficient boundary (2026-11-24)

User directed stay on Langlands. Read both current mounted attachments (R43–49 and G28–32). Live G28–32 #1548 9cc331b5ae03f07af335618ca74d8640a88b5269 / #119 4f8af7050230ba8c07387e55d47f761dc0fc63ad, identical blob 777a62b796d53f3c753b79ee0bb038e566888a37. Live Langlands #1549 07ced79e5be47401151c646d5cca13330fea789e / #120 1568c2c4738bf310d70fa291cfecded797c9c6e2, blob aed00d1cb12ad323b16de59c7015d94fabc75219. No edit of other worker branches. G28 intersects each variable's available-value projections across all scopes, improving R43 singleton-scope forcing: empty domains reject, singleton domains fix, ambiguous a has b(m)-b(m-a)<=k. Sharp via union of two minterms at distance a. G28's O(N) monotone checker is exact before b+d_m; use this in place of larger H_4 for that first band. R44 same-object isometry applies equally to the stronger fixed domains (all solutions satisfy them). G30 external theorem verified against actual HTML Corollary 5: Jarosław Błasiok and Linus Meierhöfer, *Hardness of Clique Approximation for Monotone Circuits*, CCC 2025, DOI 10.4230/LIPIcs.CCC.2025.4, https://drops.dagstuhl.de/storage/00lipics/lipics-vol339-ccc2025/html/LIPIcs.CCC.2025.4/LIPIcs.CCC.2025.4.html ; k<=n^(1/2-delta)/log^2 n gives n^Omega(delta^2 k). G22 with delta=1/24, clique k=floor(n^(5/12)), yields exp(Omega(N^(5/36) log N)), replacing the earlier G22/CKR 1/12 exponent. R46 padded exponent a becomes 5/(36a), distinct from G25 limited negation. This theorem concerns full monotone G, NOT its sandwich. G32 fixed-weight and sandwich equivalence credited to other worker.

Inspected actual master donors: DASHI/Moonshine/PenumbralSQModuleLift.agda dd1f89c24dc29f21d7030ac9799b1639ee5a3c35 (LambdaRingModuleCarrier with exteriorPower/symmetricPower/trace, an interface not a complexity theorem); PenumbralSuperFockFactor.agda 988d2d5c31d6f297234e76e3090fad5cfc917a05 (GradedModuleSeriesCarrier with exterior algebra and Cauchy coefficient law); Monster3BMultiplicityCharacterProjectorExact.agda 64641da0802c773aaff383551df17227cfc767ba (multiplicityProjectorTrace, source trace inputs explicit); ConsumerFibreRepairExact.agda 5bab8f89861559c14f3877acd5e11424b21a6a6d; Karp21NativeBinaryAdderWidthBoundExact.agda 4016924f3bfc88bf850410e983a74bea9e996088 (actual addBitsOutputBitWidthLinear, not full cost). These are typed patterns, not imported kernel proofs of new statements. R28–37 actual local Weil module, R38 shared inverter, R44 original assignment compression and R46 padding remain the direct producers. No other Millennium or Monster endpoint reopened.

### R50. A single canonical CENTRAL sandwich family is sufficient, with same-object witness preservation

For q>=1 original variables set m=4(q+1)>=8. Let b(m)=sum_(j=1..3) binom(m,j), N=N_m=sum 2^j binom(m,j), K=floor(N/2) (N even). Fix added variables q+1..m to zero using their actual singleton scopes, never modify their incompatible singleton bits. Call a pattern compatible if all its dummy coordinates are zero. There are
    A=b(m)+q*d_m+binom(q,2)*(m-1)+binom(q,3)
compatible selector coordinates: expand 2^|I intersect [q]| by subsets of active coordinates and count scopes containing each subset. In particular q<=m/4, d_m<=m^2/2 (m>=2), hence A<=(125/384)m^3+5m/6<=K for m>=8, since K=(2/3)m^3-m^2+(4/3)m. Of the N-A incompatible coordinates, m-q are forbidden dummy singleton bits and MUST remain zero; all others are inert under the fixed assignment. There is room for N_q distinct complemented copies plus K-A constant ones, because N-K>=N_q+(m-q); use N_q<=2q^3<=m^3/32 and m<=m^3/64. Fix compatible coordinates outside original scopes to one; copy original N_q bits t_i in their original scopes; reserve a distinct inert coordinate for 1-t_i; set K-A further inert bits to one; all remaining inert bits zero. Then total weight (A-N_q)+N_q+(K-A)=K independent of t. Dummy singletons are intact, and every original witness extends uniquely to (x,0^(m-q)). Explicit signed projection E: each output bit is input, its complement, or constant; O(N_m)=O(N_q) coordinate-size overhead for fixed factor m/q, counting explicit wire indices polynomial. Not monotone, because nonconstant monotone maps from full Boolean cube cannot land entirely in a constant-weight antichain.

Actual R36/44 isometry J appends dummy zeros. Pi_E(t)=J Pi_t J*, and J tensor I_P identifies actual Weil submodules, both S3 central idempotents and marked C3 projectors, all multiplicity counts W(E(t))=W(t). Exact witness inverse. Inert complementary bits are not dummy witness variables, nor erased mediator support: they affect selected weight but cannot affect the original constrained assignment fibre.

Define S_(m,K)(t)=[|t|>=K+1] OR ([|t|>=K] AND G_m(t)). G32 shows any ordinary circuit size s for G_m gives monotone circuit for S_(m,K) with polynomial overhead (construct D(t,u), replace u_i by [sum_(j!=i)t_j>=K], sandwich with the two thresholds). Conversely S_(m,floor(N_m/2)) evaluated on E(t) equals G_q(t), ordinary complemented projection overhead polynomial. Thus G in P/poly iff the SINGLE canonical central sandwich family has polynomial monotone circuits. Worst over all K no longer necessary. This is a nonuniform sufficient Clay separation route, stronger than direct P!=NP; uniform converse requires effective circuit construction, no unsupported equivalence between NP outside P/poly and P!=NP. Can instead use direct uniform original N4/N5 route. Same result in R32 positive support model with fixed trivial-type Boolean support and charged gates: support simulation gives reverse and AND/OR lift gives forward; arbitrary succinct high-dimensional rank gates are not free. G32 was the general sandwich equivalence; fixed central size and exact parsimonious same-object transport are the new crosswalk.

### R51. Actual exterior-power representation for the sandwich, not just a renamed truth bit

Let V=C^N with named selector-coordinate basis e_C and trivial Weil action. For t define T_t=span{e_C:t_C=1}, dimension w=|t|. For each original assignment x, P_x is the actual weight-b minterm, V_x=span{e_C:C in P_x}. All coordinate subspaces are actual subobjects of V; choose standard coordinate complement V_x^perp. For b<=K<=N define
    A_K(t)=direct_sum_(x in F2^m) [Lambda^b(V_x intersect T_t) tensor Lambda^(K-b)(V_x^perp intersect T_t)].
Then define actual W_F=Weil(Q3) representation
    M_K(t)=(A_K(t) direct_sum Lambda^(K+1) T_t) tensor P,
with P=1+U from R30, acting trivially on all wedge factors, and exterior convention Lambda^0 C^0=C, Lambda^r=0 above dimension. Keep the assignment-labelled summands (do NOT identify identical exterior basis vectors from different x). They embed via wedge product into separate copies of Lambda^K V, plus the distinct Lambda^(K+1) V summand; all source projectors/embeddings commute with the original central S3 and marked C3 phase idempotents on P. Let W(t)=#satisfying original assignments. With binomial zero outside its legal nonnegative range and first term zero if w<b,
    dim Hom_WF(1,M_K(t))=dim Hom_WF(U,M_K(t))
       =F_K(t)= W(t) binom(w-b,K-b)+binom(w,K+1).
Proof: first wedge is dimension 1 precisely when P_x subset t; on each such x the second available coordinate space has dimension w-b. On w<K both terms zero; w=K gives exactly W(t); w>K second term positive. Hence support F_K=S_(m,K). At w=K, actual assignment-indexed wedge bases give a canonical isomorphism up to fixed basis-order sign to the original R36 satisfying submodule, via x -> wedge of P_x followed by all remaining t coordinates. Fix standard coordinate ordering to normalize. Below K the zero representation is genuine empty object; on K it may be zero or inhabited; above K the extra wedge is inhabited regardless of actual witness relation, so must retain grade and origin if original SAT is the consumer. S_k=1 above K is not a SAT assertion. This is exact same-object exterior realization of the sandwich, not a free algorithm. Dimension of a wedge of a coordinate space is a binomial coefficient (support cheaply thresholded), but the sum over x and its joint marked incidence still costs work. Do not charge all x independently or allow a succinct high-dimensional exterior rank as one uncharged gate. Positive arithmetic DAGs computing F_K simulate monotone support, yet arbitrary monotone Boolean circuits need not compute F_K's exact multiplicities. Lower bound on exact count alone would not imply Boolean circuit lower bound.

### R52. Fourier coefficients: cheap bare witness polynomial, hard sandwich multiplicity coefficient

Treat selector coordinates as a separate Boolean translation carrier, not independent Galois automorphisms or a field map F2->F3. For H subset [N] use normalized Walsh coefficient fhat(H)=2^-N sum_t f(t)(-1)^|H intersect t| (can attach quadratic local character evaluation chi from R2 to each parity; label H external). Bare W(t)=sum_x product_(C in P_x)t_C has
    What(H)=(-1)^|H| 2^-b * #{x:H subset P_x}.
This follows by averaging each monomial: coordinates in H outside P_x cancel; those in P_x are forced t_i=1. Count is zero if the original falsifying patterns in H assign conflicting values to a common variable; otherwise 2^(m-|union of scopes in H|). Thus every individual coefficient can be computed in poly(N) exact bit operations. Inverse sum over H still exponentially many terms; coherent signs before evaluation do not eliminate cancellations on arbitrary input. Pointwise coefficient access does not give a polynomial algorithm for W or support W. This is more precise than raw spectral-rank counts.

For the first multiplicity term define the multilinear positive polynomial
    W_K(t)=sum_x sum_(J subset [N]\P_x, |J|=K-b) product_(C in P_x union J)t_C.
It equals W(t) binom(w-b,K-b) on Boolean inputs, and equivalently sum_(L subset [N], |L|=K) W(L) product_(C in L)t_C. Therefore the degree-K monomial coefficient indexed by H of cardinality K is W(H). The general Walsh formula is
    W_Khat(H)=(-1)^|H| 2^-K sum_x binom(N-|P_x union H|,K-|P_x union H|),
with invalid binomial zero. In particular at |H|=K,
    W_Khat(H)=(-1)^K 2^-K W(H).
Since e_(K+1)(t)=sum_(|L|=K+1)prod_(C in L)t_C, full F_K=W_K+e_(K+1) has
    F_Khat(H)=(-1)^K [2^-K W(H)+(N-K)2^-(K+1)]  (|H|=K).
This is an exact extraction of original witness multiplicity from ONE canonical coefficient, using the R50 central embedding H=E(t). Exact coefficient query of this weight-lifted multiplicity family is #P-hard under polynomial-time reductions: selector witness counting includes #3SAT via the explicit original clause-coordinate encoding, with unused coordinates absent, and R50 is parsimonious. In particular a polynomial algorithm for these exact rational coefficients implies polynomial SAT decision; the binary output length is polynomial because counts <=2^m and denominators powers of 2 of exponent <=N. No lower bound on arbitrary Boolean support from #P hardness. Bare W coefficient easy versus sandwich W_K coefficient hard is a precise loss of arithmetic simplification under degree-lift, not an assertion that every Fourier approach fails. Exact zero/inhabited test of W(H) on the selected layer can be expressed by subtracting the known exterior contribution (N-K)/2 after normalization, retaining the signed residual. Treat subtraction as genuine arithmetic work, not a positive support gate.

### R53. Why the known monotone CLIQUE theorem cannot directly reach the sandwich via monotone projections

General lemma: if f(e)=S_K(p(e)) for a monotone coordinate projection p (constants or unnegated input bits, allowing repetition), then projected weight w(e)=c+sum_i a_i e_i with a_i>=0. Every positive input must have w>=K, every negative input w<=K. Thus if distributions D_+,D_- supported on positive and negative inputs respectively satisfy E_(D_-) e_i > E_(D_+) e_i for EVERY essential input coordinate, no such projection exists: any nonconstant p has some a_i>0, giving E_-w>E_+w, contradicting E_-w<=K<=E_+w. It is enough that strict inequality holds for every coordinate used. Equivalently the two convex hulls of positive and negative input marginal vectors cannot be strictly ordered that way under the required nonnegative weight functional.

For CLIQUE_(n,k), 3<=k<n, choose uniformly relabelled k-clique plus isolated vertices as positive and uniformly relabelled balanced complete (k-1)-partite graph as negative. The negative edge count exceeds binom(k,2). Elementary proof: the (k-1)-partite graph with k-2 singleton parts and one part n-k+2 has edge-count difference from binom(k,2) equal to (k-2)(n-k)-1; positive except k=3,n=4, where balanced bipartite has 4>3. Balancing parts cannot decrease edge count. Therefore each negative edge marginal exceeds the positive marginal, and no nonconstant unnegated coordinate projection of this CLIQUE family to ANY S_K exists, regardless of selector padding or duplicated edges. This is not a barrier to general monotone reductions with nontrivial preprocessing, distributional/lifting arguments, or proving sandwich lower bounds by another method. It specifically excludes direct transfer of G22/G30 via their monotone coordinate projection and is consistent with R50's use of complemented inputs. A purely monotone projection to constant weight is already impossible by antichain; this argument also rules out varying projected weights for this CLIQUE family. No global lower bound on sandwich follows. G30 improves the full G and positive rep lower bounds but does not pay N5 in the new endpoint. Do not silently reuse its exponent for sandwich.

### R54. Actual local exact execution

Ran /tmp/langlands_r50.py and /tmp/langlands_wedge.py in local container Python; exact integer and Fraction arithmetic, no CI/native prover/field oracle. Counts: 396 central padding and witness-count comparisons (all 260 m=1,2 originals, 128 deterministic m=3 inputs +8 minterms), 260 bare Walsh coefficient comparisons, 222 degree-K Walsh coefficient checks, 1544 sandwich support checks, 4753 Turan density comparisons for 4<=n<=100, 3<=k<n; additionally 1544 explicit wedge-basis counts and 222 full F_K coefficient checks. All passed. The padding test evaluates only the original active assignments with dummy zero after checking every original dummy singleton, as justified by exact embedding, not brute force over all padded assignments. General claims are derived independently of finite checks. Reproduction (both actual scripts merged without changing their tested comparisons):
```python
from itertools import combinations,product
from math import comb
from random import Random
from fractions import Fraction
def scopes(m): return [I for j in range(1,min(3,m)+1) for I in combinations(range(m),j)]
def coords(m): return [(I,p) for I in scopes(m) for p in product((0,1),repeat=len(I))]
def b(m): return len(scopes(m))
def N(m): return len(coords(m))
def minterms(m):
    C=coords(m); ids={c:i for i,c in enumerate(C)}
    return [sum(1<<ids[I,tuple(x[i] for i in I)] for I in scopes(m)) for x in product((0,1),repeat=m)]
def count(t,P): return sum(p&t==p for p in P)
def fwht(v):
    v=v[:];h=1
    while h<len(v):
        for i in range(0,len(v),2*h):
            for j in range(i,i+h):
                a,c=v[j],v[j+h];v[j]=a+c;v[j+h]=a-c
        h*=2
    return v
def pad(q,m):
    C=coords(m); ids={c:i for i,c in enumerate(C)};old=coords(q)
    var=[ids[c] for c in old]
    good=[i for i,(I,p) in enumerate(C) if all(j<q or v==0 for j,v in zip(I,p))]
    gs=set(good);vs=set(var)
    inert=[i for i,(I,p) in enumerate(C) if i not in gs and len(I)>1]
    K=len(C)//2;A=len(good)
    assert A==b(m)+q*(1+(m-1)+comb(m-1,2))+comb(q,2)*(m-1)+comb(q,3)
    assert A<=K and len(inert)>=len(var)+K-A
    mask=sum(1<<i for i in gs-vs)+sum(1<<i for i in inert[len(var):len(var)+K-A])
    def emb(t):
        return mask+sum(1<<(var[j] if t>>j&1 else inert[j]) for j in range(len(var)))
    P=[sum(1<<ids[I,tuple(x[j] if j<q else 0 for j in I)] for I in scopes(m)) for x in product((0,1),repeat=q)]
    return emb,P,C,ids,K
rng=Random(20261124);padding=0;binary=0;coeff=0;support=0;proj=0
for q in (1,2,3):
    P=minterms(q);n=N(q);m=4*(q+1);emb,Ppad,C,ids,K=pad(q,m)
    inputs=range(1<<n) if q<3 else [rng.randrange(1<<n) for _ in range(128)]+P
    for t in inputs:
        T=emb(t);assert T.bit_count()==K
        assert count(T,Ppad)==count(t,P)
        for j in range(q,m):
            assert T>>ids[(j,),(0,)]&1 and not T>>ids[(j,),(1,)]&1
        padding+=1
for m in (1,2):
    C=coords(m);n=len(C);P=minterms(m);B=b(m);W=[count(t,P) for t in range(1<<n)];F=fwht(W)
    for H in range(1<<n):
        fixed={};ok=True
        for i,(I,p) in enumerate(C):
            if H>>i&1:
                for j,v in zip(I,p):
                    if j in fixed and fixed[j]!=v:ok=False
                    fixed[j]=v
        expected=(-1)**H.bit_count()*((1<<(m-len(fixed))) if ok else 0)
        assert F[H]==expected*(1<<(n-B));binary+=1
    for K in range(B,n+1):
        Wk=[w*comb(t.bit_count()-B,K-B) if t.bit_count()>=K else 0 for t,w in enumerate(W)]
        Fk=fwht(Wk)
        for H in range(1<<n):
            if H.bit_count()==K:
                assert Fk[H]==(-1)**K*W[H]*(1<<(n-K));coeff+=1
        for t,w in enumerate(W):
            wt=t.bit_count();actual=Wk[t]+comb(wt,K+1)
            assert bool(actual)==(wt>K or (wt==K and bool(w)));support+=1
for n in range(4,101):
    for k in range(3,n):
        sizes=[n//(k-1)+(i<n%(k-1)) for i in range(k-1)]
        neg=comb(n,2)-sum(comb(s,2) for s in sizes)
        assert neg>comb(k,2);proj+=1
assert (padding,binary,coeff,support,proj)==(396,260,222,1544,4753)
checks=totalcoef=0
for m in (1,2):
    n=N(m);B=b(m);P=minterms(m);W=[count(t,P) for t in range(1<<n)]
    for K in range(B,n+1):
        vals=[]
        for t,w in enumerate(W):
            ix=[i for i in range(n) if t>>i&1]
            wedges=[sum(1<<i for i in J) for J in combinations(ix,K)]
            dim=sum(count(J,P) for J in wedges)+len(list(combinations(ix,K+1)))
            expected=(w*comb(len(ix)-B,K-B) if len(ix)>=K else 0)+comb(len(ix),K+1)
            assert dim==expected
            vals.append(dim);checks+=1
        F=fwht(vals)
        for H in range(1<<n):
            if H.bit_count()==K:
                assert Fraction(F[H],1<<n)==(-1)**K*(Fraction(W[H],1<<K)+Fraction(n-K,1<<(K+1)))
                totalcoef+=1
assert (checks,totalcoef)==(1544,222)
```

### R55. Endpoint ledger (no new certification phase)

| Gate / phase | Deliverable | Status / producer -> consumer |
|---|---|---|
| R50 / B-C | central half-weight parsimonious projection, single-slice nonuniform equivalence and original Weil fibre | derived; G32, R44/R46, R38 -> R51 and N5 sufficient target |
| R51 / C | actual exterior-power sandwich representation with preserved marked phase/Hom multiplicity | derived; R30/R36, exterior interfaces -> R52 |
| R52 / C | exact bare Fourier coefficient formula, top-layer sandwich coefficient #P-hard extraction | derived; R2/R37, R50/R51 -> charged arithmetic observer; not decision lower bound |
| R53 / C | marginal obstruction to direct monotone CLIQUE-to-sandwich projection | derived; G22/G30/G32, actual selector weight -> avoid invalid lower-bound transfer |
| R54 | local exact tests | executed, no kernel/CI |
| R7a' / LGC4d / C | actual arithmetic consumer with cost-sensitive joint residual and central-slice support | exact target R51; efficient coefficient oracle not free; universal charge open |
| R7b' / LGC5 / C | universal shared nonlinear/quotient resource charge or a lower bound for monotone positive support computation of CENTRAL sandwich | OPEN P0; positive full-G lower bound not sufficient, R53 mandatory negative control |
| R7c / LGC6 / D | superpolynomial unrestricted separation via central sandwich or direct original uniform-machine N4/N5 | OPEN P0; central-sandwich route gives stronger NP not in P/poly |
| LGC7/N6 / E | original Clay endpoint | existing conditional consumer only |

### R56. Next substantive tranche

Attack the central sandwich support function on its actual marked exterior module, not another coefficient census. The degree lift exposes exact witness count in one coefficient, but Boolean support need not recover that count; any resource charge must apply to arbitrary Boolean monotone DAGs computing the sandwich, not only multiplicity-preserving arithmetic circuits. R53 rules out the existing direct clique projection, so seek a genuinely different approximation/lifting or uniform-machine argument; keep G30 stronger lower bound for the full G and R46 promised bands. A useful positive attack is a sound costed simplification of exterior-support contraction that survives the original central slice, which would be an algorithm for SAT by R50. No promotion from #P hardness to P vs NP, no field homomorphism, no invented Galois action on selector labels. Standard Fourier/exterior/CSP/complexity theory credited; DASHI/JMD and G28–32 ownership retained. No unrelated branch work or CI.

## 16. R57–R63 — affine hull and dual character descent, 3-adic Hermite precision and subexponential shortcut reconciliation (2026-11-24)

Stay on Langlands; read both current attached texts directly from mounted paths. Live other-worker #1548 d0d7d21873068fa4dc4957b24f810774163c3d53, #119 48f329a5b3ae372020f146ff68e50d51c238f9d3, matching blob 59fae07307670ad14bada57b7eb6c8cd6cd17ee3. Live Langlands #1549 d5222023331280549d5b6ddb89ce915e8974b910 / #120 afa8a6d16ac77bb540fd885c97fd2fec78403b48, matching blob 6f241c8c78d2fc157ba6608e743de691ad3ef807. No edits of other worker branches. G33 signed components, G34 component budget, G35 nonbijunctive backdoor, G36 stronger bounded-support projection no-go, G37 reported subexponential theorem transport remain their owners. G35 is a DECISION upper bound; a general bijunctive residual is not an affine residual and exact #2SAT is #P-complete (e.g. monotone negative 2CNF counts independent sets). Do not infer polynomial exact counting just from a 2-SAT decision shortcut. R57 extends G33 by all affine hull equations, R58 gives exact primal/dual Fourier counting, R59 gives actual p-adic interpolation precision, R60 uses new external algorithm authority conditionally.

Actual master source bodies reopened:
- DASHI/Information/PNFFiniteRankNullityBridgeExact.agda 964c9f7974fb115d76722fa87c1d17572dda39fe: centeredMatrixRankNullity, covarianceRankNullity, source-specific map with external rank-nullity authority. Not an existing GF2 solver.
- DASHI/Reasoning/DustNoiseWalshCanonicalAdapterExact.agda c6bab37a08ab38e90141f7ae41997695fa808755: fullProbeReconstruction/fullProbeIdentifiability, reuses finite 16-point rational Walsh owner; no promotion into arbitrary circuit proof or new YM work.
- DASHI/Core/QueryFactorisationSufficiency.agda 98c592232292bbb6c5f0df047c8df3fd42be30d3, existing FactorsThrough semantics.
- DASHI/Arithmetic/SixWheelCRTExact.agda 7f5648752595f796f16c7e6de68a557f77366fd0: actual CRT inverse; R19/R25 mixed-prime lift.
- DASHI/Foundations/PolynomialC3S3ReflectionParityFourierExact.agda 9a7a180555dad4a042b2978d576a66814b5fc15c: correct C2 Fourier over characteristic 3, not C3 averaging there. Reuse signed coordinate transport, not identification of all groups.
- R29 original actual S3 local extension and tame sign epsilon, R36/R44 projector/isometric source restriction, R50–52 exterior sandwich and coefficient formula, G33/R43 original parity/fixed-coordinate producers. Standard linear algebra, Fourier orthogonality and Hermite interpolation credited as classical; DASHI crosswalk is source-specific costed construction. JMD and other worker original attribution preserved.

### R57. Affine-hull compression of the same original assignment space

For each original scope I, nonempty A_I subset F2^I, compute all local equations h dot z = c which hold for every z in A_I. There are <=7 nonzero h per scope. Their common solutions are precisely aff(A_I). Lift to actual original coordinate labels and combine Mx=c; empty scopes or inconsistent system reject. All genuine satisfying assignments lie in this affine space. Gaussian elimination gives an injective parametrization x=x0+B y, y in F2^d, d=m-rank M. This incorporates G28's unary support and G33's parity constraints (each equation obtained from scope support), as well as genuine ternary parity, e.g. x1+x2+x3=1. Do not replace the remaining relation by its affine hull. Define J_B on named assignment basis by J_B|y>=|x0+B y>. Then J_B*J_B=I, original Pi_t factors through this affine fibre, J_B*Pi_t J_B=Pi_res and J_B Pi_res J_B*=Pi_t. J_B tensor I_P intertwines the original S3 Weil action (acts only on P=1+U), commutes with central and marked cubic sector projectors, preserves all actual Hom dimensions and exact witness count. On original central padded slice R50, same isometry followed by the marked wedge inclusion R51 yields the same exterior Hom count. Every affine-only instance has Pi_res=I, W=2^d; no enumeration. All linear equations are over F2, no field homomorphism to F3; arithmetic character values live in characteristic zero.

### R58. Dual character contraction with explicit resource charge

For each residual scope, write f_I(y)=1_{x0|I+B_I y in A_I}. The original local normalized Walsh coefficients a_I(h)=2^{-|I|}sum_{z in A_I}(-1)^(h dot z) are cheaply computed on <=8 patterns. Substituting the affine map yields
    f_I(y)=sum_{h in F2^I} a_I(h)(-1)^(h dot x0|I) (-1)^((B_I^T h) dot y).
Combine actual equal frequency labels B_I^T h, retaining signs and cancel exact zeros. A zero local function gives empty fibre; remove constant-one factors. Let L_I be a matrix with independent rows spanning the support frequencies of f_I, excluding zero from rank. k_I=rank L_I<=3. Then f_I(y)=g_I(L_I y) on the full F2^d, since L_I is surjective onto F2^k_I and each frequency has a unique coordinate relative to rows. This g_I is a Boolean function with <=8 entries, computed by small Walsh inversion; its normalized Fourier coefficients are the merged coefficients indexed by alpha_I. Stack L_I into L of s=sum k_I rows, rank r. The common local translation-invariance kernel is ker L: individual f_I(y+v)=f_I(y) for all y iff every support frequency pairs trivially with v. This is the largest translation subgroup preserving EVERY retained local factor, not necessarily largest preserving their product (cancellations or inconsistency may enlarge latter). It is a source-labelled consumer-sufficient quotient, not a rank lower bound.

Two exact equivalent contractions of the original Hom multiplicity:
    W = 2^(d-r) sum_{z in im L} product_I g_I(z_I),
    W = 2^d sum_{alpha in ker L^T} product_I ghat_I(alpha_I).
Proof first: fibre size of linear surjection L onto its image is 2^(d-r). Second: expand each Fourier factor and average over y, using character orthogonality. The sum retains only dual labels whose XOR-weighted frequency is zero. This is trivial-character projection on the external finite assignment translation group. The sign values +/-1 can be evaluated via the actual quadratic local Weil character epsilon at a fixed reflection (R30), but independent external frequency labels are NOT independent local Galois automorphisms. R30's actual ramified S3 P attaches after contraction and is not changed by it. Odd-odd contributions can become even, as in R31; the sum is signed, and local support nonvanishing cannot replace it. k_I=0 constant handling retains the zero mode.

Use unnormalized integer coefficients c_I(alpha)=2^k_I ghat_I(alpha). Then W=2^(d-s) sum_{ker L^T} product c_I, with exact final division if s>d. Each product bit length O(s), sum bit length O(s+d), exact Gaussian elimination over binary matrices and rank parametrizations charged poly(N). Primal enumerates 2^r, dual enumerates 2^(s-r), so deterministic exact count cost poly(N)*2^min(r,s-r), not independent cost for each original assignment/character. For each local factor compute its span coordinates in a chosen independent global row basis by Gaussian elimination (DO NOT enumerate full span to construct coordinates; test script does so only for tiny instances). Further exact direct-sum decomposition: connect global basis-coordinate indices which occur together in a factor's row representations. Each connected block uses disjoint independent global coordinates, so W=2^(d-r) product_B W_B, W_B the count on that block. Let r_B number of basis coordinates and s_B sum of k_I in its factors. Work poly(N) times sum_B 2^min(r_B,s_B-r_B) (include +1 for no blocks), not product of those costs. This is a constructive bound for chosen basis and graph, not a claim globally optimal decomposition or unrestricted lower bound. It supplies exact multiplicities, not automatically a compact original submodule basis or a same-budget witness extractor; witness recovery by conditioning needs its own repeated cost accounting.

Controls: one ternary parity constraint on six variables leaves d=5, r=s=0, W=32; disjoint three binary OR scopes on six variables leave d=r=s=6, three independent blocks with W=3^3=27, dual nullity zero. Dense complete collection of binary OR scopes has no affine constraints, full r=m and s=2 binom(m,2), yet W=m+1 (at most one zero). Thus both r and s-r can be large on polynomial-time count instances, even after this particular block decomposition. Do not charge primal/dual rank, nonaffine count, sign support or kernel dimension as unavoidable work. The remaining target needs semantic resource lower bound after arbitrary sharing. For central sandwich F_K on any weight w, combine computed W with binomial factors; at w=K equality F_K=W. Support outside layer decided by weight alone. No promotion of #P-hard coefficient to decision lower bound.

### R59. Actual 3-adic Hermite recovery and its precision loss (interpolation shortcut)

Reviewed actual OpenAI October 25 2026 revised source, https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex , Theorem 1.1 and overview of Sections 3–6: occurrence-specific rational polynomial linear replacements restore original clause variables at T=0; at positive integer probes i=1..Q grouped by bounded integer measurements; conditioning on measurements separates group sums; shifted-form corrections divisible by z are handled by truncated Taylor data, using inclusion-exclusion on <=J-1 fixed coordinates. This is source review, not full proof audit. We derive an independent exact p-adic final recovery rule for the SAME probe nodes, not assume changing to Teichmuller nodes preserves their measurement designs.

Write H(T) for the rational deformation of the actual count, H(0)=W, deg H<QJ; Taylor jet h_(i,k)=[z^k]H(i+z), k<J. For integral H define
    L_i(T)=product_(j!=i,1<=j<=Q)((T-j)/(i-j))^J,
    B_i(z)=product_(j!=i)(1+z/(i-j))^(-J) mod z^J.
L_i has order J at all other nodes, and B_i is the inverse of L_i(i+z) in truncated ring. Hermite CRT gives
    H(T)=sum_i L_i(T) [H(i+z) B_i(z)]_(<J) evaluated at z=T-i.
Degree <QJ and equality of all jets prove equality. At zero,
    L_i(0)=((-1)^(i-1) binom(Q,i))^J is INTEGER,
    H(0)=sum_i L_i(0) sum_(k+l<J) h_(i,k) [z^l]B_i(z) (-i)^(k+l).
Set lambda=(J-1) floor(log_3(Q-1)) for Q>=2, lambda=0 for Q=1. Each coefficient [z^l] B_i is sum of products of negative-binomial coefficients (integers) divided by products of (i-j) with total exponent l. Therefore v_3([z^l]B_i)>=-l floor(log_3(Q-1)); every final recovery weight w_(i,k) lies in 3^(-lambda) Z_3. Thus knowing INTEGRAL jets modulo 3^(h+lambda) suffices to reconstruct H(0) modulo 3^h. This is a sharper sufficient precision budget than charging full confluent Vandermonde determinant: L_i(0) is already integral. Compute scaled weights 3^lambda w_(i,k) as 3-adic integers, accumulate mod 3^(h+lambda), take canonical divisible residue and divide by 3^lambda. No rational infinite precision needed for this final step; polynomial number of ring ops in Q,J and precision bits, with truncated products and modular inverses of 3-adic units. If H rational, choose known positive integer scale D0 clearing all coefficients (e.g. D0=D^L for a common denominator D of replacement coefficients and total clause polynomial degree L); use jets of H'=D0 H. Then extra v3(D0) digits suffice, divide out its power of 3 and invert unit part. Exact rational local evaluation or denominator tracking of internal measurement reconstruction is still required: final modular rule does not prove arbitrary intermediate divisions valid modulo 3^h. Scaling may be polynomial bit length when original coefficients have polynomial bit length, as in reported rational source. Do not infer improved asymptotic contraction exponent from this final precision formula.

Since 0<=W<=2^d, choose 3^h>2^d (h=floor(d log_3 2)+1, or exact integer comparison). The residue of W then determines W and its nonvanishing. This is characteristic-zero 3-adic scalar computation, not reducing actual complex S3 irreps mod 3, not replacing norm subgroup membership with valuation, and not a field hom F2->F3. Over Q3 use original ramified P; coefficients of endomorphism traces are rational/3-adic scalars; h digits needed for exact count, not merely leading cubic phase. Actual R29 extension and conductor remain unchanged. The earlier R19/R25 CRT zero-mode boundary is retained.

### R60. Interpolation support no-go and exact published-bound transport

The recovery weights are genuinely signed. Even simple univariate H(T)=T vs H'(T)=1+T have identical support of every Taylor jet at all positive probes, while H(0)=0 and H'(0)=1. Example H(T)=T arises from genuine original contradictory unit clauses x and not x, with first occurrence unchanged and negative clause's variable replaced by (1-T)x: sum_x x*(1-(1-T)x)=T. H'(T)=1+T can be realized with a single positive literal replaced by (1+T)x. Thus a generic observer retaining only which probe jets vanish cannot recover even original SAT nonvanishing, although these tiny examples are not proof every algorithm's selected designs lose necessary support. They show why positive semiring recovery from probe supports alone cannot be presumed. Our 3-adic precision bound retains signed scalar residuals, not virtual dimensions of deformed representations. No claim deformed factors are actual Boolean projectors for T!=0. H(0) is trace on original Pi_t, but away from zero the arithmetic deformation is not that submodule.

External source Theorem 1.1 reports time poly(n+M)*2^{O_k(n log log n/sqrt(log n))}, polynomial space for fixed width, and bounded clause density time poly(n+M)*2^{O_{k,D}(n/sqrt(log n))}; Sections 3–6 rational interpolation route gives weaker n(log log n)^2/sqrt(log n) exponent, sharper bound by Appendix D tensor contraction. Distinguish reported theorem from independent audit; current turn read actual source sections, not whole proof. Independent source noting finite crossover limits: https://arxiv.org/abs/2611.00517 . G37 credit. After G33 parity component contraction (c variables), width stays <=3, so conditional reported upper applies poly(N)*2^{O(c log log c/sqrt(log c))}; do NOT apply directly with d from R57 since arbitrary affine coordinate substitution can turn each literal into a long parity. Encoding new parity auxiliaries can expand variable count; cost separately. Conditional exact count/exterior support on whole central family: w!=K trivial, w=K original width3 selector SAT on m variables, so deterministic bit-time poly(N)*2^{O(m log log m/sqrt(log m))}, with m=Theta(N^(1/3)); standard bounded-fanin circuitization may square time but keeps subexponential form. Valiant 1986, *Negation is Powerless for Boolean Slice Functions*, DOI 10.1137/0215037, https://epubs.siam.org/doi/10.1137/0215037 (classical Berkowitz antecedent) yields constant-factor monotone simulation plus O(N log^2 N). Thus conditional monotone size of central sandwich <=poly(N)*2^{O(N^(1/3) log log N/sqrt(log N))}; a lower-bound target claiming 2^{Omega(m)} on this family would conflict with reported algorithm. This does not imply polynomial size nor refute the full-G monotone lower bound of G30/R53; full G not a slice. G36's bounded-support extension rules out direct local preprocessing for the known CLIQUE projection, not all global monotone reductions. On parity-contracted inputs R58's exact Fourier/block algorithm is unconditional and can be chosen instead of reported algorithm when cheaper. Need general cost bound against both; do not add formal-certification prerequisite.

### R61. Local exact execution (actually performed)

Executed /tmp/langlands_r57.py in container, exact Python integers and Fraction; no CI, native prover or local-field oracle. 740 original selector inputs (all 260 m=1,2 and 480 deterministic random m=3..8), 489 consistent nonempty-affine-reduction cases, 366 block-level primal/dual comparisons with dual-nullity cap 14; three explicit controls as above. For Q=1..12,J=1..6: all 1,638 monomials of degree 0..QJ-1 tested Hermite linear weights, and 1,638 separate modular 3-adic recovery checks at h=8; denominator valuations checked for every weight. All passed. Tiny test enumerates span and brute force as oracle, not asymptotic algorithm. Reproduce exact weights and modular check:
```python
from fractions import Fraction as F
from math import comb
def conv(a,b,J):return [sum(a[i]*b[j-i] for i in range(j+1)) for j in range(J)]
def vp(n):
    n=abs(n);v=0
    while n and n%3==0:n//=3;v+=1
    return v
def weights(Q,J):
    out=[]
    for i in range(1,Q+1):
        b=[F(1)]+[F(0)]*(J-1)
        for j in range(1,Q+1):
            if i!=j:b=conv(b,[F((-1)**l*comb(J+l-1,l),(i-j)**l) for l in range(J)],J)
        L=F(1)
        for j in range(1,Q+1):
            if i!=j:L*=F(-j,i-j)**J
        assert L==((-1)**(i-1)*comb(Q,i))**J
        out.append([L*sum(b[l]*(-i)**(k+l) for l in range(J-k)) for k in range(J)])
    return out
checks=0
for Q in range(1,13):
    for J in range(1,7):
        w=weights(Q,J);loss=(J-1)*max([vp(j) for j in range(1,Q)] or [0])
        M=3**(8+loss)
        assert all(vp(v.denominator)<=loss for row in w for v in row)
        for deg in range(Q*J):
            jet=[[comb(deg,j)*i**(deg-j) if deg>=j else 0 for j in range(J)] for i in range(1,Q+1)]
            assert sum(w[i][j]*jet[i][j] for i in range(Q) for j in range(J))==int(deg==0)
            z=0
            for i in range(Q):
                for j in range(J):
                    a=w[i][j]*3**loss
                    assert a.denominator%3
                    z=(z+a.numerator*pow(a.denominator,-1,M)*(jet[i][j]%M))%M
            assert z%3**loss==0 and z//3**loss==int(deg==0);checks+=1
assert checks==1638
```
Affine/dual reproduction algorithm: enumerate original scopes I of size 1..3 in increasing size/lexicographic order, local pattern p in little-endian integer order; for m=1,2 enumerate every selector bitmask; for m=3..8 use Random(20261124), 80 cases each, start with all patterns, draw planted=rng.randrange(1<<m), pick rng.sample(list(A),min(len(A),rng.randrange(1,9))) scopes, keep each pattern with rng.random()<.6, add planted pattern in even cases. Use Gaussian elimination on every locally constant nonzero parity, reject empty/inconsistent, affine substitute, compute merged local Walsh coefficients as R58, use independent row basis and connect indices co-occurring in each factor, calculate each block primal count and dual count when s_B-r_B<=14, compare whole product times 2^(d-r) with brute-force original count. The actual executed script is local; the reproducer and construction above record the tests without claiming a native proof or certification of the asymptotic external theorem.

### R62. Endpoint-first ledger

| Gate/phase | Deliverable | Status / source -> consumer |
|---|---|---|
| R57/B-C | actual affine-hull projector compression; rank-nullity count on affine-only residual | derived; G33/R44 -> R58 |
| R58/C | exact dual-character contraction, common kernel and independent block count | derived; R2/R30 sign, R31, R52, FactorsThrough -> genuine charged shortcut and controls |
| R59/C | p-adic Hermite final recovery with explicit precision loss | derived; R19/R25 and actual reported probe/jet construction -> R60; no claim full preprint audit |
| R60/C | probe-support no-go, reported subexponential algorithm transport and central-slice size ceiling | derived support counterexample, external theorem-dependent time bound; G37 + Berkowitz–Valiant -> N4/N5 |
| R61 | exact local checks | executed, no CI or kernel |
| R7a'/LGC4d/C | joint ramified arithmetic residual beyond affine/dual/measurement compression | actual conditional algorithms and precise scalar consumer supplied; universal resource obstruction open |
| R7b'/LGC5/C | universal charged obstruction surviving signed dual sum, arbitrary quotient/shared circuit and interpolation/tensor shortcuts | OPEN P0 |
| R7c/LGC6/D | superpoly central sandwich monotone size or direct uniform-machine SAT lower bound | OPEN P0; cannot reuse full G's monotone bound or raw exponential dimension |
| LGC7/N6/E | literal Clay endpoint | conditional existing consumer only |

### R63. Next mathematical tranche

Do not initiate another rank/character census. R58 gives concrete bidirectional primal/dual cost and R59 supplies exact finite 3-adic recovery. Next inspect the actual shared-measurement design construction and Appendix D contraction in the reported preprint, identify precise paid parameters, and ask whether a new signed contraction or obstruction can be proved on the original central sandwich under those operations. A universal size lower bound would need to survive any alternative representation, not just these exact evaluation methods; a positive polynomial-time algorithm on central slice would solve original SAT via R50. Do not conflate finite coefficient reconstruction or #P hardness with Boolean lower bound. No unrelated Monster/YM/RH work; no new kernel certification requirement.
