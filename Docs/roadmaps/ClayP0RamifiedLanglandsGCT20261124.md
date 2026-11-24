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
