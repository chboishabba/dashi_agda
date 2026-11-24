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

## 17. R64–R70 — actual unramified occurrence grades and widespread active-coordinate reuse (2026-11-24)

Stay on Langlands. Read both current attachments directly using mounted paths /mnt/data/Pasted text.txt and /mnt/data/Pasted text (2).txt. Live other-worker heads #1548 e25853446aac2f9e20303e42899dfe71d1681653 / #119 e0e150cde49a6321de1a13ea5dc8a0882e4df4c8, identical blob 4ace4df1bf48d96d9dd51ac2d125d609762ea761. Live Langlands heads #1549 75fe88e1e1d856fbd3d3f93702792a7c28dbb8c0 / #120 b0c59146024cb81c3c7217b1e4582886b5c7e1a9, identical blob 7530e7e6f5f96c81d6b023eaa194c03e3ddba3ca. No edits to G worker or Monster. G38–41 credit: central sandwich, balanced-product arithmetic lower bound, lifted multiplicity lower bound, squarefree-trace restriction and width-two control. R29/R30 actual ramified S3 Weil parameter P=1+U; R32 positive support simulation; R33 marked-line quotient; R50 central padding; R51 exterior count; R57–60 exact affine/dual and interpolation controls remain direct producers. Classical prior art: Jukna, *Lower Bounds for Monotone Counting Circuits*, https://arxiv.org/abs/1502.01865 ; *Notes on Monotone Read-k Circuits*, https://eccc.weizmann.ac.il/report/2022/094/ (repeated occurrence in syntactically produced polynomial; our measure instead counts original-variable footprint of repeated selector coordinates). Standard LLC and conductor compatibility https://docs.magma-maths.org/ModularArithmeticGeometry/RepresentationsOfLocalFields/introduction.html ; Harris ICM 2002 https://www.imj-prg.fr/wp-content/uploads/2020/prix/harris2002.pdf . Do not claim general arithmetic-to-Boolean conversion or priority for classical grading, balanced decomposition or tensor categories.

### R64. Real Weil degree tag versus idempotent geometric support

For a formal accepting trace of a bounded-fanin monotone Boolean DAG, replace OR by addition and AND by multiplication. Positive integer trace monomials M=prod_C t_C^(n_C) retain degree D=sum n_C, support S=|{C:n_C>0}|, excess D-S. The support observer on 0/1 inputs does not retain multiplicities. Choose unramified smooth complex Weil character nu, trivial on inertia, nu(Frob)=3 for a fixed Frobenius convention. A selected input line carries nu; an unselected one is the zero representation; constants carry degree-zero trivial lines or zero. Direct sum and tensor on these SCALAR graded objects realize the evaluated nonnegative trace polynomial, with each trace contributing nu^D. Attach the original P only at the end (tensor P at each gate would change S3 constituents). For each fixed Boolean input the result is an actual finite-dimensional Weil representation with N=0:
    R_C(t)=direct_sum_j (P tensor nu^j)^{a_j(t)}
where a_j is the coefficient of z^j in the arithmetized circuit with active input t_i replaced by z*t_i. Marked fixed coordinates may instead carry degree zero. Hom_WF(nu^j,R_C)=C^{a_j}; likewise Hom_WF(U tensor nu^j,R_C) has that dimension, since U irreducible and a nontrivial power of nu cannot be its self-twist (determinant or finite Frobenius spectral modulus). All twists preserve the original inertia and cubic phase action, so a(U tensor nu^j)=5. P has one inertia-invariant line, U has none. Thus L(R_C,T)=prod_j (1-3^j T)^(-a_j). The poles at distinct 3^-j recover the occurrence-grade multiplicities IF exact local factor supplied. Conductor alone equals 5 sum_j a_j, not a degree discriminator. This is a concrete local arithmetic tag, not a free local factor algorithm, not new local Langlands correspondence, no field map between F2 and F3. The trace expansion may have exponential degree, coefficient length and dimension, so do not materialize or charge it as unavoidable work.

Truncated grade extraction has a charged symbolic implementation: for cap d, maintain homogeneous components of every gate through d; addition componentwise and multiplication by convolution. At most O((s+n+1)(d+1)^2) scalar arithmetic gates for a size-s bounded fan-in DAG with n input coordinates; no assumption coefficients explicitly small, this is formal arithmetic gate model. This computes degree d component even if actual max degree huge. It is a genuine implementation of isotypic grade selection on the actual evaluated modules, not a free rank gate. We will apply it only after fixing coordinates, with d<=b(q)=O(q^3).

There is a sharp categorical escape: a nonzero finite-dimensional actual representation B satisfying B tensor B ~= B must be a one-dimensional trivial character (dimension d^2=d, then chi^2=chi). In particular a nontrivial grade nu cannot be preserved under literal tensor AND plus exact idempotence. However on one fixed marked line nu the actual subspace intersection B_a cap B_b (a,b Boolean) realizes AND and subspace sum realizes OR at constant Boolean cost; both are honest equivariant operations. Alternatively twist a product of two selected grade-one lines by nu^-1 after the AND. These implement Boolean grade saturation, not multiplicity-preserving tensor grading. Thus exact local Weil operators by themselves do not ban reuse. For marked support sets A,B, union weight equals |A|+|B|-|A cap B|; a grade correction by nu^(-|A cap B|) reconstructs union grade when intersection supplied. Scalar degrees alone cannot determine overlap (equal singleton sets vs distinct singleton sets). This does NOT require all algorithms to track intersections explicitly.

### R65. Fixed dummy background, preserving the original minterm section without complementary inputs

Distinguish the hard constant-weight complemented padding R50 from a simpler monotone fixed-background section used ONLY for the trace theorem. Use q original assignment variables, m=4(q+1), N=N_m, K=N/2. For each dummy singleton keep allowed zero pattern on and forbidden one pattern off; other scopes touching dummies allow all patterns consistent with dummy zeros. Let A be total number of compatible coordinates (including all N_q original active bits); R50 establishes A<=K and inert non-singleton capacity N-A-(m-q), with N-K>=N_q+(m-q). Set a fixed background D of size K-b(q) outside the active coordinates, including all A-N_q compatible outside bits and fill K-b(q)-(A-N_q) inert bits. This is feasible since K>=A, N_q>=b(q), and N-K>=N_q-b(q)+(m-q). All added inert bits are incompatible with dummy zeros, so cannot affect witness sets. Same construction for width two: with q<=m/4, compatible A<=b_2(m)+q*m+binom(q,2) <= K_2=m^2 for m>=8, and N_q<=2q^2, giving same capacity. Hence section E0(t)=D union t_active satisfies
    |E0(t)|=K-b(q)+|t|,  W_m(E0(t))=W_q(t),
    Pi_E0(t)=J_pad Pi_t J_pad*.
This is exact same-object norm/projector and phase/Hom preservation by R44/R50, and is a MONOTONE coordinate projection, but NOT a reduction of full G to sandwich: above b(q) the sandwich automatically accepts. On E0(t) central sandwich equals
    f_q(t)=0 if |t|<b(q), G_q(t) if |t|=b(q), 1 if |t|>b(q).
At weight b(q), positive inputs precisely original minterms P_x (all 2^q). This section is actually easy (G27 O(N) checker H, with threshold b+1 OR H). This fact is mandatory control; no hard-source lower-bound transport from E0. A circuit C for actual full central sandwich restricts by constants to a circuit C0 for f_q; study accepting traces on exactly the original P_x in this section. Dummy-coordinate repetitions are irrelevant to this theorem. They become constants; do not claim a statement for arbitrary complemented embedding.

### R66. Partial idempotence repair and exponential widespread-reuse inequality

For any accepting trace on a minterm P_x, the distinct active selector support must equal P_x: smaller weight rejected. Define R(M)={C:n_C>=2} among ORIGINAL active coordinates, footprint U(M)=union_{C in R(M)} I_C subset [q], where I_C original scope. No independent charge per occurrence. For h<=q let X_h be the x for which SOME accepting trace of C0 has |U(M)|<=h. Pad U(M) to exactly h original variables U. Fix ALL selector coordinates on scopes I contained in U to the actual pattern x|I (1 on it, 0 on the other patterns). There are b(h) fixed ones. This removes all occurrences of those selectors at cost of constants; every remaining active coordinate occurs exactly once in the chosen trace. For each pair (U,a) with |U|=h and a in F2^U, form degree d=b(q)-b(h) homogeneous component of arithmetized C0 after this specialization. Reattach the monomial of the b(h) fixed ones, call result P_(U,a). Its formal size <=C (s+N_m+1)(b(q)+1)^2 for an absolute constant C (s size of original C). Every monomial of P_(U,a) has degree b(q); its support is accepted by f_q (setting all support bits to 1, other unfixed bits 0, respecting specialization). Thus support has cardinality >=b(q) and equals degree, so no repeat; that support must be an original minterm. No other fixed-scope polarity variables remain. Consequently P_(U,a) is a nonnegative homogeneous polynomial supported on a subset of original W_q's assignment monomials. Every x in X_h appears in at least one such polynomial. This covers with at most binom(q,h)*2^h marked grade repairs; use actual source scope provenance, not abstract cardinalities.

Re-prove the subset version of G39 balanced-product bound to avoid relying on exact coefficients. For any nonzero polynomial supported on W_q, homogeneous nonnegative arithmetic circuit of size S produces a support cover by at most O(S+N_q) balanced products A B, with each factor degree between b/3 and 2b/3 (q>=2, b>=3). Proof: choose an accepting parse tree for each monomial, descend through addition or through multiplication child of largest degree until first gate of degree <=2b/3; degree >=b/3 since parent >2b/3 and split binary. Homogeneous gates, zero branches ignored. For each selected gate, use union of all formal parse-tree contexts with one occurrence replaced by that gate's placeholder; substituting any monomial of the gate gives output monomial with nonnegative coefficient, so product support lies in output. Only need existence of these contexts, not a costed algorithm for constructing them. At most one support product per gate. Homogenization already gives actual homogeneous circuit. Each product must partition scopes into fixed two sets: fix one monomial of B, positivity and squarefree one-per-scope property force same complementary scope set for every A monomial; symmetrically for B. Let V_A,V_B be unions of their original variables. Since every pair occurs as a scope, at least one union is all [q]. Also b(|V_A|)>=b(q)/3, b(|V_B|)>=b(q)/3 and b(v)/b(q)<=v/q (binomial ratio termwise), so |V_A cap V_B|>=q/3. ALL cross-combinations must agree on overlap, so these shared original coordinates fixed across product, containing at most 2^(2q/3) distinct minterm monomials. Coefficients irrelevant. This holds for width two or three.

Combine: if beta_h=|X_h|/2^q, then
    beta_h <= C' (s+N_m+1)(b(q)+1)^2 * binom(q,h)*2^h * 2^(-q/3).
All sharing retained in homogeneous gate DAG and balanced cover. h=0 recovers squarefree-trace statement on this fixed section; h>0 permits arbitrary repeated occurrences within scopes on h original variables, and does NOT bound the exponent of any reused selector. Take h=floor(q/32); binom(q,h)<=2^(q H_2(h/q)), H_2(1/32)+1/32<1/3 (also follows from binom<= (e q/h)^h). Hence if s=poly(N_m), beta_h<=2^(-Omega(q)). For all but exponentially small fraction of actual original minterms, every accepting trace repeats active coordinates on >q/32 original variables (up to rounding). Since each repeated selector involves <=3 variables, every such trace uses >q/96 distinct repeated active selector coordinates, up to rounding. Conversely a family where every minterm has a trace with footprint<=q/32 requires exponential size in q=Theta(N_m^(1/3)). This is a restricted lower bound for concrete trace property, NOT an unrestricted Boolean lower bound. The theorem is on a fixed easy section, not a distribution over all central inputs. No charge of independent work per repeated coordinate; in fact the next gate proves why such a charge would be wrong. It strengthens the squarefree trace control by allowing arbitrary occurrence reuse localized to a small original-variable region and gives a linear (not merely q/log q) widespread footprint, because marked masks are indexed by original variables, not arbitrary subsets of N_q selectors.

### R67. Exact cheap width-two AND width-three control: order of repeated footprint is tight

Use G27 monotone checker H(t)=AND_I OR_p [t_(I,p) AND product_(i in I) t_({i},p_i)]. H is exact at weights<=b(q); H OR threshold_(b(q)+1) computes f_q in polynomial-size monotone gates for BOTH widths. Threshold can be built by standard O(N_q^2) DP or sorting network. At minterm P_x choose unique selected pattern for each scope. The explicit accepting parse term contains exactly original P_x as its support; all repeated selectors are singleton-scope bits, one per original variable, with multiplicity 1+d_q (the leading t_I plus every occurrence from a scope containing that variable, including singleton). This has q distinct repeated selectors and footprint q, even though total original scope count is Theta(q^3) for width3. Thus linear spread in R66 is attainable by a cheap concrete circuit, and C0 is known easy even for width3. Not evidence of unavoidable large work. Neither repeat count, occurrence degree, overlap size, conductor, nor #trace count by itself lower-bounds unrestricted total gate count. Need width-three-specific GLOBAL constraints on central slice outside fixed-background minterm section. G39/G40 formal lower bounds remain valid even on easy decision relations. Actual positive support computation with marked-line intersection and sum can erase occurrence grades while retaining Boolean semantics; R64 shows why a grade-preserving tensor restriction is not coverage of all Boolean circuits. Width-two implication reachability remains a separate full-family polynomial negative control.

### R68. Actual local exact execution

Executed /tmp/langlands_r64.py in container Python and SymPy, no CI/native prover. Results: 556 constant-background padding and witness-count comparisons across widths 2 and 3, q=1..3 (all q<=2 selector inputs, explicit q=3 fixtures); 78 specialization mask/grade filters on local checker; 28 explicit accepting minterm trace constructions; 14246 balanced scope partitions across widths 2 and 3, q=2..4; 729 exact distinct local Euler-denominator polynomials for grade multiplicity vectors a in {0,1,2}^6, with explicit 3-dimensional permutation matrices for original S3 inertia and invariant rank 1. Grade filters inspect H branch, threshold b+1 cannot contribute at cap b-b(h) because all its original terms squarefree of degree b+1 and at most b(h) selected bits are set to one. No evaluation of actual p-adic field oracle, no native proof, finite tests are algebraic regressions independent of general proof.

Compact reproduction of mask geometry, actual padding and explicit H traces, plus exact local grade signatures:
```python
from itertools import combinations,product
from collections import Counter
from math import comb
import sympy as S
def scopes(m,w):return [I for j in range(1,min(m,w)+1) for I in combinations(range(m),j)]
def coords(m,w):return [(I,p) for I in scopes(m,w) for p in product((0,1),repeat=len(I))]
def minterms(m,w):
    C=coords(m,w);idx={c:i for i,c in enumerate(C)}
    return [sum(1<<idx[I,tuple(x[i] for i in I)] for I in scopes(m,w)) for x in product((0,1),repeat=m)]
padding=traces=partitions=0
for w in (2,3):
    for q in (1,2,3):
        m=4*(q+1);C=coords(m,w);I=scopes(m,w);ix={c:i for i,c in enumerate(C)};orig=coords(q,w);pos=[ix[c] for c in orig]
        good={i for i,(J,p) in enumerate(C) if all(j<q or a==0 for j,a in zip(J,p))}
        fixed=good-set(pos);inert=[i for i,(J,p) in enumerate(C) if i not in good and len(J)>1]
        K=len(C)//2;extra=K-len(scopes(q,w))-len(fixed);assert 0<=extra<=len(inert)
        base=sum(1<<i for i in fixed)+sum(1<<i for i in inert[:extra])
        P=[sum(1<<ix[J,tuple(x[j] if j<q else 0 for j in J)] for J in I) for x in product((0,1),repeat=q)]
        Q=minterms(q,w);cases=range(1<<len(orig)) if q<=2 else Q+[0,(1<<len(orig))-1]+[p^1 for p in Q]
        for t in cases:
            v=base+sum(1<<pos[j] for j in range(len(pos)) if t>>j&1)
            assert v.bit_count()==K-len(scopes(q,w))+t.bit_count()
            assert sum(v&p==p for p in P)==sum(t&p==p for p in Q)
            assert all(v>>ix[(j,),(0,)]&1 and not v>>ix[(j,),(1,)]&1 for j in range(q,m))
            padding+=1
        idx={c:i for i,c in enumerate(orig)}
        for x in product((0,1),repeat=q):
            M=[]
            for J in scopes(q,w):
                p=tuple(x[j] for j in J);M.append(idx[J,p]);M.extend(idx[(j,),(v,)] for j,v in zip(J,p))
            assert sum(1<<i for i in set(M)) in Q
            assert all(len(orig[i][0])==1 for i,k in Counter(M).items() if k>1)
            traces+=1
    for q in range(2,5):
        I=scopes(q,w);B=len(I)
        for mask in range(1<<B):
            k=mask.bit_count()
            if 3*k<B or 3*k>2*B:continue
            U=set().union(*(set(J) for j,J in enumerate(I) if mask>>j&1));V=set().union(*(set(J) for j,J in enumerate(I) if not mask>>j&1))
            assert len(U)==q or len(V)==q
            assert 3*len(U&V)>=q;partitions+=1
assert (padding,traces,partitions)==(556,28,14246)
R=S.Matrix(3,3,lambda i,j:int(i==(j+1)%3));J=S.Matrix(3,3,lambda i,j:int(i==(-j)%3));E=(S.eye(3)+R+R**2)/3
assert E*E==E and E.rank()==1 and R*E==E and J*E==E
T=S.symbols('T');bases=[S.Poly(1-3**j*T,T) for j in range(6)];seen=set()
for a in product(range(3),repeat=6):
    p=S.Poly(1,T)
    for j,k in enumerate(a):p*=bases[j]**k
    key=tuple(p.all_coeffs());assert key not in seen;seen.add(key)
assert len(seen)==729
```
The 78 additional specialization checks used a concrete H + threshold gate DAG and truncated monomial-occurrence multisets: at each gate union supports under OR, concatenate/sort exponent multiset under AND, discard degrees >cap; for each U of each size and each a, substitute fixed-scope selectors to constants, cap=b(q)-b(|U|), verify every degree-cap H monomial is squarefree and after reattachment lies in original minterms. Actual script local; no claim of native kernel proof. Sum of distinct reported comparison categories 15637 (556+78+28+14246+729), overlapping categories not claimed independent trials.

### R69. Endpoint-first ledger

| Gate/phase | Mathematical deliverable | Status / producer -> consumer |
|---|---|---|
| R64 / B-C | actual unramified occurrence-grade Weil tags, local factor and charged homogeneous extraction | derived; R29/R30/R32, formal trace arithmetization, classical LLC -> R66 |
| R65 / C | fixed dummy-background section with exact original norm projector/Hom witness transport | derived; R44/R50/G27 -> R66; easy section, not hard monotone projection |
| R66 / C | partial idempotence repair, widespread linear original-variable reuse in traces of any small full central sandwich circuit on this section | derived restricted lower bound; G39/G41 -> actual overlap control |
| R67 / C | cheap polynomial explicit H and marked-line equivariant idempotence control | derived; width2 AND width3 easy section; refutes independent charge from repeat footprint alone |
| R68 | exact local tests | actually executed; no kernel/CI |
| R7a'/LGC4d/C | consumer-relevant width-three interaction beyond occurrence saturation on actual hard central inputs | open; R66 localized obstruction but R67 proves not endpoint |
| R7b'/LGC5/C | universal serial-safe charge under arbitrary idempotence/absorption, quotient, signed contraction, measurement/interpolation and sharing | OPEN P0 |
| R7c/LGC6/D | superpoly unrestricted separation via central sandwich or direct uniform-machine route | OPEN P0 |
| LGC7/N6/E | literal Clay endpoint | existing conditional consumer |

### R70. Next substantive direction

The new result allows an exponential arithmetic bound to survive arbitrary repetition localized to small original-variable sets, and explicitly proves why even linear spatial spread cannot pay global cost. Do not turn it into another mandatory representation phase. Need attack actual hard fixed-weight inputs from R50, not just easy minterms from R65. Characterize support-preserving idempotent/absorption shortcuts for original clause-overlap constraints and compare them against G35 width-two reachability and R57/R58 affine/dual algorithms. R59/R60 reported interpolation/tensor algorithm audit remains an independent shortcut control; no additional external proof audit performed this turn. The nonuniform sufficient endpoint is superpoly monotone size of one central sandwich, not formal multiplicity alone; direct uniform N4/N5 route remains sufficient and weaker. Standard source credit, DASHI/JMD ownership and G38–41 preserved; no unrelated branches or claim P!=NP.

## 18. R71–R77 — exact local-field Newton modes and Smith-optimal Cauchy tile contraction (2026-11-24)

Stay on Langlands. Read mounted attachments directly (G42–44 and R64–70). Live G42–44 #1548 cbc4dd1496c0a2a1e85044400d4a1c3251aa35c2 / #119 003733c92e00485c5ea08640cf4393582021c516, identical blob 85df78165b31c999e23568155b94480c517600bf. Live Langlands #1549 d70f6ff3ec7f57f3cedac262473f55f2a0a74b66 / #120 ec3e8df4f1532c9c03b432c9b34aa8f4126b4cde, blob c0299815fb96222d14546fcf9dbb28df7abe6ca5. G44 cheap canonical-minterm checker is a decisive control; no further minterm-only trace census. Work on actual general paired inputs J_q(t,1-t)=G_q(t) with source-preserving R50 embedding and R51 Weil Hom multiplicity.

Actual external source reopened: OpenAI, *The Exponential Time Hypothesis is False*, October 25 revised manuscript, build/quantitative-reduction.tex and build/quantitative-contraction.tex (https://github.com/openai/math/tree/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build), Appendix D tensor interface, packet packing, Cauchy deformation, integrality, tapered Hermite, cross modes, recursion identity. Source is a reported theorem, not a full independent proof audit. Classical Cauchy determinant, Newton forward differences, DVR Smith normal form and Legendre factorial valuation credited as standard mathematics; new contribution is exact specialization and charged factorization on the source's actual tiles. No claim of priority for general identities.

Reopened original DASHI owners: DASHI/Algebra/RamifiedLocalValuationSharpnessExact.agda at #585 head 2cb821df49890b51605d1b990ee0b497e490b88c, blob 833c9a5592ecf1a1664be34dae11032627359aea (not on master; ramifiedSharpCoefficientValuation needs supplied unit/branch factorization, supplied explicitly below); master DASHI/Arithmetic/SixWheelCRTExact.agda 7f5648752595f796f16c7e6de68a557f77366fd0; DASHI/Information/PNFFiniteRankNullityBridgeExact.agda 964c9f7974fb115d76722fa87c1d17572dda39fe (field rank-nullity boundary, not an existing DVR Smith proof); DASHI/Core/QueryFactorisationSufficiency.agda 98c592232292bbb6c5f0df047c8df3fd42be30d3 (FactorsThrough). R2 actual Q2(i), R29/30 actual ramified Q3 parameter, R36/50/51 original witness count, R59 Hermite precision, R64 occurrence grade distinct from valuation. Retain JMD attribution; no edits outside Langlands PRs.

### R71. Actual Appendix D arithmetic interface on general selectors

The original source's packet length L=2^a, grid {-L,...,L-1}, C(T)=prod_grid(T-j), and Cauchy deformation W_xy(T)=C(T)/(C'(0)(T-y+x)), satisfy W(0)=I. The original count is recovered from deformed contraction through Hermite reconstruction; the proof groups ports by one coordinate of a label, with cross terms expanded and truncated by 2-adic valuation. At an active probe T=t+2^(a+1)z, i=v2(t), split column tiles y=y0+2^(i+1)j, and optionally row tiles x=x0+2^(i+1)l. For a crossing pair in an unequal-symbol packet their i-th bits coincide, so v=v2(t-y0+x0)<=i. Then v2(T-y0+x0)=v, and
    W_(x0+2^(i+1)l,y0+2^(i+1)j)(T)
      = gamma/(u+A(l-j)),
    u=(T-y0+x0)/2^v a unit,
    A=2^(i+1-v), k=v2(A)>=1,
    gamma=C(T)/(2^v C'(0)).
The source integrality lemma gives v2(gamma)>=a+1-v (or gamma=0). Full tile length n=L/2^(i+1), with dummy/unused ports removed by restriction. For arbitrary residue-lift z in the source's unramified extension the same normalized valuation applies. All formulas below hold over the appropriate DVR, with p=2 and p uniformizer in that extension. Do NOT change the source to p=3 automatically: the packet flip and tapered recovery are binary-specific.

For general paired selector rails, t is the original constraint data, u_rail=1-t is padding and not an additional independent assignment variable. Original W(t) is contraction of local indicator factors with equality wires, equivalently the R36 projector trace. At central weight the actual R51 Hom multiplicity equals this count; same-object isometry R50 fixes dummy variables. Clause-network degree reduction and parity-test density reduction are the source's own techniques; no new asymptotic bound asserted merely from recoding. R71 concerns actual cross-group arithmetic in that contraction, not minterm trace repetition.

### R72. Exact Newton modes give extra factorial divisibility

For any prime p, u a p-adic unit, A divisible by p, and finite column j=0,...,n-1, set f(j)=1/(u-Aj). The exact forward-difference identity is
    Delta^b f(0)= b! A^b / product_(h=0..b)(u-Ah).
Proof by induction using difference of reciprocal products with adjacent intervals; at each difference factor (b+1)A is gained. Newton inversion on integer j gives
    gamma/(u-Aj)
      = sum_(b=0..n-1) gamma*b!*A^b/[prod_(h=0..b)(u-Ah)] * binom(j,b)
with binom(j,b)=0 for b>j. This is finite and exact, not a Taylor approximation. When u varies with row by A*l, remains unit and valuations are unchanged. For each tile replace ordinary power moments by shared column moments
    M_b(X)=sum_(real j) binom(j,b) X_j.
The coefficient on M_b has exact valuation e+k b+v_p(b!), where e=v_p(gamma), k=v_p(A)>=1 (assuming gamma nonzero). Thus at precision p^H, omit all b with e+k b+v_p(b!)>=H, and all b>=n. This is valid with missing ports by taking X_j=0. Integer binomials, unit denominators, O(n^2) elementary operations per tile (or incremental coefficient products), all residues mod p^H, bit complexity polynomial in explicit tile size and precision. The actual source's power-mode coefficient bound gains at least one valuation per degree; our exact Newton weights expose factorial divisibility and finite tile cutoff. No extra row subdivision needed for this one-sided formula if v,k,e vary by row: use the minimal valuation for common truncation and per-row exact coefficients. Retains row and column group labels, so legitimate local substitute for the shared linear forms in source. To claim an improved total recursion one must separately re-account all mode weights, packet entries, multiplicities, and inherited precision. Legendre v_p(b!)=(b-s_p(b))/(p-1); improvement in large-b weight is constant factor at fixed k, not new asymptotic exponent.

### R73. Complete Cauchy tiles have exact Smith spectrum

Let O be a DVR of characteristic zero with uniformizer p, v(p)=1, containing the integers, u unit, A valuation k>=1, gamma nonzero valuation e>=0. Consider complete n_r x n_c tile B_ij=gamma/(u+A(i-j)), 0<=i<n_r,0<=j<n_c, and n=min(n_r,n_c). For an r x r minor at distinct row positions I and columns J, Cauchy determinant gives
    v(det B_(I,J))=r e + k*r(r-1)
      + sum_(i<i' in I) v_p(i'-i)
      + sum_(j<j' in J) v_p(j'-j).
All denominator factors are units, so this is exact, no cancellation estimate. Integer Vandermonde product for any r distinct integer nodes divisible by product_(h=0..r-1) h!: determinant of integer matrix [binom(i,h)] equals Vandermonde divided by that product. Equality of valuations attained at contiguous indices 0..r-1. Therefore determinantal divisor valuation
    D_r = r e + k*r(r-1) + 2 sum_(h=0..r-1) v_p(h!), D_0=0.
By DVR Smith theorem the invariant factors have valuations
    E_j = e+2 k j+2 v_p(j!), j=0..n-1.
All finite, sorted strictly increasing. This proof constructs source-native unit times branch-power valuation rather than importing a generic sharpness claim. Rectangular complete tile covered. If arbitrary holes in row/column sets, same minor formula gives exact determinantal optimization by separately minimizing the two Vandermonde valuations, and D_r at least the complete bound; do not infer each individual exponent inequality solely from prefix-sum inequalities. For upper channel bound, simply restrict a complete-tile factorization. If gamma=0 all channels vanish. Unramified base change preserves exponents with same normalization; in ramified extension of index f normalized uniformizer valuation multiplies all exponents by f. E.g. Q2(i) v_(1+i)(2)=2, so exponents double and precision 2^H corresponds to uniformizer exponent 2H, leaving channel count unchanged. This is lattice valuation, not Artin conductor or R64 unramified Frobenius degree. The abstract formula at p=3 also applies over the ramified Q3 field with the analogous normalization, but gives no binary-to-ternary algorithm proof.

### R74. Exact minimum linear channel count at fixed precision and its scope

Over R=O/(p^H) let rho_H(B) be the least number of R-linear scalar channels through which the explicit tile map factors: B=UV with inner dimension rho. Smith form gives factorization with one channel for each E_j<H, all others zero. Conversely image of B requires exactly that many generators (image diagonal direct sum of ideals p^E_j R; reduce the image module by p times itself and count residue-field dimension). If B factors through R^r, im V is a submodule of R^r, generated by <=r elements over this principal ideal chain ring, so its image under U also generated by <=r. Thus
    rho_H(B) = #{j<n:e+2kj+2v_p(j!)<H}.
This is an exact restricted linear-information lower bound and constructive upper bound, not merely rank over residue field (which can be zero while nonzero torsion channels survive). It concerns exact uniform evaluation of the TILE MAP for arbitrary ports. Boolean ports include unit vectors, so any linear factorization correct on every Boolean port vector must agree on the full matrix. It does not exclude nonlinear summaries, output-specific contraction, dependence between ports, cancellations across packets or arbitrary circuit algorithms. Compute factorization by DVR modular elimination: select minimum-valuation nonzero pivot, swap row/col, invert unit part modulo remaining precision, eliminate row/column by quotients by pivot (exact divisibility); record elementary invertible transforms. O(n_r n_c min(n_r,n_c)) ring operations, polynomial bit overhead in precision. Keep row/column group separation by doing operations within complete single-group tiles; each retained rank-one component contributes a moment of the corresponding column group and weighted row vector in its target group. For holes restrict the completed factorization. Completing/splitting row tiles may increase overall number of modes, so optimizing each block does not assert an end-to-end gain over published one-sided packing. Example k=1,e=1,p=2,H=9,n>=8: geometric cutoff with exact starting e needs 8 degrees; Newton retains b=0..4 (5 channels), Smith exponents E_0=1,E_1=3,E_2=7,E_3=9,... so 3 channels. This is exact for complete tile, not an estimated compression ratio for SAT.

Source uses weight-budget enumeration. For comparison, if a hypothetical palette has c distinct available modes at each consecutive weight 1..B, then all 2^(cB) subsets of those modes satisfy budget P whenever c B(B+1)/2<P. Choosing B proportional to sqrt(P/c) (when P/c sufficiently large and palette extends that far) gives exp(Omega(sqrt(cP))) candidates for literal full budget enumeration. The source upper counting estimate is of that shape with c=O(M/D), P=O(MD/u). This is an exact combinatorial lower bound on enumerating an ideal filled palette, NOT an assertion that actual source instances have that palette or that every feasible monomial contributes; DAG sharing, degree restrictions, sparse terms and cancellation may remove them. Replacing weights by constant-factor larger Newton/Smith weights alone cannot change this abstract exponent order in the filled regime. Need new global contraction or structure-specific reduction of actual feasible support, not just valuation rescaling. Do not count candidates as mandatory work for arbitrary algorithm.

### R75. Actual local checks

Executed /tmp/langlands_r71.py locally with Python exact Fraction and SymPy determinant. 972 Newton reconstruction comparisons across p=2,3,5, k=1..3, units 1,p+1,2p+1, tile sizes 1..8, plus valuation and modular truncation assertions at H=1,2,3,5,8,13. 752 individual minor valuations for p=2,3, k=1,2, units 1,7, sizes 1..4, plus exact minimal determinantal divisor checks. 416 modular pivot/channel checks at H=1..13. 1252 actual source packet entry identities for a=1..4, i=0..a-1, t=2^i, z=1,2 and all same-i-bit row/column residues. Total 3392 counted comparisons, all passed, no CI or kernel proof. Reproduce core:
```python
from fractions import Fraction as F
from math import comb,factorial,prod
from itertools import combinations,product
from sympy import Matrix
def v(n,p):
    if not n:return float('inf')
    j=0;n=abs(n)
    while n%p==0:n//=p;j+=1
    return j
def vf(x,p):
    return v(x.numerator,p)-v(x.denominator,p) if x else float('inf')
def mod(x,p,H):
    x=F(x);R=p**H
    return x.numerator*pow(x.denominator,-1,R)%R
newton=minor=rank=actual=0
for p in (2,3,5):
 for k in (1,2,3):
  A=p**k
  for u in (1,p+1,2*p+1):
   for n in range(1,9):
    f=[F(1,u-A*j) for j in range(n)]
    d=[F(factorial(b)*A**b,prod(u-A*j for j in range(b+1))) for b in range(n)]
    for j in range(n):
     assert f[j]==sum(comb(j,b)*d[b] for b in range(j+1));newton+=1
    for b,z in enumerate(d):assert vf(z,p)==k*b+v(factorial(b),p)
    for H in (1,2,3,5,8,13):
     for j in range(n):
      assert mod(f[j],p,H)==mod(sum(comb(j,b)*d[b] for b in range(j+1) if k*b+v(factorial(b),p)<H),p,H)
for p,k,u in product((2,3),(1,2),(1,7)):
 if u%p==0:continue
 A=p**k
 for n in range(1,5):
  B=Matrix(n,n,lambda i,j:F(1,u+A*(i-j)));vals=[]
  for r in range(1,n+1):
   vv=[]
   for I in combinations(range(n),r):
    for J in combinations(range(n),r):
     value=vf(F(B.extract(I,J).det()),p)
     expect=sum(v(A*(j-i),p) for i,j in combinations(I,2))+sum(v(A*(j-i),p) for i,j in combinations(J,2))
     assert value==expect;vv.append(value);minor+=1
   val=min(vv)
   assert val==2*(k*r*(r-1)//2+sum(v(factorial(j),p) for j in range(r)));vals.append(val)
  E=[x-y for x,y in zip(vals,[0]+vals[:-1])]
  assert E==[2*k*j+2*v(factorial(j),p) for j in range(n)]
  for H in range(1,14):
   R=p**H;D=[[mod(F(B[i,j]),p,H) for j in range(n)] for i in range(n)];rr=0
   for t in range(n):
    w,i,j=min((v(D[i][j],p),i,j) for i in range(t,n) for j in range(t,n))
    if w>=H:break
    D[t],D[i]=D[i],D[t]
    for row in D:row[t],row[j]=row[j],row[t]
    fac=p**w;inv=pow(D[t][t]//fac,-1,R//fac)
    for i in range(t+1,n):
     c=(D[i][t]//fac)*inv%(R//fac)
     for j in range(t,n):D[i][j]=(D[i][j]-c*D[t][j])%R
    rr+=1
   assert rr==sum(x<H for x in E);rank+=1
for a in range(1,5):
 L=2**a;grid=range(-L,L);D=prod(-s for s in grid if s)
 for i in range(a):
  t=2**i;step=2**(i+1);n=L//step
  for z in (1,2):
   T=t+2**(a+1)*z;gamma=F(prod(T-s for s in grid),D)
   for x0 in range(step):
    for y0 in range(step):
     if (x0>>i&1)!=(y0>>i&1):continue
     den=T-y0+x0;w=v(den,2);assert w<=i
     u=den//2**w;A=step//2**w;g=gamma/2**w
     assert vf(g,2)>=a+1-w
     for x in range(n):
      for y in range(n):
       expected=gamma/F(den+step*(x-y))
       d=[g*F(factorial(b)*A**b,prod(u+A*(x-j) for j in range(b+1))) for b in range(y+1)]
       assert expected==sum(comb(y,b)*d[b] for b in range(y+1));actual+=1
assert (newton,minor,rank,actual)==(972,752,416,1252)
```
The modular elimination test counts pivots using row elimination; existence of both row/column transforms follows independently from the DVR argument. These are exact algebraic regressions, not a full implementation of the external algorithm, an actual p-adic oracle or an asymptotic benchmark.

### R76. Updated endpoint ledger

| Gate | Deliverable | Status |
|---|---|---|
| R71 | actual shared tensor Cauchy deformation on original paired input | source interface inspected; no full algorithm audit |
| R72 | Newton moment contraction with factorial valuation and finite tile cutoff | derived, checked |
| R73 | exact complete-tile Smith invariant exponents and ramified base change | derived, checked |
| R74 | minimum modular linear channel count; explicit factorization; filled-palette enumeration boundary | derived restricted bound, not circuit separation |
| R75 | exact local Fraction/SymPy regressions | executed |
| R7a'/LGC4d | actual globally support-preserving arithmetic contraction beyond local tiles | open; local tile maps characterized, global support not |
| R7b'/LGC5 | unavoidable global cost allowing nonlinear summaries, signed contractions, idempotence and arbitrary sharing | OPEN P0 |
| R7c/LGC6 | central sandwich superpoly or direct uniform SAT separation | OPEN P0 |
| LGC7/N6 | original Clay endpoint transport | existing conditional consumer |

### R77. Next substantive mathematical tranche

Move from full individual tile maps to actual consumer-specific contraction: (1) compute what rank-one mode products survive Boolean port/equality constraints and original local tensors, (2) seek exact joint low-dimensional quotient with original witness preservation or a barrier to such quotients, (3) test whether regrouping and shared signed recursions can avoid enumerating the entire filled-palette support. Do not require evaluation of the entire tile map from every SAT decision algorithm, nor charge the exact Smith spectrum as global cost. R74 is a sharp linear interface theorem, not general lower bound. The fixed-width subexponential theorem's full proof and implementation remain outside this partial audit; no exponent improvement claimed. G42–44 credited, R57–60 contraction/precision and R64–70 grades/cheap reuse controls remain admissible. No separate certification prerequisite; stay on Langlands, literal Clay endpoint P0.

## 19. R78–R84 — deterministic flag, dual symmetric square and exact rank-two local converse obstruction (2026-11-24)

Stay on Langlands. Read both mounted attachments directly: R71–77 and G45–48. Live G45–48 Agda #1548 head 08dad6fd61b5144d5329a024b44a5737d04b71a4, roadmap blob b59cb2b86687bcfd4495533b52b6c10c6acf7ef4; G48 Lean #119 head 20bb8b46381b as supplied by user attachment (not separately fetched this turn). Live Langlands Agda #1549 b5b345e833d92021e2f687981f62ae618dfb9942, Lean #120 e3e6d6a66349876ef5bc84e0ca0f8620edb5a59c, shared blob fb821059e5744459abf6df4401b51f01fc280dd8. Monster donor #1545 live 9838a134f2154732929b615028bfacb8265bba8c, roadmap blob 02821b90bf7e16e7c3b8c7bc831e30f686cf84bf; user's reported authentic GAP 12+Sym^2(12^dual) source-selection inspires the functorial same-phase construction ONLY. No Monster source family or matrix claims are re-certified here, no other branches edited. The actual rank-two parameter is our existing R29/R30, not a restriction of Monster.

Source producers reopened on master: DASHI/Foundations/PolynomialC3S3ReflectionParityFourierExact.agda 9a7a180555dad4a042b2978d576a66814b5fc15c (signed reflection coordinates, not a new local reciprocity theorem); DASHI/Core/ConsumerFibreRepairExact.agda 5bab8f89861559c14f3877acd5e11424b21a6a6d (necessary separation); DASHI/Core/QueryFactorisationSufficiency.agda 98c592232292bbb6c5f0df047c8df3fd42be30d3; DASHI/Moonshine/PenumbralSQModuleLift.agda dd1f89c24dc29f21d7030ac9799b1639ee5a3c35 (symmetric/exterior power interface, no imported complexity theorem). R29 actual totally ramified S3 extension of Q3, U standard 2-dimensional irrep with a(U)=5, N=0, R30 P=1+U, R36 original projector, R50 central embedding, R57/R58 exact count, R59 and R71–74 precision and tile contraction, G45/46 compiler and G48 forced flag are direct mathematical producers. Standard representation theory, local reciprocity/LLC, Deligne epsilon twist and multiplicativity credited, not new general local converse theorem. Verify epsilon twist authority: https://msp.org/ant/2016/10-6/ant-v10-n6-p04-p.pdf (unramified twist formula, sign convention irrelevant for quadratic twist); https://openmaths.org/courses/LG-GAL/local-l-factors-and-epsilon-factors.html ; LLC compatibility with pair gamma factors: Helm and Moss, *Converse theorems and the local Langlands correspondence in families*, https://pmc.ncbi.nlm.nih.gov/articles/PMC6413487/ section 7. This tranche derives an explicit source-specific collision and one-observer repair, not a universal computational lower bound.

### R78. Constant-cardinality deterministic truth graph on the locally-full core

For original q-variable selector t, let F_t(x) be the original clause-conjunction truth function; M=2^q and W(t)=sum_x F_t(x). Instead of G48's optional b=1 branch, build a deterministic gate evaluation graph with distinguished output b=F_t(x). For each gate use the usual width-at-most-three equivalence clauses for binary AND/OR or unary NOT (constant/empty-conjunction cases use a unit). Each assignment x extends uniquely to the gate variables and b, with no other assignments. Graph size polynomial in explicit selector length N_q. To keep topology independent of t if desired, compute the fixed circuit of all clause tests t_C OR not q_C(x) with t input variables pinned by unit constraints; the pin values are input data, not unknown variables. Apply actual G46 compiler: six-variable zero gadget with forbidden-pattern digits 16763747126132141175 in lexicographic triple order; private literal occurrence variables, two equality clauses padded by globally zero gadget coordinates; original gate clauses padded to distinct ternary scopes. All local unary and binary projections and affine hulls full, each triple allows seven or eight patterns. The unique extension property survives. Optional fixed-weight G46 paired inert clause construction may be applied to the uniform conditional source encoding; not needed for this theorem. R50 separate central embedding preserves the truth graph but does NOT retain local fullness of newly added dummy scopes.

Let Y_t be actual satisfying assignment set of emitted truth graph; D_t=C^{Y_t} with named source assignment coordinates. Write P_b for its diagonal idempotents marking b, not the previous P=1+U Weil representation. Then rank P_0=M-W, rank P_1=W, total M independent of t. Restriction x map is an actual bijection with all original assignments, unlike previous witness-only compression. Restricting to flag 1 recovers the actual original satisfying submodule via isometry. The flag query on this always-satisfiable, locally-full family is NP-complete even with known satisfying assignment (evaluate any x, no need to know its output ahead of evaluation). No assertion that every locally-full formula is a truth graph. G48 originally used a known b=0 witness and global affine hull; R78 uses deterministic graph to fix total dimension and supports both fibre counts.

### R79. Actual phase-matched dual symmetric square, with a hidden unramified tag

Let F=Q3, U the genuine R29/R30 standard irrep of the totally ramified S3 quotient of W_F. Let xi be the unramified quadratic character, xi(Phi)=-1 on fixed Frobenius, xi|I=1. Because inertia surjects onto S3, U|I is irreducible and a Frobenius lift Phi can be chosen to act trivially on U (multiply any lift by an inertia preimage of the inverse S3 element). Set V_b=U tensor xi^b. V_0,V_1 distinct: their traces at this lift are 2 and -2, or inertia Schur lemma forces any intertwiner to be scalar and then fails at Phi. V_b has the same inertia restriction and conductor 5; det V_b=det U=epsilon (tame sign), and V_b is self-dual. Use explicit standard matrices R=[[-1,-1],[1,0]], J=[[0,1],[1,0]], with R^3=J^2=I, JRJ=R^-1. Sym^2(U^dual)=1+U by S3 character identity, or invariant quadratic form and trace values (3,1,0) on identity/reflection/3-cycle. Since xi^2=1, Sym^2(V_b^dual)=Sym^2(U^dual)=1+U, actual functorial equality on chosen carrier. On marked C3 eigenline of phase zeta^k its dual square has phase zeta^(-2k)=zeta^k, exactly the same-phase mechanism in the Monster inspiration, while the mixed square has phase one. This is a two-dimensional Weil parameter, not the Monster 12D module.

Define B_b=V_b direct_sum V_b direct_sum Sym^2(V_b^dual). Doubling is essential for R80 epsilon cancellation; the ordinary V_b+Sym^2(V_b^dual) block alone does not give that cancellation. Each actual 7D block has N=0, determinant epsilon, conductor 15, inertia restriction 1+3U|I, and cubic phase multiplicities (1,3,3) for (0,+,-). Both share standard L(T)=1/(1-T). All are honest smooth finite-image complex Weil representations, no virtual negative multiplicities. The actual source-aligned parameter is
    R_t = direct_sum_(y in Y_t) B_{b(y)}
        ~= 1^{M} + U^{3M-2W} + (U tensor xi)^{2W}.
The direct sum is indexed by the original deterministic graph, not an independently chosen count. Named flag sectors can be recovered by actual Frobenius spectral projector (I-rho(Phi))/2, zero on invariant line and Sym^2 component, rank 4W. Because Phi chosen to act trivially on U, tr rho(Phi)=7M-8W. Cubic and all inertia action identical for every t at fixed q; determinant epsilon^M, a=15M, dimension 7M. Standard L(T)=(1-T)^(-M). No free matrix materialization: dim exponential and input is succinct original selector with compiler, not explicit matrices.

### R80. All rank-one twisted local factors fail, not just standard L

For ANY smooth quasi-character chi of W_F, U tensor chi and U tensor xi tensor chi are irreducible 2D, hence no inertia invariants: invariants are W_F-stable and a smooth irreducible rep of W_F/I_F=Z is one-dimensional. Both standard L-factors are 1, as are their dual L-factors. Their Artin conductors agree (xi unramified). Deligne unramified-twist rule at common additive character psi and Haar normalization gives
    eps(s, U tensor xi tensor chi,psi)
       = (-1)^{a(U tensor chi)+2 n(psi)} eps(s,U tensor chi,psi)
(up to reciprocal sign convention, same for -1). Thus the squares of these epsilon factors agree for every chi. Multiplicativity plus common symmetric square proves
    L(s,B_0 tensor chi)=L(s,B_1 tensor chi),
    eps(s,B_0 tensor chi,psi)=eps(s,B_1 tensor chi,psi),
    gamma(s,B_0 tensor chi,psi)=gamma(s,B_1 tensor chi,psi).
The same for R_t at fixed q, with all chi, every psi and corresponding same measure. Determinant and conductor independent. This is a full rank-one local-factor observer collision, even granting oracle access to infinitely many twists; not a computational lower bound. Two inputs at same q, empty conjunction versus contradictory unit pair, have W=M vs 0, yet identical such observer. Same holds on actual locally-full truth graph. Standard local converse theorems with adequate twisting ranks are not contradicted: here rank one is insufficient for high-dimensional parameter. By LLC each B_b corresponds to an actual GL7 parameter, and R_t to GL_(7M), preserving pair factors; rank-one equality already a known phenomenon in general, no novel universal local converse claim. Original resource question concerns succinct graph/selector representation, not computation polynomial in exponentially large 7M. No global automorphic representation asserted.

### R81. A single fixed rank-two probe repairs the exact original consumer

Take actual U^dual as a fixed 2D test parameter (GL2 supercuspidal via R30 LLC). On I, End(U)^I=C by irreducibility, with Frobenius acting +1 on this line; (U tensor xi tensor U^dual)^I carries xi. The remaining trivial summand of R_t tensored with U^dual has no I-fixed vector. Therefore
    L(R_t tensor U^dual,T)
      = (1-T)^(-(3M-2W)) (1+T)^(-2W).
It has a pole at T=-1 iff original SAT is true, and pole order 2W. The fixed rank-two probe is the minimal maximal twist rank for distinguishing THIS family: all rank-one factors fail and this rank-two factor suffices. No assertion about general minimal local converse rank. Exact first logarithmic derivative at zero also suffices:
    D=[T] log L(R_t tensor U^dual,T)=3M-4W,
    W=(3M-D)/4.
Here [T] log equals [T] L since constant term is 1. The Frobenius trace on the full actual module gives same information via (7M-tr)/8, but rank-two local factor is genuinely local Langlands pair observer rather than a newly named Boolean bit. The flag-1 projector rank or pole-presence decision, on succinctly supplied R_t graph recipe, is NP-complete, exact W recovery #P-hard via parsimonious source. A polynomial-time algorithm for the pole-presence query on this succinct promise family iff P=NP (membership via original witness, reduction above). Exact coefficient extraction #P-hard but does not imply superpoly support lower bound. In particular neither local conductor, local fullness, nor even all GL1 twists suffice as semantic quotient; actual rank-two repair is consumer-sufficient. This provides a uniform Clay-equivalent endpoint separate from the stronger nonuniform central-slice lower bound; it does not prove either endpoint.

### R82. Costed scalar consumer of the existing tile contraction

For each original x, the deterministic truth graph has unique y, so D=sum_y (3-4b(y)) =3M-4W, and tr=sum_y(7-8b(y)). Thus the required rank-two coefficient is a signed scalar tensor contraction on the SAME original graph, not construction of its full local factor rational function or all Smith modes from R74. Add a scalar unary terminal weight 3-4b to actual gate tensor network; use the same equality wires and local factors. At original deformation T=0 the R71 contraction gives D with this changed boundary tensor. Outside original parameter deformation need not retain honest dimensions. This terminal weight has fixed bit cost, respects fixed width (or one extra unary factor), and does not enlarge port dimension except any explicit output wire. Can also use directly b as terminal to compute W, so no hidden new algorithm. R71–74 source-specific linear full-tile channel lower bound cannot be imposed on this single scalar query without a separate global consumer argument. Any exact signed/interpolation algorithm computing W yields D at polynomial extra cost, and conversely. This is an exact forward/reverse reduction for the scalar arithmetic consumer, NOT a claim of paid rank-two oracle.

At p=3, 4 is a unit, so D modulo 3^h with 3^h>M recovers W exactly using W=(3M-D)/4 mod 3^h. At p=2, need two additional digits: D modulo 2^(q+3) suffices because W<=2^q, quotient after division by 4 modulo 2^(q+1). For full trace the loss is 3 binary digits, none at p=3. In the actual binary Appendix D algorithm keep p=2 and inherited reconstruction precision; R59 general p-adic Hermite recovery adds its precision losses, not automatic ternary replacement. This reduces output information to O(q) digits, not total contraction time. It shows rank-two consumer repair can be represented at low output bit width even though it is globally hard; information-size or channel census alone cannot close N4. Full local factors may be huge even in this fixed finite-quotient family. No end-to-end subexponential exponent improvement claimed.

### R83. Local exact execution

Actually ran /tmp/langlands_r78.py locally in Python and SymPy. 36 group-product symmetric-square checks, 6 exact character identities, 2 inertia projector identities/ranks, 54 truth-graph compiler cases with independent DPLL counts of both flag fibres (108 fibre comparisons), 3970 emitted clauses checked for three distinct variables and unique scopes, 132 rank-two count/trace/3-adic reconstruction cases (all W=0..2^q for q=1..6); all passed. The six-variable source gadget checked all 64 assignments. No actual local field or epsilon-factor oracle run; R80 is a proof using classical unramified twist theorem, not numerical root-number verification. No CI or native proof assistant. Reproduction:
```python
import itertools as it
import random
import sympy as S
R=S.Matrix([[-1,-1],[1,0]]); J=S.Matrix([[0,1],[1,0]])
assert R**3==S.eye(2) and J**2==S.eye(2) and J*R*J==R.inv()
def sym2(A):
 a,b,c,d=list(A);return S.Matrix([[a*a,a*b,b*b],[2*a*c,a*d+b*c,2*b*d],[c*c,c*d,d*d]])
G=[R**i*J**j for i in range(3) for j in range(2)]
for A in G:
 assert S.trace(sym2(A.inv().T))==1+S.trace(A)
 for B in G:assert sym2((A*B).inv().T)==sym2(A.inv().T)*sym2(B.inv().T)
I4=sum((S.kronecker_product(A,A.inv().T) for A in G),S.zeros(4))/6
I3=sum((sym2(A.inv().T) for A in G),S.zeros(3))/6
assert I4**2==I4 and I4.rank()==1 and I3**2==I3 and I3.rank()==1
for b in (0,1):
 V=(-1)**b*S.eye(2); B=S.diag(V,V,sym2(V.inv().T));assert B.det()==1 and B.trace()==3+4*(-1)**b
Z=[tuple((i+1)*(-1 if (int(k)>>j)&1 else 1) for j,i in enumerate(I)) for I,k in zip(it.combinations(range(6),3),'16763747126132141175')]
def sat(F,x):return all(any(x[abs(l)-1]==int(l>0) for l in C) for C in F)
assert [x for x in it.product((0,1),repeat=6) if sat(Z,x)]==[(0,)*6]
def graph(q,F):
 C=[];nextid=q
 def gate(a,b,op):
  nonlocal nextid
  nextid+=1;y=nextid
  if op=='or': C.extend([(-a,y),(-b,y),(a,b,-y)])
  else:C.extend([(a,-y),(b,-y),(-a,-b,y)])
  return y
 out=[]
 for cl in F:
  a=cl[0]
  for l in cl[1:]:a=gate(a,l,'or')
  out.append(a)
 if out:
  a=out[0]
  for l in out[1:]:a=gate(a,l,'and')
  nextid+=1;b=nextid;C.extend([(-a,b),(a,-b)])
 else:nextid+=1;b=nextid;C.append((b,))
 return nextid,b,C
def compile_full(n,F):
 C=Z[:];a=6+n
 for cl in F:
  L=[]
  for l in cl:
   x=6+abs(l);a+=1;C.extend([(-x,a,1),(x,-a,2)]);L.append(a if l>0 else -a)
  L+=list(range(1,4-len(L)))
  C.append(tuple(L))
 assert all(len(c)==3 and len(set(map(abs,c)))==3 for c in C)
 assert len({tuple(sorted(map(abs,c))) for c in C})==len(C)
 return a,C
def count(n,F):
 def rec(C,remaining):
  while True:
   if not C:return 1<<len(remaining)
   if any(not c for c in C):return 0
   unit=next((c[0] for c in C if len(c)==1),None)
   if unit is None:break
   remaining=remaining-{abs(unit)};C=[tuple(z for z in c if z!=-unit) for c in C if unit not in c]
  v=min(abs(z) for c in C for z in c)
  return sum(rec([tuple(z for z in c if z!=-l) for c in C if l not in c],remaining-{v}) for l in (v,-v))
 return rec(list(F),set(range(1,n+1)))
rng=random.Random(20261124);cases=clauses=0
for q in (1,2,3):
 pool=[tuple(i*s for i,s in zip(I,sg)) for k in range(1,q+1) for I in it.combinations(range(1,q+1),k) for sg in it.product((-1,1),repeat=k)]
 FF=[[],[(1,),(-1,)]]+[[pool[j] for j in rng.sample(range(len(pool)),rng.randrange(min(6,len(pool))+1))] for _ in range(16)]
 for F in FF:
  w=sum(sat(F,x) for x in it.product((0,1),repeat=q));n,b,C=graph(q,F);m,D=compile_full(n,C)
  assert count(m,D+[(b+6,)])==w and count(m,D+[(-b-6,)])==2**q-w
  cases+=1;clauses+=len(D)
assert (cases,clauses)==(54,3970)
counts=0
for q in range(1,7):
 M=2**q
 for w in range(M+1):
  A=3*M-2*w;B=2*w;trace=A-B
  assert (3*M-trace)//4==w and A+B==3*M
  assert 7*M-8*w==M+2*trace
  mod=3**(q+1);assert ((7*M-(7*M-8*w))*pow(8,-1,mod))%mod==w
  counts+=1
assert counts==132
```

### R84. Updated endpoint ledger

| Gate / phase | Deliverable | Status / producer -> consumer |
|---|---|---|
| R78 / B-C | fixed-cardinality locally-full truth graph with unique source extension | derived, exact DPLL; G45/46/48 -> R79 |
| R79 / C | actual unramified quadratic tag, phase-matched dual symmetric-square block | derived; R29/30 + Monster functorial inspiration, not Monster transport |
| R80 / C | complete rank-one twisted L/epsilon/gamma observer collision | derived using standard local-factor identities; FactorsThrough obstruction |
| R81 / C-D | one rank-two pair probe, exact pole/first coefficient, uniform Clay-equivalent succinct query | derived; no unrestricted lower bound |
| R82 / C | signed scalar terminal contraction and binary/ternary precision | derived; R71–74 full tile channel cost not automatically consumer cost |
| R83 | local exact execution | completed; no native certification |
| R7a'/LGC4d | actual global scalar consumer contraction beyond current arithmetic shortcuts | open; exact target R81; cannot charge full tile map or rank-one observer |
| R7b'/LGC5 | universal resource obstruction for rank-two pole presence under arbitrary nonlinear computation/sharing | OPEN P0 |
| R7c/LGC6 | unrestricted superpoly separation via central sandwich or direct uniform succinct local-probe query | OPEN P0 |
| LGC7/N6 | literal Clay endpoint | existing conditional consumer |

Next endpoint-first: work on actual scalar support contraction in R82, not a bigger representation or local-factor census. The marked phase and all rank-one factors are provably insufficient, a rank-two repair is exact but computing it is the original SAT problem. Need a width-three-specific obstruction surviving arbitrary signed contraction and Boolean idempotence, or a polynomial cost algorithm for the rank-two pole query. R57–60 affine/dual and reported subexponential algorithm, R71–74 local compression, G44 cheap minterm checker remain legitimate shortcuts. No further native certification phase, no unrelated work, no claim P!=NP. Retain original G45–48 and Monster source credit, DASHI/JMD attribution rules and classical LLC authority.

## 20. R85–R91 — weighted rank-two residue probe, exact zero/residual separation and indexed contextual hyperfabric (2026-11-24)

User explicitly requires zero mode/residual and time/k-indexed hyperfabric; stay on Langlands. Both mounted attachments read directly: R78–84 and G49–52. Live Langlands #1549 950852bf6615f1bc084f77e44cb41822f0690d7b / #120 64c2f1cd50911e664e803629601dc61a07dad154, blob 121ecaf579256167529b95784b4110cb2621175c. Live other-worker #1548 57c5bc5fe2604c9203a25562f1d91599e3f85921, blob 74a172e67e18677af55249b2fdd6ba688b2fe646; #119 be4988049c2c supplied by attachment, not separately fetched. G49–52 count/decision meet matrix, exact universal conjunction quotient and cheap nonlinear control credited. Actual H05 owner #1291 d8f05ff5fc68da3c918d50c67f00edecc1e62648, roadmap blob a40721dde3fa561f82abe80c5312363e18aee158; reopened exact DASHI/Core/GovernedIndexedResidualCubeExact.agda blob 42b70ebb7376813076934f2245ce6011b76f10c8, Cube (8 vertices/12 arrows), ExactFaces (six faces), ResidualFaces (not automatically correction), Index History Time Depth Frob Version. Master BalancedTernaryAntipodalResidualCodecExact.agda 2a5069418e25572f04941591dbc83334862c012d (dependent neutral residual versus oriented noncentral), ConsumerFibreRepairExact.agda 5bab8f89861559c14f3877acd5e11424b21a6a6d. Keep original H05 owner, no edits to #1291 or other worker, no promotion to native physical nine-DOF geometry or H07/H14 kernel. R78–82 original genuine ramified Q3 U and doubled dual-square B_b, R36 projector, R37 signed Walsh, R50 actual paired central source, R59 Hermite and R71–74 binary modular contraction are direct producers. Classical finite-field polynomial identity testing (Schwartz–Zippel), Teichmuller lifts, Fourier orthogonality and inclusion-exclusion are standard, not DASHI inventions; new construction applies them to the actual tagged rank-two local factor and indexed source. JMD attribution boundary retained.

### R85. Weighted local-converse probe: recover support without recovering full integer count

Let X=F2^q, b_t(x)=1_{x in V(t)}, M=2^q, and W_t= sum b_t. R78 deterministic graph has precisely one source extension for each x. Define the squarefree witness generating polynomial
    P_t(Z)=sum_(x in X) b_t(x) prod_(i=1..q) Z_i^x_i.
All coefficients 0 or 1, so it is formally zero over EVERY field iff original UNSAT. This polynomial retains source assignment labels, unlike W_t=P_t(1,...,1). No claim to compute coefficients in polynomial time. Fix a prime p and unramified coefficient extension of Q_p of residue size Q=p^d with Q-1>=4q (choose least such d). For alpha_i in F_Q^*, take Teichmuller lift z_i (order dividing Q-1) and choose a complex cyclotomic realization of these roots with a fixed prime above p and compatible p-adic realization. On the genuine original W_Q3, let eta_x be the unramified character with eta_x(Phi)=prod z_i^x_i=lambda_x. Coefficient prime p (including p=2) is NOT the underlying local field Q3 or its inertia. Define actual finite-image complex Weil representation
    R_t(z)=direct_sum_x (B_(b_t(x)) tensor eta_x).
Same dimension 7M, original cubic phase/inertia multiplicities retained; each x has identical rank-one twisted factors for either flag by R80 applied to chi tensor eta_x, so all rank-one L/epsilon/gamma factors of R_t(z) are independent of t at fixed q,z. Do not identify the representation or its contextual future. Rank-two first log coefficient is
    D_t(z)= [T] log L(R_t(z) tensor U^dual,T)
          = sum_x lambda_x (3-4 b_t(x)).
Thus exact zero-mode baseline A(z)=prod_i (1+z_i) and signed residual give
    (3 A(z)-D_t(z))/4 = P_t(z).
A(z) can itself be zero, e.g. character cancellation; keep D and residual, not divide by A or infer observed zero means source empty. This exact weighted trace uses finite-order unramified tags, not changing original ramification or inventing local Galois action on assignment translations.

At odd p, one p-adic digit in degree-d unramified ring suffices to recover P_t(alpha), since 4 is a unit; at p=2, evaluate D and A modulo 8 in that ring and take (3A-D)/4 modulo 2, well-defined. All lifts and weights computed in polynomial(q) bit time; e.g. at p=2 lift binary irreducible polynomial of degree d to Z/8; any representative a of nonzero residue has a^(Q-1) in 1+2R, whose fourth power is 1 mod8, so a^(4*(4^-1 mod (Q-1))) has residue a and is exact (Q-1)-root in R. Search for irreducible by trial finite polynomials degree O(log q) costs poly(q); no huge extension. This gives O(log q) output bits at fixed p, compared with O(q) for full count. Ring precision three binary digits is for final weighted scalar, NOT a claim that Appendix D intermediate reconstruction needs only three digits (its denominators/interpolation add losses); original binary algorithm must retain its own precision ledger. In a tensor graph attach product of unary weights z_i^x_i, and terminal factor 3-4b. Preserves bounded width, equality wires, unique source extension. At deformation zero gives D_t(z), not all tile channels. A weighted scalar contraction oracle with polynomial runtime would therefore yield an RP SAT algorithm, not deterministic P=NP.

### R86. Exact one-sided error and indexed amplification

Choose alpha_i independently uniform in F_Q^*. By Schwartz–Zippel on this subset, if P_t nonzero then probability P_t(alpha)=0 <= q/(Q-1)<=1/4. UNSAT yields zero always. Independent repetitions r reduce false negative probability <=4^-r. For a finite family of L indexed queries, common alpha sample is allowed; union bound across queries after independent r draws yields <=L 4^-r (no independence of queries needed). Choose r>=ceil(log_4(L/delta)). Adaptive queries require fresh randomness or a uniform bound over all possible queried inputs, not just actual path length. Keep sample identity, field prime/extension, lift, chart and precision in observer provenance. A single observed zero, even at every coarse rank-one factor, is not equivalent to empty source. Deterministic evaluation on all {a,b}^q for distinct nonzero a,b detects nonzero multiaffine polynomial by tensor interpolation, but exponential. No deterministic poly hitting set asserted; such a set plus poly weighted contraction would imply P=NP. Randomized shortcut is a real improvement of output precision, not a proof of faster overall runtime or unrestricted lower bound. Exact unweighted W remains #P-hard; randomized weighted nonzero query is sufficient for decision with one-sided error.

### R87. Time and k-indexed hyperfabric: actual source fibres, zero mode and signed residual

Use Index=(history h, event time tau, refinement/chart depth k, Frobenius iteration j, consumer version v) from actual H05 owner; tau is algorithmic event time here, not physical clock or Frobenius. Keep alpha/sample/precision as separate observer parameters. Original named assignment carrier X fixed, diagonal projector P_(h,tau,k) is source witness mask, with chart chart_(h,tau,k) a bijection to a labelled copy. Distinguish genuine refinement (new constraints) from invertible rechart. For chart permutation C, carry ALL source operators and weight diagonal Lambda by conjugation: P'=CPC^-1, Lambda'=C Lambda C^-1. Trace and exact signed weighted residual invariant. Nonidentity example x->x xor e_last, not a claimed C3^9 Singer action or physical map. Do not re-evaluate same coordinate formula for lambda after relabelling without transporting it.

For original source mask f_t, normalized Walsh coefficients fhat(h)=2^-q sum_x f(x)(-1)^(h dot x); actual assignment translation group external to local Weil group. Exact decomposition f = fhat(0)*1 + sum_(h!=0) fhat(h) chi_h. Zero-frequency multiplicity W=M fhat(0) is distinct from observed Fourier zero, signed residual and genuine empty source. Weighted polynomial P_t(z) is another (full, symbolic) lossless chart of f, not its single sampled evaluation. In particular two distinct single-witness masks 1_{x=0}, 1_{x=e_last} have same unweighted W=1, same all rank-one factors, same unweighted rank-two factor, but opposite sign on corresponding Walsh coefficient and different weighted P=1 vs Z_last. Context of authentic minterm distinguishes them by G51. This is a concrete collision even after the original scalar consumer has been paid: future/contextual consumers need more. Full symbolic coefficients recover f; G51 canonical sigma is smaller explicit source-coordinate representative, computing it Clay-equivalent, and original selector already O(N) bits. No requirement that every SAT decision algorithm reconstruct full f, sigma or kernel. G50/G52 count-to-support channel amplification is an explicit counterexample to rank-as-work.

For a monotone constraint history, P_(tau+1)=P_tau Q_tau, Q diagonal actual source survival mask. Loss L_tau=P_tau(1-Q_tau), mutually orthogonal over times. P_0=P_T+sum_tau L_tau, exact BIDI when labelled losses retained; trace versions W_0=W_T+sum loss counts and P_0(z)=P_T(z)+sum weighted losses. If nonmonotone revisions, retain gain and loss separately: P'-P=(1-P)P'-P(1-P'), no inference of chronology from signed net trace. Store labelled original masks/history and both signs even when their weighted difference is zero. A positive count loss is actual deleted fibre; weighted zero may be cancellation. Zero-mode baseline and source residual remain separately typed; neither chronological index nor k identified with unramified tag.

### R88. Six-face commuting source cube with joint residual, not first-failure identification

For a named source projector P and two commuting constraint filters Q,R (actual diagonal Boolean masks), define four pairwise orthogonal atoms
    A_ij=P Q^i(1-Q)^(1-i) R^j(1-R)^(1-j), i,j in {0,1}.
P=sum A_ij; PQ=A_10+A_11, PR=A_01+A_11, PQR=A_11. All weights and phases attach by actual trace/tensor. Exact mixed residual
    A_00=P-PQ-PR+PQR,
    trace Lambda A_00=P_P(z)-P_PQ(z)-P_PR(z)+P_PQR(z).
The two sequential first-loss ledgers are (A_00+A_01,A_10) for Q then R and (A_00+A_10,A_01) for R then Q. Same endpoint but labelled intermediate losses differ by shared double-failure atom A_00 (not paid independently twice). Without the joint atom, separate first-loss records cannot be identified. Scalar equality of endpoints cannot supply correction map. Preserve event IDs and chronological order outside commutative endpoint.

Actual finite cube axes x=apply named time constraint Q, y=apply named refinement constraint R, z=nonidentity chart transport C. At vertices retain original P,Q,R in current chart, set of applied event IDs, all applicable signed residual atoms, independent index; event maps add a label, chart map conjugates all masks/weights. The live projector is product over applied filters. x/y commute by diagonal products and event label union; x/z and y/z commute by equivariance. All six faces (two of each) and six endpoint paths have exact same labelled terminal source under these definitions. This instantiates the shape of existing GovernedIndexedResidualCubeExact in finite mathematics; no new Agda cube owner or kernel proof, no claim actual physical t/k or arbitrary noncommuting dynamics commute. Raw ordered histories not merged: carry original history as separate provenance, compare endpoint plus source-labelled joint residual under explicit identification. For noncommuting original source operations, face residual stays open, not declared zero by rechart. The exact difference above is a residual ledger on genuinely original selector masks; no physical 3/6/9DOF identification.

### R89. Joint future contexts and loss strata, not full interface cost

For independent contexts v, rank-two weighted first coefficient after adding context is 3 A(z)-4 sum_(x in V(t) intersect V(v)) lambda_x. For lambda_x=1 this is G49 count kernel after subtracting baseline. As t evolves, context-conditioned losses give exact telescoping: W(P_tau intersect V(v))-W(P_(tau+1) intersect V(v))=W(L_tau intersect V(v)). Full context response for an individual labelled loss reconstructs it (minterm queries), but a single terminal decision need not materialize those responses. For two monotone histories, mixed differences of W(P_tau intersect Q_k) equal trace of products of consecutive losses; disjoint atom partition has exact weighted analogue. Here Q_k is a second actual refinement filtration, not a pure chart index; use distinct labels for those notions. This is precise shared residual geometry rather than attributing independent work to every mode. G49–52 already exhibit exponential linear rank with cheap nonlinear support, so neither indexed number of contexts nor rank-one invisibility implies time lower bound.

### R90. Local execution (actual)

Executed /tmp/langlands_r85.py with exact Python polynomial ring arithmetic in (Z/8)[X]/f(X), mod2 field arithmetic, and original assignment bitmasks. 99 Teichmuller residue/root identities (degrees 3/4/5, irreducibles X^3+X+1, X^4+X+1, X^5+X^2+1); 1200 weighted trace/mod8 recovery comparisons across 150 bounded-width selector instances q=1..5, 8 independent samples each; 60 full residue-field grids q<=2 checked exact zero proportion bound; 150 four-atom residual ledgers; 900 six-face checks and 900 endpoint-path checks. All passed. No CI, native prover or local-field epsilon oracle; actual tests implement finite coefficient quotient, not full source Appendix D algorithm. Reproduction algorithm: use Random(20261124); for q=1..5 select least listed d with 2^d-1>=4q; represent ring elements d-tuples, multiply by convolution and reduce highest term using monic f, coefficients mod8 or mod2. For each of 30 cases, draw rng.choices(scopes,k=rng.randrange(9)), each forbidden pattern from rng.randrange(2); replace case 0 with empty clause list, case 1 with contradictory units. Enumerate source assignments in product((0,1),repeat=q) order. For each of 8 samples draw q nonzero field elements uniformly, lift by exponent 4*pow(4,-1,Q-1), compute lambda_x, A, D, verify each coordinate of (3A-D) mod8 divisible by4 and quotient equals direct mod2 witness polynomial. For q<=2 enumerate every (F_Q^*)^q point and verify SZ bound or all zero for UNSAT. Draw two rng.randrange(1<<(2**q)) masks Q,R (general diagonal contexts for cube control, not asserted arbitrary masks are width-three clauses); partition original P into four atoms and verify disjoint union, chart equivariance under index i xor1. Cube state=(P,Q,R, applied-label bitset,k); x and y OR respective label bits, z permutes all three masks by i xor1 and flips k. For each pair of axes compare both orders at base and opposite vertex; for all six permutations compare live endpoint to chart(P&Q&R). Test counts as above. Derivations for actual selector contexts are independent of arbitrary-mask finite control.

### R91. Endpoint ledger and next mathematical target

| Gate | Deliverable | Status |
|---|---|---|
| R85 | actual unramified weighted rank-two probe, all rank-one factors still collide; three-digit binary residue recovery | derived |
| R86 | randomized support detection at O(log q) output bits, one-sided error and indexed union bound | derived; oracle/runtime conditional |
| R87 | retained zero mode/signed Walsh residual, actual time gains/losses and separate k/Frob/sample labels | derived |
| R88 | six-face source-mask cube with nonidentity chart and shared loss atom, chronology retained | derived finite instance, no kernel/physical promotion |
| R89 | contextual mixed losses and G49–52 consumer boundary | derived |
| R90 | exact local regression | executed |
| R7a'/LGC4d | costed global weighted scalar contraction at sufficient precision | OPEN: output precision reduced but actual contraction/Hermite cost not paid |
| R7b'/LGC5 | unavoidable arbitrary shared nonlinear signed computation for original deterministic support query | OPEN P0 |
| R7c/LGC6 | original uniform separation or sufficient central sandwich lower bound | OPEN P0 |
| LGC7/N6 | original Clay consumer | conditional |

Next: exploit R85 weighted terminal in actual R71–74 binary packet recursion; reverse-solve inherited precision and contraction cost, not full exact count or full joint kernel. Need either polynomial deterministic support computation, or a genuine unavoidable standard-machine resource theorem; randomized RP shortcut is admissible and not equivalent to deterministic P=NP. Track all original zero/sign/residual, history/tau/k/Frob/version and sample/precision in source ledger; keep G50/G52 cheap nonlinear control. No further representation census, CI or native certification prerequisite; no unrelated work or P!=NP claim.

## 21. R92–R98 — sharp inherited Hermite precision, optimal linear taper and actual packet zero collision (2026-11-24)

Stay on Langlands. Read current mounted attachments directly: R85–91 and G53–55. Live Langlands #1549 8050f29facb1e55f132ad5338dcde87d4f03d57b / #120 e8f8b31242d1815801fa0605750572cf1b0b36ee, blob 42d51d72d5d12c7e3d4f124686efc7dedc88896a. Live G53–55 #1548 719d5ff1245d92a1da6a527d79ef62d1f44810a2 / #119 e04e9a0a426b791e6f6bab37b58e85a8f5e53f23, blob 6585482064f110e6e08afc3f7790ee4bffcf0b5a. G53 deterministic lcm residue zero criterion, G54 weighted single parity-bit consumer, G55 deterministic universal probe bounds are credited to the other worker. R85 weighted actual Weil parameter and rank-one collision, R86 randomized support, R87–89 indexed residual, R71–74 Newton/Smith tile channels, and actual H05 #1291 / GovernedIndexedResidualCubeExact (blob 42b70ebb7376813076934f2245ce6011b76f10c8) remain the producers. No other branch edits, no physical H07/H14 promotion. Classical Hermite interpolation, Gauss lemma for DVR polynomial content and bounded differences credited as standard. New result is a source-specific exact conditioning calculation and collision within its admissible degree/integrality class, plus a separate actual tensor negative control. Not a proof of necessity for all SAT algorithms.

Actual external source reopened: OpenAI October 25 revised manuscript, build/quantitative-contraction.tex, https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex (lines 1710–1828 Cauchy/integrality; 1830–1994 tapered Hermite; 1996–2076 inherited precision; 2096–2255 mode enumeration; 1496–1522 creation precision; 2360–2377 immutable descriptions). Partial source audit only, no full theorem audit. Keep M=wire count in this section, distinguish original assignment cardinality 2^q. Prime 2 coefficient field, p=precision in digits, t=interpolation node, tau=history event time, k=chart/refinement, j=Frobenius iteration, recursion depth separately indexed.

### R92. Exact Hermite origin functional and coefficientwise precision

Set L=2^a, alpha=2L, S={-L,...,L-1}, active nodes t with i=v2(t)<u, 1<=u<=a, M>=u. Degree bound B=M(2L-1). Source uses h=ceil(3M/u), multiplicities J_i=h(u-i), J_i=0 for i>=u, D_i=L/2^i. There are exactly D_i nodes of level i. For each active node t let E_t(T)=prod_(s active,s!=t) ((T-s)/(t-s))^J_v(s), and B_t(z)=[E_t(t+alpha z)^(-1)]_<J_i. Its constant coefficient 1; coefficient at degree l has valuation >=l, because each alpha/(t-s) is divisible by2 and negative binomial coefficients are integers. Write
    A_i = D_i sum_(j=1..a-i) (j/2^j) min(j,u-i)
        = sum_(j=1..a-i) (D_i/2^j) j min(j,u-i).
This is an integer. The source's exact valuation identity for E_t(0) gives v2(E_t(0))=-h A_i (not just >=-6hD_i). Proof directly count differences: s of lower valuation contribute zero; for each j=1..a-i, there are D_i/2^j nodes of valuation i+j and same number of nodes at distance valuation i+j from t; their multiplicity difference -h min(j,u-i), as given in source. Set c_i=a+1-i. If H_t(z)=F(t+alpha z), exact linear recovery weights on raw jet H_(t,k) are
    w_(t,k)=E_t(0) sum_(j=k..J_i-1) [z^(j-k)]B_t(z) (-t/alpha)^j.
Hermite identity F(0)=sum_t sum_k w_(t,k) H_(t,k). Since v2(-t/alpha)=-c_i, and B coefficients have depth >=j-k,
    v2(w_(t,k)) >= -h A_i - (J_i-1)c_i + (J_i-1-k).
For k=J_i-1, exact equality (single term, B_t(0)=1). Hence the maximum precision loss for the unrestricted linear jet functional is exactly
    Lambda_i=h A_i+(J_i-1)c_i.
Sufficient whole-node precision p_t=p+Lambda_i, rather than p+8hD_i+8M(a+1). This bound remains correct coordinatewise over the source unramified extension and truncated coefficient ring, since weights scalar rationals. For individual jets p+Lambda_i-(J_i-1-k) suffices (or compute exact weight valuations); no speed claim from individual jets because source reconstructs whole polynomial by unit-difference interpolation at common precision. Sharp as functional on independent jet coordinates, NOT proof sharp individually on actual degree/integrality-restricted polynomials. R94 supplies genuine simultaneous lower bound on that restricted polynomial class.

### R93. Reduce the actual taper multiplicity, retaining source degree and packing

Total jet count = h C where
    C = L sum_(i=0..u-1) (u-i)2^(-i)
      = L(2u-2+2^(1-u)).
Thus the minimum integer h for this linear taper to meet the Hermite degree requirement is
    h_* = floor(B/C)+1 = ceil((B+1)/C).
This retains exactly the same active nodes/packing/degree condition, with h_*<=ceil(3M/u). All source inequalities needed for the recovered precision remain valid because smaller h and exact Lambda_i are bounded by original values. No alteration of original packet construction. For any nonnegative level multiplicities m_i, m_u=0 and maximum adjacent decrement m_i-m_(i+1)<=g, telescoping implies m_i<=g(u-i); hence their total jet count <=g C. Therefore h_* is also the minimum possible maximum adjacent decrement among profiles meeting B+1 jet requirement on the same active levels, attained by linear taper. If monotone, normalized multiplier loss at each i contains the nonnegative j=1 term (m_i-m_(i+1))/2, so maximum normalized multiplier loss >=h_*/2. Linear taper has maximum <=6h_*, giving matching order in this class. This is a restricted profile optimality statement, not global minimization of all interpolation schemes.

For recursion the exact child precision p_child=p_parent+Lambda_i, and the source weighted-mode cutoff sum w_Z beta_Z < p_child may be replaced accordingly. Original child precision proof dominates the modified one, so reported asymptotic bound unchanged; changed entry creation precisions must be used consistently, not silently recompute previous tensor recipes at new precisions. Source R74 Smith and R72 Newton weights can still be used subject to actual packet/row-group constraints. Example (illustrative parameters, not claimed source asymptotic schedule) a=10,u=5,M=1000,p=1: L=1024, source h=600, h_*=248. At i=0 original budget 5003201, sharpened 1395486; i=2 original 1316801, sharpened 284944; i=4 original 395201, sharpened 31490. Exact integer calculation; not runtime or end-to-end benchmark. Source asymptotic regime D_i large vs u(a+1) and h_*=Theta(M/u) gives retained additive loss Theta(MD_i/u), even p=1.

### R94. A source-admissible whole-patch collision proving the order of the generic precision barrier

Let g=floor(M/u)>=1, r_i=g(u-i) for active i and zero otherwise. Define
    C_0(T)=prod_(s active)(T-s)^r_v(s), B0=v2(C_0(0)),
    H(T)=2^(-B0) C_0(T).
Degree = g C <= M(2L-1)=B: C=L(2u-2+2^(1-u)), g<=M/u, and L>=2^u>=u implies the deficit from 2ML is >=M. H(0) is an odd integer (unit). At every t in grid, local polynomial H(t+alpha z) has integral coefficients. Indeed v2-content of product is sum of contents of factors by Gauss lemma over Z2, so
    v2_content H(t+alpha z)
      = sum_(s active) r_v(s) min(v2(t-s),a+1) - B0
where v2(0)=infinity. At inactive t (including 0), valuation equals zero: every active s has strictly lower v2 than t. At active level i, self factor gives r_i(a+1-i), other nodes give -v2(E_t(0)) with h replaced by g. Thus
    H_i = g[(u-i)(a+1-i)+A_i] >= g D_i/2 >= M D_i/(4u).
The j=1 term gives the lower bound, including final active level u-1. All retained whole local polynomials, not merely their first few jets or values at a few sample points, vanish modulo 2^H_i. Yet original F=H and F=0 have different values modulo2 at T=0. For general requested p, compare 2^(p-1)H with zero; same probe residues whenever every node uses precision <=p-1+H_i, different origin residues modulo2^p. This proves that simultaneously lowering all active precisions to o(MD_i/u) cannot work for generic Hermite recovery under precisely the source degree and local integrality hypotheses, even for one-bit output. It does not show each individual node must have that precision if others are higher; it is a simultaneous scaled-budget obstruction. It also does NOT show H is itself an actual Cauchy-deformed tensor contraction polynomial. R95 is a separate stricter-class example.

Zero mode/original source versus observed zero is decisive: H(0) is an odd unit while the whole retained local patches are zero at stated precision. Refining their precision may reveal actual coefficient content; do not mark the original carrier empty. This is a FactorsThrough collision for the fixed modular recovery observer, not a standard-machine time lower bound. Exact valuation residual and source/refinement indices must be retained.

### R95. Actual Cauchy-deformed Boolean tensor obstruction, easy original source

In a full real L-slot packet with original Cauchy W_xy(T)=C(T)/(C'(0)(T-y+x)), at every t in S and in the local chart t+alpha z:
    W_xy(t+alpha z) mod2 = 1 if y=x+t is a real slot, 0 otherwise.
Proof: unmatched entry retains factor alpha z with at least one extra 2 after removing denominator content (source integrality). Matched entry omits that factor, remaining factors have constant odd parts and all normalized nonconstant terms even, so is constant 1 mod2. In each packet choose pins X=Y=b in {0,1}^L by unary tensors, so original contraction at T=0 is exactly one. Actual deformed polynomial is
    F_b(T)=prod_(row x) l_{b_x}((W(T)b)_x),
where l_0=1-z,l_1=z. At patch t, each row mismatch b_x != b_{x+t} (zero extend outside packet) makes its entire affine factor even. Therefore content >= Hamming distance between b and its zero-extended shift. All row factors integral even if additional cancellation occurs. Multiply across real packets. Compare with zero tensor contraction on same packet layout. Observations of all retained patches collide modulo corresponding mismatch depth, while original count differs.

Explicit construction: use u full packets with b^(i)_x = bit_i(x), one for each active level i. At t with v2(t)=i, all valid shift positions flip this bit. For outside interval, at most L/2 of the total ones are missing; more precisely mismatch >= max(L-|t|, L/2): if |t|<=L/2 valid rows alone give >=L/2, else outside rows contain at least |t|-L/2 ones, so total >=L/2. Thus for M=B_pkt*u*L wires in repeated families, every active probe has content >= M/(2u). Also a stronger existential example: choose one random bit pattern b uniformly. For any fixed nonzero t in S, expected mismatch L/2, since each valid pair uses distinct bits and outside positions compare to 0. Changing one bit changes at most two mismatch indicators. Bounded differences gives Pr(dist<L/4)<=exp(-L/32). Union bound over 2L-1 nonzero shifts is <1 for L>=512. Fix one such pattern and use it in every full real packet. Then all nonzero patch polynomials are divisible by 2^(M/4), including all active nodes, for fixed complete packet layout and M multiple of L. This proves Omega(M) simultaneous absolute child precision necessary for a generic origin recovery from those actual tensor patch residues, even when output is parity. Example uses only unary pins (and zero tensor for other input), easy direct O(M) original contraction. Applies to fixed legal full packet layout; not a claim that every chosen packing or arbitrary SAT instance exhibits that depth, and not a proof that actual tensor subclass needs the stronger MD_i/u generic bound. Source packetization may exploit original pin constraints before deforming; such shortcut must remain admissible. R95 separates actual source-native obstruction from R94 polynomial-class result.

### R96. Zero mode, signed residual, creation precision and t/k indexed ledger

G53 deterministic modular zero test using all moduli 4j does not automatically run through binary packet algorithm: it is over 2-power coefficient rings. Odd-prime or composite moduli require a new valid contraction producer or another CRT-compatible algorithm. R85 weighted and G54 parity consumers DO fit binary ring. At original T=0, the signed rank-two scalar D=3A-4P is unchanged. Use direct terminal b or weighted P rather than D if only parity needed (p=1); if signed baseline retained use p=3. Baseline and original source labels retained regardless of computational route. R92–95 show that shrinking p does not shrink additive inherited losses automatically. No new subexponential exponent claimed; G54 compilation has its own additional wire cost.

At each recursive node retain (history, tau, k, Frob iteration, consumer version, source tensor ID, creation precision p_c, recursion depth, probe t, weight sample, requested precision p, inherited Lambda_i), with separate chart vs precision refinement. R87–89 actual orthogonal gain/loss atoms and signed zero mode remain on the original source. For each active branch, precision budget telescopes exactly p_d=p_root+sum_ancestors Lambda_i, while each original source polynomial and recursive lift retains its creation precision. Source canonical lift is entrywise, not a ring map: e.g. 1+1=0 mod2, but canonical lifts sum to2 mod4. For residues a,b in R_p=Z/2^p and canonical section s:R_p->R_(p+d), exact defect
    s(a) op s(b) - s(a op b) = 2^p c_op(a,b) mod 2^(p+d)
for op=+ or multiplication, with unique c_op mod2^d. Coordinatewise analogous for unramified coefficient ring in fixed basis (multiplication followed by basis reduction, same ideal). Retain carry as dependent residual if comparing paths that perform arithmetic before versus after lift; it cannot be inferred from coarse observed zero. Pure coordinate permutation charts commute with coordinatewise canonical section; arbitrary signed linear chart need not, must keep actual defect. H05's fixed-precision source-mask six faces from R88 are not a proof of commutation with this new lift/refinement operation; exact face correction above for elementary arithmetic, no claimed physical or general cube commutation. This is a source-consistent carry ledger rather than requiring all SAT algorithms retain full exact precision or all residuals in a single consumer. The original source's creation-time canonical lifting is legitimate and can change high digits of deformed polynomial, but at original contraction it preserves required mod p semantics. Do not treat changed creation lifts as same high-precision object without source correspondence.

### R97. Actual exact local execution

Executed /tmp/langlands_r92.py and /tmp/langlands_r93.py locally using Python Fraction, integers and polynomial convolution. Results: 60 taper parameter/degree checks, 1608 exact node multiplier loss checks, 2064 patch content formula checks, 68 explicit rational polynomial content checks, 234 raw jet weight bounds, 196 packet shift cases with 2504 actual pinned row polynomial parity checks. Optimized profile: 225 parameter cases, 825 level checks, 58 exact monomial Hermite recovery identities with h_*, 7165 large-packet shift tests (fixed seeded bit patterns for L=512,1024,2048). Separate 131064 scalar modular carry reconstructions p=1..7 and extension d=1..3, all passed. No CI/native prover, no full source algorithm execution, no benchmark. Finite checks not a proof of general lower bound. Reproduction core (exact product / valuation; full script local):
```python
from fractions import Fraction as F
from math import prod
def v(x):
    x=F(x)
    if not x:return float('inf')
    n=abs(x.numerator);d=x.denominator
    return (n&-n).bit_length()-(d&-d).bit_length()
def mul(A,B,cap=None):
    n=len(A)+len(B)-1
    if cap is not None:n=min(n,cap)
    C=[F(0)]*n
    for i,a in enumerate(A):
        for j,b in enumerate(B[:max(0,n-i)]):C[i+j]+=a*b
    return C
for a in range(1,6):
    L=2**a;S=range(-L,L);alpha=2*L
    for u in range(1,a+1):
        for M in (u,u+1,2*u+1,4*u):
            h=(3*M+u-1)//u;g=M//u
            act={t:h*(u-int(v(t))) for t in S if t and v(t)<u}
            r={t:g*(u-int(v(t))) for t in act}
            assert sum(r.values())<=M*(2*L-1)
            B0=sum(r[t]*v(t) for t in r)
            for t in S:
                C=sum(r[s]*(a+1 if s==t else v(t-s)) for s in r)-B0
                if t not in act:assert C==0;continue
                i=int(v(t));D=L//2**i
                A=sum((D//2**j)*j*min(j,u-i) for j in range(1,a-i+1))
                assert C==g*((u-i)*(a+1-i)+A) and C>=g*D//2
                assert sum(act[s]*(v(t-s)-v(s)) for s in act if s!=t)==h*A
                assert h*A+(act[t]-1)*(a+1-i)<=8*h*D+8*M*(a+1)
for a in range(1,5):
    L=2**a;S=range(-L,L);alpha=2*L;den=prod(-s for s in S if s)
    for t in S:
        for i in range(a):
            b=[(j>>i)&1 for j in range(L)]
            shift=[b[x+t] if 0<=x+t<L else 0 for x in range(L)]
            if t and v(t)==i:assert sum(x!=y for x,y in zip(b,shift))>=L//2
            for x in range(L):
                row=[F(0)]*(2*L)
                for y in range(L):
                    if not b[y]:continue
                    W=[F(1,den)]
                    for s in S:
                        if s!=y-x:W=mul(W,[F(t-s),F(alpha)])
                    assert all(v(c)>=0 for c in W)
                    for j,c in enumerate(W):row[j]+=c
                if not b[x]:row=[1-row[0]]+[-z for z in row[1:]]
                assert (min(map(v,row))>=1)==(b[x]!=shift[x])
```
To reproduce optimized recovery: set C=L*(2*u-2)+L//2**(u-1), h=(B+C)//C, for each active node compute E_t(0), multiply truncated factors [1,alpha/(t-s)] with multiplicities, invert coefficient recurrence B_0=1, B_k=-sum U_l B_(k-l). Compute exact weights as R92. For (a,u,M)=(1,1,1),(2,1,1),(2,2,2),(3,2,2) and n=0..B check sum_t,k w_(t,k) binom(n,k)t^(n-k)alpha^k = 1_(n=0), term zero for k>n. Actual executed tests and proofs separate. All source results attributed correctly.

### R98. Endpoint ledger

| Gate | Deliverable | Status |
|---|---|---|
| R92 | exact Hermite node precision and raw-jet valuation profile | derived; exact tests |
| R93 | minimal linear taper and minimum max adjacent decrement | derived; verified source-compatible upper bound, no new exponent |
| R94 | simultaneous generic degree/integrality-class precision barrier with whole-patch zero collision | derived; Omega(MD_i/u) in scaled budget; not actual tensor subclass |
| R95 | actual full-packet unary-tensor zero collision, Omega(M) depth | derived; easy original source, fixed packing, no standard-machine lower bound |
| R96 | source-indexed creation precision and carry residual, original signed zero/weighted consumer | derived; H05 owner unchanged, no physical commutation promotion |
| R97 | exact local checks | executed |
| R7a'/LGC4d | joint consumer-specific arithmetic contraction that avoids generic origin recovery debt or exploits actual tensor structure | OPEN; final precision no longer proxy for internal budget |
| R7b'/LGC5 | unavoidable unrestricted cost of deterministic support under arbitrary alternative interpolation, nonlinear sharing and direct decision | OPEN P0 |
| R7c/LGC6 | literal Clay separation via original uniform route or sufficient central-slice bound | OPEN P0 |
| LGC7/N6 | original conditional consumer | existing |

Next actual mathematical target: bypass generic Hermite recovery by exploiting the restricted deformed tensor polynomial class or construct a new source-preserving contraction with no comparable precision amplification; fixed-packing pin examples are deliberately easy so an eventual lower bound must permit preprocessing them away. In particular investigate direct factorization of origin evaluation through actual tensor constraints/zero-support, rather than merely shrinking output p or counting all local channels. R94 establishes obstruction only to black-box polynomial patch recovery at too-small simultaneous scaled budgets; R95 gives a genuine actual-interface collision but lower absolute bound, not an unrestricted resource theorem. G53–55 modular/weighted/probe shortcuts and R87–89 exact history residual remain admissible. No new representation census, no certification detour, no unrelated branch work or P!=NP claim.

## 22. R99–R106 — source two-rail defect contraction, global floor complexity and binary/ternary local-field correction (2026-11-24)

Stay on Langlands. Read both mounted pasted attachments directly, R92–98 and G56–59. Actual live Langlands #1549 ef1661868132496f322b4054f7db427409e1070e / #120 e97832116b0ae028c8a354fa31e391907ab64492, shared blob 9eac2e92de0d22baf34ee9a46c6512bf66fafee8. IMPORTANT live G worker has advanced beyond attachment G56–59: #1548 549739130a81fbfb254a8f3d54df28246be8b68b / #119 e6a60428933be7f64ac2b662a6bd0fedb3b4c6e3, identical roadmap blob 8395076082289854f8f9609b67604285824470e9. Read actual G60–64: local multilinear degree, coherent alternate coefficient lifts, direct moment identity, exact Cauchy entry content, matching minimum per support pair. Reuse these, not duplicate them. G45/46 locally-full source, G48 global flag, G49–52 joint kernels and nonlinear rank escape, G53–55 low precision consumers, G56–58 low-order contextual source and indexed horizon, G59 clustered Hermite collision credited to G worker. Existing R78–82 genuine ramified Weil rank-two probe, R85 weighted witness polynomial, R87–89 indexed residual, R92–96 tapered precision, original H05 #1291 / GovernedIndexedResidualCubeExact (previously verified blob 42b70ebb7376813076934f2245ce6011b76f10c8) are direct owners. JMD attribution boundary retained; standard tensor-network basis changes, Walsh diagonalization, Smith forms and CNF bounded occurrence reductions are classical, no claim of novelty for those general tools. New source-specific derivation below concerns the two-rail monomial-support pair floor and inverse local defect kernel, not an unrestricted complexity theorem.

External original source reopened: OpenAI October 25 revised preprint, build/quantitative-contraction.tex, https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex, lines 1710–1828, actual W_xy and F(T)=sum_(X,Y) A(Y) B(X) prod_x l_(Y_x)((W(T)X)_x). At origin W=I. This is a partial source interface audit, not a full proof audit or runtime claim. No edits outside the existing Langlands PRs.

### R99. Actual two-rail source lift of the G61 moment contraction

Take original q-variable width<=3 constraints on scopes I_C, each with nonempty allowed relation R_C. Write E for labelled variable occurrences (i,C), n=|E|. Introduce two genuine binary tensor wires X_(e,0),X_(e,1) per occurrence, total M=2n. On row side, one variable vertex per i with local multilinear polynomial
    A_i(X)=sum_(b=0,1) prod_(e incident i) X_(e,b).
Column side one original constraint vertex per C with local polynomial
    B_C(X)=sum_(y in R_C) prod_(e=(i,C)) X_(e,1-y_i).
A and B are products over these disjoint local port sets, respectively; tensor entries are evaluations on Boolean local ports, not independent fictitious coefficients. If i isolated A_i=2, retain it as factor (or remove explicitly counting its free assignment multiplicity). In the nonisolated case every global monomial coefficient is +1, all A supports and all B supports have exactly n selected wires. Use explicit integer lifts (local creation precision sufficient to represent these actual nonnegative table entries); modulo2 canonical Boolean entries have the same odd multilinear supports, hence same floor-zero test, but do not use alternate lifts to claim higher-precision floors without tracking G60/R96.

At origin G61 sum over ports is exact:
    sum_X A(X) B(X)=sum_(x, (y_C in R_C)) 2^(M-|S_x union U_y|).
Each e agrees x_i=y_i iff the chosen rails are complementary and cover both; disagreement covers just one. Thus M-|S union U|=sum_C d_H(x|I_C,y_C). Define one-incidence defect kernel K_lambda(x,y)=lambda^[x!=y] with lambda=2 for actual Boolean summation. Then
    Z_t(lambda)=sum_x prod_C sum_(y in R_C) lambda^d_H(x|I_C,y).
    Z_t(2)=actual origin contraction, Z_t(0)=W(t), with 0^0=1.
For a single forbidden pattern p on d=|I_C| coordinates, the local sum is (1+lambda)^d-lambda^d_H(x|I_C,p). Free source variables and original witness labels preserved. The formal lambda-polynomial records all mismatch strata with nonnegative coefficients, but the binary evaluation 2 mixes them by valuation/carry; no free extraction of constant coefficient from arbitrary exact integer value. In particular Z_t(2) mod2=W mod2. Retain exact source zero mode separately, do not equate parity with SAT. This is a real origin tensor contraction in the source interface, not an invented auxiliary interaction.

### R100. Exact global floor = minimum number of violated original clauses

For fixed x, minimizing over allowed local patterns independently gives sum_C min_(y in R_C) d_H(x|I_C,y). For R_C all patterns except one p, this is 0 when x|I_C!=p, else 1; a full relation contributes 0. Thus
    min_(supported S,U) [v2(a_S)+v2(b_U)+M-|S union U|]
       = min_x number of violated original clauses.
For nonisolated variables use coefficient 1 on all supports as above. Isolated variables can be removed and their free count factor retained separately; don't charge it as defect. This is the EXACT global optimum of the per-pair G61/G63 valuation-floor problem at origin, not valuation of the sum, since the number of minimum terms may be even. Every zero-floor pair corresponds to exactly one satisfying x and vice versa (local patterns forced to x), so floor-zero support count is parsimonious. Optimizing the floor, or merely asking if some zero-floor pair exists, is NP-hard / NP-complete respectively, even uniform degrees n on each side and all monomial coefficients +1. The reduction uses arbitrary original clauses, then can retain the G46 locally-full promise. To make the reduction polynomial in EXPLICIT local table input size, first split every original variable's literal occurrences into copies and join by equality chain (two binary clauses per adjacent pair); every copy occurs in at most five clauses, and every original witness has a unique copy extension. Then G46 can use a separate six-zero gadget per original clause rather than one shared gadget: attach private occurrence copies, link equalities using that clause's own z0,z1 and pad its gate clause. Each local gadget has constant scope count and variables have bounded occurrence; each scope has 7 or 8 allowed patterns and all unary/binary/affine projections full. Unique extension and polynomial input length still hold. All two-rail vertex arities bounded by an absolute constant; explicit tables constant-size per vertex (no hidden unbounded-arity expansion). This variant is derived here, no claim of testing the entire compiler family anew. For ordinary bounded-occurrence CNF the simpler first split suffices. Global floor optimization is thus an actual hard operation if chosen as required by a pruning algorithm. It is NOT an unavoidable operation for any SAT algorithm; parity of minimum terms can cancel and other computation may avoid finding the minimum. G63 remains polynomial per fixed support pair.

### R101. Hard global support pruning on a genuine nonzero Cauchy patch can be an artificial deformation debt

Use four real slots per occurrence, grouped inside full packets of length L divisible by 4, no cross-packet shift needed for the selected rows. For e, slots 4r,4r+2 hold active row rails b=0,1; slots 4r+1,4r+3 are corresponding active column rails. Make odd row ports free (tensor 1) and both even column ports obligatory in one-port monomials. The column clause tensor chooses complementary odd rail for each occurrence. At actual probe t=1, G62 gives zero-content W only for column y=row x+1, and all other entries have positive integer valuation. The selected active even rows have exact unique zero-cost shifts inside their four-slot group. By G63 minimum for each pair is M-|U union shifted(S)|; positive-cost alternative matches cannot improve it. This equals original number of disagreed incidences. Therefore the global floor zero query on this actual fixed complete Cauchy packet interface at nonzero t is NP-complete by R100. The coefficientwise mod2 patch reduces to the truncated shift, so its contraction mod2 equals W(t_original) mod2. Use t_original as selector, t=1 as probe; do not identify.

At original deformation origin, however, active even row rails are already all covered by even columns, and exactly one odd rail per occurrence is uncovered regardless of x,y. Hence every term has defect n and
    F(0)=2^n * 2^q * prod_C |R_C|.
This is directly polynomial-time computable (bit length polynomial in explicit problem size). This is a stronger negative control: even NP-hard global pruning at a chosen actual shifted interface need not be necessary to compute original contraction. This construction specifies fixed full packet layouts and the source W/Boolean tensor formula. It does not establish that the external packing algorithm with its balanced-label schedule would choose this layout, or that a preprocessing-aware solver would deform this trivial disconnected origin network. No claim of a lower bound on that algorithm or original SAT from shifted cost. R94 generic Hermite collision is not shown to be realized at its full scaled MD_i/u depth on actual bounded-arity tensor instances; this tranche does not pay that open source attachment.

### R102. Exact local binary inverse recovers original weighted rank-two consumer with no inherited precision loss

K=K_2=[[1,2],[2,1]], det=-3. Let f_C in {0,1}^(2^d) be the actual original constraint table. Instead of restricting clause monomial supports to R_C, put signed coefficient vector
    beta_C=(K^-1)^tensor d f_C,
    K^-1=(1/3)[[-1,2],[2,-1]].
Use all patterns y as potential supports with those coefficients (omit zero). Then for each original x,
    sum_y beta_C(y) 2^d_H(x|I_C,y)=f_C(x|I_C).
The clause basis correction is exact over Q and over Z/2^H since 3 unit. For original width d<=3 the local transform and tensor table construction cost constant ring operations per bounded-arity table, polynomial in precision. Multiply each variable monomial for value b by the actual unramified weight z_i^b as in R85. Summation yields
    Z_corrected = sum_x prod_i z_i^x_i prod_C f_C(x|I_C)=P_t(z).
Original R85 signed rank-two D=3 A(z)-4 Z_corrected, A(z)=prod(1+z_i), retained separately. For binary weighted residue use coefficient ring of R85, inverse still exists since determinant odd. Can compute P directly mod2, or D mod8, no need for Hermite or high internal precision in these LOCAL transforms. Exact rational coefficients have only powers of 3 as denominators (per local table exponent<=d), can use finite-ring representatives; actual tensor entries agree at intended creation precision, preserve lift recipe. Negative signs are necessary for some tables; no independent charge per matching term, and no assertion that the corrected global contraction is cheap. The global computation is still a bounded-degree tensor contraction / original SAT-count consumer. This provides a direct arithmetic producer with no generic origin-recovery precision debt locally; apply G61 moments or graph separators when applicable, not an unrestricted polynomial solver.

### R103. Ternary coefficient prime has exact zero-mode depth and a locally-full source collision

Do not identify coefficient prime with original Weil field Q3 or Frobenius. Over Z_3, Walsh matrix on d bits is unimodular (det a power of 2). K eigenvalues 3 on zero frequency (1,1), -1 on signed residual (1,-1). Thus
    K^tensor d has eigenvalues 3^(d-|h|)(-1)^|h|, h subset [d].
Its exact DVR Smith valuations are j with multiplicity binom(d,j), j=0..d. Over Z_2 all are units. Over Z_3/(3^H) minimum linear channels for full explicit local map = sum_(j=0..min(d,H-1)) binom(d,j). The zero mode carries depth d, top signed residual depth 0, intermediate support modes retain their own valuation. To recover arbitrary input vector modulo 3^H from blurred vector alone, uniform precision H+d sufficient and necessary: inverse divides the zero mode by 3^d, and nonzero source vector 3^(H-1) times allones maps to 3^(H-1+d) times allones. This is restricted arbitrary-vector observer claim, not necessary for known constraint tables or SAT.

Actual locally-full source d=3: f_p=1-delta_p for forbidden pattern p, or f_full=1. g_p=K^tensor d f_p. Modulo 3, full relation maps to zero; forbidden pattern maps to a nonzero signed top Walsh mode depending ONLY on parity of p. Two distinct p,r of same parity have identical g mod3, with exact difference content 1: their Fourier difference has top coefficient zero and a weight-(d-1) coefficient nonzero of valuation zero (omit a differing bit), while every other active weight has depth>=1. Opposite parity has depth zero. Full vs forbidden has depth zero (difference a single K column containing unit). Thus for d=3 the actual 9 local relation tables collapse to three observed classes modulo3, but modulo9 distinguish all nine. This is actual source-specific loss, not generic count-only hypothetical collision. Original zero mode S(0)=7 or8 and original signed residuals retained, even if blurred zero mode lost modulo3. The binary inverse and ternary loss are distinct coefficient-field behaviours of the SAME actual source map. No implication of physical phase or local Galois identification; R79 original inertia and R80 rank-one collision remain independent. At d<=3 the full source correction is constant-size, so not a superpoly barrier.

### R104. Nonidentity moment-chart transport in the existing indexed cube

Use original H05 eight vertices/twelve arrows/six faces, history, chronological tau, refinement k, Frobenius j, version, coefficient ring/precision, creation lift, intended consumer retained. Here third axis is actual invertible moment chart K^tensor d over Q or binary coefficient ring, not physical motion or original spatial Singer action. For diagonal source filter Q, actual conjugate chart filter is Q'=K Q K^-1 (write K for tensor power). Then KQ=Q'K, and two commuting source masks Q,R retain commutation after transport, providing all six faces and endpoint paths when original labelled joint residual atoms are carried. R87/R88 original zero mode, gain/loss and A00 joint loss remain actual source labels. If one incorrectly keeps the old diagonal Q after changing chart, exact defect
    (KQ-QK)_(x,y)=K_(x,y)(Q_y-Q_x).
At mod3 the chart is not invertible, so there is no automatic conjugated filter; retain the discarded valuation strata / actual source or prove consumer sufficiency separately. This is a concrete finite arithmetic chart weld, not a proof that lossy mod3 faces commute, no H07/H14 or physical 9DOF promotion. All global matrices only semantic descriptions; local tensorized chart producer is cheap per bounded-width table, materialization of full assignment carrier not required by decision. G56 low-order source reconstruction remains separate from cost of producing those modes. Chronological and refinement indices not merged with deformation parameter or Frobenius.

### R105. Actual local execution

Executed /tmp/langlands_r99.py locally using exact Python integers, Fraction and SymPy Smith normal forms. 140 global minimum/violated-clause comparisons, 140 positive origin parity comparisons, 140 exact corrected weighted count/modular comparisons, 12698 explicit shifted support-pair checks, 1152 actual rational Cauchy patch entry coefficient parity checks (complete L=4,8), 4 Smith forms d=1..4, 185 local full/deleted-pattern collision valuation checks, 80 chart defect identities, 480 cube face and 480 endpoint-path checks, 32 independent original/shifted Boolean tensor-table contractions (shifted direct table checks when <=3 occurrences). All passed. The test enumeration includes small free-variable cases; free counts preserved. No CI/native kernel, actual proof-assistant implementation or full external recursion runtime benchmark. Reproduction core:
```python
from itertools import product,combinations
from fractions import Fraction as F
from math import prod
import sympy as S
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ
def words(d):return list(product((0,1),repeat=d))
def dist(a,b):return sum(x!=y for x,y in zip(a,b))
def mv(A,v):return [sum(x*y for x,y in zip(r,v)) for r in A]
def K(d):return [[2**dist(x,y) for y in words(d)] for x in words(d)]
def J(d):return [[F((-1)**(d-dist(x,y))*2**dist(x,y),3**d) for y in words(d)] for x in words(d)]
def vp(n,p):
 if n==0:return float('inf')
 n=abs(n);v=0
 while n%p==0:n//=p;v+=1
 return v
for d in range(1,5):
 W=words(d);n=len(W);A=K(d);B=J(d)
 for i in range(n):assert mv(A,[r[i] for r in B])==[int(i==j) for j in range(n)]
 S1=smith_normal_form(S.Matrix(A),domain=ZZ)
 assert sorted(vp(int(S1[i,i]),3) for i in range(n))==sorted(d-sum(w) for w in W)
 tables=[[1]*n]+[[int(i!=j) for i in range(n)] for j in range(n)]
 G=[mv(A,f) for f in tables]
 for i,j in combinations(range(n+1),2):
  assert min(vp(a-b,3) for a,b in zip(G[i],G[j]))==int(i>0 and j>0 and sum(W[i-1])%2==sum(W[j-1])%2)
from random import Random
rng=Random(369)
# Actual script also interleaves chart random samples before these selector samples.
for q in range(1,5):
 scopes=[s for d in range(1,min(q,3)+1) for s in combinations(range(q),d)]
 for c in range(35):
  cs=[(I,tuple(rng.randrange(2) for _ in I)) for I in rng.choices(scopes,k=rng.randrange(5))]
  allowed=[[y for y in words(len(I)) if y!=p] for I,p in cs]
  coeff=[mv(J(len(I)),[int(y!=p) for y in words(len(I))]) for I,p in cs]
  zero=0;positive=0;corrected=F(0);wanted=0;floor=999
  z=[rng.randrange(1,8,2) for _ in range(q)]
  for x in words(q):
   xx=[tuple(x[i] for i in I) for I,p in cs];u=sum(a==p for a,(_,p) in zip(xx,cs))
   assert sum(min(dist(a,y) for y in pp) for a,pp in zip(xx,allowed))==u
   floor=min(floor,u);zero+=int(u==0);weight=prod(z[i]**x[i] for i in range(q))
   positive+=prod(sum(2**dist(a,y) for y in pp) for a,pp in zip(xx,allowed))
   wanted+=weight*int(u==0)
   corrected+=weight*prod(sum(2**dist(a,y)*b for y,b in zip(words(len(I)),bb)) for a,(I,p),bb in zip(xx,cs,coeff))
   for yy in product(*allowed):
    row=set();col=set();m=0
    for (I,p),y in zip(cs,yy):
     for i,b in zip(I,y):
      row.add(m+2*x[i]);col.update((m,m+2,m+2*(1-b)+1));m+=4
    assert m-len(col|{a+1 for a in row})==sum(dist(tuple(x[i] for i in I),y) for (I,p),y in zip(cs,yy))
  assert (floor==0)==bool(zero) and positive%2==zero%2 and corrected==wanted
```
Additional chart checks: for each d=1..4 and 20 seeded random signed vectors v and masks Q,R, compare KQv to (KQK^-1)Kv, all six two-axis faces and six paths; check wrong-chart commutator entry formula. Exact patch checks: for each L=4,8, t in [-L,L-1], x,y in [0,L-1], explicitly multiply factors [t-s,2L] for s!=y-x, divide by C'(0), confirm all rational coefficients 2-integral and residue polynomial is the constant [y=x+t]. Independent table checks explicitly sum A(X)B(X) on original 2n ports and A(shift X)B(X) on 4n ports for small inputs; compare closed forms. All tests actually executed; compact reproducer may use different random sequence than full script because chart draws omitted here. Counts reported from full actual run.

### R106. Updated endpoint ledger

| Gate | Deliverable | Status |
|---|---|---|
| R99 | exact dual-rail origin moment/defect kernel with original witness strata | derived |
| R100 | global G63/G61 support-floor minimization equals minimum violated clauses; NP-complete zero floor | derived, restricted; explicit bounded arity via occurrence split |
| R101 | actual nonzero Cauchy patch hard global floor on easy original contraction | derived, fixed-packet negative control |
| R102 | direct local binary inverse, original weighted rank-two scalar, no LOCAL Hermite debt | derived; global contraction unpaid |
| R103 | exact binary/ternary Smith and signed-zero-mode spectrum, actual local 7/8-pattern observer collision | derived |
| R104 | nonidentity moment chart, six exact finite faces, actual wrong-chart defect and lossy ternary boundary | derived; no physical/kernel promotion |
| R105 | exact local regressions | executed |
| R7a'/LGC4d | shared global computation of corrected local factors or original weighted support | OPEN; per-pair matching and global floor are different, alternative algorithms admitted |
| R7b'/LGC5 | unavoidable unrestricted deterministic standard-machine cost | OPEN P0 |
| R7c/LGC6 | original Clay separation via uniform SAT or sufficient central-slice route | OPEN P0 |
| LGC7/N6 | original conditional consumer | existing |

Next endpoint-first: exploit signed corrected local factor network directly (not full local-factor census), seek actual global shared contraction or unavoidable bound surviving all legal preprocessing and nonlinear shortcuts. In particular global support-pair minimum is now exactly a hard query but the nonzero patch control proves it may be unnecessary even for that actual input; do not make it a mandatory lower-bound premise. R94/G59 strongest generic Hermite collision not realized here at full generic depth in actual bounded-arity tensor subclass. Keep G60–64 source pruning and G56–59 low-order/horizon controls, R85 weighted one-bit support and H05 zero/residual/index boundaries. No claim of a new overall SAT exponent or P!=NP; no unrelated branch or native certification detour.

## 23. R107–R113 — geometry-forward affine separator gluing, exact signed Smith channels and semantic symmetry obstruction (2026-11-24)

Governing user direction: GEOMETRY-FORWARD. Original incidence geometry -> signed/neutral residual -> semantic contraction -> shared separator -> paid resource cost -> literal Clay endpoint. Do not start from an expanded representation and charge its size. Keep source zero mode, inhabited neutral fibre, signs, observed zero, actual history/time/k/Frobenius/version and precision separately. Stay on Langlands.

Read all three current mounted attachments (G60–64, G65–69, R99–106). Live Langlands #1549 73bf0b2a23a3a1918807448ddf8f1a3b6bfb5412 / #120 f3141d51870296488b0960f6c2af87a2a314e18f, shared blob e978a6e333cb9b6125bfe23800a58e97b641e4fb. Live G worker #1548 f10fa7a0852e193e318ed49e906733a8d2e6a89d, blob 61c3a293db787f0d094eba2920b50480b2255d10, inspected actual G70–74 (crossing-only locally-full compiler, 2SAT conditional fibre, canonical projection key, guarded implication shared evaluator, restricted monotone bound). Attachment G65–69 #1548 7dcee418032a / #119 c315cce7c3d8, blob 89d6606ba60c7e5626218d4b48f3f21455362374. Do not duplicate or edit that worker. Actual H05 #1291 d8f05ff5fc68da3c918d50c67f00edecc1e62648, roadmap a40721dde3fa561f82abe80c5312363e18aee158. Reopened current master DASHI/Crypto/ConstraintCouplingSearchExact.agda 6972ab099c268b3711dad9ab378d5e8620067c85; DASHI/Crypto/ObservationSeparatorGeometryExact.agda ccbe9275669def08a2c37cc945c19e61990bece1; DASHI/Codec/IndexedCubeHyperfibreExact.agda ce42b07fbaf430685ce172895cc482f933073577; DASHI/Core/GovernedIndexedResidualCubeExact.agda 42b70ebb7376813076934f2245ce6011b76f10c8; DASHI/Core/QueryFactorisationSufficiency.agda 98c592232292bbb6c5f0df047c8df3fd42be30d3. Source-readback, no native theorem attachment or kernel. Standard finite Fourier orthogonality (https://www.cs.mcgill.ca/~hatami/comp760-W2017/files/lectures-14.pdf) and holographic inverse basis changes (https://pages.cs.wisc.edu/~tdw/files/papers/Advances%20in%20the%20Computational%20Complexity%20of%20Holant%20Problems%20-%20Tyson%20Williams.pdf), orbit/coset linear algebra, Smith theorem credited as classical. New source-specific synthesis: bilateral affine boundary gluing with signed intersection residual, exact invariant factors, polynomial symmetry certificates versus exact global symmetry hardness on the actual crossing promise. JMD/DASHI attribution boundaries preserved.

### R107. Geometry-first source boundary

Partition an actual original factor graph into two regions sharing precisely the boundary variables X=F2^w (assign each factor and each unary weight once). Sum out each region's interior, obtaining boundary messages f,g in an integer or coefficient ring. Z=sum_x f(x)g(x). The R102 corrected two-rail local factors recover the same source contraction by inverse edge basis changes, so the geometry precedes the corrected coefficient expansion. R81 actual rank-two scalar D=3A-4Z with Z the weighted original witness count, not a demand to construct whole Weil matrices.

Assume certified affine support envelopes A=a+U and B=b+V and translation eigenspaces H<=U,J<=V:
    f(x+h)=(-1)^(p dot h) f(x), g(x+j)=(-1)^(q dot j) g(x).
Messages vanish off their respective envelopes. Any character on a subspace extends to a linear functional on X, choose extensions p,q; signs and actual source labels retained. Nonnegative nonzero messages over integers cannot have a nontrivial sign eigencharacter, but signed Fourier/weighted messages can. Affine envelopes need not equal actual supports; they are supplied certificates. The following universal pairing theorem is on the indicated spaces, not a claim actual messages realize every vector in them.

### R108. Exact bilateral affine gluing and Smith spectrum

Solve A intersect B by Gaussian elimination. If empty, actual contraction zero. Otherwise C=c+W, W=U intersect V. Let H'=H intersect W, J'=J intersect W, D=H intersect J (already contained in W), S=H'+J'. Put d=dim D, r=dim W-dim S. Represent f on H-cosets in A by coefficients f_i times the source character (-1)^(p dot x), similarly g_j on J-cosets in B with q. Pairing matrix
    M_ij=sum_(x in (a_i+H) intersect (b_j+J)) (-1)^((p+q) dot x).
If intersection nonempty it is an affine D-coset, so its entry is zero when (p+q)|D nonzero, else signed 2^d. If characters disagree on D, whole scalar is zero, even if both original supports inhabited. This is signed cancellation, not an empty source.

If compatible, discard rows/cols missing C. Their restrictions to C are distinct H'- and J'-cosets. Each intersects exactly one S-coset in C. Within a fixed S-coset all row/column pairs intersect; outside it none intersect. The signs factor as a row sign times column sign times a block sign: for block anchor z write each row as z+j_i+H', column as z+h_j+J', intersection contains z+j_i+h_j, sign factorizes because combined character is trivial on D. Each block is thus unimodular sign-equivalent to 2^d times an all-ones rectangular matrix. Integer row/column subtraction reduces each such matrix to one entry 2^d. EXACT Smith normal form: 2^r nonzero invariant factors, all 2^d (and zeros); compatible nonempty case. On Q or any odd residue field rank=2^r. Over Z/2^P, minimum linear factor channels =2^r if P>d and zero if P<=d; to recover divided quotient scalar modulo2^h requires h+d digits of this scalar, but direct signed coset factors can compute divided value without ever making a higher-precision scalar. Over odd prime no binary loss. This is exact universal linear interface rank in the specified bilinear model, not a bound on nonlinear evaluation of one input. Formula:
    Z=2^d sum_(z in C/S) eps_z L_z R_z
where L_z and R_z are signed sums of source coset coefficients, eps_z is anchor sign (define signs relative to anchor). Unsigned case all signs positive. Given explicit compressed regional tables, assign each relevant coset to a block and compute signs via Gaussian elimination, accumulate signed sums and contract in poly(w)*(#left entries+#right entries+2^r) ring operations, without expanding the full 2^w assignment carrier or matrix. Construction of the tables themselves is a separate cost. Example w=12, U=V=X, H=span first six coordinate axes, J=span axes 3..8 (zero indexed), d=3, dim S=9, r=3: 64 rows and columns -> eight independent channels, each with 2^3 valuation. Source symmetry overlap paid once. Zero mode for f,g is retained; nontrivial sign cancellation is not literal UNSAT.

### R109. Source-certified translation symmetries and actual production cost

For each bounded-width factor f_I, compute its translation stabilizer H_I by finite local table comparisons. It is an F2 subspace. Lift the linear annihilator equations H_I^perp to original regional coordinates and intersect using Gaussian elimination. The resulting H_all preserves every local factor, hence their product; project H_all to boundary to get H_B. Translation of internal coordinates is a bijection, so the regional summed message has H_B symmetry. With local signed characters use consistent sign equations on the same subgroup, multiply them; if nontrivial character on kernel of boundary projection, message identically zero by paired internal summation; otherwise it descends to boundary character. Over characteristic2 sign collapse is observed modularly, not literal equality of original signed integer source. This cert is sufficient, not necessary: global cancellations or constraints can create additional symmetries. The affine support envelope from local affine hull equations is also a sound superset via elimination. Both computed with polynomial overhead for bounded width. For known full-region symmetry subspace of dimension h and boundary image dimension h_B, enumerate full-region orbit representatives (2^(n-h)), sum weights at projected boundary cosets with multiplicity 2^(h-h_B) per represented assignment and signed phase as appropriate; for signed case choose compatible phase and zero kernel check. No free enumeration if quotient exponential. This is one actual producer algorithm; G67–69 separator DP and G73 guarded evaluator remain admissible alternatives. Large original treewidth, number of cosets or universal rank alone not a time lower bound.

### R110. Exact semantic symmetry recognition on the original always-inhabited crossing source is Clay-equivalent

Distinguish cheap certificate from finding ALL legitimate symmetries. For any Boolean formula F(x), use deterministic width<=3 truth graph b=F(x) with unique gate extensions (R78), add a fresh variable c and one clause (not b OR not c). This family always has c=0 witness for every x. Its exact fibres are:
    #b=0,c=0 = #b=0,c=1 = 2^q-W,
    #b=1,c=0 = W, #b=1,c=1 = 0.
The translation flipping c alone preserves the entire solution relation iff W=0. Other gate coordinates unaffected since truth graph independent of c. Use actual G72 locally-full crossing compiler with eight zero gadget coordinates, private occurrence copies, and padded equality clauses. Flip c AND all its copies, no other coordinates; zero block remains fixed. Unique extension is equivariant for the transported flip on the two c-branches when they both exist. Padded equality constraints are preserved SEMANTICALLY on the zero block, not literal syntactic clause equality (their padding z6,z7 differ). Thus even on always-inhabited width-three locally-full crossing instances, with known witness, deciding if this specified original translation is a true symmetry is coNP-complete. Membership: a source assignment with f(x)!=f(x+h) is a polynomial-size certificate of failure. Hardness from above reduction of UNSAT, no extra unbounded-width clauses. Consequently constructing the full actual translation stabilizer in polynomial time iff P=NP (converse: with SAT oracle find membership for specified h; for entire subgroup use existential search for h outside current span with forall x equality, in P=NP the fixed two-level polynomial hierarchy collapses, then at most n basis augmentations). Do not infer arbitrary SAT algorithms must compute full stabilizer. Local G46/G72 seven-pattern relations have trivial translation stabilizer per constrained triple, but globally hidden translation can still occur. This is a specific semantic contraction hardness result, not a universal lower bound. The guarded G73 polynomial representation and other nonlinear/direct algorithms remain legal.

### R111. Weighted rank-two consumer and precision/chronological residual

For original independent unramified weights lambda(x)=prod z_i^x_i (R85), gluing matrix becomes sum_(x in intersection) (-1)^((p+q) dot x) lambda(x), not generally 2^d sign. If weights are character (-1)^(s dot x) times a common scalar, fold s into p+q and R108 applies. Arbitrary Teichmuller product weights need not preserve translations; include them in local certificates or retain actual intersection weight sum. Example one free bit: count W=2 vanishes mod2, polynomial 1+z does not vanish identically. Cannot discard neutral mode at coarse precision then claim weighted zero. R85 genuine weighted rank-two observer and rank-one collision remain unchanged; full weighted contraction still global computation. For two independent regions' weights split once across separator (no double counting). In same-precision invertible rechart transport BOTH messages contravariantly/covariantly for pairing, affine subspaces and sign characters through actual map; for a linear rechart C, f'(x')=f(C^-1 x'), g' likewise, characters use C^-T. R88's actual six-face commuting source-mask cube with joint A00 residual remains original H05 instance, no new physical faces. A new constraint event can shrink stabilizer or change affine envelope, hence old quotient classes split; retain original source/labelled provenance and gains/losses, not an assertion that prior coarse table suffices for every update. Time tau, k chart/refinement, Frobenius j, version, coefficient ring/precision and creation lift/carry R96 remain distinct. At lossy precision, a zero pairing or vanished block may conceal inhabited source; retain signed and valuation residual; no unrestricted lower bound from channel size or loss. No H07/H14 physical/native promotion.

### R112. Actually executed local tests

Python integers and SymPy Smith normal form: 300 seeded affine envelope / subgroup / signed character gluing comparisons, 300 independent Smith forms, 300 arbitrary product-weight comparisons (against exact intersection sums, NOT asserting same rank), 300 bounded-width local symmetry certificate checks on actual summed regional functions. Independently verified G72 eight-variable zero gadget all 256 assignments, 36 compiled deterministic flag/translation instances with full DPLL model counting of 144 b,c fibres and 3,749 emitted crossing clause checks, plus 36 semantic flip checks after proved zero-gadget simplification. The first test incorrectly required syntactic flip equality of padded clauses; corrected to semantic equality. Initial naive DPLL branch order timed out, reran with priority to the eight gadget coordinates, without assuming their values, all pass. No CI/native kernel, no full runtime benchmark.

Reproduce core affine test (actual run used Random(369), w=1..5, 60 cases each; independent random signed coefficients and weights):
```python
from random import Random
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import smith_normal_form
rng=Random(369)
def span(gs):
 s={0}
 for g in gs:s|={x^g for x in s}
 return s
def chi(h,x):return (-1)**((h&x).bit_count())
def reps(A,H):return sorted({min(x^h for h in H) for x in A})
for n in range(1,6):
 X=set(range(1<<n))
 for _ in range(60):
  U=span(rng.randrange(1<<n) for _ in range(rng.randrange(n+1)))
  V=span(rng.randrange(1<<n) for _ in range(rng.randrange(n+1)))
  H=span(rng.choices(sorted(U),k=rng.randrange(n+1)))
  J=span(rng.choices(sorted(V),k=rng.randrange(n+1)))
  a,b,p,q=[rng.randrange(1<<n) for _ in range(4)]
  A={a^u for u in U};B={b^v for v in V};C=A&B;D=H&J;W=U&V
  HH=H&W;JJ=J&W;S={h^j for h in HH for j in JJ}
  ar,br=reps(A,H),reps(B,J)
  AA={r:{r^h for h in H} for r in ar};BB={r:{r^j for j in J} for r in br}
  mat=[[sum(chi(p^q,x) for x in AA[i]&BB[j]) for j in br] for i in ar]
  incompatible=any(chi(p^q,d)==-1 for d in D)
  expected=0 if not C or incompatible else len(W)//len(S)
  snf=smith_normal_form(Matrix(mat),domain=ZZ)
  assert sorted(abs(int(snf[i,i])) for i in range(min(snf.shape)) if snf[i,i])==[len(D)]*expected
  f={i:rng.randrange(-3,4) for i in ar};g={j:rng.randrange(-3,4) for j in br}
  fv={x:chi(p,x)*f[i] for i in ar for x in AA[i]};gv={x:chi(q,x)*g[j] for j in br for x in BB[j]}
  val=0
  if C and not incompatible:
   for z in reps(C,S):
    block={z^s for s in S}
    left=[i for i in ar if AA[i]&block];right=[j for j in br if BB[j]&block]
    i0,j0=left[0],right[0];e=mat[ar.index(i0)][br.index(j0)]
    lf=sum(f[i]*(mat[ar.index(i)][br.index(j0)]//len(D)) for i in left)
    rg=sum(g[j]*(mat[ar.index(i0)][br.index(j)]//len(D)) for j in right)
    val+=e*lf*rg
  assert val==sum(fv[x]*gv[x] for x in C)
  weights=[rng.randrange(1,8) for _ in range(n)]
```
Additional actual tests used product weight sums over each exact intersection, and five random width<=3 factors on n=2..6 (60 cases each, entries -1..1), enumerate certified local stabilizer intersection and verify projected symmetries of interior-summed function. Compiler reproducer: use actual G72 gadget digit string 737362511425175275471342317614566635167417725234 on crossing triples in lex order, all 256 assignments unique zero. Build standard deterministic AND/OR gate truth graph with b output, append (-b,-c), compile with G72: original variables on L, first occurrence copy on L later on R; equalities padded by Z6,Z7, unit main padded by Z4,Z5, binary by Z0. For q=1,2,3 use empty formula, contradictory units, and ten seeded random normalized clause lists (Random(369), sample up to five from width<=3 pool). Full DPLL on emitted formula with b,c pins, gadget variables branched first but not preassigned; verify four counts R110 and distinct crossing scopes. Check flip exchanges padded equalities after simplifying zero gadget, only final clause changes. No claim independent benchmark or new native code committed; mathematics and reproduction procedure in roadmap.

### R113. Endpoint ledger

| Gate | Deliverable | Status |
|---|---|---|
| R107 | original geometric boundary and actual source messages | derived |
| R108 | bilateral signed coset gluing, exact Smith spectrum and shared quotient | derived, checked |
| R109 | polynomial local symmetry certificates and costed orbit producer | derived, checked |
| R110 | actual globally hidden symmetry recognition coNP-complete on G72 always-inhabited crossing promise | derived, checked |
| R111 | weighted consumer boundary, source zero/residual and independent indices | derived |
| R112 | local regressions | executed |
| R7a'/LGC4d | global source-aware contraction after legitimate symmetry/affine/guarded reductions | OPEN; no universal small quotient or polynomial joint solver |
| R7b'/LGC5 | unavoidable unrestricted deterministic cost without mandatory full symmetry discovery, boundary materialization or counting | OPEN P0 |
| R7c/LGC6 | original uniform separation or sufficient central sandwich | OPEN P0 |
| LGC7/N6 | literal Clay endpoint | existing conditional consumer |

Next: geometry-forward. Reverse-solve a joint weighted support contraction that adapts to actual separator symmetries without computing the full stabilizer; allow G73's shared guarded evaluator, local certificates and arbitrary direct algorithms. Study cost of source-specific surviving coupled residual, not raw graph width or class count. R108 exact rank is restricted; R110 exact symmetry recognition is hard but not obligatory. No proof P!=NP, no certification detour, no unrelated PR edits, no physical TOE promotion.

## 24. R114–R120 — geometry-forward weighted affine trellis, complete conditional stabilizer and symmetry-free crossing fibres (2026-11-24)

Stay on Langlands. Read both mounted pasted attachments directly: R107–R111 and G70–G74. Live Langlands Agda #1549 0208b560be2af193f7d6c68f20e79cf70adc2c30 / Lean #120 69e842c43939f74b297b604b19c5e825a9eda175, shared blob 51fb25c94ed2a4d07eef35c26aee26ba1e17bc13. Live general P vs NP worker has advanced to G75–G78: #1548 a81e2f6d0eea3f2f8f768eeb68ec5f18d7986cbf / #119 048398039a65de5c4e2d459074c8ced9caa1c9b7, shared blob cafd38e41ff43f8fd4565ba234d49ee066b14c32. Read actual G75–78 section: bounded right components, exact guard hypergraph elimination, shared path pairs, exponential prime guard control and division-free parity transfer. Credit G70–78, no edits to their PRs. Existing R58 affine/Walsh contraction, R85 weighted actual rank-two Weil probe, R87–89 indexed original loss atoms, R102 binary local inverse, R103 ternary depth, R107–113 exact signed separator and symmetry recognition remain owners. Existing H05 #1291 / GovernedIndexedResidualCubeExact (previously verified blob 42b70ebb7376813076934f2245ce6011b76f10c8), ConstraintCouplingSearchExact, ObservationSeparatorGeometryExact, IndexedCubeHyperfibreExact retained. Geometry-forward, actual incidence -> signed/neutral residual -> semantic contraction -> paid resource; preserve JMD attribution boundary. Classical linear-code syndrome trellis, Gaussian elimination and 2-SAT implication algorithms are not newly claimed inventions. This is an actual weighted consumer weld and a source-specific rigidity construction. No external SAT algorithm audit or new unrestricted lower bound.

### R114. Weighted intersection is an affine syndrome fibre; division-free geometric contraction

R108's signed coset pairing has entries sum_(x in A_i intersect B_j) chi_L(x)chi_R(x) lambda(x), with lambda(x)=prod z_i^x_i from R85. Every nonempty intersection is an affine coset c+D of the actual shared translation subspace D=H intersect J. Unlike unweighted R108, incompatible characters on D do not force a zero weighted entry. Do not reuse the unweighted Smith spectrum for arbitrary weights.

Choose a binary parity-check matrix C with ker C=D, from actual basis by Gaussian elimination. For the given affine coset set s=Cc; let C_i denote its original-coordinate columns. With sign character chi_h(x)=(-1)^(h dot x), the required scalar is
    E_s(z,h) = sum_(Cx=s) prod_i [(-1)^h_i z_i]^x_i.
Works over ANY commutative coefficient ring; signs and neutral contributions retained (not a local Weil Galois action on binary coordinates). At cut l define U_l=span(C_1,...,C_l), V_l=span(C_(l+1),...,C_w). Feasible partial syndromes are
    B_l=U_l intersect (s+V_l).
For nonempty fibre B_l is an affine copy of U_l intersect V_l, with dimension
    kappa_l=rank(C_prefix)+rank(C_suffix)-rank(C).
Use actual coordinate ordering, independent of chronological time tau, source chart k and Frobenius j. Initialize m_0(0)=1. For each state u in B_l, transitions with bit b=0,1 go to u+b C_(l+1) if in B_(l+1), accumulating m_l(u) times w_(l+1)^b, where w_i=(-1)^h_i z_i. Return m_w(s). Exact induction on partial assignments; no division by 2, no Walsh normalization, no generic Hermite recovery. If s not in im C return known empty affine fibre. If scalar zero on nonempty fibre, retain observed zero separately. Feasible affine layer bases and memberships computed by Gaussian elimination, no need to enumerate the full prefix/suffix spans (finite tests below use such enumeration as independent small-instance check). Time O(poly(w,rank C)*(1+sum_l 2^kappa_l)) ring/bit operations with ring cost and coefficient growth charged separately; space O(poly(w)+2^max kappa_l) ring entries. Also legitimate primal orbit enumeration 2^dim D, choose cheaper certified route; no free optimal ordering or global separator search. G78 even parity is exactly one syndrome coordinate with at most two live states, not a new parity algorithm. Free coordinate columns zero yield independent factors 1+w_i. At any cut, two feasible distinct partial syndromes have disjoint nonempty suffix extension sets, so the residual feasibility row classes number 2^kappa_l, and corresponding Boolean compatibility matrix has rank 2^kappa_l over every field (disjoint nonzero all-ones blocks). This is a restricted exact state result, not a lower bound for arbitrary computation.

For R108 weighted gluing, use this trellis per needed coset intersection, or share layers/syndrome tables when justified by actual message consumer. Arbitrary regional f,g may need exponentially many intersections; per-fibre polynomial width is NOT global polynomial cost. In particular the zero-mode W and signed h residual are separate specializations; E_s(1,0)=2^dim D, E_s(1,h)=0 if h nontrivial on D, while a weighted residue can be nonzero. Original labels and source affine coset retained. Coefficient prime remains independent of original ramified Weil field Q3, and R85 unramified tags remain actual original source weights.

### R115. Complete translation stabilizer of an individual inhabited bijunctive fibre is polynomially computable

Use G71 actual canonical unary/binary projections for a satisfiable conditional 2-CNF relation R on n right variables. They determine R exactly by majority closure (or just note all original clauses have arity <=2, so an assignment satisfying every projected constraint satisfies the original clauses). Each projection computable by polynomially many 2-SAT tests with one/two pins. Empty fibre is separately marked; don't assign it an inhabited neutral orbit.

A translation h in F2^n preserves R iff its local projections preserve every unary/binary projection. Necessity is direct; sufficiency follows from the exact reconstruction. On a unary projection of size 1, h_i=0; size 2 gives no condition. On binary projections the exact stabilizers are:
- singleton: both bits zero;
- two-element axis pair: pinned coordinate cannot flip, other free;
- two-element diagonal/antidiagonal: h_i=h_j (signed equality orientation retained as relation data);
- three elements: both bits zero (an odd cardinality subset cannot be invariant under a nonzero involution);
- full four elements: no condition.
Thus union-find on diagonal-pair edges and freezing the components touched by pinned or three-pattern projections gives the COMPLETE group, generated by disjoint coordinate block flips of the remaining unforced components. Polynomial in original 2-CNF size; no need for exponential truth table or exact count. General R110 coNP-hard recognition is not contradicted: it concerned the entire joint width-three relation, not a fixed conditional 2-CNF fibre.

### R116. Exact weighted quotient by the complete conditional stabilizer

Each free component C is connected by actual signed equalities, so its configurations are exactly a_C and complement a_C, with a chosen anchor fixed to 0 for a_C. A component of one variable is permitted. Since the component flip preserves R, its cross-component pair projections with outside variables are products of the full unary bit and the outside unary projection. The actual canonical relation therefore decomposes as the Cartesian product of the two-point free components and a residual bijunctive relation R_core on the remaining coordinates. Equivalently, gauge pin one anchor per free component, yielding a unique representative per orbit; the orientation bits recover the original assignment bijectively. Use actual free-component pattern signs, not a raw coordinate drop.

For arbitrary independent unary weights w_i(0),w_i(1), possibly signed or zero, exact contraction is
    P_R(w)=P_core(w) prod_C [prod_(i in C) w_i(a_Ci) + prod_(i in C) w_i(1-a_Ci)].
All factors computed directly with O(n) ring operations once the component structure and orientations are certified. Unweighted zero mode multiplies by 2^number_of_components; a signed/weighted factor can vanish despite its source component containing two actual orientations. In binary coefficient rings use the displayed sum, not division by the zero mode. If only support needed, gauge pins preserve existence and the representative witness polynomial is formally nonzero iff R inhabited; for weighted original rank-two consumer retain the actual factor, not merely the representative. This is a complete symmetry contraction for this individual fibre, including arbitrary product weights, but computing P_core exactly is not generally supplied by the polynomial decision algorithm. G75 has trivial-size right components, G76 can eliminate them directly; do not require stabilizer computation there. On changing guard assignment or crossing event, component orientation and membership may change, so retain original source rather than blindly reusing old quotient.

### R117. Actual crossing extension removes ALL conditional translation symmetries at known multiplicity

For one right variable y attach four fresh private right variables a,b,c,d. Introduce the six binary clauses
    (not y OR a), (not y OR b),
    (y OR c), (y OR d),
    (a OR b), (c OR d).
When y=0, c=d=1 and (a,b) ranges over the three nonzero binary patterns. When y=1, a=b=1 and (c,d) ranges over those same three patterns. Each original y has exactly three extensions, independent of y. The relation on these five coordinates restricted to y fixed 0 or 1 has trivial translation stabilizer (fixed coordinates cannot flip, and a three-element subset has no nonzero translation). With both y values allowed, no translation can flip y: the set of variable auxiliary coordinates in the two conditional fibres differs (translations preserve which coordinates vary). A translation fixing y then has to vanish on all auxiliaries by the same three-element argument. Therefore EACH nonempty projection onto this five-coordinate block has trivial stabilizer, whether y is fixed or free.

Apply to every right coordinate of the actual G72 crossing compiler (including its right zero-gadget variables if desired), before asking about global selection. Pad each new binary clause with left gadget literal Z0, globally forced zero by the original G72 eight-zero gadget. Each new ternary clause has exactly one left and two right coordinates, unique scope because all auxiliaries private and the six pairs are distinct; each selected relation still allows seven of eight patterns and full unary/pair/affine local projections. On every inhabited left fibre Z0=0, so gadget semantics exact. Every translation of the extended right relation must preserve each of its five-coordinate projections, hence all original and auxiliary bits are fixed. The full conditional right translation stabilizer is trivial on EVERY nonempty left fibre. The original left geometry, conditional 2-SAT tractability, and actual original guard labels retained. If applying to G75, each nongadget right component grows only by constant factor (at most 5x), private gadgets attached to deleted original gadget variables become isolated small components; left induced edges unchanged. For tree decomposition of original primal graph, add Z0 to all bags and attach a bag {y,a,b,c,d,Z0} to an original bag containing y; width <=max(tw(original compiled)+1,5). Right treewidth <=max(old,4) by a right bag of five. No free large-width or semantic contraction inference.

If r is number of extended right variables, every original joint witness has exactly 3^r extensions. This is NOT parsimonious; it is exact constant multiplicity. With weights on original coordinates and all new auxiliaries assigned weight 1, extended witness polynomial is exactly 3^r P_original(z), not a new original Weil parameter. Recover original R85 weighted rank-two scalar D=3A-4P using division by 3^r in binary coefficient rings (unit). Over ternary ring the raw scaled output has additional r digits of valuation; use higher precision or eliminate private gadgets directly, not a required intrinsic precision cost. Exact original counts can divide as integers. If all extended bits need arbitrary weights, use actual branch-dependent gadget factor rather than assuming constant multiplicity. Known original witness extends explicitly by setting all aux bits to 1. Original SAT decision thus remains NP-complete even on locally-full crossing geometry with polynomial individual fibre decision, polynomial COMPLETE conditional symmetry discovery, and trivial conditional symmetry on all inhabited fibres. This shows full conditional stabilizer quotient alone cannot give a universal SAT solver unless P=NP. It does not rule out other semantic contractions: indeed each private gadget can be eliminated immediately by G76, proving that conditional rigidity itself cannot be charged as unavoidable cost. G75's repeated original guard labels still carry the remaining interaction. No unrestricted lower bound.

### R118. Indexed residual and consumer transport

Retain H05 history, event time tau, source refinement/chart k, Frobenius iteration j, version, original named guard coordinates, coefficient ring, creation precision and chosen consumer. Add trellis cut index l separately (not tau/k). Affine fibre basis/anchor, free-component signed parity labels and representative gauge are dependent on actual source state. For each new event, restrict original relation and recompute or certify its new quotient; gain/loss identities from R87–89 remain on original carrier and weighted scalar sums additive, with no implication observed zero equals empty source. In particular removing a component flip after a pin is a refinement of admissible source orientations; reconstruct pre-event from original representative plus orientation, not from the coarse product scalar. Chart changes must transport parity-check columns, weights and source masks together; arbitrary linear chart may turn product weights into coupled factors, so R114 trellis must use actual original coordinate weights or their correctly transformed coupled factors. R96 creation-precision carry remains separate. No automatic six-face equality for arbitrary lossy projection, no physical H07/H14 or 9DOF promotion. Preserve existing H05 owner; no unrelated branches changed.

### R119. Actual local regression

Executed /tmp/langlands_r114.py in local Python exact integers, seeded Random(369). 2240 weighted affine trellis comparisons (560 random syndrome systems on 1..8 bits, moduli 2,8,9,125, signed weights); 571 complete stabilizer comparisons, 571 exact gauge/reconstruction checks and 571 weighted free-component factor comparisons (700 random 2-CNFs on 1..7 bits, skip empty); three complete local rigidity projection cases; all 256 original G72 zero-gadget assignments; three actual 13-variable crossing gadget formula checks (enumerated complete assignments, free/fixed y); 136 nonempty arbitrary source right relations on 1..3 variables, with all private extensions and weighted multiplicity/projection rigidity checked. Total 4351 comparisons/groups passed. No CI/native prover or external algorithm benchmark. Test harness computes projections and small spans by exhaustive enumeration for independence, not claimed polynomial implementation of the production algorithms; production method is 2-SAT pins and Gaussian elimination as proved. Compact reproduction:
```python
from itertools import product,combinations
from random import Random
from math import prod
from collections import defaultdict
rng=Random(369)
def span(g):
 s={0}
 for x in g:s|={y^x for y in s}
 return s
def trellis(cols,s,z,sg,mod):
 n=len(cols); pre=[span(cols[:i]) for i in range(n+1)]; suf=[span(cols[i:]) for i in range(n+1)]
 if s not in pre[-1]:return 0
 L=[pre[i]&{s^x for x in suf[i]} for i in range(n+1)]
 D={0:1}
 for i,c in enumerate(cols):
  E=defaultdict(int)
  for t,a in D.items():
   if t in L[i+1]:E[t]=(E[t]+a)%mod
   if t^c in L[i+1]:E[t^c]=(E[t^c]+a*z[i]*sg[i])%mod
  D=E
 return D.get(s,0)
for n in range(1,9):
 for _ in range(70):
  r=rng.randrange(n+1); C=[rng.randrange(1<<r) for i in range(n)];s=rng.randrange(1<<r)
  z=[rng.randrange(-3,6) for i in range(n)];sg=[rng.choice([-1,1]) for i in range(n)]
  from functools import reduce
  from operator import xor
  X=[x for x in range(1<<n) if reduce(xor,(C[i] for i in range(n) if x>>i&1),0)==s]
  v=sum(prod(z[i]*sg[i] for i in range(n) if x>>i&1) for x in X)
  for m in (2,8,9,125):assert trellis(C,s,z,sg,m)==v%m
def rel(n,F):return {x for x in range(1<<n) if all(any((x>>i&1)==b for i,b in c) for c in F)}
def stab(R,n):return {h for h in range(1<<n) if {x^h for x in R}==R}
def cert(R,n):
 par=list(range(n));frozen=set()
 def root(i):
  while par[i]!=i:i=par[i]
  return i
 for i in range(n):
  if len({x>>i&1 for x in R})==1:frozen.add(i)
 for i,j in combinations(range(n),2):
  P={(x>>i&1,x>>j&1) for x in R}
  if len(P)==3:frozen.update((i,j))
  if len(P)==2 and len({a for a,b in P})==2 and len({b for a,b in P})==2:par[root(i)]=root(j)
  if len({a for a,b in P})==1:frozen.add(i)
  if len({b for a,b in P})==1:frozen.add(j)
 return [sum(1<<i for i in range(n) if root(i)==g) for g in {root(i) for i in range(n)}-{root(i) for i in frozen}]
for n in range(1,8):
 pool=[tuple(zip(I,b)) for k in (1,2) for I in combinations(range(n),k) for b in product((0,1),repeat=k)]
 for _ in range(100):
  R=rel(n,rng.choices(pool,k=rng.randrange(2*n+1)))
  if not R:continue
  G=cert(R,n);assert span(G)==stab(R,n)
  pins=[(g&-g).bit_length()-1 for g in G];Q={x for x in R if all(not(x>>i&1) for i in pins)}
  assert {x^h for x in Q for h in span(G)}==R
  z=[rng.randrange(-2,6) for _ in range(n)];w=lambda x,I:prod(z[i] for i in I if x>>i&1)
  used=0;factor=1;x0=min(Q)
  for g in G:
   I=[i for i in range(n) if g>>i&1];used|=g;assert all((x&g)==(x0&g) for x in Q)
   factor*=w(x0,I)+w(x0^g,I)
  assert sum(w(x,range(n)) for x in R)==factor*sum(w(x,[i for i in range(n) if not(used>>i&1)]) for x in Q)
F=[((0,0),(1,1)),((0,0),(2,1)),((0,1),(3,1)),((0,1),(4,1)),((1,1),(2,1)),((3,1),(4,1))]
R=rel(5,F)
for allowed in ({0},{1},{0,1}):
 S={x for x in R if x%2 in allowed};assert len(S)==3*len(allowed) and stab(S,5)=={0}
D='737362511425175275471342317614566635167417725234'
Z=[tuple((i,1-(int(p)>>j&1)) for j,i in enumerate(I)) for I,p in zip((I for I in combinations(range(8),3) if min(I)<4<=max(I)),D)]
assert rel(8,Z)=={0}
H=[tuple((i+8,b) for i,b in C)+((0,1),) for C in F]
for b in (None,0,1):
 C=Z+H+([] if b is None else [((8,b),(0,1),(1,1))])
 assert len({tuple(sorted(i for i,v in c)) for c in C})==len(C)
 S=rel(13,C);assert all(x%256==0 for x in S) and len(S)==(6 if b is None else 3) and stab(S,13)=={0}
for n in range(1,4):
 for _ in range(50):
  R={x for x in range(1<<n) if rng.randrange(2)}
  if not R:continue
  E={x|sum(g<<(n+4*i) for i,g in enumerate(ys)) for x in R for ys in product(*[[g>>1 for g in rel(5,F) if g%2==(x>>i&1)] for i in range(n)])}
  assert len(E)==len(R)*3**n
  for i in range(n):assert stab({((x>>i)&1)|(((x>>(n+4*i))&15)<<1) for x in E},5)=={0}
  z=[rng.randrange(-2,5) for i in range(n)];w=lambda x:prod(z[i] for i in range(n) if x>>i&1)
  assert sum(map(w,E))==3**n*sum(map(w,R))
```

### R120. Endpoint-first ledger

| Gate | Deliverable | Status |
|---|---|---|
| R114 | original affine weighted signed syndrome trellis, exact feasible separator dimension | derived, checked; local coset not global pair enumeration |
| R115 | complete conditional bijunctive translation stabilizer by canonical unary/pair geometry | derived, checked; empty separately |
| R116 | free-component orientation quotient, division-free arbitrary weighted factors | derived, checked |
| R117 | crossing locally-full extension with trivial stabilizers on every nonempty conditional fibre, constant 3^r weighted multiplicity | derived, checked; NP-complete global decision, easy private elimination |
| R118 | source-indexed weighted quotient/neutral/zero/carry transport | derived semantics; no new physical/kernel claim |
| R119 | exact local regressions | executed |
| R7a'/LGC4d | global weighted contraction of original repeated guard interactions after all legal reductions | OPEN |
| R7b'/LGC5 | unavoidable unrestricted deterministic cost without mandatory stabilizer/trellis/prime cube materialization | OPEN P0 |
| R7c/LGC6 | literal Clay uniform separation or sufficient central sandwich | OPEN P0 |
| LGC7/N6 | original conditional consumer | existing |

Next geometry-forward: G75–G76 original guard hypergraph survives local component elimination; R114–116 now eliminate complete conditional translation and weighted affine geometry when available. R117 proves there need not be any remaining conditional symmetry, yet artificial rigidity can be removed cheaply; neither it nor G78's prime cube count can be charged as unrestricted work. Seek actual coupled residual contraction or a direct standard-machine lower-bound theorem, allowing arbitrary shared symbolic reachability and nonlinear factorization. Preserve original source zero mode, inhabited neutral fibre, signed residual, time/k/iteration/creation precision/consumer indices; no compulsory coefficient materialization, no certification detour or P!=NP claim.

## 25. R121–R127 — original weighted gluing geometry, exact matroid-intersection rank and shared-orientation residual (2026-11-24)

Geometry-forward; stay on Langlands. Read current mounted attachments R114–120 and G75–78. Live Agda #1549 dd68910684ca33c5c11101cf8cf78772e27ee517 / Lean #120 cc5228088c202b2486624c8739c6ad1d655d2096, shared blob d34da42a75e2ef3cb975c70c6b785ebf813eab49. Live G worker #1548 a81e2f6d0eea3f2f8f768eeb68ec5f18d7986cbf / #119 048398039a65de5c4e2d459074c8ced9caa1c9b7, shared blob cafd38e41ff43f8fd4565ba234d49ee066b14c32. Credit G75–78 original repeated-guard component elimination and weighted parity control. R58 affine dual, R85 actual unramified weighted rank-two Weil probe, R102 binary inverse, R108 bilateral unweighted gluing, R114 affine syndrome trellis, R115–117 conditional symmetry and rigidity control are direct producers. Existing ConstraintCouplingSearchExact, ObservationSeparatorGeometryExact, IndexedCubeHyperfibreExact and H05 #1291 / GovernedIndexedResidualCubeExact (previously verified blob 42b70ebb7376813076934f2245ce6011b76f10c8) remain source owners. Master code search for matroid/Matroid found corpus indexes but no direct theorem module in returned results (not exhaustive absence). Classical Edmonds–Lawler matroid intersection theorem and polynomial algorithm credited: MIT lecture notes https://ocw.mit.edu/courses/18-997-topics-in-combinatorial-optimization-spring-2004/e987389ab7a39eac57490805adcec8bc_co_lec11.pdf and https://www.extremalcombinatorics.com/optimization/notes/sec_matroidIntersection.html. New result is exact weighted pairing rank for the actual transverse source geometry and a division-free factorization, not a new general matroid theorem or unrestricted lower bound. JMD attribution boundary retained. No unrelated branch edits.

### R121. Original coordinate coupling on a transverse affine gluing block

R108: common affine boundary c+W, H'=H intersect W, J'=J intersect W, D=H' intersect J', S=H'+J'. First take D=0. On any fixed coset of S in W the original named coordinates have unique parameterization x=c+A u+B v, over F2, A and B column bases for H', J'. Let a=dim H', b=dim J'. Each regional source message is constant along its own symmetry space up to a certified character. Thus one message depends on v and the other on u, with character signs in the original x factoring as a constant times one row sign times one column sign (absorb into the messages); arbitrary signs do not alter the rank. This step does not require compatible restrictions on D, which is zero here. Use independent R85 unramified product weights z_i^x_i (formal indeterminates first, actual coefficient specializations later). Exact block matrix is
    M_z(u,v)=prod_i z_i^(c_i xor A_i u xor B_i v).
Each original coordinate has two binary row vectors A_i,B_i, possibly zero. These are actual repeated coordinate restrictions, not independent edge labels or a separately postulated matrix. A zero row on either side is a unary or scalar weight; mixed rows carry the actual coupling. At z_i=1 all entries are one (up to separable character signs) and rank is 1, reproducing the transverse R108 case. Generic weights can restore many channels.

### R122. Exact generic rank from matroid intersection, not independent channel charging

Define r_A(I)=rank_F2 {A_i:i in I}, r_B analogously, ground set E=original boundary coordinate indices. Let
    nu = max{|J| : {A_i:i in J} and {B_i:i in J} each independent}
       = min_{I subset E} [r_A(I)+r_B(E minus I)].
Equality and polynomial computation of maximum common independent set and dual rank partition follow from classical matroid intersection using Gaussian-elimination independence oracles. Zero rows are loops. No optimal semantic stabilizer or global separator assumed; the result uses the actual certified A,B.

Theorem: over the rational function field K(z_1,...,z_w) for ANY coefficient field K,
    rank M_z = 2^nu.
Proof upper bound, stronger than field rank: for any I, J=E minus I, use s=A_I u and t=B_J v, with 2^r_A(I) and 2^r_B(J) possible syndromes. Define
    L_(s,t)(u) = [A_I u=s] prod_(i in J) z_i^(c_i xor A_i u xor t_i),
    R_(s,t)(v) = [B_J v=t] prod_(i in I) z_i^(c_i xor s_i xor B_i v).
Then M_z(u,v)=sum_(s,t) L_(s,t)(u) R_(s,t)(v) identically in ANY commutative ring (0^0=1). Exactly one pair of syndromes contributes for each u,v. Minimize partition to obtain 2^nu channels. This factorization also gives an exact division-free weighted scalar contraction sum_(s,t)(sum_u f(u)L_(s,t)(u))(sum_v g(v)R_(s,t)(v)), including source signs absorbed earlier. On explicit regional messages, grouped construction costs O(poly(w)*(2^(a+r_B(J))+2^(b+r_A(I))+2^nu)) ring operations; generating regional messages, other blocks, optimal original separators and bit costs remain paid. This is not necessarily faster than direct evaluation for every input. Polynomial matroid intersection finds the compact partition/bases without materializing all channels; full factors may still be exponential.

Lower bound: take a maximum common independent index set C of size nu, specialize z_i=1 for i not in C, retain z_i as variables for i in C. Both maps u->A_C u and v->B_C v are surjective onto F2^nu. Choose one representative per syndrome on each side. The resulting 2^nu square submatrix, after independent row/column permutations removing c_C, is tensor product over i in C of [[1,z_i],[z_i,1]]. Determinants 1-z_i^2 nonzero as polynomials over EVERY field, including characteristic 2. Thus a full minor exists at specialization, so generic rank >=2^nu. Together with division-free upper bound equality. For fixed actual weights rank can decrease; no claim generic rank holds for all finite-field samples of R85 or that choosing this specialization is sufficient for SAT fingerprints. Formal rank is exact minimum separated linear channels for this whole block over the rational function field, not a lower bound on arbitrary nonlinear computation or one scalar consumer.

### R123. Exact specialized Smith spectrum and binary/ternary precision

On the above common-independent-set specialization, over a DVR O and integral z_i, elementary unit-pivot operations diagonalize [[1,z],[z,1]] to diag(1,1-z^2). Tensor products of these invertible row/column operations diagonalize the full specialized matrix; duplicated rows/columns outside the chosen syndrome representatives add only zeros. Nonzero Smith valuations are the sorted subset sums
    sum_(i in T) v_p(1-z_i^2), T subset C,
with infinity representing exact zero invariant factors. At precision p^H the minimum linear channels equals number of subset sums <H by the previously used chain-ring image-generator argument. No generic Smith claim for arbitrary unspecialized weights. At p=2 in an unramified extension, choosing a nontrivial Teichmuller unit z whose residue is not 1 gives v_2(1-z^2)=0; characteristic 2 squaring is injective. With ordinary odd integer weights, v_2(1-z^2)>=3 (or infinity), so extra residual depth occurs. At p=3, z residue +/-1 causes positive depth, but nontrivial residue outside +/-1 in a suitable extension gives a unit. The coefficient prime remains independent of original Q3 Weil ramification. This tracks actual signed residual and zero-mode degeneration, not an intrinsic precision demand.

Concrete geometry control: take w=2m, A rows (e_i,0) and B rows (e_i,e_i) for paired original coordinates i, i+m (equivalently A first m basis, B first and second m basis). Combined columns independent; H and J disjoint. nu=m. Specialize z_(i+m)=1; weighted block is tensor product of m two-by-two kernels and can have rank 2^m while unweighted rank 1. For factorized messages, each block scalar is product of m two-bit sums, O(m) ring operations; general explicit messages can use tensor transform, O(m 2^m) rather than dense matrix evaluation O(4^m). This is another exact exponential-rank/cheap-scalar negative control. Use only actual original weights, not an assertion that source independence always holds.

### R124. Nontrivial shared intersection creates an additional genuine coupling

Do not apply R122 unchanged when D != 0. Choose actual direct complements of D in H',J', parameterize x=c+A u+B v+G d on each S block, with d in F2^delta, delta=dim D. Then
    M_z(u,v)=sum_d chi(d) prod_i z_i^(c_i xor A_i u xor B_i v xor G_i d)
up to separable row/column signs. In the weighted case incompatible characters on D no longer imply cancellation. Apply R122's same partition to each fixed d (constant c changes) to get exact rank upper bound min(2^a,2^b,2^(delta+nu)), and division-free factorization with d included in channel labels. Alternatively R114 trellis sums each actual D-coset; no claim cheaper overall. This upper bound is not asserted sharp in general.

Actual source example: A=e1, B=e2, G=(1,1,1) in F2^3, c=0 and signs trivial. There is no mixed A/B coordinate, so nu=0. Shared d integrates to
    M=[[1+z1*z2*z3, z2+z1*z3],[z1+z2*z3, z1*z2+z3]],
    det M=z3(1-z1^2)(1-z2^2).
Generic rank 2, exceeding 2^nu. Thus shared orientation itself mediates coupling after marginalization. At all weights=1, matrix constant 2; over binary precision1 it vanishes while actual shared fibre has two points. With chi(d)=(-1)^d the two outer products subtract, again potentially nonzero at general weights. Inhabited neutral fibre, original count, signed cancellation, weighted residue separate. More generally disjoint pure A and B coordinates and one common orientation give sum of two outer products; generic rank 2 even though no direct mixed coordinate exists. No complete arbitrary-D generic-rank theorem claimed; investigate actual elimination of shared orientations or multiple separators rather than substituting the unweighted multiplicity.

### R125. Indexed hyperfabric and source semantics

Retain original source history, event time tau, chart/refinement k, Frobenius iteration j, source version, coefficient field, creation/requested precision, R85 sample, intended consumer; additionally actual affine block anchor c, basis A,B,G, matroid partition I and its common independent certificate, and chart cut order if using trellis. Matroid rank is invariant under invertible basis changes in u and v separately; arbitrary mixing of left/right coordinates changes the chosen separator and arbitrary source-coordinate linear rechart may make product weights coupled. Transport the weights, original labels and sign forms, not only dimensions. R108's signed unweighted zero mode, R114 actual affine orientation and R87–89 gain/loss/overlap atoms remain independently indexed. A new source event can change the original symmetry spaces and all their certificates; do not assert old weighted factorization commutes with arbitrary lossy updates. No new physical H05/H07/H14 claim and no required materialization of every mode or channel.

### R126. Actual local regression

Executed /tmp/langlands_r121.py with exact Python integers, modular elimination, and SymPy rank/Smith normal forms. 315 seeded full-column-rank binary A,B pairs (a,b=1..3; w in [a+b,a+b+4]); 315 common-independent-set vs min-rank-partition comparisons by exhaustive small-instance oracle; 630 specialized rank checks over Q and F5; 1260 exact signed scalar factorizations modulo 2,8,9,125 and rank upper checks over F5; 240 specialized Smith valuation spectra (m=1..4,20 draws each, primes 2,3,5); 100 general-D rank-upper checks, weak since tested small dimensions make bound automatic; separately 48 nonvacuous common-orientation pure-A/B rank-2 cases (a,b=1..4, z=2,3,4) and one symbolic SymPy determinant identity. Total 2594 comparison groups, of which 100 are weak controls. No native kernel, CI, integrated matroid algorithm implementation or runtime benchmark. Small reference enumeration is not the production polynomial algorithm. Reproduction core:
```python
from itertools import product
from math import prod
from random import Random
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import smith_normal_form
rng=Random(369)
def rank(v):
 B={}
 for x in v:
  while x:
   i=x.bit_length()-1
   if i in B:x^=B[i]
   else:B[i]=x;break
 return len(B)
def bit(x):return x.bit_count()%2
def proj(x,L):return tuple(bit(x&i) for i in L)
def mat(A,B,z,c,a,b):
 return [[prod(z[i]**(bit(A[i]&x)^bit(B[i]&y)^(c>>i&1)) for i in range(len(A))) for y in range(1<<b)] for x in range(1<<a)]
for a,b in product(range(1,4),repeat=2):
 for case in range(35):
  w=rng.randrange(a+b,a+b+5)
  while True:
   A=[rng.randrange(1<<a) for _ in range(w)];B=[rng.randrange(1<<b) for _ in range(w)]
   if rank([x|(y<<a) for x,y in zip(A,B)])==a+b:break
  c=rng.randrange(1<<w);masks=range(1<<w)
  def sub(v,m):return [x for i,x in enumerate(v) if m>>i&1]
  m=max((m for m in masks if rank(sub(A,m))==rank(sub(B,m))==m.bit_count()),key=int.bit_count)
  cut=min(masks,key=lambda m:rank(sub(A,m))+rank(sub(B,((1<<w)-1)^m)))
  nu=m.bit_count();assert nu==rank(sub(A,cut))+rank(sub(B,((1<<w)-1)^cut))
  z=[2 if m>>i&1 else 1 for i in range(w)]
  assert Matrix(mat(A,B,z,c,a,b)).rank()==2**nu
  I=[i for i in range(w) if cut>>i&1];J=[i for i in range(w) if not(cut>>i&1)]
  for mod in (2,8,9,125):
   z=[rng.randrange(-3,5) for _ in range(w)];M=mat(A,B,z,c,a,b)
   f=[rng.randrange(-3,4) for _ in range(1<<a)];g=[rng.randrange(-3,4) for _ in range(1<<b)]
   al={proj(x,[A[i] for i in I]) for x in range(1<<a)};be={proj(y,[B[i] for i in J]) for y in range(1<<b)}
   assert len(al)*len(be)==2**nu
   v=0
   for s,t in product(al,be):
    L=sum(f[x]*prod(z[i]**(bit(A[i]&x)^t[j]^(c>>i&1)) for j,i in enumerate(J)) for x in range(1<<a) if proj(x,[A[i] for i in I])==s)
    R=sum(g[y]*prod(z[i]**(s[j]^bit(B[i]&y)^(c>>i&1)) for j,i in enumerate(I)) for y in range(1<<b) if proj(y,[B[i] for i in J])==t)
    v+=L*R
   assert v%mod==sum(f[x]*g[y]*M[x][y] for x in range(1<<a) for y in range(1<<b))%mod
for n in range(1,5):
 for _ in range(20):
  z=[rng.choice([0,2,3,4,5,7,8,9]) for _ in range(n)]
  M=Matrix([[prod(z[i]**(((x^y)>>i)&1) for i in range(n)) for y in range(1<<n)] for x in range(1<<n)])
  S=smith_normal_form(M,domain=ZZ)
  def vp(x,p):
   if not x:return float('inf')
   v=0
   while x%p==0:x//=p;v+=1
   return v
  for p in (2,3,5):
   assert sorted(vp(abs(int(S[i,i])),p) for i in range(1<<n))==sorted(sum(vp(1-z[i]**2,p) for i in range(n) if x>>i&1) for x in range(1<<n))
for a,b in product(range(1,5),repeat=2):
 for z in (2,3,4):
  M=Matrix([[z**(x.bit_count()+y.bit_count())+3*z**(a+b-x.bit_count()-y.bit_count()) for y in range(1<<b)] for x in range(1<<a)])
  assert M.rank()==2
```

### R127. Endpoint ledger

| Gate | Deliverable | Status |
|---|---|---|
| R121 | Original weighted transverse affine block and shared-coordinate coupling | derived |
| R122 | Exact generic rank 2^nu via matroid intersection, division-free optimal field-linear interface | derived, tested; D=0, actual specialization may lower rank |
| R123 | Exact specialized DVR Smith subset-sum spectrum; exponential rank cheap product control | derived, tested |
| R124 | Shared orientation mediated coupling, explicit determinant, general upper factorization | derived, tested; full general-D generic rank OPEN |
| R125 | Indexed source and signed/neutral residual transport | derived semantics |
| R126 | Exact local regressions | executed |
| R7a'/LGC4d | Global weighted contraction of repeated original guard dependencies, including shared orientations and message production | OPEN |
| R7b'/LGC5 | Unavoidable unrestricted deterministic cost after all legitimate contractions | OPEN P0 |
| R7c/LGC6 | Original Clay uniform separation or sufficient central sandwich | OPEN P0 |
| LGC7/N6 | Original conditional consumer | existing |

Next geometry-forward: extend source-specific weighted gluing to nontrivial shared orientations, or identify global guard interaction factorization that actually pays the original rank-two scalar rather than the whole matrix. R122 is sharp for its linear interface but a large nu is not a resource lower bound on arbitrary algorithms; even the tensor-product control has cheap scalar contraction. Do not require global stabilizer, optimum separator, full Smith spectrum, or entire message production if the actual consumer bypasses it. Preserve original zero mode, inhabited neutral fibre, signs, actual history/time/k/iteration/creation precision and observer labels. No certification detour, no unrelated PR edits or P!=NP claim.

## 26. R128–R134 — exact general shared-orientation weighted rank, cut factorization and local-field convolution (2026-11-24)

Geometry-forward; stay on Langlands. Directly read mounted pasted R121–127 and G79–83. Live Langlands Agda #1549 48577ab92422904cf8f3df25a829a9c591ea6d10 / Lean #120 266ade6fd1f50aa7ad301ae410ce11380c6156ca, shared blob 364a28fec27af403adf73906d6e76ae4465d56ca. Live G worker Agda #1548 7821f6d2b7efd70919b68f21850af115b73123a1 (attachment c146cbe8c546f35c069b2abc5bcd5cf21cd1439b advanced without roadmap change) / Lean #119 5767912968d2854f3059864d0ebaf8f7a8f8baf7, identical roadmap blob 71e8d067fe40c5a4c3192bde6da0685ba1b8a33f. Credit G79–81 least joint linear-overlap geometry and indexed refinement, G82 full-affine nonlinear encoding, G83 large-separator cheap cardinality control; do not turn any into obligatory channel materialization. R58 affine dual, R85 original actual weighted Weil rank-two probe, R87–89 loss atoms, R102 local inverse, R108 original unweighted shared gluing, R114 syndrome trellis, R121–124 transverse rank and shared-orientation obstruction are direct producers. Existing H05 #1291 / GovernedIndexedResidualCubeExact (previously verified blob 42b70ebb7376813076934f2245ce6011b76f10c8), ConstraintCouplingSearchExact, ObservationSeparatorGeometryExact, IndexedCubeHyperfibreExact remain owners. Classical Edmonds–Lawler matroid intersection min–max/augmentation theorem checked at https://www.extremalcombinatorics.com/optimization/notes/sec_matroidIntersection.html and MIT lecture 11 https://ocw.mit.edu/courses/18-997-topics-in-combinatorial-optimization-spring-2004/e987389ab7a39eac57490805adcec8bc_co_lec11.pdf. Classical Fourier/group-algebra and affine-relation block decomposition credited, JMD attribution boundary retained. New theorem is the exact generic weighted rank with shared orientation, closing R124's restricted interface question; NOT unrestricted SAT cost, no physical H07/H14 promotion or other branch edits.

### R128. General shared-orientation exact rank

Use actual original block x=c+A u+B v+G d, all binary, [A B G] full column rank, a=dim u, b=dim v, delta=dim d. This holds for direct complements of the shared translation space in the original R108 regions. Up to separable row/column signs, original weighted pairing is
    M_z(u,v)=sum_(d in F2^delta) (-1)^(h dot d) prod_i z_i^(c_i xor A_i u xor B_i v xor G_i d).
Define the two row matroids L=[B G] and R=[A G] on the SAME original coordinate set E. Let nu_* be their maximum common independent set size, equivalently
    nu_* = min_(I disjoint J=E) [rank([B G]_I)+rank([A G]_J)].
Then for ANY coefficient field K, over K(z_1,...,z_w),
    rank M_z = 2^(nu_*-delta).
This includes arbitrary shared sign h and characteristic two. Full column rank guarantees nu_*>=delta; nu_*<=delta+min(a,b). R122 is delta=0. R124 upper 2^(delta+nu) is refined since rank([B G]_I)<=rank(B_I)+delta and likewise A. The exponent is invariant under separately changing region bases and adding shared-coordinate combinations to chosen complements. Indeed [B G] and [A G] represent actual full right/left symmetry spaces, independent of complement choice. Row-coordinate weight labels cannot be freely changed by arbitrary linear rechart.

### R129. Upper bound: actual joint affine source across a cut, no independent shared charge

For any partition I,J, consider the affine relation of pairs
    l=(u,x_I), r=(v,x_J), x=c+A u+B v+G d.
The map (u,v,d)->(l,r) is injective because G full column rank. Its affine dimension is a+b+delta. Left projection dimension is a+rank([B G]_I); right projection dimension b+rank([A G]_J). An arbitrary affine relation between two vector spaces decomposes into disjoint complete bipartite blocks between cosets of its left-only/right-only kernels: for linear relation T<=L0 direct_sum R0, define K_L={l:(l,0) in T}, K_R={r:(0,r) in T}; matching quotient classes P_L(T)/K_L and P_R(T)/K_R are isomorphic by unique partner class. Affine anchor supplies the translated identification. Number of blocks =2^kappa, kappa=dim P_L+dim P_R-dim T. Thus here
    kappa(I)=rank([B G]_I)+rank([A G]_J)-delta.
Extend h on shared d to a binary character ell on original x with ell A=ell B=0 and ell G=h, possible by full column rank. Sign (-1)^(h dot d)=(-1)^(ell dot c) (-1)^(ell_I dot x_I) (-1)^(ell_J dot x_J). Each complete bipartite block contributes a separated product after summing the left/right actual projections with original local weights and signs. There is NO multiplicity error: original (u,v,d) corresponds bijectively to admissible pairs (l,r). This proves a factorization of M through 2^kappa channels over ANY commutative ring, no Fourier divisions, and exact weighted scalar
    Z=(-1)^(ell dot c) sum_k L_k R_k,
    L_k=sum_(u,x_I in left block k) f(u)(-1)^(ell_I dot x_I)prod_(i in I) z_i^x_i,
    R_k=sum_(v,x_J in right block k) g(v)(-1)^(ell_J dot x_J)prod_(i in J) z_i^x_i.
Gaussian elimination gives actual projection and kernel bases and shared quotient labels without expanding entire relation. Given explicit messages, enumerate each projection independently, accumulate keyed sums, cost O(poly(w)*(2^(a+rank([B G]_I))+2^(b+rank([A G]_J))+2^kappa)) ring operations plus message access, bit cost and other quotient blocks. Choose minimizing partition or another cost-effective valid partition; minimizing channels need not minimize total work. May be more costly than other scalar contractions. Does not require enumerating every d for every pair u,v. Matroid intersection gives min kappa=nu_*-delta. This is the exact generalization of R122's upper bound.

### R130. Lower bound: common independent certificate pins actual shared coordinates

Take maximum common independent row set C, |C|=nu_*. Then G_C has full column rank delta: otherwise some row G_i outside its span exists by full G rank; adding i to C preserves independence in BOTH augmented matrices, contradiction to maximality. Put Q=F2^C/im G_C of dimension k=nu_*-delta. Because [A G]_C and [B G]_C have full row rank |C|, the induced maps Abar_C, Bbar_C onto Q are BOTH surjective. Specialize z_i=0 on C and z_i=1 elsewhere (formal polynomial specialization, 0^0=1; not a nonzero unramified character sample). Then weighted summand survives exactly if
    c_C+A_C u+B_C v+G_C d=0.
For a given u,v there is exactly one such d iff their quotient syndromes match after the affine offset. Its coefficient is +/-1; the sign separates in u,v by extending h to a form on F2^C. Choose one u,v per quotient syndrome. The resulting 2^k square minor is a signed permutation matrix, determinant unit in EVERY coefficient field. Thus generic polynomial rank >=2^k. Combined with R129 proves R128 exactly. No need to bound cancellations for arbitrary weight samples. A stronger nonzero finite-order realization follows R131. This closes generic D!=0 rank, not a lower bound on global message production or scalar evaluation.

### R131. Common-independent specialization = signed group-algebra convolution, exact odd-prime Smith and binary unit criterion

Keep z_i=1 outside C, arbitrary weights on C; let ell_C be any extension of shared character h, satisfying G_C^T ell_C=h. After separable row/column signs and translation by c_C, duplicate rows/columns reduce by integral unimodular operations to square convolution matrix N on Q. Define
    F(s)=sum_(x_C projects to s) (-1)^(ell_C dot x_C) prod_(i in C) z_i^x_i,
    N_(s,t)=F(s+t).
In group algebra O[Q],
    F = prod_(i in C) (1+(-1)^ell_i z_i [e_i mod im G_C]).
This preserves original shared residual as the actual pushforward of weighted named coordinates, NOT independent invented weights. All quotient characters l in Q^* correspond to linear forms l on F2^C annihilating im G_C. Eigenvalues over characteristic not 2:
    lambda_l = prod_(i in C) (1+(-1)^(ell_i+l_i) z_i).
Det N=prod_l lambda_l as integer polynomial identity (prove over Q(z), then specializes in every commutative ring). Over odd-prime DVR, Walsh matrix is unimodular (2 unit), so EXACT nonzero Smith valuations are sorted {v_p(lambda_l)} (infinity means zero invariant, omitted from nonzero Smith list), including extra zero rows/columns in original matrix. Mod p^H required linear channels of this specialization are #l with valuation <H. This is not an arbitrary-unspecialized Smith theorem. R123 transverse case delta=0 is recovered (for each i valuation of product pairs combines to v_p(1-z_i^2) after reordering and unit conditions; at odd prime with both factors units no depth).

In binary coefficient ring, Walsh inversion need not be integral; use determinant/group algebra instead. Reduction mod 2 in residue field gives det N = (prod_(i in C)(1+z_i))^(2^k), since all signs equal. Therefore N is invertible over the unramified binary DVR or its finite quotients iff every selected z_i residue differs from 1. This is realizable with genuine nonzero finite-order Teichmuller lifts in F_(2^m) for m>=2, outside-C weights 1. Thus R128 full rank is not merely formal specialization at zero; actual unramified weights can realize unit channels. Over odd prime choose residue not +/-1 on selected coordinates in a suitable unramified extension for sufficient unit condition. This does NOT replace R85 randomized support sampling or give a universal hitting set: forcing these coordinates or others to 1 may hide other original witnesses. The coefficient field prime and residue extension remain independent of actual original W_Q3 ramification and Frobenius. At z=1 all original shared orientations inhabited; with trivial h unweighted matrix entries 2^delta, with nontrivial h signed sum cancels. Modulo binary precision<=delta may report zero even in trivial h case. Keep actual source zero mode, signed character residual and sample/precision separately.

### R132. Indexed hyperfabric, G79–83 and actual cost boundary

The new certificate belongs to the actual source block and weight consumer, retaining history, event time tau, refinement/chart k, Frobenius iteration j, version, creation/requested precision, coefficient ring, sample and original named coordinate/affine anchor data. Rank partition, common independent set, shared subspace basis and quotient syndrome labels are dependent residual data. Invertible region basis change preserves both augmented matroids. If a new event changes original subspaces, use G81 actual shared dependency refinement and recompute/certify new block; do not treat monotone quotient enlargement as automatically independent or rechart as physical time. H05 original six faces, R87–89 gain/loss atoms, R96 carry and R114 coordinate trellis remain independently typed. When the actual original weights and messages factor, use G79–80 regional independence or G83's nonlinear sector aggregation first; large nu_* does NOT imply necessary exponential time. Example R124 A=e1,B=e2,G=(1,1,1): nu_*=2,delta=1,k=1, exact generic rank2 even though transverse nu=0. If shared space occupies entirely separate original coordinates from A,B, it supplies scalar weights only; aug matroids automatically subtract shared dimension once, and rank can stay 1. This resolves the prior shared-orientation rank question without turning it into compulsory linear state expansion. G82's nonlinear code decoding and G83's cardinality transfer remain admissible. No mandatory optimal global separator/stabilizer search or materialization; R7b'/c still open. Actual R85 D_t=3A(z)-4P_t(z) is unchanged; gluing is a valid exact producer for P_t(z) when actual regional hypotheses hold, not a polynomial algorithm for arbitrary SAT.

### R133. Executed exact regression and implemented certificate discovery

Actual local /tmp/langlands_r128.py used exact Python integer bitset Gaussian elimination, BFS augmenting paths, modular elimination, and SymPy rank/determinant/Smith. 324 random full-column-rank arrangements (a,b=1..3,delta=0..2,12 each) with exhaustive reference maximum common independent set, 324 rational pinned-specialization ranks, 972 pinned ranks mod 2/3/5, 324 arbitrary signed integer sample rank upper checks, 1296 cut scalar checks mod 2/8/9/125, 324 exact signed quotient convolution determinants, 648 odd-prime Smith spectra (3,5). TOTAL 4212 comparison groups passed. Actual polynomial augmenting algorithm now implemented (not just exhaustive discovery), test harness still exhaustively validates small cases and computes small affine blocks by enumeration as independent oracle; no integrated production message engine/runtime benchmark, no CI/native kernel. No empirical finite extension arithmetic in this round; binary unit criterion proved by determinant identity, not claimed Teichmuller test. Compact reproduction of ACTUAL augmentation and rank checks:
```python
from itertools import product
from random import Random
from collections import deque
from math import prod
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import smith_normal_form
def rank(xs):
 b={}
 for x in xs:
  while x:
   p=x.bit_length()-1
   if p in b:x^=b[p]
   else:b[p]=x;break
 return len(b)
def mi(A,B):
 E=set(range(len(A)));S=set()
 def ind(M,T):return rank(M[i] for i in T)==len(T)
 while True:
  O=E-S
  Q=deque(i for i in sorted(O) if ind(A,S|{i}));prev={i:None for i in Q};end=None
  while Q:
   i=Q.popleft()
   if i in O:
    if ind(B,S|{i}):end=i;break
    N=[j for j in S if ind(B,S-{j}|{i})]
   else:N=[j for j in O if ind(A,S-{i}|{j})]
   for j in sorted(N):
    if j not in prev:prev[j]=i;Q.append(j)
  if end is None:
   J=set(prev);I=E-J
   assert rank(A[i] for i in I)+rank(B[i] for i in J)==len(S)
   return S,I,J
  path=set()
  while end is not None:path.add(end);end=prev[end]
  S^=path
  assert ind(A,S) and ind(B,S)
def bit(x):return x.bit_count()&1
def mat(A,B,G,c,h,z,a,b,g):
 return [[sum((-1)**bit(h&d)*prod(z[i]**(bit(A[i]&u)^bit(B[i]&v)^bit(G[i]&d)^(c>>i&1)) for i in range(len(z))) for d in range(1<<g)) for v in range(1<<b)] for u in range(1<<a)]
rng=Random(369)
for a,b,g in product(range(1,4),range(1,4),range(3)):
 for _ in range(12):
  n=rng.randrange(a+b+g,a+b+g+4)
  while True:
   A=[rng.randrange(1<<a) for i in range(n)];B=[rng.randrange(1<<b) for i in range(n)];G=[rng.randrange(1<<g) for i in range(n)]
   if rank([x|(y<<a)|(z<<(a+b)) for x,y,z in zip(A,B,G)])==a+b+g:break
  L=[y|(z<<b) for y,z in zip(B,G)];R=[x|(z<<a) for x,z in zip(A,G)]
  C,I,J=mi(L,R);k=len(C)-g
  assert rank(G[i] for i in C)==g and 0<=k<=min(a,b)
  assert len(C)==max(m.bit_count() for m in range(1<<n) if rank(L[i] for i in range(n) if m>>i&1)==rank(R[i] for i in range(n) if m>>i&1)==m.bit_count())
  c=rng.randrange(1<<n);h=rng.randrange(1<<g)
  N=mat(A,B,G,c,h,[0 if i in C else 1 for i in range(n)],a,b,g)
  assert Matrix(N).rank()==2**k
  z=[rng.randrange(-2,4) for i in range(n)]
  assert Matrix(mat(A,B,G,c,h,z,a,b,g)).rank()<=2**k
```
Full local test additionally: form projection adjacency (u,x_I),(v,x_J) by enumerating all (u,v,d) for the small harness; group left vertices by their identical right-neighborhood sets, confirm each group complete bipartite and 2^k groups, extend sign ell by exhaustive small reference, compare weighted group sums with direct scalar in four rings. For each C enumerate im G_C, canonical coset reps, extend h to ell_C, compute F(s), N(s,t)=F(s+t); enumerate annihilator characters, compare N.det to product lambda_l and Smith valuations at primes 3/5. Modular pinned rank via ordinary elimination. Actual full test interleaves random draws for weights/messages and convolution weights, so compact script's random sequence differs. This is finite exact evidence for the derived theorem, not a substitute for proof.

### R134. Endpoint ledger

| Gate | Deliverable | Status |
|---|---|---|
| R128 | sharp general shared-orientation generic rank 2^(nu_*-delta) | derived; R124 generic rank OPEN closed |
| R129 | actual affine cut block factorization and costed division-free scalar producer | derived, tested |
| R130 | actual shared-coordinate pinning, full minor over every characteristic | derived, tested |
| R131 | signed quotient convolution, odd-prime Smith and binary unit criterion | derived, tested determinant and odd Smith; binary unit algebraic |
| R132 | indexed geometry and consumer residual, G79–83 admitted | derived |
| R133 | polynomial augmenting certificate implementation and exact local regression | executed |
| R7a'/LGC4d | global paid weighted contraction of repeated original guard dependencies after semantic reductions | OPEN |
| R7b'/LGC5 | unrestricted unavoidable deterministic cost allowing arbitrary nonlinear/shared computation | OPEN P0 |
| R7c/LGC6 | literal Clay uniform separation or sufficient central-slice route | OPEN P0 |
| LGC7/N6 | original conditional consumer | existing |

Next geometry-forward: exact weighted gluing rank is now solved in the entire affine shared-orientation class, so do NOT keep measuring larger compulsory linear interfaces. Use the actual cut factorization when cheaper, G79–80 genuine independent regional contraction, G82 decoding and G83 nonlinear sector aggregation. Investigate actual nonlinear composition of the repeated original guard factors, including shared scalar circuit reuse or a direct uniform-machine obstruction, rather than deriving further rank proxies. General global contraction and unrestricted Clay endpoints remain unpaid. Retain actual zero mode, inhabited neutral fibre, signed residual, separate history/time/k/Frob/version/precision/consumer indices. No certification detour, no unrelated PR edits or P!=NP claim.

## 27. R135–R143 — geometry-forward ordered guard algebra, nilpotent signed reordering and consumer-specific residual (2026-11-24)

Stay on Langlands; read both actual mounted pasted attachments directly, R128–134 and G84–88. Live Langlands #1549 b9443ceb0f28f0fea26e931dc6c9040a09dfe1c7 / #120 dd6c33352dca2a9631d4a2fa292ac622497dc040, shared blob 30b6833e0b111b8eaa70d96269a459a0520766cb. Live G worker #1548 41bf8d6ed02d0e3fbbff5dd6465e5e86ffac8e2e / #119 43898587b2e0986a02bc78f13b4cc83a77765068, shared roadmap blob d13acfbfda00542f3cd762659c2c9fce1f251cb7 (heads advanced since pasted report but roadmap same). Read actual G84–88: row-vector U,S,D transfer, bilinear affine conditional fibres, noncrossing recurrence, cover algorithm, exact signed commutator residual. Credit G84–88 as actual producers; no edits to those PRs. R85 original weighted rank-two Weil consumer D=3A-4P, R87–89 actual chronological gain/loss, R96 creation precision, R114 weighted affine trellis, R128–134 exact shared-orientation matroid gluing remain owners. H05 #1291 / GovernedIndexedResidualCubeExact and original ConstraintCouplingSearchExact / ObservationSeparatorGeometryExact / IndexedCubeHyperfibreExact retained. Geometry-forward: actual word/label geometry -> signed commutator residual -> shared scalar contraction -> paid cost. Standard associative algebra ideals, tensor products, Gaussian elimination and two-sided contextual annihilator are classical; new derivation is an explicit bounded-commutator residual contraction on this actual weighted interface, plus precise G84 source/consumer boundary. No claimed new general algebra theorem or unrestricted complexity separation. JMD attribution boundary retained.

### R135. Actual ordered interaction algebra and nilpotent residual filtration

Let R be a commutative coefficient ring and let A be the unital R-algebra generated by ALL actual d-by-d transfer matrices (both orientations of each named guard, plus constant transfers). J is the two-sided ideal generated by the commutators of those generators, equivalently the span of A[A,A]A: the quotient by generator commutators is commutative because generators commute there. Actual word length m, original guard count q, each unary weight charged once even for repeated reads. For an actual adjacent swap AB=BA+[A,B], the signed residual belongs to J. A product with r explicit residual factors and arbitrary A factors between lies in J^r. If J^s=0, every term with >=s residuals vanishes exactly. No inference that the source words are equal; the equality is a signed sum of their actual ordered products. Over a field, a nilpotent ideal J of an algebra in M_d has index <=d: chain J^i K^d is descending, and equality before zero implies persistent equality under multiplying by J, incompatible with nilpotence. This proof does not assume algebraically closed field or simultaneous diagonalization.

### R136. Finite signed sorting expansion and shared tensor transfer

Choose any fixed total order of original guard labels, including constant positions at the beginning (constants preserve their relative order). Stable sorting only exchanges different labels, preserving same-label occurrence order. At each adjacent inversion, use the exact two-branch identity AB=BA+[A,B]. On the main branch swap A,B; on the residual branch replace them by the ordered defect [A,B], separating the remaining ordinary word into two segments. Continue stable sorting independently within all segments, NEVER moving factors across a retained defect. Each residual uses its actual original labels/positions and matrix orientations. Drop a branch only when its explicit defect count reaches s (by J^s=0). At depth r, deterministic main sorting has at most B=m(m-1)/2 swaps across all segments; each new residual removes two ordinary occurrences. Hence at most sum_(r=0..s-1) max(1,B)^r terminal terms, each of form
    P_0(x) C_1(x) P_1(x) ... C_r(x) P_r(x),
where each P_t is grouped by increasing original guard label and each C_t is an actual commutator of two source occurrences. This includes constant swaps; no erroneous independent fresh variable for a repeated occurrence.

For a terminal term condition only the original guard labels that appear in retained commutators (<=2r, so <=2^(2r) assignments). This makes C_t fixed matrices. For each segment t and guard i let P_(t,i)(b) be its ordered product of the occurrences with that label (identity if absent). Let constant prefix P_(t,*) be the original-order constant product in segment. The exact tensor of simultaneous segment products, weighted over remaining original labels, is
    K = (tensor_t P_(t,*)) product_(i in label order)
          [sum_(b allowed by pins) w_i(b) tensor_t P_(t,i)(b)].
The tensor matrix dimension is d^(r+1). This formula holds without division, with arbitrary signed or zero weights, over any commutative ring. It uses the fact that the order of labels within ALL segments agrees; multiplying tensor factors coordinatewise gives the actual products, and then summing each original bit once shares all its repeated occurrences. Unused guard weights multiply as w_i(0)+w_i(1). Apply the linear bridge multiplication map on pure tensors, extended linearly:
    Phi_C(X_0 tensor ... tensor X_r)=X_0 C_1 X_1 ... C_r X_r.
Then sum Phi_C(K) over the pinned guard assignments and all terminal terms. No assumption that the segment functions are independent after marginalizing shared guards; the tensor representation is precisely what retains their shared dependence.

Using ordinary dense matrix arithmetic, one upper bound is
    O(sum_(r=0..s-1) max(1,B)^r 4^r poly(m,q,d) d^(3(r+1))).
Polynomial for fixed d,s, and for fixed field matrix dimension d with nilpotent J since s<=d. Signed exact integer bit sizes remain polynomial in explicit word length and coefficient bit sizes at fixed d,s; finite-ring bit costs charged separately. This is an actual algorithmic upper bound, not a required representation or time lower bound. It can be worse than G85 noncrossing, G86 cover, R129 matroid cuts or other scalar circuits; choose cheapest known applicable method. No assumption of efficient global word minimization. A constant-width transfer with arbitrary commutator algebra is not covered.

### R137. Polynomial source certificate and residue-field lifting

Over a field, compute A by linear closure starting from identity and generators, multiplying basis matrices by generators until rank stabilizes. At most d^2 independent matrices. Compute J by starting with actual generator commutators and closing under left/right multiplication by A basis. Compute descending powers J^i via products of basis elements. If J^s=0, valid cutoff; if a nonzero power stabilizes, nilpotence fails. Gaussian elimination and closure use polynomially many field operations in d and explicit generator count; actual source matrices used. No need to find an optimal algebra representation or common eigenbasis.

For coefficient ring O/(p^H), including an unramified extension, a residue-field certificate of nilpotence index s yields a valid bound sH at the higher precision: reduction maps J^s to zero, so J^s consists of matrices divisible by p, and J^(sH) is zero modulo p^H. This is not the assertion that the same s works at every precision. Can exploit R85 direct binary weighted P with H=1 or signed D with H=3 and log-degree unramified coefficient extension; both constant H. For variable H the exponent can grow, not a polynomial runtime guarantee. Coefficient prime remains independent of original ramified W_Q3 and source Frobenius. The finite tests here use scalar Z/p^H, not actual extension-field arithmetic. Canonical lifting residual R96 remains independently recorded; no use of residue vanishing as an exact source zero.

### R138. Explicit fully interleaved genuinely noncommuting cheap source

Take upper unitriangular 3-by-3 matrices
    U(a,b,c)=I+a E12+b E23+c E13.
Actual multiplication U(a,b,c)U(a',b',c')=U(a+a',b+b',c+c'+a b'). Commutators of two such matrices are (a b'-a' b) E13, and all such ideal products of length two vanish. Thus J^2=0 for their generated algebra, even when the guard word is (1,...,q)^3 and every pair interleaves. Concrete nonzero residual [I+E12,I+E23]=E13. For any ordered list, complete product is exactly
    I + (sum_j a_j)E12 + (sum_j b_j)E23
      + (sum_j c_j + sum_(j<k) a_j b_k)E13.
Contract each term by grouping its one or two actual guard labels. For each affected label, sum its two weighted values of the product of all its factors (when labels coincide, same bit!), and multiply unaffected baseline factors w_i(0)+w_i(1). This gives O(m^2 q) ring operations by direct baseline products, division-free even when some baseline factors vanish. Can precompute products excluding any one/two labels by interval products for further speedup; not implemented/benchmarked. This is a stronger negative control than G87 commuting involutions: maximal interleaving, true signed commutators, yet polynomial exact weighted contraction. It is a matrix-transfer example, not necessarily a Boolean deterministic SAT encoding. Preserve source origin and rejected/acceptance semantics only when actual transfer is deterministic.

### R139. Consumer-specific contextual annihilator, not whole-matrix rank

Actual Langlands producer ultimately needs only scalar endpoint lambda(X)=a^T X b. Define
    I_lambda={Z in A : lambda(X Z Y)=0 for all X,Y in A}.
This is a two-sided ideal: left or right multiplying Z merely changes X or Y; closed under sums and scalars. It is the largest two-sided ideal contained in ker(lambda), since any ideal in the kernel absorbs all contexts. Compute it over a field by linear equations against all pairs of A basis matrices. Equivalently, for each power J^s test lambda(X Z Y)=0 on basis triples. If J^s subset I_lambda, the same sorting expansion is exact AFTER applying lambda even if omitted full matrices are nonzero. Every omitted term is contextually unobservable for that specific consumer, not erased source geometry. The quotient A/I_lambda has nilpotent commutator ideal iff such s exists; if nonzero powers stabilize without inclusion, condition fails. Polynomial field certificate via Gaussian basis and powers; at fixed d, s<=dim A+1 sufficient search (nilpotent chain in quotient). We use full tensor bridges in the test for clarity, not an optimized smaller quotient representation. Example block-diagonal transfer with observable triangular block and unobservable full M2 block has nonnilpotent whole J but scalar-specific cutoff <=2. Actual context labels, source history and intended consumer retained: changing endpoint may expose the hidden ideal. No blanket lifting of scalar-only residue certificate to p^H; full matrix lifting R137 is proved, scalar variant not claimed here.

### R140. Actual G84 acceptance core is nonnilpotent; baseline is a different observer

Read actual G84 source row-vector transitions (U,S,D):
    I=identity,
    T=[[0,1,0],[0,1,0],[0,0,1]] (true literal),
    B=[[0,0,1],[1,0,0],[0,0,1]] (clause boundary).
For any nonempty normalized CNF these actual possible matrices occur (false literal I). All are in algebra isomorphic to M2(K) direct_sum K: each has upper-left 2x2 block P, bottom-right scalar lambda, bottom-left zero and upper-right column determined by lambda*(1,1)^T - P*(1,1)^T. This is a multiplicative and linear isomorphism (row sums all lambda). Show generated algebra is full: on upper-left blocks t=[[0,1],[0,1]], b=[[0,0],[1,0]]. Pair T-BT=(E12,0), then multiply by B to get (E11,0), left multiply by B to get (E21,0), multiply E21 E12 to get (E22,0); subtract diagonal sum from identity to get (0,1). Therefore dimension5 over EVERY coefficient field. Commutator ideal is exactly M2(K) direct_sum 0, dimension4, since e.g. [E11,E12]=E12, and multiplying by matrix units generates full M2 ideal. It satisfies J^2=J !=0. No full-matrix nilpotent shortcut on this actual universal hard transfer.

The original acceptance endpoint lambda_acc=e_U X e_U^T reads P_11. Its contextual annihilator is exactly 0 direct_sum K: nonzero P can be brought by matrix units to nonzero P_11, whereas scalar lambda component never enters that entry. Hence observable quotient is M2(K), J never becomes invisible. The total baseline endpoint lambda_all=e_U X (1,1,1)^T reads scalar lambda; annihilator is M2(K) direct_sum0. It kills all commutators, cutoff s=1. Rejected residual is baseline minus accept, not same observer or same source relation. This exact split preserves original W and signed/weighted P; for deterministic G84 and R85 product weights recover A(z)=prod_i(1+z_i), P_t(z)=accept weighted scalar, actual rank-two D=3A-4P. The literal acceptance selector is still hard globally by G84; no proof every algorithm must use this algebra. Same nonnilpotent G84 algebra occurs on an easy single literal or many repetitions of one unit clause, whose original weighted accept sum is simply w_1(1). Thus nonnilpotent commutator ideal, even in the actual acceptance quotient, is NOT an unrestricted resource lower bound. Bounded-occurrence G84 hard family still admits all other algorithms; do not require the supplied word or full ideal discovery.

### R141. Indexed source, reordering and dependent signed defects

Preserve original history, chronological tau, chart/refinement k, Frobenius iteration j, version, coefficient ring/creation/requested precision, original guard labels and word positions, chosen sorting order, source occurrence bijection, defect order/depth r, retained consumer and actual contextual ideal. These are independent indices: sorting does not edit chronology; swapping is an algebraic identity with signed residual, not an identification of source histories. Source coordinates remain original in all pinned/neutral assignments and bridge tensors. Nilpotent defects can be omitted only with actual J-power or contextual certificate; scalar zero does not mean uninhabited fibre. R87–89 gain/loss and joint overlap, R96 lift/carry, R128–134 affine matroid cuts and G85 nested contraction remain available, no mandatory materialization. If a new event or chart introduces matrices outside certified algebra or changes consumer/precision, recertify the actual ideal/cutoff. H05 original six-face semantics not promoted to arbitrary reordering, physical H07/H14/9DOF unchanged.

### R142. Actual local execution

Ran /tmp/langlands_r135.py in local container Python exact integers, modular matrix products and finite-field Gaussian elimination. 180 nilpotent ideal certificates (p=2,3,5, d=2,3), 260 weighted signed sorting contractions (mod 2,3,8,9,125, d=2,3, random repeated labels/constants and possibly zero weights, direct exhaustive assignment references), 210 fully interleaved Heisenberg moment comparisons (q=1..7, 3 reads, five moduli), 5 actual G84 algebra/ideal dimension comparisons (p=2,3,5,7,11), 70 easy nonnilpotent repeat-clause controls, 10 actual G84 acceptance-vs-baseline contextual quotient checks, 36 hidden M2/observable triangular block endpoint comparisons, 54 residue-certified lifted cutoff contractions (mod8,9,25). Total 825 comparison groups passed; final rerun measured about 1.5s local test harness only, not algorithm benchmark. Max terminal terms 19 in the first sorting test set. No CI, native Agda/Lean or external algorithm execution. Standalone local script not committed; reproducer below is algorithm core and sufficient test recipe, not a claim of a committed production engine. Actual finite-field basis closure implemented; exact rational field extension and unramified binary extension operation not separately executed. No resource extrapolation.

Reproduction core (ordinary exact modular matrix functions add/sub/mul/scale, identity, zero, Kronecker product; use stable increasing-label order with constants label -1). The actual local implementation:
```python
from itertools import product
from collections import defaultdict
from math import prod
# F=(label,M0,M1), constants label=-1 and M0=M1.
def get(F,x): return F[1+(x.get(F[0],0) if F[0]>=0 else 0)]
def terminal(segs,defects,w,d,p):
 r=len(defects); labels=sorted({F[0] for D in defects for F in D if F[0]>=0})
 out=zero(d)
 for bits in product((0,1),repeat=len(labels)):
  pinned=dict(zip(labels,bits))
  br=[sub(mul(get(A,pinned),get(B,pinned),p),mul(get(B,pinned),get(A,pinned),p),p) for A,B in defects]
  if any(not any(x for row in C for x in row) for C in br):continue
  pre=[];groups=[]
  for seg in segs:
   c=eye(d);g=defaultdict(list)
   for F in seg:
    if F[0]<0:c=mul(c,F[1],p)
    else:g[F[0]].append(F)
   pre.append(c);groups.append(g)
  K=kprod(pre)
  for i in range(len(w)):
   H=zero(d**(r+1))
   for b in ([pinned[i]] if i in pinned else (0,1)):
    M=[]
    for g in groups:
     c=eye(d)
     for F in g.get(i,[]):c=mul(c,F[b+1],p)
     M.append(c)
    H=add(H,scale(kprod(M),w[i][b],p),p)
   K=mul(K,H,p)
  digits=list(product(range(d),repeat=r+1))
  T=[[0]*d for _ in range(d)]
  for I,ii in enumerate(digits):
   for J,jj in enumerate(digits):
    T[ii[0]][jj[-1]]+=K[I][J]*prod(br[t][jj[t]][ii[t+1]] for t in range(r))
  out=add(out,tuple(tuple(x%p for x in row) for row in T),p)
 return out
def contract(word,w,d,p,s):
 def visit(segs,defs):
  r=len(defs);out=zero(d);segs=[list(x) for x in segs]
  for k,seg in enumerate(segs):
   while True:
    i=next((i for i in range(len(seg)-1) if seg[i][0]>seg[i+1][0]),None)
    if i is None:break
    A,B=seg[i:i+2]
    if r+1<s:
     new=segs[:k]+[seg[:i],seg[i+2:]]+segs[k+1:]
     out=add(out,visit(new,defs[:k]+[(A,B)]+defs[k:]),p)
    seg[i:i+2]=[B,A]
  return add(out,terminal(segs,defs,w,d,p),p)
 return visit([word],[])
```
To reproduce certificate tests: flatten matrices, build echelon basis using pivot inverses mod prime; close A under right generator multiplication, close J under both multiplication sides by A basis, iterate J powers until zero or equal dimension. For endpoint cutoff test all lambda(X Z Y) on basis triples. Actual tests seeded Random(369), random upper triangular matrices d=2,3, unitriangular d=3; compare entire result with sum over all q<=4 assignments, each label weighted once, word length<=6, and all p above. For Heisenberg q=1..7 compare explicit pair moment formula with direct full assignment sum; for G84 check A dim5, J dim4, J^2 dim4, endpoint cutoff absent vs 1; use block-diagonal upper triangular plus E12/E21/I hidden block; for residue lifting use d=2 matrices lower-left divisible p and compare actual weighted contraction at precision H using residue certificate sH. Reproduction core is exact and includes actual bridge map; original full local harness also records counts and seeded draws.

### R143. Endpoint-first ledger

| Gate | Deliverable | Status |
|---|---|---|
| R135 | actual ordered commutator ideal filtration | derived |
| R136 | exact signed sorting + shared multi-segment tensor transfer; polynomial for fixed nilpotence index/dimension | derived and executed |
| R137 | polynomial finite-field source certificate; residue precision lifting sH | derived and executed on scalar modular rings |
| R138 | genuine noncommuting fully interleaved cheap Heisenberg control | derived and tested |
| R139 | exact consumer-specific two-sided contextual annihilator and scalar cutoff | derived and executed |
| R140 | actual G84 algebra M2 x field, acceptance quotient M2 vs baseline field; easy nonnilpotent control | derived and tested |
| R141 | original indexed signed source/residual/consumer transport | derived |
| R142 | local exact regression | executed |
| R7a'/LGC4d | global paid nonlinear contraction on actual nonnilpotent acceptance core or another valid source algorithm | OPEN |
| R7b'/LGC5 | unavoidable unrestricted deterministic cost, allowing arbitrary shared contractions/reordering/representations | OPEN P0 |
| R7c/LGC6 | original uniform Clay separation or sufficient central sandwich | OPEN P0 |
| LGC7/N6 | original conditional consumer | existing |

Next geometry-forward: R140 isolates actual noncommutative M2 acceptance core in G84, but easy repeat clause control prevents promoting this as intrinsic hardness. Investigate reusable source-specific products in this core (rank-one actual resets, repeated original labels, true source factorization, weighted scalar vs all endpoint matrix), or direct standard-machine resource theorem, not another compulsory rank or commutator invariant. Admit G85–88 noncrossing/cover, R128–134 matroid cuts, R136/R139 nilpotent and consumer-specific shortcuts, and arbitrary direct SAT decision; do not replace endpoint by exact count or maximal algebra optimization. Preserve zero mode, inhabited neutral fibre, signed residual, original time/k/Frob/history/precision and consumer. No new certification prerequisite, no P!=NP claim, no unrelated branch edits.

## 2026-11-24 — R144–R149: original clause-reset / signed ternary intersection contraction

Scope: Langlands only. G89–G93 (#1548/#119) are donor mathematics, not a branch migration. Continue actual R140 G84 matrices and R85 weighted rank-two Weil consumer. Gate numbering continues after live R143.

### R144. Actual rank-one clause reset
Project row vectors of the original G84 three-state transfer to their U,S coordinates (the rejected absorbing coordinate is retained in the source, not identified with an empty assignment). The induced literal matrices are I,Y=[[0,1],[0,1]], and boundary R=[[0,0],[1,0]]. For literal truth values L_jr, e_U^T prod_r Y^L_jr R=(1-V_j)e_U^T with V_j=prod_r(1-L_jr), since Y^2=Y and e_U^T R=0. Thus the actual weighted acceptance P_t=sum_x prod_i w_i(x_i) prod_j(1-V_j(x)); for R85 w_i=(1,z_i). No independence of repeated labels assumed. D_t=3A-4P_t, A=prod_i(w_i(0)+w_i(1)).

### R145. Signed ternary intersection (dual clause selection)
V_j is the indicator of a partial falsifying assignment sigma_j. Repeated identical pins coalesce; opposite pins make a tautological clause (V_j=0). Empty clause has V_j=1. For each partial assignment sigma use E_sigma(x)=1 iff x extends sigma. E_empty=1; E_sigma E_rho=E_(sigma union rho) on compatibility, 0 otherwise. The ternary pin states are unpinned (neutral, both values inhabited), pinned 0, pinned 1; incompatible intersection is bottom, distinct from neutral. Expand F_t=prod_j(1-E_sigma_j). Exact weighted contraction is sum over compatible selected clause subsets S of (-1)^|S| prod_{i forced by union} w_i(sigma_i) prod_{i unforced}(w_i(0)+w_i(1)). This is inclusion-exclusion on the original violation cylinders, not an assumed new intrinsic lower bound. Identical union states can merge with signed coefficients, not independent per-occurrence guard weights. Conflict graph alone is insufficient: the union records repeated same-polarity pins and pays their weights only once.

### R146. Exact sparse frontier
For a supplied clause order, frontier after step j is original guards appearing in both processed and remaining clauses. Initialize D[empty]=product of total weights of never-occurring guards. At each clause, copy each state coefficient to the unselected branch, subtract it into the compatible union state on the selected branch, and drop incompatible branches with an exact contradictory-pin certificate. Forget all guards at their final occurrence, multiplying by the weight of their pinned value or the sum of weights if unpinned. Merge equal remaining keys by addition; coefficient zero only deletes a contribution to this consumer, not the source fibres. At termination D[empty]=P_t. Inductively D is the signed sum over prefix selections with all completed guards contracted; future factors cannot mention forgotten guards, proving the step over any commutative ring. If max frontier width is b, at most 3^b live states and at most twice that many temporary branch contributions per clause. Fixed-width array implementation O(c q 3^b) ring operations and polynomial bookkeeping; sparse dictionary sorting may add log factors. Compare primal 2^b frontier DP on the same cut, which is a better worst-case width bound; dual advantage is sparse reached states or symbolic cancellation, not a superior universal exponent. No requirement to compute an optimal order. Exact component separation, duplicate clauses and subsumed violation cylinders can be simplified with certificates. Reverse direction: each expansion branch determines the chosen source clause occurrences and their intersection, but merged coefficients do not recover those choices; source IDs, signs and independent provenance remain attached. A final scalar cannot recover the complete source.

### R147. Symmetry/orbit contraction beyond wide frontiers
Suppose the normalized signed clause set is invariant under all permutations within supplied disjoint blocks B_l of original guards (can certify sufficient syntactic invariance by adjacent transposition checks on the set). Then F_t depends only on count vector h_l=sum_{i in B_l} x_i. For arbitrary signed and unequal weights form Q_l(u)=prod_{i in B_l}(w_i(0)+w_i(1)u). Exact P_t=sum_h F_t(x_h) prod_l [u^h_l]Q_l(u), where x_h is any canonical assignment of the indicated counts. Compute coefficient arrays by multiplication, O(sum_l |B_l|^2) ring operations; evaluate source on prod_l(|B_l|+1) representatives. Polynomial for fixed block count even without weight symmetry. Reverse orbit members are the original assignments with that count vector, not reconstructed from the contracted coefficient. Original clause example: all positive r-subset clauses on q guards, F=1 iff #zeros<r; P_t=sum_{h=q-r+1}^q [u^h]Q(u). For fixed r>=2, polynomial source size, complete primal interaction graph, nonnilpotent actual G84 transfer algebra, but one-block polynomial contraction. This is a negative control against mandatory frontier/algebra cost, not an intrinsic lower bound.

### R148. Precision / indexed transport
All contractions division-free. For actual R85 D_t=3A-4P_t, D mod 2^(H+2) and A at sufficient precision recover P_t mod 2^H by exact division of the known divisible residual; e.g. D mod8 yields P mod2. Ring result also applies to unramified extension coefficients, but only scalar modular rings were executed in this tranche. Preserve independent (history,tau,k,j,v,field,p_c,p,consumer) indices plus original clause/literal occurrence IDs, pin orientations, zero mode, conflict witnesses, signed subset residual, live frontier, and optional symmetry orbit certificate. Clause processing order is an algebraic contraction order, not physical chronology. The neutral pin does not stand for zero coefficient or absence of assignment. Exact accepting/rejected weights sum to A. G92 counting/decision distinction retained: this weighted contraction is not a compulsory intermediate for arbitrary decision algorithms.

### R149. Local acceptance and reproducible core
Executed in local Python integers and SymPy, seed 144. Actual 3x3 matrix reset truth comparisons 63/63 (all literal strings length 0..5); signed dual vs exhaustive 400/400 (q=1..8, 0..9 clauses, clause length 0..4, weights -3..3, repeated labels, contradictory pins, empty clauses); modular 2000/2000 (2,4,8,9,25); rank-two mod8 identity 400/400; all-positive r-subset orbit 165/165 (q=2..10, r=1..min(q,4), five signed weight draws). Total 3028 comparison groups. No CI/native kernel, no extension-field execution, no measured asymptotic speed claim.

Core pseudocode:
    normalize each clause to its falsifying partial assignment; skip contradictory pins
    last[i] = last clause containing i
    D = {(): product(sum(w[i]) for absent i)}
    for j,c in enumerate(clauses):
        E = defaultdict(0)
        for s,a in D.items():
            E[s] += a
            if compatible(s,c): E[union(s,c)] -= a
        D = defaultdict(0)
        for s,a in E.items():
            for i with last[i]==j:
                a *= w[i][s[i]] if i in s else sum(w[i])
                erase i from s
            D[s] += a
        reduce coefficients in target ring; remove zero coefficients
    return D.get((),0)

| Gate | Status |
|---|---|
| R144 actual G84 reset / weighted scalar | derived, tested |
| R145 signed compatible pin union | derived, tested |
| R146 sparse frontier contraction | implemented, tested |
| R147 certified block symmetry orbit contraction | derived; one-block family tested |
| R148 precision and indexed residual | derived; scalar mod8 tested |
| R149 local exact regression | executed |
| R7a'/LGC4d global paid nonlinear contraction | OPEN |
| R7b'/LGC5 unrestricted unavoidable deterministic cost | OPEN |
| R7c/LGC6 literal Clay separation | OPEN |

Next: actual mixed affine/orbit/frontier decomposition on original weighted Weil probe, not a compulsory rank invariant. For any global result admit primal decision, clause simplification, symmetry, contextual quotient, nilpotent sorting and arbitrary direct machine algorithms. No general Langlands correspondence claim or unrestricted separation. No unrelated branch edits.

## 2026-11-24 — R150–R156: mixed affine/orbit/pin interface and costed nonlinear packet composition

Scope: Langlands continuation only; G94–G98 donor source Agda #1548 head 5bfc4a078984, Lean #119 head 12ec96edf1b6 (live PR metadata verified). Their flat bijunctive cover obstruction and disjoint OR3 compositional bypass are credited, not new Langlands results. Continue R128–134 affine gluing, R135–143 contextual algebra, R144–149 actual reset and signed intersection. No unrelated branch edits.

### R150. Joint geometric interface
For original Boolean guards x, let gamma(x)=(Hx mod 2,Bx,x|K), with H binary, B nonnegative integral, K original labelled pins. Replace H by a row basis for rank r; restore redundant syndrome coordinates by the original row map. The pushforward W(gamma)=sum_{x:gamma(x)=gamma} prod_i w_i(x_i) charges each original guard exactly once. Joint rather than marginal pushforward is essential; no generic independence of chart observations. If using a fixed affine offset, add it once, not per block. A zero coordinate in the pin projection is an actual false branch; the earlier R145 unpinned neutral is represented by omission of the coordinate, not by that false value.

### R151. Division-free coefficient algebra
Use the group algebra of binary syndrome and pin coordinates tensored with the polynomial algebra of count coordinates. For columns H_i,B_i and e_i the pin coordinate unit or zero, the joint packet is prod_i (w_i(0)+w_i(1) X^H_i u^B_i Y^e_i). X and Y exponents add by XOR, u by ordinary nonnegative addition. Coefficient extraction gives W. No Fourier division or field assumptions. Induction on source labels proves the identity over any commutative ring. With r rank, k=|K|, L_j=sum_i B_ji, ambient M=2^(r+k) prod_j(L_j+1); reachable support can be smaller. Iterative monomial shifts cost O(q M) ring operations plus polynomial coordinate bookkeeping. Explicit reachable state enumeration is charged; large count coefficients encoded in binary do not automatically imply polynomial M.

### R152. Mixed separator law and exact observer collision
Let left/right share original S and have disjoint private interiors, with source weights assigned once. Suppose their private-contracted functions satisfy L(x_S)=ell(alpha(x_S)), R(x_S)=rho(beta(x_S)) for all original separator assignments (certify this factorization, not merely sampled equality). Then P=sum_{a,b} W_S(a,b) ell(a) rho(b), by partitioning the original separator sum. W_S is the joint pushforward of its original unary weights; neither private sum includes those weights. This extends to finitely many factors with a shared separator and pairwise disjoint private interiors. Each private consumer may use R136/R139/R146 or affine/orbit methods only when its boundary contract is certified. For general overlap graphs need further conditional messages or charge explicit separators. The matrices [[1,0],[0,1]] and [[0,1],[1,0]] have identical marginals and different (0,0) consumer; realizable by a unit-weight binary source with alpha=x and beta=x vs beta=1-x. Thus separate chart marginals do not determine the joint consumer. All delta consumers distinguish any unequal joint packets; a restricted actual consumer family may quotient further by its common kernel, but this is a scoped observation statement, not a mandatory computation or lower bound.

### R153. Disjoint nonlinear region packets and additive global interface
For disjoint original blocks B_j with local acceptance F_j, define P_j=sum_{x_Bj} F_j(x_Bj) w_Bj(x_Bj) X^(H_j x_Bj) u^(B'_j x_Bj) Y^p_j. Then P=prod_j P_j by distributivity and disjoint source weights. Apply any global acceptance test g of the joint coordinates after this convolution, giving P_t=sum_gamma g(gamma)[gamma]P. No need to expand G94 flat witness-preserving binary cover. Complexity O(sum C_j+m M^2) ring operations using direct convolution, plus coordinate bookkeeping and global consumer evaluation; C_j includes local packet discovery/construction. A supplied certified chart may reduce C_j, but a black box scalar cannot serve as a boundary packet without a factorization proof. Local bounded-size enumeration is one valid construction.
Actual disjoint OR3 family of G94–98 with global Hamming weight h and parity s of the first original guard in each block: each local packet sums the seven accepting assignments. At unit weights, local support consists of (s,h)=(0,1),(0,2),(1,1),(1,2),(1,3). Exact coefficients are respectively 2,1,1,2,1. Their m-fold convolution has 4m+1 reachable states for m>=1: for each h=m..3m-1 both parities occur (vary number a of first bits from max(0,h-2m) to min(m,h), an interval of >=2 integers for m>=1 and h<3m), while h=3m forces parity m mod 2. Each a in that interval is feasible because remaining pairs contribute h-a between m-a and 2m. Thus m=12,24,48 give 49,97,193 states and total acceptance weight 7^m. The added global observations are not an assertion that the G94 lower bound survives every additional filter. A desired Boolean g can be compiled via a unique-extension Boolean circuit/Tseitin graph into the earlier selector source; auxiliary weights must be unit on both values or explicitly retained, and size/cost of g charged. This example is a regional source control, not a proof of general contraction on every original Langlands selector.

### R154. Support and signed packet separation / reverse weld
Alongside ring-valued W retain Boolean support S(gamma)=exists x extending original acceptance and coordinate gamma. Compose S using OR/AND convolution independent of signed weights; it does not test W!=0. For example weights +1,-1 in the same inhabited neutral signature give W=0,S=1. Store one original local witness per inhabited coordinate or an exact local witness algorithm, and predecessor (old coordinate, local coordinate) for each inhabited prefix convolution state. Reverse gives one genuine source witness for any admissible target; it does not invert the scalar or recover all original witnesses. Store all alternatives if full fibre enumeration required, with output cost. Pin labels, local source IDs and original assignment constraints preserved. Independent history/tau/k/j/v/field/p_c/p/consumer indices and R145 signed subset residual retained; contraction order not chronology. Weight-independent S is source support, not nonzero weighted contribution support. Contextual annihilation does not imply S=0.

### R155. Rank-two terminal precision
For actual R85 consumer D_t=3A-4P_t with A=prod_i(w_i(0)+w_i(1)), all above packets and separator contractions are division-free. Work modulo 2^(H+2) for numerator, recover P_t mod 2^H; binary extension ring result algebraic, scalar modular tests only. If g filters accepting source, rejection is A-P_t relative to all original assignments (including any explicitly encoded auxiliary source, with intended unique-lift consumer accounted for). No mandatory counting for unrestricted deterministic decision. The mixed contraction theorem is conditional on supplied valid local signatures and paid packet construction.

### R156. Actual local acceptance and reproduction
Local Python integer and SymPy run, seed 150: 240 joint block-vs-exhaustive comparisons; 1200 modular comparisons (2,4,8,9,25); 586 reconstructed witnesses verified against original clauses and target signatures; 240 rank-two mod8 residual checks; 180 overlapping separator comparisons with arbitrary signed unary weights and private Boolean factors; 32 disjoint OR3 joint comparisons with exhaustive original sums; 3 large OR3 cases (12,24,48 blocks) exact total 7^m and reachable states 49,97,193; 2 collision controls (exact symbolic equal marginals, signed zero with inhabited support). Total 2483 comparison groups passed. No CI, native proof kernel, extension-ring execution or asymptotic runtime measurement. Local script langlands_r150_156.py; reproduction core below, standalone script not separately committed.

    gamma_add(a,b) = (a.s XOR b.s, a.h+b.h, a.p XOR b.p)
    block_packet(ids, clauses):
        for original local assignment y:
            if clauses_accept(y):
                t = sum_gamma(columns[i] for i with y[i]==1)
                W[t] += product(w[i][y[i]] for i in ids)
                S.add(t); local_witness[t] = y
        return W,S,local_witness
    D={zero:1}; T={zero}
    for region in disjoint_regions:
        W,S,local_witness=block_packet(region)
        Dnew[gamma_add(s,t)] += D[s]*W[t] for all s,t
        Tnew={gamma_add(s,t) for s in T,t in S}
        store one (s,t) predecessor per Tnew coordinate
        D,T=Dnew,Tnew
    P=sum(D[g] for g satisfying global filter)
    reverse target through predecessors and local witnesses

Test fixture uses random 1..9 guards, blocks up to size 3, 0..3 syndrome rows, 0..2 count rows with column entries 0..2, <=3 pinned guards, signed weights -3..3, random clauses including repetitions and empty clauses. Overlap fixture: 1..7 separator guards, two syndrome bits, count and pin first coordinate, one private Boolean per side, random Boolean tables on the indicated chart and private bit; compare direct full assignment sum against joint weighted law. OR3 q=3m exhaustive small m=1..4 (8 draws each), large m=12,24,48.

| Gate | Status |
|---|---|
| R150 joint source signature | derived |
| R151 division-free joint generating kernel | derived; packet convolution tested |
| R152 mixed separator law, marginal collision | derived and tested |
| R153 disjoint nonlinear regional convolution | derived and tested |
| R154 independent support and reverse witness weld | implemented and tested |
| R155 rank-two precision transport | derived; mod8 tested |
| R156 local regression | 2483 passed |
| R7a'/LGC4d general paid nonlinear contraction | OPEN |
| R7b'/LGC5 unrestricted deterministic resource obstruction | OPEN |
| R7c/LGC6 original endpoint separation | OPEN |

Next: derive paid mixed separator discovery and a regional tree contraction on the actual compiled selector with shared labels, including signed pin constraints and affine syndrome quotient compatibility. Need a theorem covering cyclic cross-region dependencies without compulsory expanded boundaries, or a direct endpoint argument. Do not infer unrestricted cost from M, flat cover, semantic backdoor, nilpotence, or rank. No general Langlands correspondence claim.

## 2026-11-24 — R157–R163: consumer-directed cyclic contraction and signed refinement faces

Scope: Langlands only, continue R150–156. Donor ideas from user-supplied COMP5u (Agda #1546 at 52013742c16e), F8 H05 evolution/refinement (Agda #1547 at 9b601db), and G99–104 (Agda #1548, Lean #119, supplied report). These are conceptual donors, not claims of re-executing their implementations. No donor branches changed. Endpoint remains actual R85 D_t=3A-4P_t, not a general Langlands correspondence theorem.

### R157. Consumer-specific monoid quotient (COMP5u donor)
For nonnegative additive count h and threshold consumer h>=a, use q_a(h)=min(a,h), with operation u⊕v=min(a,u+v). This is a monoid homomorphism; modular counts h mod d likewise. XOR syndromes and explicit original pins retain their previous semantics. For a supplied consumer factoring through these joint coordinates the contracted answer is unchanged over any commutative coefficient ring; no inversion or division required. Equality h=a needs overflow distinction (cap a+1), and arbitrary count consumers need their own sufficiency proof. Bound M_C=2^(r+k) prod_j(a_j+1) prod_l d_l with joint reachability allowed to be smaller. Use all required coordinates jointly, not independent marginals. Original count remains in source and may be reopened. The criterion is source/consumer dependent, not mandatory for decision.

### R158. Paid discovery of signed incidence regions
For each original guard i construct two clause-ID sets P_i,N_i indicating positive and negative occurrences. Group identical pairs by exact equality; source incidence scan and sorting polynomial (even dense q*c bit tables suffice). Duplicates within a clause are immaterial; tautologies are handled by both signs; an empty clause is immediately rejected. Every nonempty group has states all-zero, all-one, mixed (respectively flags 1,2,3); true-positive clauses receive P_i iff a one occurs, true-negative clauses N_i iff a zero occurs. The source clause predicate factors through OR of these flags, hence no semantic symmetry oracle required. For arbitrary unequal signed unary weights and syndrome columns, construct a joint group packet by iterating each original guard, OR-ing its zero/one flag, XOR-ing its syndrome and pin coordinate, and combining capped and modular counts. At most 4 M_C local states. Every source guard is weighted exactly once. Store original guard IDs and a witness per inhabited local signature. This is a sufficient syntactic partition, not necessarily maximal semantic compression.

### R159. Cyclic region frontier and actual control
Order the discovered groups (implementation uses first original occurrence). DP state contains which still-live clauses have been satisfied plus joint consumer coordinates. At each group OR its satisfied clause mask; when a clause reaches its last group, reject if not satisfied and otherwise forget its bit. Unseen clauses have deterministic unsatisfied status. Invariant: all completed clauses satisfied; live status precisely OR of processed true literals. Store ring-weight sums and source support separately in the sense that zero-weight inhabited keys survive, with a genuine witness. Reverse witness attached to each key by joining disjoint group assignments. Bound O(q M_C + m 2^b M_C^2) ring operations and polynomial bookkeeping, where b=max number of live clauses after a group cut, m=number of groups; witness bitsets add polynomial q cost. This is a sufficient order-dependent bound, not a universal lower bound; no optimal order finder claimed.
Concrete cyclic source: m groups each with n guards; for each j one clause OR(all positive B_j, all negative B_{j+1}), cyclic wrap. Only forbidden neighboring sector pair is (all-zero,all-one). Unit-weight sector multiplicities c=(1,1,2^n-2). Independent transfer T_ij=c_j except T_01=0; total accepting multiplicity tr(T^m). Actual local run discovered m groups and contracted joint parity of alternating original coordinates, count capped at 3 and count mod 3. For (m,n)=(12,8),(24,8),(48,8): q=96,192,384; peak global DP keys 33 each; terminal keys 11 each; all three total multiplicities matched independent trace. Four small cyclic controls also matched exhaustive weighted packets. Wide clauses in large controls are not the actual compiled 3-CNF selector: deterministic OR-gate unique-extension encoding is available, but auxiliary incidence geometry and cost on that compiled source not executed here. Do not promote this as a general cyclic contraction theorem with bounded state count on arbitrary sources.

### R160. Signed refinement / observation face
Use column packet vectors x_j on exact stage modules, exact transitions T_j, coarse maps C_j and chosen linear sections J_j with C_j J_j=I on the coarse carrier (coordinate merge admits a section choosing representatives). For weighted packets use coarse transition U_j=C_{j+1} T_j J_j. Exact projected face defect:
  d_j=C_{j+1} T_j x_j-U_j C_j x_j
     =C_{j+1} T_j (I-J_j C_j)x_j.
Thus C_{j+1}x_{j+1}=U_j C_j x_j+d_j. This is the exact signed source-derived defect, distinct from earlier commutator residual and physical chronology. The lift J is a representative linear section, not an inverse recovering original assignments. C may merge inhabited support; support must remain an independent Boolean carrier. Affine offsets can be included as an extra constant coordinate, but the tested model is linear. Exact lumpability iff C_{j+1}T_j annihilates ker C_j (equivalently the defect map is zero), or on a specified reachable submodule if only that submodule is claimed. For count cap or modular quotient the monoid law establishes exact lumpability of shift transitions, whereas dropping a live clause status does not generally commute with the next source factor.

### R161. Reverse-solved scalar defect budget
For initial y_0=C_0 x_0 and coarse y_{j+1}=U_j y_j, define coarse adjoint g_N=g, g_j=U_j^T g_{j+1}. For exact terminal row f^T the exact scalar identity is
  f^T x_N-g^T y_N = sum_{j=0}^{N-1} g_{j+1}^T d_j + (f-C_N^T g)^T x_N.
Proof: subtract projected evolution from coarse, telescope with the backward adjoints; add terminal observation difference. If initial mismatch exists add g_0^T(C_0x_0-y_0). This is the endpoint-weighted refinement residual; no need to certify every face zero if actual contracted defect sum vanishes. Conversely if all residual terms vanish mod 2^H, then endpoint is certified at that precision; cancellation between terms is allowed only with exact sum certificate. Sufficient exact certificate on all reachable states can be checked using actual defect maps and backward rows when finite modules and bases are available, with cost charged. The full fine prefix x_j might be expensive; evaluating d_j or its scalar contraction is not automatically cheap. No free oracle or asymptotic speed promotion.
Source counterexample: original clause x OR y, future pin y=0. Dropping the prefix satisfied bit identifies histories x=0,1, but actual terminal acceptance differs. This shows the need for the F8-style transport defect or retained refinement. An observer zero, signed cancellation, modular zero and empty support remain separate.

### R162. Fail-closed consumer controller and indexed hyperfabric
A controller may ACCEPT a weighted quotient when its factorization or contracted defect is certified at target precision; REFINE the chart if a nonzero relevant defect is witnessed or the certificate cannot establish sufficiency; REJECT INVALID only for malformed source/weight/coordinate/section contracts (not ordinary unsatisfiability). An exact empty source support is a separate valid outcome; weighted zero does not establish it. This is a proposed decision contract, not an implemented adaptive optimal planner. Preserve the original R85 D=3A-4P precision loss of two binary digits (compute numerator mod 2^(H+2) to obtain P mod 2^H). Retain zero mode, inhabited neutral orientation, signed positive/negative and observation/refinement defects, independent history/time/tau/k/Frobenius/field/precision/consumer and original clause/guard identities. Algebraic stage index j not physical time or refinement k. Reopening complete source fibres remains optional and charged. G99–104 signed Shannon defects are donor analogy only; no candidate failure theorem is claimed here.

### R163. Executed regression and repo-only reproducibility
Standalone identical JavaScript BigInt reproducer in both branches: scripts/check_langlands_consumer_refinement_20261124.js (run with Node). The same function body was actually executed in local JS tool before commit, seed 157. Results: 240 exact joint source packet vs exhaustive comparisons, 1222 original witness/signature checks, 1200 modular weighted packet comparisons (weights reduced modulo 2,4,8,9,25 then exact arithmetic and output congruence), 4 small cyclic exhaustive comparisons, 3 large cyclic independent trace checks, 200 exact signed linear telescopes, 1000 congruence checks of those exact telescopes, 1 original OR suffix collision. Total 3870 checks/groups. Modular telescope checks are congruence of integer identities, not independent modular matrix execution; modular packet implementation reduces input weights, not every internal step. PRNG is a deterministic LCG with modulo sampling and correlated low bits; these are finite smoke/regression tests, not broad statistical coverage. No CI, SymPy/native kernel, unramified extension arithmetic, native Node process or production selector benchmark. No claim that this proves general Langlands or separates complexity classes.

| Gate | Deliverable | Status |
|---|---|---|
| R157 | consumer-specific capped/modular count quotient | derived and tested |
| R158 | syntactic signed incidence region discovery | implemented and tested |
| R159 | cyclic clause frontier with joint consumer | implemented and tested on explicit source controls |
| R160 | signed refinement/transport defect | derived |
| R161 | reverse endpoint adjoint telescope | derived and tested on integer linear fixtures |
| R162 | fail-closed endpoint controller / source preservation | contract derived; adaptive planner open |
| R163 | standalone exact regression | executed and committed |
| R7a'/LGC4d | general paid nonlinear contraction on actual compiled selector | OPEN |
| R7b'/LGC5 | unavoidable unrestricted deterministic cost | OPEN |
| R7c/LGC6 | original endpoint separation | OPEN |

Next exact obligations: (i) compile the cyclic source with unique extension and establish a quotient that preserves original regional structure after auxiliary introduction; (ii) apply this to actual R78–85 selector/Weil packet producer, not merely analogous wide clauses; (iii) implement scalar-directed defect evaluation without reconstructing fine packet when possible, charge discovery, section and adjoint cost; (iv) six-face indexed composition including changes in precision and independent support, with actual source-specific witnesses. No compulsory full reconstruction or generic representation lower bound.

## 2026-11-24 — R164–R169: original truth-graph contraction and direct rank-two revision residual

Scope: Langlands only. G105–109 (user-supplied Agda #1548 29f1690dc541, Lean #119 287e2eaac855) are conceptual donors: sound verification, neutral does not mean empty, shared repair cannot be charged per defect. No donor branches edited, no P!=NP claim. Reopened actual R78 compiler code at roadmap lines 1637ff (six-variable gadget digits 16763747126132141175, binary gate equivalences, private occurrence copies, zero padding) and R79–R85 actual 7D blocks/weighted probe. Continue R157–163.

### R164. Unique-extension quotient through compiled locally-full source
Original R78 deterministic truth graph Y_t has one extension ell_t(x) for each original Boolean assignment x, with flag b=F_t(x). The gate equations enforce unique values in topological order; six-variable zero gadget has unique all-zero solution; each private occurrence equality forces its original gate/source value; padding by the forced zeros preserves clauses. Thus restriction to original variables is inverse to ell_t on Y_t. The flagged module is the original accepting source, not the complete graph (all original x extend even if b=0). For weights only on original variables, or unit auxiliary weights, weighted trace of flag equals P_t=sum_x w(x)F_t(x), and baseline A=sum_x w(x). This allows R158 original signed-incidence discovery and R159 regional contraction without processing the auxiliary incidence graph as independent choices. Compiled source size and reconstruction of a witness cost polynomial in explicit source and emitted clauses. Arbitrary extra auxiliary weights/constraints/observations must be pulled back through ell_t and costed; cannot silently erase them. No generic recognition of arbitrary compiled instances claimed: require original source and compiler metadata, or an independently paid certificate. The implementation reproduces the R78 gate and G46 padding procedure for nonempty clauses (empty conjunction supported), with variable numbering convention and zero gadget unchanged. Empty input clauses require explicit constant false gate, not tested in this compiler tranche.

### R165. Direct rank-two scalar revision residual
For an appended original clause C with truth indicator Q_C, F'=F Q_C and L_C=sum_x w(x) F(x)(1-Q_C(x)). If C has no conflicting falsifying pins, evaluate L_C by the existing regional weighted contraction with all literal-false original pins; if both signs of a guard occur the clause is tautological and L_C=0. An empty appended clause gives L_C=P. No full joint packet or difference of large expanded arithmetic states required. D'=3A-4(P-L_C), so D'-D=4 L_C at fixed original source carrier and weights. Multiple appended clauses give disjoint first-failure masks and telescoping losses. For nonmonotone revision define L=F(1-F'), G=(1-F)F', so D'-D=4(L_w-G_w); individual signs retained. General revision may require new joint constraints and their cost. A valid satisfying assignment verified through ell_t gives support YES; weighted zero or a failed route does not give support NO. This is not counting repair basins or a universal lower bound. A signed loss scalar may cancel even when loss support is inhabited. Ring formula is exact at fixed coefficient precision; weighted loss mod2 is recovered from D difference mod8. No need to materialize all loss fibres for scalar consumer.

### R166. Indexed compilation/revision/precision cube
On source-indexed packet records with immutable original x labels, define three axes: a=append named original clause, b=replace original flag graph by its unique extension ell_t, c=reduce coefficient ring precision. When a operates after b it recompiles the revised graph using ell_t' on the same original x, not the old auxiliary coordinates; b after a uses the same ell_t'. Precision reduction is a ring homomorphism, independent of source and compilation. For raw D or P, a/b commute after the explicit original-label identification; a/c commute by ring homomorphism; b/c commute by weight pullback. This gives all six faces (two each) and six endpoint paths for this specified source cube, not arbitrary revision dynamics. Support is retained separately and never reduced modulo p. For recovered P from D, use mod 2^(H+2) before division by 4 and compare to P mod 2^H; reducing D to mod2 first destroys information. The executed finite checks compare canonical endpoint values at the relevant cube vertices and all six label orderings, not separately implemented path-dependent transitions; no native proof kernel. History, chronological time, refinement k, Frobenius, coefficient precision, source/consumer labels, signed gain/loss and zero/neutral support remain distinct.

### R167. Actual coefficient-ring cyclic controls
Use original R159 cycle with m groups of n=8 original guards, each clause OR(positive group j, negative group j+1). Compile through R164, retaining original source and flag. At each region the three sector masses are a=prod_i w_i(0), b=prod_i w_i(1), c=prod_i(w_i(0)+w_i(1))-a-b. Independent transfer T_j has column masses (a,b,c) with entry (all-zero,all-one) forbidden; trace of product gives weighted acceptance (cyclic indexing of group masses irrelevant by trace cyclicity when starting at consistent group). Use R85 actual finite coefficient ring (Z/8)[X]/(X^3+X+1), Teich lifts via eighth powers of nonzero binary residues, original w_i=(1,z_i). Compute regional DP and independent transfer trace. Actual large controls:
| original guards | compiled vars | emitted clauses | peak global frontier keys | P coefficients | D coefficients |
|---:|---:|---:|---:|---|---|
|96|1635|3277|4|[5,7,1]|[4,4,4]|
|192|3267|6541|4|[6,4,6]|[0,0,0]|
|384|6531|13069|4|[6,2,6]|[0,0,0]|
Three compiled assignments per large fixture reconstructed and checked. Large traces compare contracted original source and independent regional transfer, not exhaustive compiled CNF solving. Peak keys exclude compilation, local group construction and witness costs. Degree 3 insufficient for R86 Schwartz-Zippel support guarantee at these q; arithmetic control only. No local L/epsilon oracle executed; uses R85 proven scalar formula D=3A-4P.

### R168. Executed regression
Identical repository-only JS BigInt/finite ring implementation scripts/check_langlands_compiled_probe_20261124.js. Actual function executed in JS tool, then exact R78 padding convention corrected and updated function re-executed successfully. Seed 164 xorshift32. Exhaustive 64 zero-gadget assignments (unique all-zero); 7 Teich root checks; 2088 original assignment lifts across 100 small random sources q<=6 checked against original predicate, emitted CNF and independent unit propagation with zero gadget pre-pinned after its exhaustive uniqueness check; 100 weighted source/compiled/region comparisons; 100 directly pinned revision-loss and D difference comparisons; 600 cube endpoint/vertex checks and 600 label-order terminal checks; 3 large ring-valued cyclic trace controls and 9 large compiled witness samples. Counts are separate groups, not asymptotic evidence. Ring coefficients reduced during arithmetic. No CI, native Agda/Lean, Node subprocess, full production selector benchmark or local-factor oracle. Tests cover specific compiled source controls and small bounded-width input formulas; not general arbitrary succinct selector contraction. No files delivered in chat.

### R169. Remaining exact obligations
| Gate | Status |
|---|---|
| R164 original R78 unique-extension projection and reverse lift | derived and tested |
| R165 direct original pin-conditioned scalar revision residual | derived and tested |
| R166 source revision / compilation / precision faces | derived, endpoint checks only |
| R167 actual finite binary extension coefficient ring cyclic control | executed |
| R168 repo-only reproducer | committed |
| R165-general arbitrary revision and contextual defect evaluation without full fine packet | OPEN |
| R166-general path-dependent chart/precision refinement with explicit signed defects | OPEN |
| R7a'/LGC4d general paid nonlinear weighted contraction | OPEN |
| R7b'/LGC5 unrestricted deterministic obstruction | OPEN |
| R7c/LGC6 endpoint separation | OPEN |
Next: construct source-derived backward consumer rows for general bounded-frontier factor schedules and use actual pin loss queries for scalar-directed chart repair, retaining support witnesses and exact gain/loss. Prove when certificates can be obtained without full fine packet, including cyclic graphs beyond this family. Do not charge every local defect as independent work or infer hardness from compiled source size. No general Langlands correspondence or Clay separation claim.

## 2026-11-24 — R170–R176: joint backward environments, signed revision and precision-local consumers

Scope: stay on Langlands #1549/#120 only; P vs NP is the overarching endpoint but its branches are untouched. Read supplied G131–136 reverse scalar DAG and G137–142 finite obstruction reports. Direct donors: G131 original unary-weight derivatives, G132 shared reverse accumulation, G133 neutral/joint controls, G137–139 finite invariant search and G140 global fixed-rank anti-control. No claim of re-running their implementations. Starting Langlands heads 650a1c218eb2 / 41ee9b63851e, identical R169 roadmap blob 582694331e352e2c2b9e592e7142869d28ca6dc9. Reuse R78 unique extension, R85 actual rank-two scalar, R88 shared failure atom, R146 frontier, R158 incidence regions, R160–161 reverse defect telescope, R165 original pin loss, R167 coefficient-ring control. Standard variable elimination / sum-product inside-outside and reverse differentiation used; no literature novelty claim.

### R170. Original source elimination tree and joint weighted environment
P=sum_x prod_i w_i(x_i) prod_j Q_j(x_Cj), D=3A-4P. Retain original guard labels; compiler auxiliaries are eliminated by R164 only under its unique-extension and unit-weight contract. Make a factor tree by consuming each original unary/clause factor once and each intermediate factor once, product of bucket factors then sum over eliminated guard; final scalar multiplies remaining constant factors. For any node factor M_B on boundary B, reverse environment E_B=partial P/partial M_B (formal derivative treating entries as independent) gives P=sum_b E_B(b) M_B(b). This linearity uses the single-use factor tree, not arbitrary shared DAG occurrence duplication. In this elimination tree J_B(b)=E_B(b) M_B(b) equals original weighted joint marginal restricted to B=b: variables eliminated inside that subtree cannot occur outside it, so conditioning B partitions the full source sum; equivalently insert a boundary mask at the node and expand the contraction. Support computed separately via Boolean inside/outside (OR/AND) with each original guard branch logically allowed even when its coefficient is zero. Support of J_B is inside_B(b) AND outside_B(b), not J_B!=0. Sum and product reverse rules use projected indices. At a product bucket, prefix/suffix products of other child entries yield all child environments without division even when factors zero. Charge each factor once. Explicit original clause IDs, guard labels and elimination order retained separately from physical history and refinement.

### R171. All original single-factor replacements / clause deletions
For any single node replacement M_B -> N_B on same scope, exact scalar difference is sum_b E_B(b)(N_B(b)-M_B(b)); E_B independent of that node in the single-use tree. For original clause Q_j, E_j excludes that very clause. Removing it changes P by G_j=sum_b E_j(b)(1-Q_j(b)); gain support OR over falsifying clause assignments with outside support true. In particular J_j=Q_j E_j has zero entries precisely where outside can reveal a removed constraint's previously rejected fibres; do not try to recover E_j by dividing J_j by Q_j. D_new-D_old=-4G_j (fixed original carrier/weights). All original clause deletion gains can be evaluated from a single backward pass plus local sums; no independent full evaluation per clause. The same formula handles replacement by another predicate on same original scope with signed gain/loss separated by disjoint Boolean changes; only deletion tested explicitly. Sequential multi-revisions change outside environments in general; no assumption of independent updates.

### R172. Joint bag insertion and shared correction
For new clause/filter Q supported within existing bag B, L_Q=sum_b J_B(b)(1-Q(b)), D_new-D_old=4L_Q. If two appended filters Q,R fit same bag, P_new=P-L_Q-L_R+L_QR where L_QR=sum_b J_B(b)(1-Q(b))(1-R(b)). This is R88 shared failure atom contracted directly from joint bag. Arbitrary finite filters in same bag may be applied jointly by product of indicators, cost charged per local entry/filter. Original support and signed mass remain separate. Queries spanning different bags require adequate conditional paths or larger bags; independent marginals do not determine their joint. A zero weighted loss does not imply no source revision; an empty clause and tautology are valid boundary controls.

### R173. Consumer-directed precision and finite invariant scope
At a fixed environment, endpoint update DeltaP=sum_b E_B(b) delta M_B(b). Modulo 2^H, each entry delta M_B(b) need only be known mod 2^max(0,H-v2(E_B(b))) with valuation capped at H. This is a sufficient local precision taper, not a method for cheaply obtaining E_B or a necessary condition in the presence of joint cancellation. Compute D at precision H+2 before division by4 for recovery of P mod2^H. Ring in current regression is unramified binary coefficient ring, distinct from original Q3 Weil ramification. Signed losses and gains and support survive independently of precision. G137–139 finite invariant closure applies to any separately supplied uniform finite linear contextual transfer: for chain-ring length H and dimension d, nonzero context observable has a word of length <=Hd-1. It does NOT supply a uniform representation of all original formula inputs (G140 anti-control), and finite per-source bags need not bound across all sources. Apply only to explicitly certified fixed-carrier context schedules; do not treat a zero modular sample as exact support absence. These are algebraic deductions, no new valuation-adaptive planner or invariant closure implementation in this tranche.

### R174. Paid backward contraction and actual cyclic controls
Given supplied elimination ordering, maximum multiplied bag width b (number of original guard labels), and factor incidence count across buckets L (linear in #original factors + #eliminations for single-use tree), table arithmetic O(L 2^b) and corresponding stored table entries bound, plus polynomial index/projection bookkeeping. Product reverse uses prefix/suffix per entry, total same order; all bag J and all deletion losses computed within this budget. No search for optimal order or global polynomial bound. For new query of scope included in a bag, marginalize/filter its table, charge O(2^b) per query (or shared local computation). Large cyclic source uses n original Boolean guards and clauses (x_j OR NOT x_(j+1)), including wrap; original acceptance has only all-zero/all-one states, so it is an easy cyclic anti-control, not arbitrary cycle complexity. Independent 2x2 weighted transfer trace with pin filters confirms all bag entries. Actual source counts:
| guards | max bag scope | forward operation counter | reverse operation counter | joint entries verified |
|---:|---:|---:|---:|---:|
|12|3|343|1371|86|
|48|3|1495|5979|374|
|192|3|6103|24411|1526|
Counters include one multiplication per child per product entry, one add per eliminated entry, reverse product pre/suffix and 3 arithmetic ops per child per entry, one add per sum reverse entry. Exclude input construction, index/projection and Boolean bookkeeping, independent reference traces and local query sums. Not measured runtime; forward DAG is a tree of factor operations, scalar arithmetic can reuse entries. Large ring degree 3 is arithmetic control, not sufficient general randomized detection field size at n=192. No new compiled CNF execution in this tranche; original R164 equivalence permits source contraction, not a claim of new compiler tests.

### R175. Executed regression, repo only
Identical scripts/check_langlands_joint_backward_revision_20261124.js executed in JS tool, seed 170 xorshift32. Actual ring (Z/(2^h))[X]/(X^3+X+1) at h=1,2,3 with reduction during arithmetic; seven nonzero Teich lifts at mod8 verified. 100 pseudorandom original CNFs n<=6 (including empty/repeated/tautological clauses and cyclic controls), arbitrary ring unary weights or (1,z) Teich specialization. 300 scalar/support comparisons, 4500 joint weighted/support entry comparisons vs exhaustive source, 4800 independent lower-precision scalar/joint comparisons vs reduction from mod8, 1305 deletion gains/support and actual D delta comparisons, 1104 two-filter joint revision comparisons (including overlap), 180 inhabited zero joint-entry observations. Three larger cyclic independent transfer checks and 1986 pinned bag entries total (86+374+1526) verified. No explicit adaptive taper execution, proof kernel, CI, native Node subprocess, local-field epsilon/L oracle, full production selector benchmark or general Langlands correspondence claim. All code and derivations remain in repos, no chat attachments.

### R176. Remaining exact gates
| Gate | Status |
|---|---|
| R170 joint original guard environment with separate support | derived and tested |
| R171 shared signed single-clause deletion | implemented and tested |
| R172 mixed local filter loss / joint atom | derived and tested |
| R173 endpoint precision taper / finite context scope | derived; adaptive implementation open |
| R174 bounded-width shared cost and cyclic controls | derived, executed |
| R175 repository-only regression | executed |
| R7a'/LGC4d general paid nonlinear contraction | OPEN |
| R7b'/LGC5 unrestricted deterministic obstruction | OPEN |
| R7c/LGC6 original endpoint separation | OPEN |
Next: actual multi-bag conditional messages and incremental revision of backward environments with independently indexed time/refinement/precision, including direct scalar face defect without full fine reconstruction. Establish costed chart discovery and nontrivial cyclic shared dependencies (R159 regional 3-sector source, not just binary implication cycle), keep G140 global-rank anti-control. Retain zero mode, inhabited neutral, signed residual, source/consumer identity, ramification, Frobenius and independent history/time/k labels. No donor branch edits.

## 2026-11-24 — R177–R183: ordered cyclic separator transport, incremental signed revision and local precision execution

Scope: stay on Langlands only, both #1549/#120 at R176 starting heads 4d00318efa96 / a6ee4af75622 and common roadmap b4ac6c65e7ef0d66000fe021728299b7624621a2. Read both supplied pastes R170–176 and G143–148; latter is a conceptual paired original/refined state donor only (reported Agda #1548 62ae7f47484e / Lean #119 fdae7b5feb00), no claim of rerunning its code or editing P vs NP. Reuse R159 original cyclic wide-clause family, R164 original deterministic compiler projection, R165 signed rank-two revision, R170–173 inside/outside, joint overlap and local precision, R160–161 signed face and endpoint residual. Standard junction-tree path contraction and ordered segment product tree used; no literature novelty claim.

### R177. Multi-bag path environments
Given a supplied tree decomposition with running intersection and factors assigned exactly once, select a path of bags and absorb all incoming off-path subtree messages into their local factors. For a path bag with incoming/outgoing separator sets S,T, construct K(s,t)=sum over private bag coordinates of the resulting local factor conditioned on both separator assignments; incompatible shared labels have entry zero. Variables appearing in more than one path bag persist across the separators by running intersection. Source message delta propagates linearly by K^T (column convention), destination scalar delta is E_dest^T K_last^T ... K_first^T delta. Off-path environments and other path factors fixed; no division. Boolean OR/AND transport independently supplies source support for actual original/revised messages, not for the signed arithmetic difference as if it were a Boolean predicate. Multiple changed factors require mixed terms. General path identity derived, not a new arbitrary-tree implementation; tested specialization is cyclic three-sector transfer with closing sector retained, below. Cost per path bag is its local table enumeration and separator representation, not free discovery or arbitrary global joint recovery.

### R178. Actual R159 ordered cycle, incremental product tree
Original m disjoint nonempty regions B_j, cyclic clauses OR(all positive B_j, all negative B_(j+1)). Three sectors 0=all zero, 1=all one, 2=mixed. Original guard weights multiply once. Under original local unit pins, construct masses by four-flag OR DP (empty, only zero, only one, both); retain Boolean support independent of ring mass, including zero weights. T_j(i,k)=mass_j(k) except forbidden (i,k)=(0,1), then exact zero and false support. Cyclic contraction P=tr(T_1...T_m) with consistent cyclic labelling; each region factor consumed once. A regional unit constraint modifies one T_i, with unchanged original baseline A for acceptance filtering. E_i=T_(i+1)...T_m T_1...T_(i-1). Delta P=tr(delta T_i E_i). Ordered balanced segment tree caches interval products including identity padding, never assumes commutation. Local change recomputes log2 padded m ancestor products; arbitrary interval query O(log m) matrix products; original sector DP O(|B_i|) ring operations; full build O(sum region sizes + m) for fixed 3 sectors. Storage O(m) matrices plus original labels and input weights. The original source can be reopened and locally pinned weights reconstructed; no full witness extraction implementation in this tranche. R164 equivalence permits original source contraction under unit-weight auxiliaries; no new compiled CNF execution. The large fixtures use nontrivial mixed sectors, not only all-zero/all-one implication cycle.

### R179. Two-bag signed mixed correction and independent loss support
For i<j write P_scalar=tr(U T_i V T_j W), where U,V,W are ordered products before, between and after the edits. On replacing T_i by T_i+delta_i and T_j by T_j+delta_j, exact new-old difference is
  tr(U delta_i V T_j W) + tr(U T_i V delta_j W) + tr(U delta_i V delta_j W).
Last term is cross-path defect missed by independently using both old environments. If applying sequentially, updated second environment already incorporates it. Original single-unit insertions in two disjoint regions also give genuine loss strata by complementary pins: L_i, L_j, L_ij computed on original accepted cycle using opposite local pin, with the other region unpinned for single losses and both opposite pins for shared loss. Then P_new=P-L_i-L_j+L_ij. The support of these original losses computed separately via Boolean matrix products; signed delta matrices are only arithmetic and are NOT support carriers. This is a direct R88 joint atom across different bags without full joint distribution. A revised weighted zero or zero delta is not emptiness. For arbitrary replacement matrices, mixed signed identity persists; gain/loss support requires original masks, not signed coefficients.

### R180. Executed local consumer precision taper
In the fixed old environment E_i, write Delta P=sum_k e_k delta mass_i(k), where e_k=sum over l allowed(l,k) of E_i(k,l). For output P mod2^H, capped valuation s_k=min(H,v2(e_k)) (minimum coefficient valuation in the unramified basis) permits computing/storing delta mass only mod2^(H-s_k). This is sufficient since discarded term times e_k lies in (2^H). Local environments themselves must be obtained with certified precision; old environment not reusable for arbitrary simultaneous revision without R179 mixed correction. Implemented entry truncation and recombination at H=1,2,3 in actual (Z/32)[X]/(X^3+X+1). Across 103 fixtures and all three target precisions, aggregate 1854 coefficient-precision exponent units requested before taper (3 sectors per fixture per H) and 143 exponent units omitted, i.e. 1711 retained; each unit corresponds to one binary digit per coefficient of the fixed degree-3 ring. These are sufficient residue-width counters, not physical memory savings, reduced arithmetic cost or adaptive construction at low precision: implementation first constructs full mod32 masses/env, then truncates their delta and verifies. Seven nonzero root lifts via 32nd powers checked to have order dividing 7; this permutes residue samples, not an assertion of identical input-residue lift. At fixed A, D_new-D_old=-4 Delta P; recover -Delta P mod2^H from mod2^(H+2) difference, actual checks executed. Original Q3 ramification distinct from binary coefficient precision.

### R181. Indexed refinement and conditional transport boundaries
At any fixed source, ring reduction commutes with ordered product tree construction and local update by homomorphism. If applying a coarser separator projection C along a path, exact face defect d_j=C_(j+1) K_j^T x_j - U_j C_j x_j, with chosen coarse map U_j, is retained and telescopes under R161 destination adjoint. Source revisions, ordered transfer positions, refinement k, history/time, original ramification and Frobenius, precision and consumer remain independent; a product-tree level is not physical time. Exact update and precision transport do not imply arbitrary coarse projection naturality. No new general path-dependent six-face cube test here. Fixed context invariant results G137–140 require supplied finite carrier, not a global bound on all Langlands inputs. Preserve zero mode and inhabited neutral fibres; no mandatory global exact linear representation.

### R182. Actual local execution and repository-only regression
Identical script scripts/check_langlands_cyclic_path_revision_20261124.js executed in JS tool (seed 177 xorshift32), actual arithmetic reduced modulo32 in degree3 quotient, Boolean support separately. 100 small original cyclic sources m=3..4, region sizes 1..2, arbitrary ring weights or nonzero root weights; 400 exhaustive original source checks (initial, joint pins, one complementary loss, shared complementary loss), 103 mixed signed residual checks, 206 incremental updates, 103 revised support/sequential rebuild comparisons, 1236 local precision comparisons (3 entries plus scalar for each H=1..3), 309 actual Weil residual precision checks, 7 root identities; 13 inhabited zero mod2 base observations. All fixtures also checked initial direct transfer and complementary loss mass identity (103 each). Three larger controls m=12,48,192 with 8 guards/region, 96/384/1536 original guards, padded initial products 15/63/255 and per local update 4/6/8. Both updates on each fixture have these counts. Large original assignment counts not enumerated; direct sequential matrix transfer reference used. Large degree3 field insufficient for general R86 random detection guarantee, arithmetic control only. No full witness search, native proof kernel, CI, Node subprocess, local-factor oracle, actual adaptive low-precision evaluation cost measurement, arbitrary-tree implementation or production benchmark. All artifacts committed to repo only.

### R183. Remaining exact frontier
| Gate | Status |
|---|---|
| R177 general tree-path separator formula | derived, tested specialization only |
| R178 original cyclic ordered product tree | implemented and tested |
| R179 multi-region mixed signed and support loss | derived and tested |
| R180 local valuation taper and D precision | truncation implemented and tested; cost-saving producer open |
| R181 indexed arbitrary chart face defects | conditional algebra, general cube execution open |
| R182 repo-only regression | executed |
| R7a'/LGC4d general paid nonlinear contraction | OPEN |
| R7b'/LGC5 unrestricted deterministic obstruction | OPEN |
| R7c/LGC6 original endpoint separation | OPEN |
Next: move beyond the R159 cycle to actual source-derived tree decomposition / mixed separator discovery with shared regional factors; implement path transport on arbitrary supplied tree decomposition and extend incremental updates to nonlocal edits, plus certified low-precision producer without first materializing full precision. Keep original source and support provenance for reverse witness recovery. No global Langlands correspondence or Clay endpoint claim. No donor branches edited.

## 2026-11-24 — R184–R190: source-discovered geometry, bidirectional path defects and demand-directed residue evaluation

Scope: stay on Langlands #1549/#120 only. User explicitly reiterates geometry-forward, steelman, BIDI and reverse solve; retain zero mode, signed residual, inhabited neutral, source provenance and independently indexed hyperfabric. Starting heads d961b5f7aeaa / b793fb2b4cde, common R183 blob 61a72100d1139a3483d34c4e72036f7ad12fb2e2. Read attached R177–183 and user-supplied G149–154 (reported P vs NP heads 92d62779be87 / 79604d8b7b21). G149 deterministic unique extension, G150 direct source verifier without assignment mask and G152 actual rerouting distinct from fixed witness loss are conceptual donors only, not a change of programme or independent execution of donor code. Reuse R114 affine syndrome, R121 transverse gluing, R146 frontier, R158 signed incidence, R164 unique extension, R170–176 joint outside environment, R177–183 path revision and precision, R85 rank-two consumer. Standard min-fill elimination tree, junction-tree sum-product and valuation arithmetic are used; no literature novelty claim.

### R184. Paid source-derived geometry
Build original primal guard interaction graph by cliquing each original clause scope. Greedy min-fill chooses remaining guard with least number of missing neighbour edges, breaks ties by remaining degree then original order. Make bag B_i = {i} union current neighbours, fill neighbour clique, eliminate i. Parent is earliest eliminated remaining neighbour, or artificial empty root if none. Every separator is included in its parent (fill clique), every original factor is assigned once to the bag of its earliest eliminated guard, empty clause to empty root, and every guard weight assigned once to its own elimination bag. Running intersection follows because a surviving neighbour appears in the parent and continues on its ancestor path until eliminated; all bags containing a guard thus connect to its elimination bag. Verify all these properties in actual implementation. Empty/repeated/tautological clauses and disconnected components handled. The supplied R164 deterministic extension permits use of original guard graph only with original source labels and unit auxiliary weights; not a free generic recovery of original source from arbitrary compiled CNF. Steelman: this is one paid heuristic, not optimal decomposition or compulsory primal chart; R158 signed incidence and affine/nonlinear charts remain admissible and may beat it. Naive repeated fill-pair scans cost polynomial (O(n^4) pair checks worst-case), plus scans, factor placement and certification. For bag width b, rooted messages require O(sum_i 2^|B_i| (1+degree_i+assigned factor count_i)) ring/Boolean operations plus explicit source/index bookkeeping; actual implementation scans clause list per bag entry, so charge this overhead separately. No global bounded-width claim.

### R185. BIDI path contraction and original witness reverse lift
For adjacent bags i,j use actual intersection S_ij with original labelled coordinates. Directed message m_i->j(s) = sum over B_i assignments restricting to s of local factor times all incoming messages excluding j. The running-intersection property ensures conditional separation and independent factor ownership; no division by weights or marginal entries. Reverse directions computed on same tree, caching directed messages on demand. Rooting at any bag yields original P by final sum. Boolean messages use OR/AND with independent logical support; zero coefficients do not invalidate a logically allowed assignment. Each inhabited message entry retains one actual bag assignment with compatible child support. Root witness then recursively follows these backpointers and verifies original clauses and pins; one witness, not all-source enumeration or numerical inversion. For a pin at i, replace local factor by masked version; delta is signed new-old. Traverse any path i->j absorbing fixed off-path messages, multiply signed delta along the path and sum at destination. This is the actual R177 path kernel implementation for discovered trees. Tests compare three paths: A on old source, B on source already pinned by A (reverse orientation), and A on source already pinned by B. Shared mixed identity Delta_B P_A - Delta_B P = Delta_A P_B - Delta_A P. Revised models built separately for checks; no dynamic nonlocal cache invalidation/update implementation yet. Signed arithmetic delta is not Boolean support; independently reconstructed support and witness. Once appropriate incoming messages cached, charge path table entries and degrees; cold messages, search for path and source construction are additional cost. No arbitrary joint marginal recovered from independent marginals.

### R186. Reverse-demand precision producer (not post-hoc full precision truncation)
For a fixed division-free scalar DAG and requested output mod2^h, compute capped certified lower valuation bounds L(g) without evaluating intermediate ring values: leaves use actual coefficient input valuations capped at H; sum gate min of input bounds, product gate capped sum. These are lower bounds, not exact valuations of intermediate sums (cancellation can increase). Starting at root demand h, reverse topological demand propagation: if demand <= L(g), residue is known zero and need not evaluate gate. Otherwise a sum asks both children for same precision, a product uw asks u for max(0,h-L(w)) and w for max(0,h-L(u)). Multiple consumers share maximum demand. Proof: chosen child representatives preserve guaranteed valuations whenever their demand exceeds valuation bound; omitted child has true value divisible by required modulus. Product error lies in (2^h) since each child error times the opposite actual/representative value is sufficiently divisible; when a child omitted because its bound meets demand, its replacement zero is also valid. Sum by ring homomorphism. Forward evaluate demanded residues only at their requested moduli, skipped gates use zero; do not compute full intermediate values before pruning. Leaf valuations read from provided mod32 input coefficients, not free high-precision black-box information; valuation propagation, graph building, precision scheduling and support messages charged separately. Multiplication still uses ordinary JS numbers, not bit-packed kernels; exponent budgets and skipped gate counts not measured runtime or memory savings. This is a sufficient structural taper, not globally minimal demand; cancellation-aware strengthening can be sought with paid residue probes. Retain support and provenance even when all numerical gates omitted. R85 D=3A-4P at precision h+2 (fixed original A), actual signed pin-loss checks for h=1..3 with mod32 arithmetic.

### R187. Steelman neutral and nonzero large tree controls
Use branching tree of triangles with parent p=(i-1)/2 for sibling pair i,i+1 (0-based odd i), clauses (p OR i OR i+1), (not p OR not i OR i+1), (p OR not i OR not i+1), original labels shifted to 1-based. No supplied decomposition; min-fill discovers maximum bag size 3. Two controls per n=31,63,127: mixed random ring weights with high valuations (joint pinned endpoint structurally zero mod32, support inhabited), and nonzero-mod2 control w_i(0)=[2,0,0], w_i(1)=[1,1,0], both selected pins 1. All-ones source accepted, only all-ones monomial odd, hence nonzero residue (unit powers in F8), prevents all numerical work being pruned. Actual results:
| guards | clauses | bag width | fill pair checks | nonzero-control aggregate uniform exponent budget | demanded exponent budget |
|---:|---:|---:|---:|---:|---:|
|31|45|3|1385|4950|2123|
|63|93|3|6249|10230|4277|
|127|189|3|26633|20790|8622|
The neutral controls each used zero numerical gate exponent units across H=1..5 while retaining original support and witnesses. This is intentional high-valuation degeneracy, not a general saving. The nonzero controls each have approximately 42% demanded exponent budget retained. At n=127 actual nonzero-control path visited 12 bags / 64 bag entries, excluding off-path construction. No brute enumeration at large n; independent full-precision message evaluations and direct original witness verification, small cases exhaustive. No claim about generic source width or R86 detection guarantee; degree3 arithmetic control only.

### R188. Geometry-forward BIDI and remaining chart choice
Forward source discovery and backward consumer demands meet on original labels. An optimal chart is not demanded: any certified separator, signed-incidence region, affine syndrome or nonlinear route with adequate support/provenance may compete; paid cost includes discovery, storage, update, reconstruction, precision planning. High valuation zero is an arithmetic annihilator, not empty support, and positive/negative revision residual and common mixed correction are independent. Source revision and chart change distinct from actual candidate rerouting (G152 donor). Independent chronological history, refinement k, source/consumer labels, coefficient precision, original Q3 ramification, Frobenius and bag/path position kept; no identification of tree levels with time. General chart face defect R181 remains open beyond the executed original pin-revision faces. General nonlinear contraction not solved by finite chart or structural valuation.

### R189. Actual regression and repository-only receipt
Identical scripts/check_langlands_geometry_demand_20261124.js; final corrected code executed in JS tool, seed 184 xorshift32. Initial attempt stopped on harness variable shadowing before commits; corrected and ran, then added nonzero large controls and D recovery and reran. Exact arithmetic in (Z/32)[X]/(X^3+X+1), demand evaluation at h=1..5. 100 pseudorandom small original CNFs n=2..8, 6 large controls above. 400 exhaustive source scalar/support comparisons (old and three pins), 318 bidirectional path residual checks, 106 mixed face comparisons, 216 actual original/pinned witness validations, 530 demand vs full-precision residue comparisons, 318 rank-two signed recovery checks, 51 inhabited zero-mod2 original endpoints. Aggregate uniform arithmetic-gate precision exponent budget 116130, demand budget 18349, 32801 gate evaluation omissions across these 530 evaluations (counts exclude extra base precision evaluations for probe checks, leaves, symbolic construction, support, index bookkeeping). Fixed degree3 each exponent unit equals 3 coefficient bits; no physical storage or runtime claim. No CI, native proof kernel, Node subprocess, production local-factor oracle, full compiled CNF re-execution, optimal chart search, or arbitrary nonlocal incremental cache implementation. All artifacts in repos only.

### R190. Remaining gates
| Gate | Status |
|---|---|
| R184 paid original min-fill geometry and certificate | implemented and tested |
| R185 original multi-bag BIDI path / witness reverse lift | implemented and tested |
| R186 actual demand-directed numerical producer | implemented and tested |
| R187 neutral and nonzero branching controls | executed |
| R188 arbitrary chart refinement / cost selection | conditional; open generally |
| R189 repo-only regression | executed |
| R7a'/LGC4d general paid nonlinear contraction | OPEN |
| R7b'/LGC5 unrestricted deterministic obstruction | OPEN |
| R7c/LGC6 original endpoint separation | OPEN |
Next geometry-forward maximum cut: compare actual primal bag vs signed-incidence/affine mixed interfaces using the same original source and endpoint, derive certified consumer-aware quotient without global truth-mask materialization, implement nonlocal message-cache update with exact mixed defects and cancellation-aware precision. Steelman all shortcuts and charge chart construction. No general Langlands correspondence or Clay separation claim, no donor branch edits.

## 2026-11-24 — R191–R197: competing original charts, common contextual quotient and exact paired finite transport

Scope: Langlands #1549/#120 only. Starting heads 0572455be409 / 94af75749f29, common R190 roadmap 0805d96fe528508bef5129a5eb92a6ac78357fd4. Read attached R184–190 and user-supplied G155–160 (reported P vs NP #1548 7bf3c0dd41d3 / #119 adc1fbb9395e). G155 finite paired secants, G157 reverse covector, G158 mixed source square and G159 changed-support anti-control are conceptual donors; no rerun or edits to those branches. GEOMETRY-FORWARD, endpoint-first, steelman/BIDI/reverse solve. Reuse R114 feasible affine syndrome layers, R150–152 joint signatures, R158–159 signed incidence frontier, R164 original unique-extension projection, R165 signed Weil revision, R170–176 backward environments, R177–183 ordered cross-region transport, R184–190 source geometry and precision. Standard binary linear algebra, ordered decision diagrams / suffix-function interning and product-difference telescoping are used, no literature novelty claim.

### R191. Certified original affine extraction
Group original clauses of width 2 or 3 with distinct variable labels by exact sorted scope. A clause on its full scope forbids exactly the assignment with its negative literals set to 1 and positive literals to 0. If all forbidden assignments of one parity p occur in that scope group, their conjunction is exactly XOR(scope)=1-p. Remove only those original clause IDs (duplicates may be removed together); retain other clauses. If both parity sets occur extract both rows, which is contradictory. Original formula F equals residual CNF F_res AND Hx=s over F2, pointwise; forward and reverse proof is equality of the prohibited assignment set. Keep original labels and extraction ledger, do not infer parity from an incomplete set. Empty clauses remain explicit rejection. Discovery is a source scan, constant-size scope pattern enumeration, grouping and linear algebra, not a semantic affine-factor oracle. Scope restricted to widths 2/3 for this implementation, not all affine subrelations. R164 original deterministic compiler equivalence applies if its unique-extension/unit-auxiliary contract is paid; no new compiled-CNF execution. Original R85 P=sum_x w(x) F(x), D=3A-4P, unchanged.

### R192. Three actual source charts in one original order
Use original guard order (not optimal/min-fill primal ordering). Primal chart retains the assignments of processed guards whose last original incident clause is not yet completed, evaluates each clause at its last guard, then forgets dead coordinates. Signed incidence chart retains live satisfied-clause bits, ORs actual positive/negative occurrence masks, rejects an unsatisfied clause at its last guard and forgets its bit. This is per-variable R159 status geometry, not new grouped-region execution. Mixed chart uses residual clauses plus partial syndrome h_k in the original extracted row coordinates (including redundant rows); prune iff s-h_k not in span of suffix columns, with actual binary elimination bases. At terminal require residual status completed and h_n=s. Inconsistency detected by initial suffix membership. Original guard weights charged once; labelled transitions b=0/1 retain original index. Reachable layered graph discovered by actual states, not all ambient assignments. Original clause parsing, mask and suffix-basis construction, bit widths, state dictionary and membership cost charged; one attempted transition is not one equal-cost CPU instruction. Given graph with E edges and N layers, forward/backward weighted/support evaluation O(E+N) ring/Boolean operations plus state storage/bookkeeping. No generic polynomial graph-construction guarantee. A full primal frontier is not mandatory, and a poor fixed order is not a lower bound for optimized primal or other nonlinear algorithms.

### R193. Common reverse contextual quotient
On each constructed layered graph, terminal acceptance key is 0, dead continuation key -1. Backward at original variable k, intern ordered pair of keys of the 0/1 successors, replacing all-dead pair by dead. Induction shows keys characterize exact Boolean suffix functions on remaining original coordinates; two histories with same key have identical weighted suffix consumer for arbitrary shared original unary weights and future pin filters. No arbitrary history-dependent observation assumed to factor. Preserve original labels on each edge and Boolean support independent of weighted value; accepted witness recovered by following actual labelled compatible edges and directly checking original F and pins. Intern across all completed charts using one dictionary per layer; reachable nondead suffix-class sets and root key coincide because original relations are identical, despite different forward state counts. Actual common interning test compares sets at each layer; not scalar coincidence. This is a coarsest deterministic same-depth suffix-function quotient for these Boolean continuations, not a general nonlinear quotient, not a bijection of original histories, not a promise to generate it efficiently without a paid forward graph. Construction O(E) dictionary operations plus representation costs after graph available; no mandatory materialization of larger chart. A current numerical zero or equal scalar is not a valid substitute for suffix keys. Weight and pin edits at fixed original order commute with this quotient. Clause edits changing F require new structural certificates or an explicit paired chart covering both sources.

### R194. Exact finite paired BIDI transport and mixed correction
For fixed chart, source pin filters change edge weights and admissibility on original labelled edges. Let T_k^old and T_k^new be the two actual weighted transitions, f_k^old the old forward prefix row, g_(k+1)^new the new backward suffix column, terminal unchanged. Exact product difference:
 Delta P = sum_k f_k^old (T_k^new-T_k^old) g_(k+1)^new.
Proof by expanding product difference with old prefix and new suffix, no infinitesimal or frozen old covector. Reverse orientation uses new prefix/old suffix with opposite signed edge delta (or reverse the old/new roles); tests evaluate actual oriented pairs. With two distinct pin edits, mixed difference M=P_11-P_10-P_01+P_00 is same in both orders; each constituent signed edge contraction paid and tested in both base graph and quotient. Terminal equality alone does not say internal transports agree. For all old/new pin combinations original A fixed (acceptance filtering not changing original weights), Delta D=-4 Delta P at mod2^(H+2) recovers -Delta P mod2^H. Support/witness computed from actual revised admissible graph, not signs of numerical differences. Neutral endpoint may have changed interior. Paired transport applies to weight/mask revisions on fixed structural chart, not arbitrary candidate rerouting, clause rewriting or arbitrary chart change for free. No dynamic nonlocal cache update in this tranche; separate forward/backward evaluations, then explicit secant sum. No compulsory dense global matrices.

### R195. Actual cyclic parity/incidence controls and paid comparison
Original m-region cycle, 6 original guards per region. Wide original clause OR(all positive region j, all negative next region) for each j, two local ternary odd-parity blocks per region encoded by four clauses each, and pair equality of first guards in consecutive regions encoded by two clauses. Thus 11m original clauses; extracted 3m rows, 10m original clauses discharged, rank 3m-1 from redundant cyclic equalities. All ones satisfies original F; w(0)=[2,0,0], w(1)=[1,1,0] in degree3 mod32, so base endpoint nonzero mod2 (only all ones odd monomial). Arbitrary source-order pins also tested. Measured chart construction counts:
| original guards | original clauses | affine rows/rank | primal peak / attempts | incidence peak / attempts | mixed peak / attempts | common quotient peak / total states |
|---:|---:|---|---|---|---|---|
|36|66|18/17|1024 / 19078|12 / 344|6 / 280|4 / 101|
|72|132|36/35|aborted at 30001 attempts|12 / 740|6 / 604|4 / 209|
|144|264|72/71|aborted at 30001 attempts|12 / 1532|6 / 1252|4 / 425|
Peak is number of reachable raw states in one completed layer, attempts includes both outgoing bit trials including rejected, total quotient states include terminal. Fixed 30000 attempt cap on large primal builds; the 30001st counted attempt triggers abort without evaluation. Aborted charts not counted as successful endpoint comparisons or included in common interning; no general primal impossibility claim. 36-guard raw totals 9540/173/141 respectively; same quotient from each. Larger mixed/incidence endpoint and support match, common suffix quotient matches. Large base P coefficients [3,31,2], [13,26,9], [21,31,29]. Smaller raw chart does not imply smaller runtime because syndrome basis work, wider bit representations and source chart extraction are additional; all three share final quotient only after constructing it. These controls deliberately have local affine structure and cyclic residual clause geometry, not arbitrary sources. Ring degree3 is arithmetic control, not R86 generic randomized support detection guarantee.

### R196. Actual regression and acceptance
Identical scripts/check_langlands_mixed_chart_secant_20261124.js executed in JS tool, seed191 xorshift32, exact arithmetic (Z/32)[X]/(X^3+X+1), original labels and clause/syndrome masks as BigInt. 100 small pseudorandom n=3..8 CNFs (including complete/incomplete parity patterns, contradictory parity sets, empty and repeated clauses), 3 larger cyclic controls; 8192 exhaustive pointwise extraction BIDI checks; 1200 original exhaustive weighted/support comparisons across charts and pins; 1228 inter-chart endpoint/support comparisons (includes mixed self-comparison) and 1228 graph-to-quotient endpoint/support checks; 2154 cross-chart layer class-set checks (includes reference self-comparison), max common peak4; 3070 oriented paired secant cases each tested on raw and quotient graphs; 307 mixed endpoint residual comparisons; 921 rank-two precision checks; 548 original/pinned witnesses validated (raw and quotient); 117 inhabited zero-mod2 endpoint observations counted across charts/pin cases. Added common chart interning and quotient secants, reran final code successfully. Two bounded primal construction aborts recorded. No CI, native Agda/Lean, Node subprocess, new local-factor oracle, compiled source rerun, independent large brute enumeration, incremental arbitrary cache invalidation, cancellation-aware precision strengthening, optimal chart choice or production runtime benchmark. No chat artifacts; no donor branch edits.

### R197. Exact remaining frontier
| Gate | Status |
|---|---|
| R191 original affine extraction with clause provenance | implemented and tested |
| R192 competing original primal / incidence / mixed charts | implemented and tested; two primal budget aborts |
| R193 common contextual suffix quotient | implemented and tested on constructed graphs |
| R194 paired finite secants, signed mixed revision and D recovery | derived and tested |
| R195 nontrivial cyclic affine/incidence controls | executed |
| R196 repository-only regression | executed |
| R188-general paid consumer-aware chart discovery/selection | OPEN |
| R7a'/LGC4d general paid nonlinear contraction | OPEN |
| R7b'/LGC5 unrestricted deterministic obstruction | OPEN |
| R7c/LGC6 original endpoint separation | OPEN |
Next maximum cut: discover compressed context directly from source without first generating a larger raw graph; extend source-derived mixed chart to actual signed incidence group packets plus affine crossing basis and original support witness; implement incremental nonlocal cache update / chart-changing finite secant with explicit residual for mismatched carriers, and cancellation-aware precision on shared quotient. Retain zero mode, inhabited neutral, original source/consumer identities, signed residual, ramification/Frobenius, history/time, refinement k, variable order/position, chart and precision independent. No general Langlands correspondence or Clay separation claim.

## 2026-11-24 — R198–R208 integrated source-to-endpoint contraction tranche

User direction: stop small bites; one integrated geometry-forward, steelman, BIDI, reverse-solved tranche. Stay on Langlands #1549/#120; P vs NP is a donor only. Inputs attached R191–197 and G161–166 (reported P vs NP heads bf355d0c26f7 / 9c4eda439fe3); causal output-cut and exact consumer geometry are conceptual donors, not new execution of their code. Live starting Langlands heads 8395071e813b / 7ccf1856df5d, common roadmap 045cee7ed54d2b288b9ac7400967974f31807221. Reuse R114 affine crossing spaces, R150–152 joint signature, R158 grouped incidence, R164 deterministic original lift, R165 signed original revision, R170–190 outside/precision/path, R191–197 extraction and paired secants. Standard subsumption, binary Gaussian elimination, sum-product and arithmetic DAG incremental evaluation used; no literature novelty claim. No other branches edited.

### R198–R200. Direct original paired geometry, grouped packets and crossing coordinates
Fix original labels and common weight carrier, old and revised original clause lists F0,F1. Independently extract exactly the width2/3 parity patterns from each as in R191; retain source IDs, remaining CNF and affine constraints H_j x=s_j. Group original guards by equality of all six attributes (positive/negative residual-clause occurrence sets, affine column) across BOTH source versions; group order first original occurrence. This joint refinement is essential when one edit changes incidence or breaks a formerly complete parity pattern. Each original guard weighted once. A nonempty group assignment has zero-occurs flag z, one-occurs flag o, parity p; exact packet computed by OR of flags and XOR of p with each original bit, storing weighted sum and separately logical support. At most four attainable signatures for a nonempty group (all-zero, all-one, mixed-even, mixed-odd), implementation allocates eight including neutral intermediate. A group satisfies positive incidences iff o, negative iff z; its syndrome contribution is p times its common column. The same grouping works for arbitrary unequal signed unary weights and original pins. Weight/pin changes do not require repartition; arbitrary new clause edits require a new certified joint chart, not reuse of incompatible keys for free.

At cut k for each source j, U=span of processed group columns, V=span of remaining group columns. If target not in U+V initially, this source is dead. Otherwise choose a particular solution of total column equation, let a_k be its prefix syndrome. Feasible partial syndrome is in a_k+(U intersect V), dimension kappa=rank U+rank V-rank(U+V). Compute intersection basis by projecting prefix columns modulo suffix span, eliminating projected columns while tracking actual prefix lifts; kernel relations give exactly U intersect V. Use actual group column and parity to update decoded partial syndrome, reject if outside target+next suffix span, then encode in next crossing basis. Implementation stores coefficient bitmask at original pivot positions (sparse positions, not physical packed kappa-bit allocation), not raw ambient syndrome as state; basis construction, lifting and BigInt costs explicitly charged. Affine consistency is not residual CNF support; retain them jointly. All-zero parity is not a rejected or empty fibre.

### R201. Direct residual-obligation quotient before raw graph construction
Represent each remaining clause as a set of signed group literals. A group containing both signs in a clause makes that clause tautological (nonempty group with identical signed incidences). Each step removes satisfied obligations, strips processed literals from unsatisfied ones, rejects empty obligation, deduplicates remaining obligations and removes any superset of a smaller obligation. Pointwise Boolean equivalence by CNF subsumption, independent of weights, pins and affine constraints. Canonical sorted antichain + feasible crossing coordinate is a sufficient exact future key. It may not be minimal semantic suffix quotient; extra logical implications and differing group orders can improve it. Unlike R193, this key is computed during source-derived discovery, without first building a larger raw clause-status/primal graph. Two histories in same key have identical future acceptance function of remaining group assignments; multiplicities combine by sum, support by OR. Group weights factor independently across disjoint original groups, so merge preserves scalar and support. Recover actual original assignments by local signature witness plus backward accepted group path. This is not an inverse reconstruction of every old history; original guard labels, source maps and replay remain available.

### R202. Chart-changing revision strata and parameterized sufficiency
Paired state (q0,q1), each component either live residual-antichain/crossing coordinate or distinguished dead. Drop both-dead only; at terminal keep disjoint labels 1=old only (loss L), 2=new only (gain G), 3=both (common C). Weighted P0=L+C, P1=G+C, DeltaP=G-L. Support of each stratum is a separate Boolean relation with original witness; numerical zero never implies empty. No need to equate state labels across charts; pairing uses the common original group assignments. This implements actual chart-changing clauses (including removing a clause from an extracted parity relation), not merely weight edits on one frozen graph. Arbitrary new online structural edit still needs paid joint chart construction; existing precompiled pair can be reused for changing pins/weights. Let a_jk count reachable canonical obligation sets on cut k and kappa_jk crossing dimension; paired width bounded by (1+a_0k 2^kappa_0k)(1+a_1k 2^kappa_1k)-1 (loose product; actual reachable joint states may much smaller). Given graph, E transitions, m groups and n guards, packet circuit O(n) and contraction O(E+m), with fixed signature alphabet and constant number terminal strata, plus support, storage and labels. Graph discovery includes basis ops, clause normalization, group incidence scans and actual transition attempts; no guarantee these widths or antichain counts polynomial for arbitrary source. One can choose alternative chart or ordering; no compulsory expanded representation or lower bound by counting this chart. For original R85 D=3A-4P fixed carrier, DeltaD=-4(G-L), recover mod2^h with D precision h+2. If a pin changes baseline carrier A, retain full DeltaD=3DeltaA-4DeltaP; source edit at fixed pins keeps A fixed. Ring is unramified binary coefficient ring, not the actual Q3 ramification.

### R203. Exact paired secants, incremental reuse and six-face transport
Compile a shared division-free arithmetic/Boolean DAG from grouped packets and actual paired transition graph, terminal weighted/support channels L,G,C. Original leaf pin changes update only gates with changed predecessors, propagate only actual value or support changes. Reference implementation still scans subsequent topological gates; gate evaluation reduction is not time or memory benchmark. Independent recomputed circuit checks every update. The original paired graph structural version is fixed for these dynamic pin edits; general online structural cache update remains open. For two actual pin histories p,q, independent grouped message evaluator computes old f and revised g for all three strata. Each stratum exact finite difference sum f_k^old (T_k^new-T_k^old) g_(k+1)^new; T delta is changed local packet on fixed paired graph. Forward and reverse orientations tested, mixed source/pin residual equals DeltaG-DeltaL. Source changing extraction uses paired chart with actual old/new terminal masks; no claim frozen gradient handles arbitrary source rerouting.

Three independent axes are source version F0/F1, pin history p/q, coefficient precision 5 vs h+2 for h=1,2,3. Actual high and lower precision weighted D contractions independently evaluated at all vertices using same joint structural chart, original pinned baseline A computed at each pin vertex. Six signed faces: two source/pin mixed faces at fixed precision, two source/precision and two pin/precision faces. All six endpoint paths use actual signed vertex increments and ring reduction. These are specified source/pin/precision faces, not independent physical time evolution or arbitrary path-dependent chart morphisms; h=3 is identity precision control. Both orientations of each actual edit tested. Retain chronological history, time, refinement k, source/consumer, chart/order, Frobenius, Q3 ramification, coefficient precision independently. Do not identify source version with time.

### R204. Actual cancellation-aware precision with cost anti-control
Use R186 structural valuation lower bounds; optional one-bit residue pass on shared arithmetic DAG certifies cancellations, raises valuation bound to at least 1 for zero mod2, propagates improved bounds to successors. Cache this pass across requested precisions per fixed pin history, invalidate on actual input change. Reverse demand all three output strata simultaneously, shared gate takes maximum demand; forward evaluates only demanded residues at requested widths, no full-precision intermediate values required by this precision evaluator (separate full graph evaluated as reference and incremental control). Actual source weights supplied mod32, leaf valuation inspection charged. On 104 fixtures x 4 pin histories x 5 precisions, arithmetic-gate uniform exponent budget 2892360; structural-only demand 586829; cancellation-enhanced demand 577498; extra 192824 one-bit probe gate operations after cache sharing. Treat each one-bit gate as one additional exponent-unit for this accounting proxy: enhanced total 770322 > structural 586829. Therefore unconditional probe is not economical on this suite; default structural planner for this accounting, allow paid selective probe under demonstrated benefit; adaptive selective policy not implemented. No physical bit packing, machine-cycle timing, memory savings or optimal valuation claim. Fixed degree3 coefficient ring; each exponent unit corresponds to one bit per coefficient. Boolean support independent of all tapering. 64-guard independent equality-pair cancellation control with equal unit weights executed; support may be inhabited with zero scalar. The aggregate counts exclude star controls and independent secant/cube reference work, graph construction/support costs.

### R205. Direct exponential raw-frontier bypass, with independent closed form
Original F=AND_{i=1}^{n-1}(a_i OR x), F'=F AND x, with original a_i processed before x. Raw signed-incidence chart distinguishes every subset of satisfied original clauses after all a_i, hence raw peak 2^(n-1) (distinct original clause IDs and distinct a_i signatures). Direct residual antichain has only two live histories at each such cut: no unsatisfied processed clause, or obligation x subsumes all others. New source always retains x. Exact chart peak2, O(n) transition attempts on this family, but naive subsumption pair scan incurs polynomial overhead. Independent weighted closed form common C=w_x(1) prod_i(w_i(0)+w_i(1)), loss L=w_x(0) prod_i w_i(1), gain G=0 (replace weights by pin filters as appropriate). Actual 3 pin states per n independently matched formula and original witnesses, 2 edits both orientations. No need to build raw graph for large n.
| n | direct peak | attempts | raw peak if executed | raw attempts | subsumption pair checks |
|---:|---:|---:|---:|---:|---:|
|9|2|34|256|1022|329|
|13|2|50|4096|16382|887|
|33|2|130|not built|not built|12717|
|129|2|514|not built|not built|724669|
|257|2|1026|not built|not built|5692797|
This is an actual bypass of a particular raw source chart, not general SAT complexity lower bound, nor optimal chart selection. One can even solve the family by direct closed form; steelman it. The key point is direct construction rather than compressing exponential raw states afterwards.

### R206. Actual large cyclic mixed chart and incremental controls
Use 6,12,24 regions of respectively 8,16,24 guards. Wide cyclic signed regional clauses, local odd ternary parity, cyclic equality of first guard. Revised original list removes one parity-pattern clause and appends unit x1, so extraction changes. Original old/new affine rows 12/11,24/23,48/47; crossing max dimensions 2/1 each. Joint grouped chart compared to both raw grouped status and singleton status charts; all matched strata, not independent brute at large size. Unit weights w(0)=[2,0,0],w(1)=[1,1,0]. Large source:
| guards | groups | paired peak | grouped attempts | singleton attempts | arithmetic gates | 3 update gate evaluations / complete reevaluations |
|---:|---:|---:|---:|---:|---:|---:|
|48|19|4|154|298|1770|331 / 5310|
|192|37|4|316|1182|6618|416 / 19854|
|576|73|4|640|3542|19386|1588 / 58158|
Direct canonical and raw grouped charts same peak/attempt count here; subsumption has overhead (1528/15362/138718 pair checks), so do not claim it always helps. Basis-reduction loop counters 9955/61231/412183, not complete construction cost. Larger original assignment spaces not enumerated; same-algorithm singleton/raw independent chart checks and direct source witnesses, not independent production solver. Degree3 ring not sufficient generic randomized support detection guarantee at these sizes. Structural grouping reduces chart attempts but packet gate cost and basis work are charged.

### R207. Exact regression and endpoint scope
Identical scripts/check_langlands_integrated_crossing_20261124.js executed in JS tool, seed198 xorshift32, exact (Z/32)[X]/(X^3+X+1), BigInt source masks, no native Node subprocess. First attempt syntax failure before any commit/acceptance, corrected harness and actual run; extended canonical obligations, cached cancellation, star independent formula, paired secants and cube and reran final code. 100 small random CNF pairs n=3..7 with append/delete and parity edits, 3 large cyclic controls, 1 independent equality control, 5 star controls. Counts excluding stars where noted: 1200 brute source stratum comparisons; 1248 paired chart stratum checks (each against singleton and raw grouped); 312 incremental updates with 3 channel rebuild comparisons each; 333 original stratum witnesses validated, 155 inhabited zero-mod2 observations; 6240 precision cases comparing structural and enhanced with full reference; 1248 D signed source recovery checks; 8544 changed-support gate evaluations vs 153683 complete evaluations (scans excluded). Including stars: 1932 paired stratum secants, 644 mixed source/pin face checks (both orientations), 11592 signed cube faces and 11592 endpoint paths (includes h=3 identity control); 15 independent star formula/support checks, 20 original star witness checks (initial two, later one each), counts separate. Exact finite arithmetic and stated proof arguments only. No CI/native Agda/Lean, general local L/epsilon oracle or general Langlands correspondence, new compiled-CNF execution, actual runtime/memory benchmark, arbitrary chart online incremental cache or unrestricted polynomial solver.

### R208. Consolidated mathematical boundary, not another piecemeal checklist
The restricted mixed-geometry route now has one executable pipeline from original paired clause lists through paid direct quotient, affine crossing, region packets, exact gain/loss/common, original witness, paired secants, dynamic pin update and precision-aware rank-two D. The sufficient theorem is conditional on paid finite interface construction; no assumption of an optimal chart. R7a'/LGC4d general nonlinear contraction remains open: a generic exact original-support decision for arbitrary CNF in polynomial time would solve SAT (P=NP), and polynomial general weighted scalar evaluation with sufficiently large binary extension field yields the previously identified randomized RP=NP route; exact integer count at all weights one is #SAT. These are consequences, not new separation proofs; scalar zero is inconclusive without support, arbitrary SAT algorithms need not evaluate any of these scalar representations. The star example explicitly defeats attempts to turn a particular large raw interface into an unrestricted lower bound. R7b'/LGC5 and R7c/LGC6 remain unpaid. No native standard proof or general Langlands endpoint claim. Next maximum tranche should attack general source-derived contraction/obstruction and actual local-factor correspondence using prior exact Langlands owners; only extend structured implementations when they close a real general obligation or provide a decisive anti-control. Preserve attribution and all independent indices. All artifacts repo-only.

## 2026-11-25 — Endpoint maximum cut: all-rank local-factor classification, exact complexity and deterministic residue-query obstruction (R209–R215)

Scope: stay on Langlands #1549/#120, not P vs NP branch edits. Attached R198–208 and P vs NP maximum-cut resource report (reported #1548 bdb74f190ddb / #119 24430459e46b) are context/donors only. Starting common roadmap 35350e74fee792c566793b27d21e33ffd43e2f4e. Reopened R29–30 actual totally ramified S3 extension of Q3 and standard U (Artin conductor 5), R78–85 actual source-labelled deterministic graph and doubled phase-matched block, R102–104 coefficient-field separation. Geometry-forward, endpoint-first, steelman/BIDI/reverse solve; no new structured contraction benchmark for its own sake. Classical WD determinant, multiplicativity and Deligne unramified epsilon twist rule used (see https://umrep.github.io/Fall2024/notes/lecture01.pdf and https://openmaths.org/courses/LG-GAL/local-factors-and-epsilon-factors.html for exposition, and LLC pair factor preservation; no new general LLC theorem). Standard complexity classes #P, parity-P and Schwartz-Zippel are used. The actual local field remains Q3; binary coefficient extension is NOT its ramification or Frobenius.

### R209. Arbitrary-rank Weil–Deligne local-factor classification
B_b=1+U+2(U tensor xi^b) by R79 actual Sym^2 dual identity, xi unramified quadratic. Each original assignment x of R78 has unique extension, tag lambda_x=prod z_i^x_i and truth b=F(x), actual WD direct summand B_b tensor eta_lambda. For ANY admissible complex Frobenius-semisimple WD probe V=(rho,N) of any rank, put K0=(ker N)^I and KU=(ker(1 tensor N))^I in U tensor V; A0,AU actual Phi actions. On tensoring by eta_lambda, both inertia and monodromy kernels unchanged and Phi multiplies lambda. Therefore inverse Euler factor of each summand is
 det(1-lambda T A0) det(1-lambda T AU) det(1-(-1)^b lambda T AU)^2.
This is genuine local-factor formula, not an analogy to a Boolean observer. The same direct sum multiplication, with arbitrary probe, shows epsilon(R_F tensor V) independent of F at fixed original tags: changing b replaces TWO copies of W=U tensor eta_lambda tensor V by W tensor xi; the WD unramified twist rule multiplies epsilon by (-1)^(a(W)+dim(W)n(psi)) per copy (reciprocal convention same sign), and square is 1. Conductors unchanged (including monodromy), determinant unchanged. Gamma follows from epsilon and L for parameter and dual. This is a theorem using standard local identities; no numeric epsilon/root-number oracle executed. Via classical GLn LLC these are pair local factors of the corresponding representations, not new global automorphy. Rank one K_U=0 as in R80, so all rank-one observations blind. For arbitrary rank the fixed U^vee probe suffices to recover ALL source-dependent local-factor data on this family, as next section.

### R210. Exact spectral quotient and its kernel, odd/even tag dichotomy
At fixed original tag multiset define A_lambda=#all source assignments with tag lambda and W_lambda=#accepted assignments with that tag; absent tags have zero counts. Actual semisimple WD decomposition R_F=direct_sum_lambda [eta_lambda^A_lambda + (U tensor eta_lambda)^E_lambda], E_lambda=3A_lambda-2W_lambda+2W_{-lambda}. Isotypic multiplicities unique since inertia Schur distinguishes distinct unramified U twists (actual fixed Phi trivial on U). On fixed U^vee rank2 probe trivial inertia part from eta disappears and End(U)^I rank1; inverse Euler polynomial exactly prod_lambda (1-lambda T)^E_lambda. Thus for fixed A and tags, equality of full rank2 L iff equality of E iff actual isomorphism of R_F iff equality of all rank pair L/epsilon/gamma factors. The data in arbitrary probe L are product over lambda det(1-lambda T A0)^A_lambda det(1-lambda T AU)^E_lambda. Recovering these formally requires knowing probe matrices/factors; no free arbitrary probe computation assumed. This is a full observer classification within THIS family, not arbitrary local converse rank reduction.
For odd-order tags (e.g. R85 p=2 Teich group order 2^d-1), negative coset disjoint. For lambda in tag group W_lambda=E_{-lambda}/2. Full rank2 L recovers exact accepted tag histogram, hence SAT and #SAT. For even-order tags, only antisymmetric W_lambda-W_-lambda=(3A_lambda-E_lambda)/2. Kernel consists exactly of symmetric perturbations with admissible nonnegative multiplicities <=A; retain common opposite-tag residual independently. Actual source counterexample q=1,z1=-1: all-true formula vs contradictory units (all-false) have A_+=A_-=1, W=(1,1) vs (0,0), E=(3,3) both, hence isomorphic actual WD parameters and all local factors equal despite different original support. This is a source-level nonfaithful even-order chart, not counterexample to LLC/local converse. Odd-order tag choice repairs support for full L, not necessarily any one modular coefficient. Even in odd case distinct assignments with same tag are not identified in original source or provenance; histogram is not a bijection of histories.

### R211. Exact unrestricted complexity of full vs residue consumers
Use polynomial-size original formula, explicit binary extension field representation, tag subgroup order m polynomial in n (as in least d with 2^d-1>=4n), compressed exponent list as output rather than expanded degree 3*2^n polynomial. Exact histogram W can be computed with polynomially many #P counting queries, one per tag, verifying F and product tag in polytime; A via baseline counting or O(nm) group-algebra convolution. Conversely at all z_i=1 (odd-order subgroup) W_1=#SAT, recovered from E_-1/2. Thus exact compressed rank-two full factor function is #P-equivalent under polynomial-time oracle reductions on this promise family (function class FP^#P under Turing reductions; not a hardness proof for SAT decision). Exact pole at some negative coset tag is NP-complete decision (all ones for hardness, original witness for membership; if a specific tag desired include tag check); full factor would solve that, but expanding it is unnecessary and exponentially large.
For residue P_F(alpha) in explicit F_(2^d), d polynomial in original input, each coefficient bit in a fixed field basis is parity of the #P relation consisting of assignments satisfying F and contributing 1 in that coefficient of prod alpha_i^x_i. A deterministic polynomial-time procedure with parity-SAT oracle computes all d bits via ordinary deterministic verifier-to-CNF with unique extension (or parity-preserving #P reduction). Conversely setting all alpha=1 returns parity-SAT. Hence exact binary rank-two residue recovery for all such inputs is polynomial-time iff parity-P=P (often written P=⊕P); Turing-equivalent to parity-SAT in the function-oracle sense. For D mod8 rather than P, compute A cheaply and use the exact signed relation both ways. This is stronger than merely identifying RP=NP as a consequence of poly residue evaluation; by R86 random nonzero detection Schwartz-Zippel over field of order >=4n+1 it indeed gives RP=NP, not a deterministic P=NP proof. Exact integer D at all tags 1 is #SAT-equivalent. No assumption P!=⊕P or FP!=#P proved. Source-aware algorithms need not evaluate these stronger arithmetic observers; do not transfer a counting complexity lower bound to unrestricted SAT decision.

### R212. New deterministic modular observer obstruction (even for simple 2-CNF)
For t prescribed queries alpha^(j) in (F_(2^d_j)^*)^n, if sum_j d_j<=n, choose disjoint original blocks I_j of d_j variables. On block j, 2^d_j distinct binary assignments map by monomial product to at most 2^d_j-1 nonzero field values at query j, so two distinct assignments u_j,v_j collide. A conjunction of units on coordinates agreeing and equality/complement binary clauses to one differing pivot enforces EXACTLY these two assignments; no auxiliary variables. Combine blocks independently, pin any unused original guard to 0. Original formula F is satisfiable with precisely 2^t distinct witnesses; P_F(Z)=prod_j (Z^u_j+Z^v_j) with original disjoint coordinate labels. At query j its factor j vanishes in char2, hence all t residue samples vanish. This is a real source collision against UNSAT for any chosen tags under budget, not just arbitrary polynomial interpolation. Construction can be paid by enumerating block assignments; existence suffices for query lower bound. For fixed field d, any deterministic black-box adaptive algorithm making at most floor(n/d) queries cannot distinguish UNSAT from some satisfiable original 2-CNF: follow zero-reply path, then construct F for those queries. Adaptivity is only through black-box replies; if formula/other observer data available, no such lower bound follows. For R85 minimal d=O(log n) gives Omega(n/log n) necessary deterministic residue queries in that restricted model (more precisely >floor(n/d)); not superpolynomial, not impossibility of explicit polynomial hitting set, not an unrestricted computation bound. Even a simple source-aware solver bypasses this collision. It is a modular residue observation obstruction, not exact full factor obstruction: odd-order full factor retains support. Distinguish random hitting guarantee for fixed F from adversarial F after deterministic sample selection. For full rank-two D residues, baseline A same for F and UNSAT at each sample; equality D mod8 exactly follows from P mod2. No loss of inhabited neutral witness sector.

### R213. Reverse-solve general source contraction and steelman
The actual local-factor correspondence on our explicit family is no longer an unspecified black box: arbitrary-rank source-dependent information factors through E, full fixed rank2 recovers it, odd-order histogram gives exact support, modular first coefficient gives parity computation and randomized support. Remaining general theorem must either furnish a paid source-aware polynomial witness/pole-presence decision (not require exact parity/counting/full factor), or rule out all such decisions, including algorithms bypassing this chart and all local factors. The P vs NP universal-resource donor is consistent with this boundary. Neither finite sample query lower bound nor general count-class equivalence solves the Clay separation. R7a' general polynomial residue evaluation would pay the stronger P=⊕P consequence; polynomial pole presence equivalent to P=NP; R7b'/LGC5 universal decision lower bound remains open. No general source-aware deterministic hitting set or efficient exact local-factor algorithm established. No mandatory full factor, spectral histogram, or finite quotient.

### R214. Actual exact acceptance
scripts/check_langlands_all_rank_20261125.py actually executed locally using Python and SymPy (not CI): 36 independent explicit inertia-kernel/Frobenius determinant comparisons using actual S3 matrices and probes made from trivial/sign/standard inertia reps with monodromy lengths 1,2,3 and tags +/-1; Frobenius N Frobenius^-1=N/3 checked. 560 finite histogram classifications including 478 nontrivial symmetric perturbation collisions (arbitrary admissible histogram, not all claimed actual CNF sources), 384 independent exact block-CNF truth comparisons, 384 blind samples over F8 and F16 (128 seeded fixtures, 3 disjoint blocks each), actual witnesses verified. No numerical epsilon oracle, no general arbitrary probe execution, no full production local-factor API, no native Agda/Lean. The all-rank assertion is the mathematical determinant and standard WD twist proof, finite controls only. All artifacts repo-only.

### R215. Consolidated frontier
Restricted source-to-endpoint pipeline R198–208 complete as stated; actual all-rank local-factor classification R209–210 derived, explicit WD controls passed; compressed full/finite residue computational classification R211 derived; deterministic residue black-box obstruction R212 proved and finite controls passed. The genuinely general R7a'/LGC4d paid nonlinear support contraction, R7b'/LGC5 universal deterministic obstruction, R7c/LGC6 unrestricted endpoint separation remain OPEN. No general Langlands correspondence theorem or Clay solution. Next mathematical maximum cut should address a source-aware unrestricted pole-presence upper/lower bound, not additional local-factor census or finite regression size, and preserve independently indexed original history/time/k, ramification, Frobenius, source/consumer and precision, zero mode, signed residual and inhabited support. No P vs NP branch edits.
