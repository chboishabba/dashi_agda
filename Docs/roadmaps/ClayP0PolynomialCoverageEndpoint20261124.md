# Clay P vs NP P0 — polynomial semantic coverage and universal resource obstruction

Date: 2026-11-24. Shared Agda/Lean roadmap, independently based on their default branches. Priority: solve the literal Clay P vs NP endpoint (P0). Endpoint mathematics before additional certification; no other programme is a prerequisite. This document records research obligations, not a separation proof. Proposed lemma identifiers below are not existing declarations unless explicitly marked.

## 1. Exact endpoint and scope

Use a fixed deterministic finite machine D on canonical binary encodings of Boolean formulas (invalid inputs handled consistently). Let T_D(n) be its worst-case runtime over length <= n, infinity if it does not halt. The target is SAT not in P: for every D and c,k >= 1, if D halts within c(n+1)^k on all inputs then some valid formula phi is decided incorrectly. Equivalently, every total correct SAT decider has no polynomial worst-case bound. Quantify over D before choosing n or phi. Do not take the per-length minimum over unrestricted machine descriptions (hardcoded finite tables invalidate that formulation). An explicit NP language with superpolynomial unrestricted bounded-fanin Boolean circuit complexity would suffice but is stronger; restricted circuits do not suffice.

Existing Agda endpoint is PNotEqualsNPClayCoreExact.SATLowerBoundProducer, field satNotPolynomialTime : SATNotInP cost, consumed by satLowerBoundProducerClosesClayCore with PNotEqualsNPEstablishedBackground. DirectSATLowerBoundExact.universalDecisionFailureGivesSATLowerBoundProducer and universalDecisionFailureClosesPNotEqualsNP consume UniversalPolynomialSATDecisionFailure. The cost parameter is not automatically the standard model; attach concrete standard binary-machine coverage and SAT-in-NP background. Only SAT in NP is needed for the implication SAT not in P -> P != NP; NP-completeness and P subset NP also give the converse. If using a constructive universal error witness, distinguish it from classical negation of a universal correctness statement; an explicit search may require classical reasoning or decidable finite enumeration plus termination proof.

## 2. First P0 enabling result: sufficient normalization, not global minimization

For each fixed D, construct one effective uniform lowering N(D) in the actual target model with Eval(N(D),enc(x)) = D(x) on every halting input, and termination/rejection correspondence. Bound all charged target work, including input/outputs and decoding, by a polynomial p_D(n,T_D(n)), with fixed coefficients and degrees independent of n. Bound input encoding length polynomially and prohibit advice or preprocessing depending on uncharged future inputs. Fixed D-specific compilation overhead may be absorbed into constants; any n-dependent construction must be charged. Use a nondecreasing polynomial majorant with nonnegative coefficients.

**N3 transport (mathematical proof):** assume every total correct normalized SAT decider has no polynomial worst-case bound. If a source D correctly decides SAT in time c(n+1)^k, then N(D) correctly decides SAT with cost <= p_D(n,c(n+1)^k), a polynomial. Contradiction. Thus SAT not in P. It is enough to prove the target lower bound on the actual image of one polynomially costed compiler; a proof on the larger target class also works. No inverse efficient compiler is required for this direction, although backward simulation can validate faithfulness. No global optimal compiler, canonical equivalence decision, Monster classification, global MDL optimum, complete corpus ingestion or all-prover translation required.

**Concrete fallback:** take target as standard-machine transition traces, with fixed finite control and tape access; record read/write/move/state and event identities. Identity lowering has unit simulation cost (or linear charged logging on fixed D); a fully materialized configuration trace can instead have polynomial overhead O((n+t+1)(t+1)) on fixed tapes. This is a classical construction, not a fresh kernel proof or completed attachment to the repository's cost model. It establishes that exotic normalization is not inherently required for coverage. Use this fallback immediately if FRACTRAN lowering stalls. A lower bound for a trace representation is relevant only when it bounds the actual charged work of correct target executions, not the size of an unnecessarily inflated proof log.

## 3. Phases, exact deliverables and dependency order

| Phase | Deliverable / exit criterion | Status |
|---|---|---|
| P0-A / N1-N3 | One concrete fixed-machine lowering, exact whole-run simulation, cost polynomial, and transport theorem; explicit carrier/cost-model attachment | P0 enabling; classical transport supplied, source weld open |
| P0-B / R1-R5 / N2 | One reusable separator/residual/overlap/charging packet with counterexamples, not another generic framework | elementary mathematics and existing source donors; target-specific attachment open |
| P0-C / U2-U4 / N4 | Original SAT family (or explicit NP reduction) and universal global charged-resource lower-bound producer that covers arbitrary sharing, rereads and alternative algorithms | open research; run in parallel with A |
| P0-D / A1-A2 / N5 | Same-carrier superpolynomial lower-bound proof, or directly universal fixed-machine polynomial SAT failure | open research; controlling endpoint |
| P0-E / N6/A3 | Feed actual theorem into SATLowerBoundProducer and literal Clay statement in Agda and native Lean, with standard semantics | terminal wiring source exists in Agda; native Lean endpoint and actual producer unpaid |
| P0-F | Independent mathematical review, native Agda/Lean checking, exact reproducibility and attribution | after endpoint derivation; local tests may falsify conjectures earlier, no CI request |

Parallel alternative P0-Q/F2: finish behavioural self-specialization, cost closure, and same-object SAT contradiction only if viable; not mandatory if P0-C/D succeeds. Do not mistake an additional abstract interface, a finite test or a conditional consumer for payment of C/D. No solvedness percentage.

## 4. Exact proposed lemma ledger

Notation: cost is deterministic primitive transitions or explicitly bit-costed operations; a circuit route uses paid bounded-fanin gates, with free input/fanout scoped. Cost units must stay fixed across inequalities. Program text, proof size, peak memory, elapsed time and total work are separate.

| ID | Exact theorem/obligation | Existing producer or donor | Status |
|---|---|---|---|
| N1a canonicalInputRoundTrip | decode(enc(x))=x; encoding length <= poly(n); canonical start independent of clock | #1129 CodedStandardCanonicalInputExact; #1474 codecs | source donors; same-carrier attachment |
| N1b wholeRunSimulation | every D run of t steps maps to an accepting/rejecting target run with same output; no spurious terminal result | #1129 raw interpreter + fidelity, halting bridge; #123 CompilerSimulation | source/contract; chosen target proof needed |
| N1c polynomialChargedSimulation | for fixed D, target work <= p_D(n,t) including initialization, guards, input access, addressing, arithmetic bit cost, output; no advice | #1129 RawInterpreterCostExact; #123 CostVector; #1006 polynomial cost owners | actual target weld open |
| N1d standardCostCoverage | each standard polynomial SAT decider is admitted on original formula encoding and fixed cost model | #1129 CodedStandardHaltingPolynomialDeciderExact, CodedStandardHaltingPolynomialCostModelExact, PNotEqualsNPHaltingCodedCandidateBridgeExact | source reconciliation open |
| N2/R1 completeSeparatorFactorisation | full separator including bypasses determines downstream output; for F(x,q)=g(h(x),q), h independent of q; otherwise justify interactive transcript rectangles | FactorsThrough; Lean collisionBlocksFactorization | elementary topological induction, target attachment |
| R2 indexedResidualInjection | h(x)=h(y) implies identical query rows; K distinct rows imply >= K states and b >= ceil(log2 K) bits | residual-fibre, query-indexed adequacy donors | elementary proof, restricted to stated split |
| R3 jointResidualOverlap | H(R_1,...,R_m)=sum H(R_i | R_<i) <= H(h(X)) <= b for jointly recoverable rows | intersectional FactorsThrough, typed fibres | elementary entropy identity, not work lower bound |
| R4 weightedPaidCutPacking | for paid events V, cuts S_j subset V and a_j>=0 with sum over j containing v a_j<=1, sum a_j |S_j|<=|V| | fast pi shared DAG, zkperf cost scope | elementary double counting; existence of cuts open |
| R5 traceAndLiveness | exact trace->factorisation preserving evaluation; repeated dynamic work counted per execution event, shared static gate once, live memory separately | fast pi #1546; #1129; #123; zkperf/zkSEC | target attachment open |
| N3 normalizedLowerBoundTransfers | polynomial coverage plus no polynomial correct target decider implies SAT not in P | section 2 proof; #1040 endpoint | classical proof supplied; source formal weld |
| A1 originalHardFamily | uniform NP language or original SAT input family with polynomial encodings/reductions and hard instances, no exponential expansion hidden | #1474/#1502, Cook-Levin | original hard-family argument open; SAT itself is eligible |
| U2/N4a unavoidableObligationAttachment | for every fixed total correct target decider M and each selected hard input length, find obligations on actual computation(s), including input rereads, control and arbitrary representations; justify their necessity via consumer separation, not an assumed SAT search tree | #1006 UniformObserverNonDescent; FactorsThrough; external RC2 | open |
| U3/N4b boundedOverlapCharge | charge those obligations to actual paid primitives with per-event charge <= cost, without independent private-gate assumption; account for shared states and bypasses | #1546, #123, typed DAG, R4 | open |
| U4/N4c globalCostLowerBound | obtain B_M(n) <= T_M(n) from U2/U3, using a common worst-case run or prove valid cross-run averaging; never sum work across unrelated inputs as one runtime | R1-R5, #1006, #1040 | open |
| A2/N5 superpolynomialExclusion | for every correct fixed M and c,k>=1, exists n with B_M(n)>c(n+1)^k (or directly T_M(n)>bound); prove asymptotic amplification survives sharing and alternate computation | #123 noCheaperEquivalentInsideSearch is only bounded contract | open; major mathematical breakthrough |
| N6/A3 originalClayTransport | correct standard cost coverage + N3 + lower bound yields SATNotInP and PNotEqualsNP on literal original carrier | #1040 PNotEqualsNPDirectSATLowerBoundExact, PNotEqualsNPClayCoreExact | conditional source consumers; actual theorem unpaid |
| Q1/D1 behaviouralSpecialization | fixed actual machine/program consumes its own relevant quotation with fidelity, not literal syntactic self-containment | #1129 Kleene/quoted interpreter | open construction |
| Q2/D2 sameObjectResourceClosure | prove quote/generate/simulate/decider/suffix cost <= B on precisely the same B in Cook description | #1129 ResourceClosingBudgetNecessity, fixed quotation no-gos | open; ordinary tableau grows with B |
| Q3/D3 oppositeDecision | derive SAT(phi) iff D(phi)=0 on that same phi and discharge F3 | #1040, #1129 halting terminal | conditional |

R4 proof: exchange finite sums, sum_j a_j |S_j| = sum_v sum_{j:v in S_j} a_j <= |V|. General weighted version: if obligation weights w_j are split into nonnegative charges gamma(j,v) with sum_v gamma(j,v)>=w_j and sum_j gamma(j,v)<=cost(v), then sum_j w_j<=sum_v cost(v). The hard part is finding a charge scheme and large total weight for arbitrary correct computation. For adaptive computations, a separate run for each q cannot be charged to a single run without a valid distribution/worst-case argument.

## 5. Bounded minimality and the exact gap

#123's BoundedSearchCertificate.noCheaperEquivalentInsideSearch concerns a declared search class and equivalence relation, not an inhabited all-SAT lower bound. Define F_B as the semantics realizable by legal cost-bounded executions with fixed uniform machine and all chargeable resources included. Proving non-membership for a finite enumerated class is not uniform separation. A finite program-length bound is not inherent in a time bound uniform over different machines. If using per-n circuits instead, bound gate count and encode all gate choices; counting shows many hard functions, not an explicit NP hard language.

Do not minimize a mixed L + lambda Cost score and infer a time lower bound; a shorter description may take longer to execute. FRACTRAN first-enabled rule selection and exponent updates must be costed; expanded Goedel integers may have enormous bit length compared to sparse exponent vectors. No unit-cost huge integer or oracle instruction. #123 is a donor for constructive lowering, not a completed efficient universal FRACTRAN compiler. A fixed deterministic interpreter using bounded-bit state is sufficient; global minimum is irrelevant.

A candidate useful U3 approach: prove an obligation measure with bounded change per charged primitive (including all rereads and state changes), and prove large necessary cumulative progress on actual runs, not just an exponential set of potential witnesses. Static entropy of the n input bits cannot by itself exceed n bits. Identity observer h=x and final-output observer h=SAT(x) are negative controls: their semantic sufficiency does not constrain the cost of computing h. For a SAT decision bit, two output classes alone give only one bit. For a cut with q-independent h, residual rows can bound width, not arbitrary circuit size without additional structure. A universal claim must survive arbitrary AND/OR/NOT, shared gates, recomputation, bypass and alternate encodings.

## 6. Existing producers and PR ledger (source/status snapshot)

Directly inspected this turn:
- [Agda #123](https://github.com/chboishabba/dashi_agda/pull/123), merged; head 7ac328ee76f3d7a80e98039c70fce0d1cdf6fe04. [VerifiedFractranCrankPipeline.agda](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Interop/VerifiedFractranCrankPipeline.agda), blob 368f6b196fb833a2ca596bf7cc64f43c03c952fe: CompilerSimulation, FractranMachine, ArchitectureLowering, MicroOpToFractran, CrankCandidate.observationallyEquivalent, CostVector, MDLVector, BoundedSearchCertificate.noCheaperEquivalentInsideSearch. Fields are required evidence, not automatic inhabitants.
- [Agda #1040](https://github.com/chboishabba/dashi_agda/pull/1040), merged; [PNotEqualsNPDirectSATLowerBoundExact](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Mathematics/Complexity/PNotEqualsNPDirectSATLowerBoundExact.agda), blob 0838b3252b3ffb91993e4cb47a5d5c06a00e4fe1. Existing conditional consumer source bodies inspected. Anchored collision requires correct orientation on one true and one false SAT formula; complement-of-SAT negative control.
- [PNotEqualsNPClayCoreExact](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Mathematics/Complexity/PNotEqualsNPClayCoreExact.agda), blob fc5aed11a1bc0a095ba3c64c7a3468bd059d1aae. Actual terminal source bodies inspected. No unconditional lower-bound inhabitant established.
- [Agda #1129](https://github.com/chboishabba/dashi_agda/pull/1129), merged; head 730ec95ce0442b8ab48a17a3cc9a3d1307ba8c76. PR metadata and changed-file paths inspected: CodedFiniteStandardRawInterpreterExact/FidelityExact/CostExact, CodedStandardCanonicalInputExact, CodedStandardHaltingPolynomialDeciderExact/CostModelExact, PNotEqualsNPHaltingCodedCandidateBridgeExact, CodedFiniteStandardExactPhaseSizeExact, PNotEqualsNPResourceClosingBudgetNecessityExact. Actual-halting input distinct from padding, finite phase size |Q|(T+1), rules T|R|. Recover these before introducing new machine definitions. Source-reported results, not freshly checked.
- [Agda #1006](https://github.com/chboishabba/dashi_agda/pull/1006), unmerged, non-master base; head fc930b20d8449d2c79904891de7670c46dd84f09. PR metadata/paths: PolynomialFactorisationCostExact, PolynomialClassicalObserverExact, PolynomialBoundClosureExact, RSAQuantumShorPvsNPCrossPollinationExact, MillenniumResidualDescentClassifierExact (UniformObserverNonDescent). Prior roadmap also names SATDecisionToWitnessSelfReductionExact and BooleanFormulaSATSelfReductionExact; recover concrete declarations before reuse. Do not wholesale merge divergent branch. Factoring is not known NP-complete; Shor is quantum not classical.
- [Lean native consumer sufficiency](https://github.com/chboishabba/dashi_lean4/blob/main/Integration/ScopedVerifierConsumerSufficiency.lean), blob 1afa1425acb4130fe545f626f2513d9e842f87a5: ConsumerFactorization, factorizedConsumersEqual, collisionBlocksFactorization, validatorCollisionBlocksAdequacy, adequateRefinementMustSeparate. Actual source proof bodies inspected; use instead of duplicate FactorsThrough.
- [Lean TerminalCensus](https://github.com/chboishabba/dashi_lean4/blob/main/MillenniumExternal/TerminalCensus.lean), blob 9bd45df6546ddcefe919341012c72b139aefea28: reports Agda-owned PNP, exact quoted size 10+2*machineCodeLength, semantic interpreter work <= T*(|rules|+1) plus parsing, literal U residual. These are census statements, not native Lean theorem proofs.
- [Lean #117](https://github.com/chboishabba/dashi_lean4/pull/117), unmerged: external brilliant-hq/pequalnp-proofs gitlink b3787c5889d7039ad509e5cb7306613325b70f49; separate Lean toolchain and attribution. RC2/private-gate geometry is a restricted-model proving ground, not required for Clay. Shared quadratic decoder negative control; finite polynomial lower bound insufficient.
- [Lean #118](https://github.com/chboishabba/dashi_lean4/pull/118), unmerged, prior roadmap [at 9edb5100e3fa](https://github.com/chboishabba/dashi_lean4/blob/9edb5100e3fadc020e53ff4208deb4fea76a5ad0/Docs/ClayP0ResourceFactorisationRoadmap20261124.md) inspected (blob 2a96281386c6be89953e88293101d2b14da437e4). This document consolidates and extends that roadmap without requiring merge.
- [Agda #1499](https://github.com/chboishabba/dashi_agda/pull/1499) six-Clay coordinator: metadata merged, body includes historical branch-specific warnings; do not infer theorem closure. PNP endpoint P0, YM #1444/#1536 separate.
- [Agda #1474](https://github.com/chboishabba/dashi_agda/pull/1474), merged; [#1502](https://github.com/chboishabba/dashi_agda/pull/1502), merged stacked Cook–Levin convergence; original Karp codec/verifier, polynomial clock and source transport. Full Karp-21 network not necessary for SAT not in P.
- [Agda #1546](https://github.com/chboishabba/dashi_agda/pull/1546), unmerged; exact GMP pi source restoration, in-place P/Q/T, quotient/residual, observed performance. Use equal-output optimization, lifetime release and bit-cost as adversarial controls. #1529 historical donor; no claim that memory savings imply work lower bound.
- [Agda #1291](https://github.com/chboishabba/dashi_agda/pull/1291), unmerged; indexed compatible reductions and overlap only within proved scope.
- November typed-world PR metadata verified merged: [#1483](https://github.com/chboishabba/dashi_agda/pull/1483) exact statement fibres/distinct occurrences/bounded search (52c073db1bb0); [#1484](https://github.com/chboishabba/dashi_agda/pull/1484) streaming/cache/cost counters (fb1a481d7e06); [#1491](https://github.com/chboishabba/dashi_agda/pull/1491) pinned elaboration/import closure (e5522215f66d); [#1494](https://github.com/chboishabba/dashi_agda/pull/1494) content-addressed native handoff (d3201842bd15); [#1495](https://github.com/chboishabba/dashi_agda/pull/1495) authoritative builder contracts (5a2dc0bf30d4). No corpus-wide equivalence, authoritative admission or compiler completeness inferred. Use typed identities for shared computation and lookup; retrieval absence is not nonexistence.

Prior-roadmap donor references, not freshly source-audited in this turn:
- FactorsThrough, IntersectionalNonFactorability, QueryFactorisationSufficiency, QueryIndexedProjectionAdequacyExact, ProjectionFibre, ResidualFibreLowerBoundExact, ResidualBitLowerBoundThreeExact, FibreProgramComplexityExact; resolve paths and proof bodies before asserting exact reuse. Automata/Wette/FRACTRAN/Wolfram and Goedel diagonal modules in Lean imported Agda corpus are discovery candidates, not native Lean results.
- [PNF logical calculus](https://github.com/chboishabba/dashi_agda/blob/c36aa4a423091063bb3741cc74044726279b47c4/DASHI/Reasoning/PredicateNormalFormLogicalCalculusExact.agda), [ShiftFiniteEvolutionWitness](https://github.com/chboishabba/dashi_agda/blob/c36aa4a423091063bb3741cc74044726279b47c4/DASHI/Physics/ShiftFiniteEvolutionWitness.agda), PredicateNormalWorldModelCore, WorldModelFormalismBundle: logical meaning/context, finite witnesses. PNF is not classical prenex normal form. Skolemization is satisfiability preservation in expanded signature; Herbrand expansion may grow enormously. Use costed Tseitin transformation where needed, preserve extension/projection of satisfying assignments.
- [ITIR Oct 17 proof spine](https://github.com/chboishabba/ITIR-suite/blob/8a784366fe8325c52caa208185e09da95ae6fc79/docs/superpowers/specs/2026-10-17-da51-slr-jmd-proof-spine-maxcut-design.md), [Oct 29 proof triangulation](https://github.com/chboishabba/ITIR-suite/blob/8a784366fe8325c52caa208185e09da95ae6fc79/docs/planning/formal_proof_deduplication_and_triangulation_roadmap_20261029.md), [ITIR #73](https://github.com/chboishabba/ITIR-suite/pull/73), [zkSEC #1](https://github.com/chboishabba/zkSEC/pull/1): provenance, typed DAG deduplication and observed execution trace/cost receipts. Need original cost schema attachment; measured time, ZK validity and provenance cannot establish universal resource necessity.
- Historical proof-world targets nativeLeanTermDecodeEncodeRoundTrip, typedExpressionCodecExactReconstruction, acceptedTypedMDLMoveStrictlyDecreasesTotalLength, selectedFractranStepSimulation, generatedFractranCodecReconstructsCompleteLeanObject are discovery targets, not claimed proven. JMD attribution: FRACTRAN/minimal generative computation and MDL inspiration; DASHI attribution: typed residual/cost and proof-world extensions. No theorem of Monster classification of all programs.

## 7. Execution and negative controls

One large endpoint-directed tranche: construct explicit standard fixed-machine coverage and attach concrete cost model, then establish R1-R5 on that carrier. In parallel work backward from N5 to candidate N4 resource invariant, attack original SAT not a toy class, and test both direct resource and behavioural diagonal routes. A restricted RC2 application is optional evidence, not a critical path. A mathematical derivation must explicitly discharge each antecedent, and be cross-transported with statement/encoding identity, not silently import Agda proof claims into Lean. Use local SymPy/exact arithmetic and finite regressions in lieu of CI where useful; no kernel or CI run is claimed by this documentation PR. No new sorry, postulate or axiom to pay an open lemma.

Required falsification tests: identity and output observers; repeated identical queries; bypass inputs; alternative algorithms and rereads; shared gate/DAG and recomputation; fast pi equal-output memory/work separation; RSA certificate/quantum/classical cost distinctions; expanded vs sparse exponent representation; hardcoded per-length truth tables; invalid/promise input escape; exponential expansion hidden by encoding; arbitrary negation and fanout; multi-input/cross-run charge leakage; diagonal quotation budget circularity. Compare against known relativization, natural-proofs and algebrization barriers when applicable, without claiming avoidance by renaming the model.

Exit only when a valid standard-model unconditional SAT lower bound or equivalent universal SAT failure is mathematically derived. Report precise failed lemmas and counterexamples rather than promoting conditional machinery. Subsequent native verification is separate. All phases serve Clay P vs NP as P0.


## 9. P0-G — Aristotle BIDI nonlinear-generation geometry (2026-11-24)

**Status:** classical mathematical derivations and finite falsification probe, not kernel certification or a Clay separation. P0 remains solving the endpoint. This is an OR route for N4/N5, in parallel with the standard-machine route. It targets a stronger nonuniform lower bound; failure here does not rule out a direct uniform proof.

### G1–G3: exact model and bidirectional geometry

For n input bits use the Boolean algebra A_n = F2[x_1,...,x_n]/(x_i^2-x_i), identified with F2-valued functions on the n-cube, with pointwise multiplication. Set V0=span(1,x_1,...,x_n). Vertices are linear subspaces containing V0. A productive directed edge V -> W has W=V+span(ab), a,b in V, ab not in V. Its cost is one AND. Every step grows dimension exactly one.

**G1 (circuit-to-path):** Any bounded-fanin Boolean circuit can be rewritten with AND/XOR/NOT; OR(a,b)=a+b+ab, and any binary Boolean gate has affine terms plus at most one product. Scan gates topologically; available functions are the span of inputs, 1 and AND outputs. XOR/NOT preserve the span; AND adds at most one direction. Skip redundant ANDs. This maps any s-gate circuit to a path of length <= s ending at a subspace containing its output f. All input rereads, arbitrary fanout, sharing, recomputation and nonlinear feedback are allowed. No tree expansion.

**G2 (path-to-circuit):** At each edge express a and b as affine combinations of inputs and earlier AND outputs, compute their product once, retain it. Express f in final span. An m-edge path costs m ANDs and O((m+1)(n+m+1)) bounded-fanin Boolean gates in total. Thus shortest productive path length to f exactly equals multiplicative complexity MC(f). Polynomial MC and polynomial unrestricted circuit size are equivalent as nonuniform family existence statements, not uniform synthesis statements. We need no efficient optimal-path search. Every proper V containing V0 has an outgoing edge: if closed under product, it contains all monomials and hence A_n.

**G3 (exterior quotient):** For fixed V define mu_V(a,b)=ab+V in A_n/V. It is bilinear and alternating (a^2=a). Since 1*b=b in V, it factors through the exterior square of V/<1>. The productive directions are exactly the nonzero images of decomposable bivectors. For a two-plane over F2, the three nonzero vectors are a,b,a+b; all basis choices yield the same product modulo V, since a(a+b)=a+ab. Replacing a or b by its translate by 1 also changes only an element of V. Thus exact observer quotient: retain V and image of a plane, not arbitrary syntax. In reverse, V is a legal predecessor of W iff V0 subset V, V is a codimension-one subspace of W and a decomposable bivector maps to the unique nonzero line W/V under mu_V. One must test decomposability, not just membership in the linear image of mu_V; the latter can represent a sum of multiple products. G3 is a local admissibility theorem, not a lower bound on all paths.

### G4: backward cost certificate, and what remains

For a potential P on the reachable subspace vertices, P(V0)=0 and P(W)-P(V)<=1 for every productive edge imply P(V)<=m along every length-m path. If P(V)>=b_n for all V containing f_n, then MC(f_n)>=b_n. Proof: telescope increments along every path. This is the geometric bounded-charge certificate, not a claim that such a useful P has been constructed. Exact shortest distance is a circular choice; seek a separately justified invariant using the product-plane constraint. Arbitrary span dimension alone cannot pay a single-output hard target (it could enter in one direction if arbitrary extensions were free). Merely counting possible inputs or using the identity observer fails; a polynomial input-length entropy cap cannot establish superpolynomial work.

A sound explicit baseline: deg(f)<=m+1 for nonconstant f with m AND gates. Regard each AND output as a fresh formal Boolean variable y_i. The final output is affine in input and y variables. Substitute y_i in reverse topological order by a product of two affine forms in earlier variables; multilinear reduction means each substitution raises degree by at most one. Thus MC(f)>=deg(f)-1, attained by n-way conjunction. This degree certificate is bounded by n-1, so is not an asymptotic separation. One-step discriminator: for quadratic f, the off-diagonal coefficient matrix over F2 of the quadratic part of ab has rank <=2 (outer sum u v^T + v u^T); conversely rank-two alternating form is decomposable and gives one AND modulo affine terms. x1*x2+x3*x4 has rank four, so requires exactly two ANDs; adding rank bounds across arbitrary nonlinear stages without proof is invalid.

G5 coverage: any fixed deterministic finite-tape standard machine halting on every length-n input in t(n) steps has a bounded-fanin circuit of size O((t(n)+1)(n+t(n)+1)) with machine-dependent constants. Encode O(n+t) cells, head indicators, fixed alphabet/control; read symbols by head-conditioned OR reductions, update control and cell/head encodings locally; unroll t steps, halt absorbing. Hence a superpolynomial MC lower bound for canonical binary SAT f_n (invalid input rejected) implies SAT not in P. This is a sufficient classical coverage argument, not yet a native Agda/Lean source attachment. Keep f_n fixed before analyzing arbitrary circuits. Use no uncharged construction of exponential truth tables as an algorithm. Truth tables here are mathematical carriers for lower bounds.

G6 controlling open lemma: construct explicit noncircular P_n (or a different globally admissible path obstruction) whose edge increment is at most one for **all** reachable V and decomposable planes, with goal value b_n for every V containing canonical SAT f_n; prove for every c,k>=1 there exists n with b_n>c(n+1)^k. Alternatively prove direct uniform N4/N5. If obtained, G5 and N3/N6 transport to SATLowerBoundProducer. No superpolynomial bound claimed. This nonuniform route would prove NP not subset P/poly. Check Razborov–Rudich natural-proofs conditions (largeness, constructivity, usefulness) rather than assuming an algebraic reformulation evades barriers; their obstruction is conditional on strong pseudorandomness assumptions.

### Aristotle search control and exact producer ledger

Inspected current controlling PRs #1548 (Agda) and #119 (Lean), same initial roadmap blob 88690cd04eb28e0972c6b5ee92e4f47de573afda; source owner DASHI/Reasoning/AristotleMCGSHypergraphExact.agda (#607), and DASHI/Reasoning/AristotleActiveExperimentalProofSearchLoopExact.agda (#678, blob ffbd5374100bdc2dae8c536589ec0a87912912c0). The former owns SearchHypergraph, StateProved/ActionProved, QuotientSound and FeedbackRefinement; the latter separates collision/discriminator/refinement/guarded merge/reopening. Use these, not another scheduler. Alpha here is qualitative frontier impact, not an invented numeric score. Use direct source proofs to close theorem leaves; finite experiments may only falsify or steer. Preserve JMD FRACTRAN/MDL provenance (#123), DASHI residual/geometry extensions and established external multiplicative-complexity theory separately.

| Gate | Exact deliverable | Producer / current boundary |
|---|---|---|
| G1/G2 | circuitToProductFlag / productFlagToCircuit | proof above, #123 simulation, #1546 shared DAG, #1006 cost; native source transport open |
| G3 | multiplicationResidualAlternating / decomposablePlaneSuccessorIff | proof above, FactorsThrough and indexed quotient #1291; native weld open |
| G4 | flagPotentialLowerBound / reverseEliminationDegreeBound | proof above; linear-degree control not endpoint |
| G5 | boundedMachineToBooleanCircuit / polynomialMCExclusionTransfers | proof sketch above, #1129 standard-machine/interpreter, #1040 terminal |
| G6a | SATProductFlagPotentialStepBound | OPEN; all legal nonlinear extensions, not restricted circuits |
| G6b | SATProductFlagGoalSeparation | OPEN; same canonical f_n, all goal states |
| G6c | SATProductFlagSuperpolynomialGrowth | OPEN; arbitrary c,k, not a finite sample |
| N6 | originalClayTransport | conditional source consumer #1040; no unconditional producer |

Aristotle AND action for this route requires G5 AND G6a AND G6b AND G6c; other OR routes remain available. G1–G4 establish a concrete search carrier and reject false cuts. Highest-alpha next probe: find a product-plane obstruction that remains bounded under arbitrary previous nonlinear generators and separates all goal-containing flags; try dual annihilators ell(V)=0, whose pullback ell(ab) is alternating on V/<1>, and joint constraints on their decomposable images. A single rank or nonzero dual obstruction at V0 is insufficient. Track the collision between a candidate invariant on easy conjunction/parity and the proposed hard family; reopen if an unrestricted shared nonlinear witness violates it. Do not equate proof-search depth with target runtime. Retain external RC2 as restricted proving ground, not a dependency.

### Finite exact falsification probe

Locally executed Python bitset/GF(2) arithmetic; no CI or Agda/Lean kernel execution. Enumerate productive subspaces with canonical reduced bases; independently compare plane-derived directions with all-pair product directions at initial and first-step subspaces. Output cosets are counted modulo affine V0, so multiply by 2^(n+1) for number of functions. Each first-admitted coset has exact minimum AND count by G1/G2 and exhaustive breadth-first search in this small carrier.

| n | exact 0 AND | exact 1 AND | exact 2 AND | exact 3 AND | total affine cosets | independent pair checks |
|---|---:|---:|---:|---:|---:|---:|
| 3 | 1 | 7 | 8 | 0 | 16 | 8 |
| 4 | 1 | 35 | 988 | 1024 | 2048 | 36 |

For n=4 retained 35 depth-one and 2485 depth-two subspaces. All affine cosets reached at depth three. 44 independent direction-set comparisons passed at depths zero and one, not all deeper states. These finite results neither prove an asymptotic result nor assert novelty of the known multiplicative complexity model. Reproduction code is below.

References: Boyar, Peralta, Pochuev, *On the multiplicative complexity of Boolean functions over the basis (AND,XOR,1)* (2000), https://www.sciencedirect.com/science/article/pii/S0304397599001826 ; NIST overview https://csrc.nist.gov/Projects/circuit-complexity ; degree bound and small-function results https://pmc.ncbi.nlm.nih.gov/articles/PMC7802510/ ; Razborov–Rudich natural proofs https://www.cs.toronto.edu/tss/files/papers/1-s2.0-S002200009791494X-main.pdf . The subspace/exterior formulation is a working synthesis here, not a claimed novel published theorem.

```python
from itertools import combinations

def reduce(v, basis):
    for b in basis:
        if v & (1 << (b.bit_length() - 1)):
            v ^= b
    return v

def extend(basis, v):
    v = reduce(v, basis)
    if not v:
        return basis
    pivot = 1 << (v.bit_length() - 1)
    return tuple(sorted([b ^ v if b & pivot else b for b in basis] + [v], reverse=True))

def span(basis):
    values = [0]
    for b in basis:
        values += [v ^ b for v in values]
    return values

def affine(n):
    basis = ()
    for f in [(1 << (1 << n)) - 1] + [sum(1 << x for x in range(1 << n) if x >> i & 1) for i in range(n)]:
        basis = extend(basis, f)
    return basis

def plane_directions(basis):
    q = sorted(v for v in span(basis) if v and not v & 1)
    return {r for a, b in combinations(q, 2) if a ^ b > b if (r := reduce(a & b, basis))}

def all_pair_directions(basis):
    return {r for a, b in combinations(span(basis), 2) if (r := reduce(a & b, basis))}

def search(n, max_depth):
    base = affine(n)
    seen = {0}
    layer = {base}
    counts = [1]
    checks = 0
    for depth in range(1, max_depth + 1):
        following, reachable = set(), set()
        for v in layer:
            directions = plane_directions(v)
            if depth <= 2:
                assert directions == all_pair_directions(v)
                checks += 1
            for d in directions:
                w = extend(v, d)
                assert len(w) == len(v) + 1 and reduce(d, w) == 0
                if depth < max_depth:
                    following.add(w)
                quotient = ()
                for b in w:
                    quotient = extend(quotient, reduce(b, base))
                reachable.update(span(quotient))
        counts.append(len(reachable - seen))
        seen.update(reachable)
        print(f'n={n} AND={depth} new={counts[-1]} cumulative={len(seen)} retained_states={len(following) if depth < max_depth else "not retained"}')
        layer = following
    assert len(seen) == 1 << ((1 << n) - len(base))
    print(f'n={n} counts={counts} independent_all_pair_checks={checks}')
    return counts, checks

if __name__ == '__main__':
    assert search(3, 2) == ([1, 7, 8], 8)
    assert search(4, 3) == ([1, 35, 988, 1024], 36)
```


## 10. P0-G7/G8 — joint dual Walsh geometry and frozen-batch rank (2026-11-24)

Priority remains literal Clay P vs NP. This section advances the G6 research action using exact classical derivations and local GF(2) probes, not a new infrastructure or certification prerequisite. G6a–c remain open. Both controlling PRs were read at heads 70c6529a83c2 (Agda #1548) and 6b2e96c63c9c (Lean #119), common blob 0d71c3b1f398479afcf9c3c43b6503ca59e5e93a. Reuse Aristotle #607/#678 (BIDI, collision, discriminator, guarded merge/reopen), #123 (JMD MDL and FRACTRAN), #1006, #1040, #1129, #1291 and #1546 as in preceding sections.

### G7a: exact joint residual multiplicity by dual rank

Fix V containing V0, U=V/<1> of dimension d, R=A_n/V of dimension k; mu: U x U -> R is alternating bilinear. For ell in R*, let omega_ell=ell o mu with rank r_ell. For z in R define N_V(z)=#{(a,b) in U^2: mu(a,b)=z}. Character orthogonality gives

    N_V(z) = 2^(2d-k) sum_{ell in R*} (-1)^ell(z) 2^(-r_ell).

Proof: insert the orthogonality indicator for mu(a,b)+z=0. The sum of (-1)^omega_ell(a,b) over b is 2^d if a belongs to the radical and zero otherwise. The radical has dimension d-r_ell, hence the double sum is 2^(2d-r_ell). Sum over ell. This handles joint constraints, not independent per-ell charges. All quantities are exact; implementation uses integer Walsh transform of 2^(2d-r_ell) and division by 2^k. For z != 0, each contributing pair is independent and each two-plane has six ordered bases, all mapping to the same residual; P_V(z)=N_V(z)/6. The zero fibre includes dependent pairs and cannot be divided by six. G3 backward predecessor is equivalent to positive N_V(z) for the specified nonzero direction; an unsigned rank histogram cannot replace the signed character sum.

### G7b: projected dual, sound refinement and saturation

For a selected dual subspace L <= R*, dimension j, replace R by L*, mu by its projection, and k by j in G7a. The count equals the sum of full-fibre counts over directions having the same L-signature. Enlarging L therefore monotonically decreases the projected count for a fixed target z. A zero count excludes the full target; a positive projected count need not imply full reachability. This is a sound Aristotle discriminator refinement, not a cost lower bound on the execution being analysed. Do not charge the Walsh transform's work to the target circuit.

A useful reversed inequality: if every nonzero ell in L has rank >= rho, then every projected target has positive count whenever (2^j-1)2^(-rho)<1. Indeed its normalized signed sum is at least 1-(2^j-1)2^(-rho). In particular rho>=j suffices for j>0. Large dual ranks can make ALL projected directions available in a single gate, rather than impose an obstruction. Keep this as an adversarial control against rank-growth heuristics.

### G7c: exact annihilator transport and cardinality no-go

For a productive extension W=V+<c>, c=ab outside V, W^perp=V^perp intersect {ell:ell(c)=0}. This cuts the dual dimension by one. For a surviving ell, the form on W/<1> has a matrix obtained by bordering the old alternating matrix by the column ell(v_i c), its transpose, and a zero corner (ell(c^2)=ell(c)=0). Its rank increases by either zero or two: if the column is in the old column space, congruence eliminates it (the self-pairing vanishes); otherwise it adds a hyperbolic pair. This does not bound the rank of a functional which disappears, and must not be used as such.

Fix f outside V, let E_f(V)={ell in V^perp:ell(f)=1}. Then |E_f(V)|=2^(k-1). If f remains outside W, the new and target constraints are linearly independent on V^perp, and |E_f(W)|=|E_f(V)|/2. If f is in W, E_f(W) is empty: the last gate discharges ALL surviving target witnesses. Thus unweighted witness cardinality and its logarithm, without target-specific product geometry, are determined only by dimension and goal membership; they do not distinguish different off-goal targets at a fixed depth. A single gate can remove exponentially many witnesses, even at V0 (choose f=x1*x2). Independent witness charging and a universally bounded log-loss at terminal transition fail. This is an exact negative control for N4b, not a general impossibility theorem for weighted or structured potentials.

### G8a: exact frozen-operand batch metric by minimum alternating rank lift

Let M: exterior^2 U -> R be the induced multiplication map. Represent a bivector b by its alternating coefficient matrix (zero diagonal, symmetric in characteristic two). Define

    batch_V(z) = min_{b: M(b)=z} rank(b)/2,

with infinity for an empty fibre. This is precisely the minimum number of products of operands from the ORIGINAL fixed V whose XOR equals z modulo V. Every r-term sum of wedges has matrix rank <=2r by rank subadditivity. Conversely an alternating matrix of rank 2r admits a congruence to r hyperbolic blocks plus zeros (split off a pair with nonzero pairing and take its orthogonal complement, inductively). Transporting back expresses the bivector as a sum of r decomposable wedges. Applying M yields r products; affine/free V terms can be added without AND. This works for arbitrary V and quotient kernel, not only initial affine V. For V0 and quadratic f it reproduces the established half-rank theorem for quadratic Boolean forms (Mirwald–Schnorr 1992; https://www.sciencedirect.com/science/article/pii/0304397592902358). That known theorem covers unrestricted scalar quadratic complexity; the batch formula here is derived for any fixed V.

Do NOT infer a lower bound on arbitrary serial flags from this batch metric: x1*x2*x3 is outside V0^2 (so batch_V0 is infinite), yet two serial gates compute it. For a serial lower bound the changing V must be charged and controlled.

### G8b: exact serial-safe relative degree potential

For r>=1 let V^[r] be the linear span of products of at most r elements of V; 1 in V ensures monotonicity. Define delta_V(f)=min{r>=1:f in V^[r]}. This is finite since V contains the input variables. If W=V+<c>, c=ab, a,b in V, expand any product of r W operands as a sum of terms. Because c^j=c for j>=1, each term either has <=r V factors or has c times <=r-1 V factors. Hence W^[r] subset V^[r+1]. It follows that delta_V(f)-delta_W(f)<=1 for every productive edge, including unrestricted reuse. This is a concrete G6a-style potential Phi_f(V)=delta_V0(f)-delta_V(f). At every goal-containing V, delta_V(f)=1, so the bound is delta_V0(f)-1=max(1,deg(f))-1. It recovers the known degree bound, at most n-1; G6c not paid. It is important that this is an actual edgewise proof, not an empirically fitted potential.

A stronger-looking fixed-cut matrix-rank potential also fails: equality of two m-bit strings has communication matrix I_(2^m) of rank 2^m over F2, yet compute AND of the m affine equality bits with m-1 AND gates. Exponential cut rank is not exponential nonlinear cost. Use this easy family as a negative control for arbitrary rank-based potentials.

### G9: serial-safe affine-restriction lower bound (known mathematics, reusable)

Along an m-gate AND/XOR/NOT circuit, start with the entire input affine space; on the surviving flat all prior gates are affine. For the next AND, both operands restrict to affine functions. If either is constant, the product is affine; otherwise impose one nontrivial affine constraint setting one operand to zero. The flat remains nonempty, losing at most one dimension. At the end all outputs restrict to affine functions on a common affine flat of dimension >=n-m (or >=0). Thus for any output space W, MC(W)>=n-max{dim H: all outputs restrict affinely on the affine flat H}. For quadratic scalar f, its polar form has rank 2r, and the maximum totally isotropic dimension is n-r (radical plus maximal isotropic in symplectic quotient), yielding MC(f)>=r even with arbitrary nonlinear intermediates. Symplectic decomposition realizes r products, proving equality. This is established gate-elimination/normality mathematics (https://pmc.ncbi.nlm.nih.gov/articles/PMC4957665/ and Mirwald–Schnorr above), not a novel separation. The bound is capped by n, so use as a serial-safe discriminator only.

### Exact local execution receipt

Python integer bitsets and GF(2) elimination, no CI or proof-assistant kernel. G7a/b: independent direct ordered-pair counts compared to Walsh-transform rank counts; all 48 states and 38,984 residual coordinates agree (counts include zero). Full dual at V0 and all productive one-gate successor subspaces for n=3 and n=4. At n=5,6,7,8 use first eight coordinates of reduced quotient only, not full dual. Checked total pair count and divisibility by six for nonzero directions. Full cases: n=3 depth 0: 1 state/16 coordinates/7 nonzero supported directions; depth 1: 7/56/49; n=4 depth 0: 1/2048/35; depth 1: 35/35840/2975. Four projected states add 1024 coordinates. Projected nonzero support sizes 64,71,71,71 respectively. G8a: all alternating matrices on U enumerated and compared with shortest XOR-sum distance using fixed-V product directions: 44 states, 36,360 matrix lifts, 4,608 attainable residual distances, all agreed. n=3: 8 states, 456 lifts, 64 distances, max batch distance 1; n=4: 36 states, 35,904 lifts, 4544 distances, max distance 2. These are finite falsification checks, not proofs of asymptotic complexity.

Reproducer (same integer algorithm as executed; combines checks in one entry point):
```python
from collections import Counter
from itertools import combinations

def red(v,B):
    for b in B:
        if v & (1<<(b.bit_length()-1)): v^=b
    return v

def ext(B,v):
    v=red(v,B)
    if not v:return B
    p=1<<(v.bit_length()-1)
    return tuple(sorted([b^v if b&p else b for b in B]+[v],reverse=True))

def span(B):
    s=[0]
    for b in B:s += [v^b for v in s]
    return s

def affine(n):
    B=()
    for x in [(1<<(1<<n))-1]+[sum(1<<j for j in range(1<<n) if j>>i&1) for i in range(n)]:B=ext(B,x)
    return B

def rank(rows):
    B=()
    for r in rows:B=ext(B,r)
    return len(B)

def fwht(v):
    v=v.copy(); h=1
    while h<len(v):
        for i in range(0,len(v),2*h):
            for j in range(i,i+h):
                a,b=v[j],v[j+h];v[j],v[j+h]=a+b,a-b
        h*=2
    return v

def verify(B,n,selected=None):
    N=1<<n
    Q=tuple(b ^ ((1<<N)-1) if b&1 else b for b in B)
    R=()
    for q in Q:R=ext(R,q)
    d=len(R);assert d==len(B)-1
    piv={b.bit_length()-1 for b in B}; free=[i for i in range(N) if i not in piv]
    if selected is not None:free=free[:selected]
    k=len(free)
    def label(v):
        r=red(v,B)
        return sum(((r>>p)&1)<<j for j,p in enumerate(free))
    M=[[label(a&b) for b in R] for a in R]
    assert all(M[i][i]==0 for i in range(d))
    spectrum=[]
    for l in range(1<<k):
        rows=[sum((((l&c).bit_count()&1)<<j) for j,c in enumerate(row)) for row in M]
        r=rank(rows);assert r%2==0
        spectrum.append(1<<(2*d-r))
    transform=fwht(spectrum)
    assert all(x>=0 and x%(1<<k)==0 for x in transform)
    predicted=[x>>k for x in transform]
    s=span(R); direct=Counter(label(a&b) for a in s for b in s)
    assert predicted==[direct[i] for i in range(1<<k)]
    assert sum(predicted)==1<<(2*d)
    assert all(x%6==0 for x in predicted[1:])
    return len(predicted),sum(x>0 for x in predicted[1:]), min((x//6 for x in predicted[1:] if x),default=0),max(predicted[1:],default=0)//6

def batch(V,n):
    mask=(1<<(1<<n))-1; U=()
    for v in V: U=ext(U,v^mask if v&1 else v)
    d=len(U); edges=list(combinations(range(d),2)); images=[red(U[i]&U[j],V) for i,j in edges]
    minlift={}
    for w in range(1<<len(edges)):
        rows=[0]*d; z=0
        for h,(i,j) in enumerate(edges):
            if w>>h&1:
                rows[i]^=1<<j; rows[j]^=1<<i; z^=images[h]
        r=rank(rows);assert r%2==0
        minlift[z]=min(minlift.get(z,d),r//2)
    s=span(U); dirs={red(a&b,V) for a,b in combinations(s,2)}-{0}
    dist={0:0}; fringe={0}
    while fringe:
        nxt={a^b for a in fringe for b in dirs}-dist.keys()
        for v in nxt: dist[v]=dist[next(iter(fringe))]+1
        fringe=nxt
    assert minlift==dist
    return 1<<len(edges),len(dist),max(dist.values())

if __name__=='__main__':
    states=coords=lifts=targets=batchstates=0
    for n in (3,4):
        V=affine(n); vals=span(V)
        first={ext(V,a&b) for a,b in combinations(vals,2) if red(a&b,V)}
        for W in {V}|first:
            r=verify(W,n); states+=1; coords+=r[0]
            l,t,m=batch(W,n); batchstates+=1;lifts+=l;targets+=t
    for n in (5,6,7,8):
        r=verify(affine(n),n,8);states+=1;coords+=r[0]
    assert (states,coords)==(48,38984)
    assert (batchstates,lifts,targets)==(44,36360,4608)
    print('DUAL AND BATCH EXACT COUNTS PASS',states,coords,batchstates,lifts,targets)
```

### Aristotle frontier / phase and next mathematical action

| ID | Exact deliverable | Status |
|---|---|---|
| G7a | jointDualRankResidualCount; nonzeroPlaneCount | derived, exact finite checks |
| G7b | projectedDualCountMonotone; rankSaturationSufficient | derived, finite projected check of count only |
| G7c | annihilatorHyperplaneUpdate; survivingRankBorderBound; targetWitnessCardinalityNoGo | derived, proof above |
| G8a | frozenBatchMinimumAlternatingRankLift | derived, exact finite checks |
| G8b | relativeDegreeEdgeBound | derived, serial-safe but <=n-1 |
| G9 | commonAffineRestrictionBound / quadraticRankExact | classical proof above; known, <=n |
| G10a | historySensitiveRankLiftTransport | OPEN: find serial-safe joint obstruction not reset by a single reused product |
| G10b | SATSpecificGoalSeparation | OPEN: actual canonical SAT family, not random functions or arbitrary truth tables |
| G10c | superpolynomialSerialPotential | OPEN: prove all-edge bound and superpolynomial goal gap on same carrier |
| G5/N6 | machine coverage and endpoint transfer | classical coverage argument supplied; original formal weld conditional |

G10a-c refine G6a-c, not additional mandatory phases for another successful route. Highest alpha now: back-solve through the exact relative-power inclusion W^[r] <= V^[r+1] while retaining the joint kernel of M, rather than collapse all fibres to degree or frozen rank. Seek a target-dependent obstruction that cannot be discharged by a common reused nonlinear term (in a batch of W products their expansions have the form sum of V-products + c times one element of V, since c^2=c and 1 in V). The latter identity is exact: (u_i+alpha_i c)(v_i+beta_i c) = u_i v_i + c(alpha_i v_i+beta_i u_i+alpha_i beta_i), and summing combines all reuse into one coefficient. It gives a reverse-search branch rule, not yet a serial rank-charge bound. Use equality, conjunction, cubic, quadratic half-rank and cheap shared decoders as adversarial controls. A zero marginal excludes one step, not all short paths. Do not optimize a finite proof-search graph as if its search cost were SAT runtime. Keep direct uniform N4/N5 and behavioural alternative available. No superpolynomial separation, native kernel certification, or proof of P != NP claimed.


## 11. P0-G10/G11 — serial rank transport and affine orbit collapse (2026-11-24)

P0 is the literal Clay P vs NP endpoint. User-supplied geometric donors: hyper-hollow B4 signed-permutation cell collapse (Round55/56, #564), hierarchical tree addresses, multiscale contraction, collar absorption, chord/arc shortcut, and CRT independent-channel collapse. Only their transferable mathematical patterns are used here. No physics, E8/Monster identification, UV, continuum-measure or fluid-regularity theorem is inferred or needed. The previous G7–G10 packet is the direct source; inspected both controlling branches at 6082f641fa6f (Agda #1548) and 1b4855b5be32 (Lean #119), same blob cfcbd095abd6d886d94225cce3e71d8b1ca37bc3. Aristotle #607/#678 governs backward discriminators and counterexamples.

### G10a-local: exact rank-lift transport for a productive extension

Let W=V+<c>, c=ab outside V; U=V/<1>. Choose a basis of U and the appended c in W/<1>. A bivector on W/<1> decomposes uniquely as B0+c wedge L, where B0 in exterior^2 U and L in U. Its alternating matrix has blocks [B0 L; L^T 0] (coordinates of L in the selected basis). Its rank equals rank(B0) plus 0 if L lies in the column space of B0, or plus 2 otherwise. Proof: if L=B0 t, a congruence change of the appended vector eliminates L and t^T B0 t=0; otherwise L pairs nontrivially with the radical, adding exactly a hyperbolic pair (or use rank-nullity on the bordered matrix). Rank and column-space membership do not depend on the choice of compatible basis.

Consequently the exact G8a batch-cost transport is

    batch_W(f+W) = min { rank(B0)/2 + 1[L notin im B0] :
                        M_V(B0) = f+cL (mod W) }.

Here M_V has values in A_n/V and equality modulo W means compose the quotient A_n/V -> A_n/W. L is represented by any lift to V (changing lift by 1 changes cL by c, absorbed modulo W). Empty fibre has infinity cost. Proof: apply G8a in W and the unique bivector decomposition; the image is M_V(B0)+cL modulo W. This is exact for all productive edges, and includes arbitrary reuse of the new generator. It pays a local transport identity, **not** G10a's requested global serial-safe bounded-charge invariant: the shifted target f+cL may be much easier or harder than f, and might change on every step. Cubic f remains the negative control (initial frozen batch infinite, after one product finite). Do not replace this minimization with rank of one arbitrary lift, or impose equality modulo V without allowing the c offset.

### G11a: exact orbit quotient of Boolean product flags (B4 pattern)

Use G=AGL(n,2) acting on A_n by precomposition with affine bijections (use inverses for a left action if desired). It preserves addition, multiplication and 1, and preserves V0. Hence g(V+<ab>)=gV+<(ga)(gb)>: productive edges and their cost are equivariant. The quotient graph has an edge [V]->[W] iff some representatives have an edge. Every quotient path starting at [V0] lifts to an actual path by transporting the next edge so its source is the current representative. Conversely every actual path projects at identical length.

For a fixed f, goal states are V containing f. Full-group orbit distance from [V0] to the set of orbits with some representative containing f equals actual distance to f: lift the path, then use a single group transformation mapping its final state to the representative containing f; V0 stays fixed. Alternatively carry the pair (V,f+V0), or restrict to the stabilizer of f+V0 to keep the target fixed throughout local backward search. Do not quotient by arbitrary GL(A_n): preservation of multiplication is essential. For multi-output target S use its orbit or its stabilizer. Canonicalization/search cost is not execution cost.

The complete affine coset action on scalar functions modulo V0 has 3 orbits for n=3 (sizes 1,7,8) and 8 orbits for n=4 (sizes 1,16,28,35,120,448,560,840). The reachable flag layers have:

| n | depth | states | orbit types | orbit sizes |
|---|---:|---:|---:|---|
| 3 | 0 | 1 | 1 | 1 |
| 3 | 1 | 7 | 1 | 7 |
| 3 | 2 | 35 | 2 | 7,28 |
| 4 | 0 | 1 | 1 | 1 |
| 4 | 1 | 35 | 1 | 35 |
| 4 | 2 | 2485 | 4 | 105,280,420,1680 |

These are exact finite local Python bitset results, not a correspondence to B4/E8 or an asymptotic lower bound. All depth-two orbits are hit from depth-one representatives. Checked rank-transport formula on one incoming edge per depth-one and depth-two orbit: n=3 three edges, 2112 (B0,L) pairs, 16 residual distances; n=4 five edges, 132096 pairs, 1408 residual distances; independent BFS on frozen product-direction XOR sums agreed on all 1424 attainable distances. No CI/kernel run.

### G11b: no-go for forcing orbit-invariant intermediate states (chord/arc pattern)

Quotienting the actual graph is not the same as restricting all states to invariant subspaces. For n>=4 consider the S_n-symmetric target AND(x1,...,xn). Any first productive S_n-invariant extension of V0 must have its one-dimensional quotient line fixed (F2 has no nontrivial scalar), and its generator modulo affine is a nonzero invariant quadratic form. Coordinate permutations are transitive on unordered variable pairs, so that form must be q=sum_{i<j} x_i x_j. Its polar matrix has all off-diagonal entries 1 and diagonal 0: rank n if n even, n-1 if n odd (kernel consists of constant vectors for odd n). Hence rank >=4. But a single product of affine forms has quadratic polar rank <=2. There is no productive invariant first state, whereas the symmetric target has an unrestricted path of n-1 AND gates. This is an exact symmetry-breaking shortcut. A lower bound on symmetry-restricted paths, monotone paths, block-local paths or chosen representatives without lifting cannot certify unrestricted MC. The orbit quotient G11a is sound precisely because it does not exclude such paths.

Also, orbit reduction cannot by itself collapse all functions to a polynomial family: there are 2^(2^n-n-1) affine cosets and |AGL(n,2)|=2^n product_{i=0}^{n-1}(2^n-2^i) <=2^(n^2+n). Thus there are at least 2^(2^n-n^2-2n-1) scalar coset orbits. This lower bound counts orbits, not SAT circuit size. To extract a stronger theorem one must exploit a particular succinct target, not assume all cases reduce to a few types at arbitrary n.

### G11c: hierarchical slice and gluing (tree / CRT / collar pattern)

For a split x=(u,t), t one Boolean bit, write f=f0(u)+t(f0(u)+f1(u)). Restriction to t=0 or 1 never increases MC; independent branch computations can be glued by one additional AND. Therefore max(MC(f0),MC(f1)) <= MC(f) <= MC(f0)+MC(f1)+1. Lower bound by MAX, not SUM: one gate can work simultaneously on both restrictions. The same applies to hierarchical restrictions on many bits. Under the algebra isomorphism A_n = A_(n-1) x A_(n-1) (two Boolean slices), multiplication is coordinatewise; a gate is shared across the slices. CRT-like independent coordinate representation is not independent resource payment. Any dyadic/p-adic-style decomposition or weighted multiscale charging must establish bounded overlap on actual primitives (R4); geometric contraction of a residual is neither a lower bound on work nor proof of asymptotic separation. This does not assert any physics donor theorem. The two-sided inequality is an exact general control for multiscale attempts.

### G12 highest-alpha frontier

| ID | Exact obligation | Status |
|---|---|---|
| G10a-local | borderedAlternatingRank / reverseBatchLiftTransport | mathematical derivation, exact local checks |
| G11a | affineOrbitProductFlagPathLift / targetOrbitDistanceExact | mathematical derivation, finite orbit check |
| G11b | invariantFlagShortcutCounterexample / orbitCountNoGo | mathematical derivation |
| G11c | sliceRestrictionAndGluingBound | mathematical derivation |
| G12a / G10a / G6a | serialTargetShiftBound: control f -> f+cL for all legal histories with bounded per-gate charge, using joint rank fibres, not sum of restrictions | OPEN |
| G12b / G10b / G6b | SAT-specific goal gap for the same invariant, after orbit lifting | OPEN |
| G12c / G10c / G6c | superpolynomial gap in encoded input length | OPEN |
| G5/N6 | polynomial coverage / actual Clay terminal | classical coverage derivation; source attachment and actual lower bound remain unpaid |

Next BIDI action: seek a SAT-specific obstruction in the joint slice/target-shift rank-lift fibre that is invariant under arbitrary representative changes; use orbit quotient only to eliminate duplicate proof-search states. Discriminate by comparing cheap symmetry-breaking flags and shared slice circuits against proposed progress measures. Need a reason a single cL cannot resolve many target obligations, not a bound on canonicalization or proof search. Explore exact small residuals and original SAT restrictions only as falsification; do not let extended finite orbit census delay the endpoint. G12a-c refine G6, not an extra mandatory phase; direct uniform N4/N5 remains active OR route. No superpolynomial lower bound or Clay closure claimed.

### Local reproduction (Python exact integer GF(2); no CI)

```python
from itertools import combinations

def red(x,B):
    for b in B:
        if x>>(b.bit_length()-1)&1:x^=b
    return x

def ext(B,x):
    x=red(x,B)
    if not x:return B
    p=1<<(x.bit_length()-1)
    return tuple(sorted([b^x if b&p else b for b in B]+[x],reverse=True))

def basis(xs):
    B=()
    for x in xs:B=ext(B,x)
    return B

def span(B):
    s=[0]
    for b in B:s += [x^b for x in s]
    return s

def affine(n):
    return basis([(1<<(1<<n))-1]+[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)])

def dirs(V):
    return {red(a&b,V) for a,b in combinations(span(V),2)}-{0}

def succ(V):
    return {ext(V,c) for c in dirs(V)}

def gens(n):
    N=1<<n; ps=[]
    for i in range(n):ps.append([x^(1<<i) for x in range(N)])
    for i in range(n-1):
        ps.append([x^(((x>>i^x>>(i+1))&1)*((1<<i)|(1<<(i+1)))) for x in range(N)])
        ps.append([x^(((x>>(i+1))&1)<<i) for x in range(N)])
    return ps

def transform(f,p):
    return sum(1<<i for i,j in enumerate(p) if f>>j&1)

def orbits(S,action,ps):
    remaining=set(S); out=[]
    while remaining:
        seed=min(remaining);seen={seed};queue=[seed]
        for s in queue:
            for p in ps:
                t=action(s,p); assert t in S
                if t not in seen:seen.add(t);queue.append(t)
        remaining-=seen;out.append((seed,seen))
    return out

def lift_tables(V,W,c,n):
    mask=(1<<(1<<n))-1
    U=basis(v^mask if v&1 else v for v in V)
    assert len(U)==len(V)-1
    d=len(U); es=list(combinations(range(d),2))
    images=[red(U[i]&U[j],V) for i,j in es]
    rev={}
    for w in range(1<<len(es)):
        rows=[0]*d;z=0
        for h,(i,j) in enumerate(es):
            if w>>h&1:rows[i]^=1<<j;rows[j]^=1<<i;z^=images[h]
        B=basis(rows);r=len(B);assert r%2==0
        for l,L in enumerate(span(U)):
            zW=red(z^(c&L),W)
            cost=r//2+bool(red(l,B))
            rev[zW]=min(rev.get(zW,100),cost)
    direct={0:0};fr={0};D=dirs(W)
    while fr:
        nxt={a^b for a in fr for b in D}-direct.keys()
        level=direct[next(iter(fr))]+1
        for z in nxt:direct[z]=level
        fr=nxt
    assert rev==direct
    return (1<<len(es))*(1<<d),len(direct)

for n in (3,4):
    V=affine(n);ps=gens(n);layer={V};first=None;second=None
    for d in range(3):
        O=orbits(layer,lambda W,p:basis(transform(w,p) for w in W),ps)
        print(n,d,len(layer),len(O),sorted(len(x[1]) for x in O))
        if d==1:first=O
        if d==2:second=O
        if d<2:layer=set().union(*(succ(W) for W in layer))
    piv={b.bit_length()-1 for b in V}
    qs=span(tuple(1<<i for i in range(1<<n) if i not in piv))
    Q=orbits(set(qs),lambda f,p:red(transform(f,p),V),ps)
    print('function cosets',len(Q),sorted(len(x[1]) for x in Q))
    actual=set().union(*(succ(W) for _,orb in first for W in orb))
    rs=set().union(*(succ(W) for W,_ in first))
    assert all(any(w in rs for w in orb) for _,orb in second)
    assert actual==set().union(*(orb for _,orb in second))
    count=cases=targets=0
    for W,_ in first:
        c=next(w for w in W if red(w,V))
        a,b=lift_tables(V,W,c,n);count+=1;cases+=a;targets+=b
    for W,_ in second:
        P=next(P for _,orb in first for P in orb if all(not red(p,W) for p in P) and W in succ(P))
        c=next(w for w in W if red(w,P))
        a,b=lift_tables(P,W,c,n);count+=1;cases+=a;targets+=b
    assert (count,cases,targets)==({3:(3,2112,16),4:(5,132096,1408)}[n])
    print('reverse lift',count,cases,targets)
```
