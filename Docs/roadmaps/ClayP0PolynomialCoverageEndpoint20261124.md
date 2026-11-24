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
