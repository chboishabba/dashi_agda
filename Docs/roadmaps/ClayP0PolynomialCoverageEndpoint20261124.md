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


## 12. P0-G13 — same-endpoint computational chords and the actual SAT selector geometry (2026-11-24)

Clay P vs NP remains the sole P0 endpoint. This packet replaces a generic search for a hard geometry with a specific NP-complete family and exact local lift criteria. It does not claim a superpolynomial bound or close N4/N5/G12. Source review (default-branch file blobs):
- [KSW668BraneBulkRationalNullComparatorExact](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Physics/Gravity/KSW668BraneBulkRationalNullComparatorExact.agda), blob 73e84d841e6d5311d227afa21fc055191a047375: ambientNullArrivalSavesFour, noIntrinsicAmbientEqualLengthHere, sameSourceDestinationCoordinate. Reuse the same-endpoint ambient/intrinsic distinction, not the physical claim. Actual computational shortcuts must preserve the identical Boolean target and legal cost.
- [Monster3BAtlasSymplecticSimilitudeHeisenbergLiftExact](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Moonshine/Monster3BAtlasSymplecticSimilitudeHeisenbergLiftExact.agda), blob 9f83005c83acd25e9a9d3665a3780b9c8bcf36a1: central correction and cocycle compatibility separated; characteristic-three half-polarization is NOT transported to characteristic two. Reuse linear-first, coupled quadratic residual methodology only.
- [PNotEqualsNPDirectSATLowerBoundExact](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Mathematics/Complexity/PNotEqualsNPDirectSATLowerBoundExact.agda), blob 0838b3252b3ffb91993e4cb47a5d5c06a00e4fe1: actual SATDecisionFailure, anchored candidates and terminal consumers. #1040/#1129/#1474/#1502 remain standard machine and formula owners; #123 JMD computational lowering, #1006 costed FactorsThrough, #1546 sharing, #1291 indexed geometry, #607/#678 Aristotle remain donors. Prior PR heads 049e4ed2d9f7 / b35f249b3b21, common blob 27d6e518c1e242062d759e13f22c476623afbd95.

### G13a — fixed-operand linear chord lift (unrestricted preceding V)

Let V contain 1 and the inputs, a in V, X_i={x:a(x)=i}. Then f in V+aV iff f|X_i in V|X_i for both i=0,1. Necessity by restriction; sufficiency choose u,v in V matching the two restrictions, and f=(1+a)u+av=u+a(u+v). This is an exact single-AND shortcut test; solve for u,v by GF(2) Gaussian elimination after choosing a. Equivalently V+aV=(1+a)V direct-sum aV, as disjoint-support function spaces. Dimension equals rank of each restricted evaluation matrix added, and dual nonmembership is a linear witness annihilating the entire V+aV. A collision here means a linear dependence of rows with incompatible target labels, not necessarily two inputs indistinguishable by V (V contains inputs). A fixed a can be chosen modulo 1. Enumerating a is still exponential in dim V; proof-search cost is not circuit cost.

### G13b — exact two-gate chord normal form

Modulo additions from V, the targets reachable with <=2 productive ANDs over V are exactly the union of
(i) parallel: ab+uv, a,b,u,v in V;
(ii) serial: (ab+u)v, a,b,u,v in V.
For the proof, let c=ab be the first gate and the second have operands u+alpha*c, v+beta*c with binary alpha,beta. The output is d+gamma*c+(u+alpha*c)(v+beta*c), d in V. If both alpha,beta zero, the result is parallel (gamma may be zero). If exactly one is one, absorb gamma into the other operand via v+gamma, and absorb the resulting affine-in-V correction. If both one, use (u+c)(v+c)=(u+c)(u+v+1) by idempotence; then absorb gamma as in the one-serial case. Conversely both forms are legal two-gate circuits. This also works using any representative c of the first direction modulo V since the difference is absorbed into u. It is an exact local chord characterization, not an all-depth lower bound; two-gate serial and parallel routes must both remain live. The failed first probe excluded constants from the second serial operand; it missed legal outputs. Restoring all of V (including 1) corrected the mismatch. This is a concrete Aristotle collision/reopening.

### G13c — a specific NP-complete geometric target (no arbitrary truth-table family)

For m>=1, let C_m contain all non-tautological clauses on j distinct variables, 1<=j<=3, with every polarity. Put N_m=sum_{j=1}^3 2^j binom(m,j), interpreting out-of-range binomials as zero. Input s in F2^N_m selects clauses. Define F_m(s)=1 iff conjunction of selected clauses is satisfiable; language rejects lengths not equal to an N_m. Membership in NP: m-bit assignment, evaluate each selected clause. NP-hardness: normalize arbitrary 3-CNF (rename variables to 1..m, delete repeated literals/clauses and tautologies, handle empty clause separately), set corresponding selector bits. Construction polynomial in original input length; N_m=Theta(m^3) and m<=original length after renaming. The standard 3-SAT NP-completeness theorem gives this language NP-complete; #1474/#1502 provide existing reduction/codec donors. This is a concrete classical reduction, not yet an attachment to the precise repository binary formula codec. No superpolynomial blowup hidden; input length is N_m, NOT 2^m.

For each assignment x, define Z_x={C: x falsifies C}. A satisfying selector lies on the coordinate flat H_x={s:s_C=0 for C in Z_x}. Thus the actual positive set is exactly union_{x in F2^m} H_x. Put b(m)=sum_{j=1}^3 binom(m,j). Each |Z_x|=b(m) (one falsified polarity per variable subset), so dim H_x=N_m-b(m). If dist_H(x,y)=h, common falsified clauses use only the m-h agreeing coordinates, hence |Z_x intersect Z_y|=b(m-h), and

    codim(H_x intersect H_y)=2 b(m)-b(m-h).

For arbitrary assignment set X, codim intersection H_x = sum over coordinate subsets I, 1<=|I|<=3, of |{x|I:x in X}|; this follows because distinct restrictions correspond to distinct falsified polarities. This is the exact joint overlap invariant, not a sum of pairwise distances. Signed permutations of assignment coordinates induce clause-selector permutations preserving the entire family; quotienting witnesses does not restrict circuits to symmetry-invariant intermediate flags. For an arbitrary V and selector operand a, G13a applies on the original selector cube, not on the assignment cube: do not conflate the two.

### G13d — solve the existential lift, isolate deterministic resource obstruction

For each clause C let q_C(x) be the product of its false-literal indicators, so it equals one iff C is false. For width 3 introduce p_C=l_1*l_2 and q_C=p_C*l_3; width 2 needs q_C=l_1*l_2; width 1 already affine. All these are quadratic equations, and require s_C*q_C=0 for each clause. For fixed (s,x) auxiliaries are uniquely determined by those definitions; after existentially quantifying x and auxiliaries, the projection is precisely F_m. There are O(N_m) auxiliary variables/constraints, explicitly. With x fixed the remaining selector constraints are linear, the coordinate flats above. This is the promised linear + quadratic extension model, not a deterministic algorithm: x is existential.

An unrestricted m_gate-AND scalar circuit is equivalently a triangular quadratic lift: fresh bits y_i=A_i(s,y_<i) B_i(s,y_<i), both affine, followed by an affine output. For each s, y_i are uniquely generated in order; arbitrary XOR/fanout and all prior generators allowed. Conversely any such system gives exactly that AND count (including redundant gates, which may be removed). Thus the geometric lower-bound problem is to exclude polynomial-size TRIANGULAR DETERMINISTIC lifts of this concrete existential projection. Merely exhibiting polynomial equations or unique satisfying assignments is insufficient; the equations must admit the specified triangular execution. If MC(F_m) is superpolynomial in N_m then the selector language has no polynomial bounded-fanin circuits by G1/G2, and hence is not in P by G5; NP-completeness implies P != NP. This route would establish the stronger NP not subset P/poly. The uniform N4/N5 route stays active in parallel.

### G13e — exact covering obstruction and matching shortcut control

Every assignment gives the maximal allowed selector s^x=1 outside Z_x and 0 on Z_x. All these 2^m selectors are distinct (unit clauses distinguish assignments) and equally sized, so no one dominates another; every positive input is below one of them. Any DNF implicant that contains two different maxima also contains their bitwise OR (each literal fixed on both remains fixed). That OR is not positive, by maximality. Thus minimum DNF term count is exactly 2^m: one term per maximal selector suffices, as the flat formula shows. Since N_m=Theta(m^3), this is superpolynomial in encoded input length, but ONLY a DNF lower bound. Do not promote this to unrestricted MC.

Restrict all width-two and width-three selector bits to zero. Then F_m restricted is the unit-clause consistency function U_m=product_i(1+p_i*n_i), with p_i,n_i the positive and negative unit selectors. It has degree 2m and hence MC>=2m-1 by G8b; m pair products and m-1 combining ANDs attain equality. Its DNF also needs exactly 2^m terms by the same maximal-selector argument. This is the actual same-family chord negative control, not an unrelated easy function. It proves MC(F_m)>=2m-1 under restriction, which is only Omega(N_m^(1/3)). Therefore the missing lemma cannot be paid merely by counting maximal flats, their DNF terms or assignment witnesses. Need width-two/three interaction obstruction surviving arbitrary triangular lifts.

### Local exact checks (not kernel proofs)

Executed Python integer truth-table and GF(2) elimination, no CI. G13a: 120+1136=1256 fixed operand subspace equalities V+aV=(1+a)V direct-sum aV at initial and all first productive states of n=3,4. G13b: independent exhaustive two-gate product-flag outputs modulo V0 versus union of forms:
| n | parallel | serial | union | serial only | parallel only |
|---|---:|---:|---:|---:|---:|
|3|8|16|16|8|0|
|4|64|996|1024|960|28|
All exact. The serial normal form initially failed with v restricted modulo constants; corrected to v in full V. Unit family ANF verified for m=1..7, degree 2m and 2^m terms; exact MC=2m-1 follows from proof, not enumeration of all circuits. Pair codimension formula checked for 10,795 distinct assignment pairs m=1..7. Union-of-flats vs clause truth evaluated on all selector inputs for m=1,2 (4+256=260). Reproduce with basis/ext/red/span/affine/dirs helpers from section 11, using:
```python
from itertools import combinations
from math import comb
for n in (3,4):
    V=affine(n); mask=(1<<(1<<n))-1; D=dirs(V)
    first={ext(V,c) for c in D}; checks=0
    for W in {V}|first:
        Q=basis(v^(mask if v&1 else 0) for v in W)
        for a in span(Q):
            assert basis([*W,*[a&b for b in W]])==basis([*[v&(mask^a) for v in W],*[v&a for v in W]])
            checks+=1
    direct={0}|D
    for W in first:
        for r in dirs(W)|{0}:
            direct.update(red(r^w,V) for w in W)
    par={a^b for a in D|{0} for b in D|{0}}
    ser={red((c^u)&v,V) for c in D|{0} for u in span(V) for v in span(V)}
    assert direct==par|ser
    assert (checks,len(par),len(ser),len(direct))==({3:(120,8,16,16),4:(1136,64,996,1024)}[n])
def b(m):return sum(comb(m,j) for j in range(1,min(3,m)+1))
pairs=0
for m in range(1,8):
    cs=[(I,p) for j in range(1,min(3,m)+1) for I in combinations(range(m),j) for p in range(1<<j)]
    Z=[sum(1<<h for h,(I,p) in enumerate(cs) if p==sum(((x>>i)&1)<<j for j,i in enumerate(I))) for x in range(1<<m)]
    assert len(set(Z))==len(Z) and all(z.bit_count()==b(m) for z in Z)
    for x,y in combinations(range(1<<m),2):
        assert (Z[x]&Z[y]).bit_count()==b(m-(x^y).bit_count())
        pairs+=1
    if m<=2:
        for s in range(1<<len(cs)):
            assert any(not s&z for z in Z)==any(all(not(s>>h&1) or any(((x>>i)&1)!=((p>>j)&1) for j,i in enumerate(I)) for h,(I,p) in enumerate(cs)) for x in range(1<<m))
    n=2*m
    a=[int(all(not((x>>(2*i)&1) and (x>>(2*i+1)&1)) for i in range(m))) for x in range(1<<n)]
    for i in range(n):
        for x in range(1<<n):
            if x>>i&1:a[x]^=a[x^(1<<i)]
    assert a[-1]==1 and sum(a)==1<<m
assert pairs==10795
```

### Endpoint-first frontier (same P0-C/D, no new prerequisite phase)

| Gate | Exact deliverable | Status / producers and consumers |
|---|---|---|
| G13a | fixedOperandLinearChordIff | derived, finite checks; FactorsThrough, chord same-endpoint donor; feeds G7/G10 |
| G13b | twoGateParallelOrSerialNormalForm | derived, exact checks; G8/G10, #1546 shared DAG; feeds BIDI search |
| G13c | selector3SATPolynomialReduction / selectorFlatsJointIntersection | classical construction derived; #1474/#1502; actual original codec weld still open |
| G13d | selectorExistentialQuadraticLift / triangularLiftCircuitIff | derived; #123 simulation, #1129 machine, Monster linear/quadratic methodology (no F3 arithmetic imported) |
| G13e | selectorDNFExact / unitRestrictionMCExact | derived; width-one negative control; only restricted superpoly DNF and linear-in-m general MC |
| G12a/G6a | serialTargetShiftBound | OPEN: target-specific admissible invariant, all triangular gates, including both chord types |
| G12b/G6b | selectorGoalSeparation | OPEN: simultaneous width-two/three obligations with actual s-input semantics |
| G12c/G6c | selectorSuperpolynomialGrowth | OPEN: gap exceeds all polynomials in N_m, not assignment count |
| N6 | originalClayTransport | #1040 conditional producer; no unconditional payment |

Highest alpha: use the explicit clause-coordinate overlap lattice, not a generic dimension count, and backsolve necessary triangular lift properties on F_m while requiring the same measure to correctly admit the unit-only shortcut. Try linear completion on arbitrary a already available (not merely coordinate splits), and retain joint rank-lift fibres under serial target shifts. Any potential must survive all such chords; a proof of only the two-gate local criterion does not extend automatically. The existential quadratic lift's witness uniqueness conditional on x does not construct x. Keep direct uniform machine lower bound and behavioural diagonal alternative alive. Endpoint mathematics first; no new Monster/physics task, no exhaustive large flag census, no CI. Native Agda/Lean attachment follows the mathematical endpoint.


## 13. P0-G14/G15 — orbit parity, phase-sensitive boundary jets and the 2-SAT shortcut (2026-11-24)

**P0 remains literal Clay P vs NP.** This section combines the attached G13 selector geometry with the labelled relative-line/translation construction from the parallel arithmetic donor [Agda #1549](https://github.com/chboishabba/dashi_agda/pull/1549) (head 0e371f0004be) / [Lean #120](https://github.com/chboishabba/dashi_lean4/pull/120) (head c7746dc0f61a), whose PR metadata was checked. Use the Boolean derivative exponents directly. No Langlands, Monster, physical or additional arithmetic endpoint is required. The characteristic-two cocycle matrix equation C+C^T=B requires B alternating; do not assume this for arbitrary pairings. For the G7 annihilator pairing the diagonal vanishes by Boolean idempotence. Previous P0 roadmap heads 9cd7ebdc7459 / ca3364ab5eb5, common blob 7254ad6c6460bb355e57e7bdbcea4cc18dd6fa61.

### G14a — full algebraic degree, all widths (general proof)

For 1<=w<=m (or truncate w at m), let C_m,w contain all clauses on 1..w distinct variables, all polarities. Define N_m,w=sum_{j=1}^w 2^j binom(m,j), b_m,w=sum_{j=1}^w binom(m,j), and F_m,w(s) as satisfiability of the selected clauses. The actual NP-complete family G13 is w=3, input length N_m,3=Theta(m^3). In complementary coordinates t=1+s, F(1+t)=1+prod_{x in F2^m}(1+prod_{C in Z_x} t_C), as Boolean functions. All products are multilinearized using t_C^2=t_C. The coefficient of the full monomial prod_C t_C equals parity of subsets X of assignments such that union_{x in X} Z_x=C_m,w. The additive group F2^m acts on these subsets by translation and on the clause universe by polarity flips, preserving the cover condition. Every nonsingleton orbit has even size because the group is a 2-group. A subset invariant under the entire transitive translation action is empty or the whole cube. Exactly the whole cube is a cover (each clause is falsifiable). Hence the coefficient is 1. Input complementation preserves algebraic degree, so deg F_m,w=N_m,w for every m>=1,w>=1. Equivalent parity statement: the number of satisfiable selector inputs is odd.

G8b relative-degree edge bound now yields the unconditional unrestricted AND/XOR/NOT lower bound

    MC(F_m,3) >= N_m,3 - 1.

This replaces the weaker 2m-1 unit restriction as the strongest established bound in this roadmap for the actual selector family. It allows arbitrary shared nonlinear computation and all G11 symmetry-breaking paths. It is linear in encoded input length, NOT superpolynomial. This argument also proves full degree for w=1 and w=2, so degree cannot separate these easy families from w=3. Do not infer novelty of known degree or symmetry arguments.

### G14b — exact local boundary isolation and sharp escape

At maximal satisfiable selector s^x=1+1_Zx, let R be removed clauses (subset of C minus Z_x), A added clauses (subset of Z_x). The modified input is compatible with another assignment y iff Z_y minus Z_x is contained in R and A is disjoint from Z_y. This follows by intersecting the selected clause set with Z_y. If y!=x and h=Hamming(x,y), then |Z_y minus Z_x|=b_m,w-b_(m-h),w. Its minimum is

    D_m,w = b_m,w-b_(m-1),w = sum_{j=0}^{w-1} binom(m-1,j).

Thus if |R|<D_m,w no other assignment survives; satisfiability iff A empty. The Hamming ball of radius D_m,w around s^x agrees with the single-flat indicator prod_{C in Z_x}(1+s_C), since for any nonempty A there are at most D_m,w-1 removals. Sharpness: choose y differing by one assignment bit, remove Z_y minus Z_x (exactly D_m,w clauses), and add one C in Z_x minus Z_y. The resulting selector is satisfiable by y but not x at distance D_m,w+1. For w=3 D=1+(m-1)+binom(m-1,2). The separation of witness regions is quadratic in m but does not charge all legal computational chords.

### G15a — exact phase-sensitive local derivative ranks

For distinct selector coordinates T, define the Boolean mixed derivative Delta_T as the sum modulo 2 over toggles of all subsets of T (empty T gives the function). Relative-character phases from the attached arithmetic donor are (-1)^Delta_T, so the following retains signed information, not absolute Walsh magnitudes. For |T|<=D_m,w, G14b implies

    Delta_T F(s^x) = 1[T subset Z_x] = prod_{C in T} q_C(x).

Proof: every vertex of the toggle subcube lies within the radius-D ball. The local flat indicator is 1 exactly for toggles avoiding Z_x; their number is 2^|T minus Z_x|, odd exactly when T subset Z_x. The first-derivative matrix (rows x, columns C) is the clause falsification matrix. Every column has degree <=w in assignment bits. Conversely each monomial of degree 1..w is a column, and the constant is a sum of complementary unit columns. Thus rank=b_m,w+1 over F2.

The cumulative labelled jet matrix J_r, rows indexed by x and columns by T with |T|<=r, has exact rank

    rank J_r = sum_{j=0}^{min(w*r,m)} binom(m,j),   0<=r<=D_m,w.

Each column is a product of <=r degree-w clause indicators, so is in the claimed polynomial space. Conversely any monomial of degree <=wr is partitioned into <=r disjoint variable blocks of size <=w, giving precisely such a product; empty block product supplies the constant. Independence of distinct squarefree Boolean monomials proves equality. For w>=2 and r=ceil(m/w), r<=D_m,w and rank=2^m. This is an exact, exponentially large, phase-sensitive geometric invariant for the actual NP-complete width-three family.

### G15b — decisive same-family negative control: width two

The complete width-two selector function also has full algebraic degree, 2^m maximal flats, exponentially large DNF, and cumulative signed boundary jet rank 2^m at r=ceil(m/2). Yet 2-SAT is decidable in polynomial time. Explicit unrestricted circuit: build the implication graph on 2m literals from selected clauses, with a unit clause giving the edge from its negation to itself; compute reachability by the Boolean Floyd-Warshall recurrence, using O(m^3) bounded-fanin Boolean gates (OR expressed using AND/XOR); reject iff some variable and its negation are mutually reachable. Thus MC(F_m,2)=O(m^3) on N_m,2=2m^2 inputs, with lower bound N_m,2-1. This is a direct counterexample to treating exponential labelled jet rank, full degree, DNF count, or their conjunction as an unrestricted superpolynomial resource bound. Even a phase-sensitive reconstruction of the truth table is not in itself a resource obstruction. The remaining invariant must distinguish the width-three interaction and satisfy a uniform per-gate charge. The derivative order grows with m in this example; no claim about every fixed-order invariant or every weighted jet potential.

### G15c — deterministic section equivalence, not merely uniqueness of lift

For selector F_m, the polynomial-size existential quadratic lift of G13 is exact, but a deterministic triangular circuit deciding F need not explicitly choose a satisfying assignment. The existing SAT decision-to-witness self-reduction resolves this gap with only polynomial overhead: query F on the input, then for each assignment coordinate test the input plus all previously chosen unit clauses and a proposed unit literal (set its selector bit to 1 by Boolean OR). If satisfiable choose that value, otherwise choose the other; induction preserves at least one assignment, and the final assignment is satisfying. Return a default vector on unsatisfiable inputs. At most m+1 decision calls plus polynomial wiring and control. Conversely any total candidate section that returns a satisfying assignment whenever one exists can be checked by O(N_m) clause operations; no assignment passes on unsatisfiable inputs. Hence existence of a polynomial-time decider is equivalent to existence of a polynomial-time verified total section, and the same equivalence holds for polynomial circuit-family size. The section may be the lexicographically first witness, but canonical minimization is unnecessary for the converse. This is a classical constructive reduction on the original selector carrier, reusing #1006 SATDecisionToWitnessSelfReductionExact and BooleanFormulaSATSelfReductionExact, #1040 terminal, #1129 machine costs, #1474/#1502 encoding; native source attachment still separate. A lower bound on one chosen section alone does not imply decision hardness unless every efficient decider would yield that section (lex-first is such a section by the stated algorithm). No lower bound on any section established here.

### Local exact execution receipt, reproducible in Python, no CI/kernel

Newly executed integer bitset/GF(2) tests: cover parity for widths 1,2,3 and m=1..4 (197,436 subsets of assignments); direct selector truth table parity for N<=16 (860 selector inputs, counted across families); width-three incidence rank m=1..8 (8 ranks), pair differences (43,435 pairs), local one-bit boundary (216,116 checks), sharp escape witnesses (8). Cumulative product-span rank for widths 1..3,m=1..8 through ceil(m/w) (71 rank comparisons). Direct mixed derivative checks at every maximal selector for widths 1..3,m=1..4 and orders 0..min(D,2) (46,486). All passed. Example cover counts at m=4: 63,775 / 27,535 / 743 for w=1,2,3, all odd. These are checks of formulas, not asymptotic evidence independent of the proofs. Reproducer:

```python
from itertools import combinations
from math import comb

def masks(m,w):
    C=[(I,p) for j in range(1,min(w,m)+1)
       for I in combinations(range(m),j) for p in range(1<<j)]
    Z=[sum(1<<i for i,(I,p) in enumerate(C)
           if sum((x>>j&1)<<k for k,j in enumerate(I))==p)
       for x in range(1<<m)]
    return C,Z

def basis(xs):
    B={}
    for x in xs:
        while x:
            p=x.bit_length()-1
            if p not in B:
                B[p]=x
                break
            x^=B[p]
    return list(B.values())

cover_checks=cube_checks=pairs=boundary_checks=ranks=0
for m in range(1,5):
    for w in (1,2,3):
        C,Z=masks(m,w); N=len(C); full=(1<<N)-1
        covers=[0]*(1<<len(Z))
        for S in range(1,len(covers)):
            lo=S&-S
            covers[S]=covers[S^lo]|Z[lo.bit_length()-1]
        assert covers.count(full)%2==1
        cover_checks+=len(covers)
        if N<=16:
            assert sum(any(not s&z for z in Z) for s in range(1<<N))%2==1
            cube_checks+=1<<N
for m in range(1,9):
    C,Z=masks(m,3); N=len(C); full=(1<<N)-1
    def b(t):
        return sum(comb(t,j) for j in range(1,min(3,t)+1))
    D=b(m)-b(m-1)
    assert len(basis(Z))==b(m)+1; ranks+=1
    for x,y in combinations(range(1<<m),2):
        a=(Z[y]&~Z[x]).bit_count()
        assert a==b(m)-b(m-(x^y).bit_count()) and a>=D
        pairs+=1
    for z in Z:
        s=full^z
        for i in range(N):
            assert any(not (s^(1<<i))&y for y in Z)==(not(z>>i&1))
            boundary_checks+=1
    remove=Z[1]&~Z[0]; A=Z[0]&~Z[1]; add=A&-A
    s=((full^Z[0])&~remove)|add
    assert remove.bit_count()==D and s&Z[0] and not s&Z[1]
assert (cover_checks,cube_checks,pairs,boundary_checks,ranks)==(197436,860,43435,216116,8)
jet_checks=filtration_checks=0
for m in range(1,9):
    for w in (1,2,3):
        C,Z=masks(m,w); N=len(C); one=(1<<(1<<m))-1
        cols=basis([one]+[sum(((z>>i)&1)<<x for x,z in enumerate(Z)) for i in range(N)])
        Q=[one]
        for r in range(1,(m+w-1)//w+1):
            Q=basis(a&b for a in Q for b in cols)
            assert len(Q)==sum(comb(m,j) for j in range(min(w*r,m)+1))
            filtration_checks+=1
        D=sum(comb(m-1,j) for j in range(min(w-1,m-1)+1))
        if m<=4:
            full=(1<<N)-1
            for z in Z:
                s=full^z
                for r in range(min(D,2)+1):
                    for I in combinations(range(N),r):
                        t=sum(1<<i for i in I); v=0; J=t
                        while True:
                            v^=any(not (s^J)&y for y in Z)
                            if J==0:break
                            J=(J-1)&t
                        assert v==int(t&z==t)
                        jet_checks+=1
assert (jet_checks,filtration_checks)==(46486,71)
```

### Active Aristotle frontier (P0-C/D, no extra mandatory phase)

| ID | Exact deliverable | Status / owner |
|---|---|---|
| G14a | selectorFullDegreeByTranslationParity | mathematical proof, exact checks; G11 orbit geometry, G13 selector, G8b degree; yields MC>=N-1 |
| G14b | maximalSelectorIsolationRadiusAndSharpEscape | mathematical proof and checks; G13 overlap; chord source |
| G15a | signedBoundaryJetRankExact | mathematical proof and checks; labelled relative-line donor #1549/#120, G13 |
| G15b | widthTwoFullJetPolynomialShortcut | mathematical proof, 2-SAT implication graph; refutes uncharged exponential-rank inference |
| G15c | selectorDecisionToVerifiedSectionPolynomialIff | classical constructive argument; existing #1006/#1040/#1129/#1474/#1502, source weld remains |
| G12a/G6a/N4 | serialTargetShiftBound | OPEN: a width-three-sensitive invariant with unit progress for every legal product flag, or a direct uniform lower bound |
| G12b/G6b | selectorGoalSeparation | OPEN: beyond degree and boundary jet rank, same target and legal chords |
| G12c/G6c/N5 | selectorSuperpolynomialGrowth | OPEN: superpolynomial in N_m,3, not merely 2^m witness or jet count |
| N6 | originalClayTransport | #1040 conditional terminal; actual universal SAT failure unpaid |

Highest-alpha next action: back-solve the width-three-specific obstruction from the deterministic section (or decision) on the full original selector carrier, not just its isolated maximal-selector neighbourhood. The new exact jet calculation gives a discriminator and the width-two shortcut disproves the proposed simple charge; use Aristotle #607/#678 collision/reopening, #123 costed lowering, #1006 FactorsThrough, #1291 indexed joint geometry and #1546 shared computation. Test any next target-sensitive measure against width-one and width-two families before spending time on more finite flag census. Direct uniform N4/N5 remains an OR route, and is weaker than unrestricted circuit separation. Do not claim that phase-sensitive data alone evade natural-proofs or other complexity barriers. No unconditional separation or native kernel verification claimed.


## 14. P0-G16–G19 — binary/ternary constraint geometry, monotone separation and propagation lift obstruction (2026-11-24)

**Controlling endpoint: literal Clay P vs NP.** Continue P0-C/D, no additional mandatory research phase. Reuse the two supplied inspiration documents (G14/G15 and the binary/ternary arithmetic donor #1549/#120); no Langlands or Monster closure is needed. G14's unrestricted MC(F_m,3)>=N_m,3-1 is stronger than the donor's stabilizer bound ceil(N_m,3/2). Retain both with their scope. Field, carrier cardinality, clause width, relation arity and circuit basis are distinct.

Source owners reopened on default branch this turn:
- DASHI/Codec/BalancedTritBitFibre.agda, blob 9fa72fc85938f78aa64cc53443a06ada3824280a: encodeFibre/decodeFibre, decode-encode, encode-decode, supportBit, OptionalSignBit, encode-commutes-involution. Zero has absent sign; signed nonzero fibres remain distinct.
- DASHI/ComputerScience/BinaryBalancedTernarySubcarrierExact.agda, blob c9ade4f43191c2790f62230c805e95d29e2e36e6: embedBit false=-1, true=+1, binaryTernaryRoundTrip, centreIsUnusedByBinaryEmbedding, complement as antipode.
- DASHI/Foundations/Base369BinaryTernaryRefinement.agda, blob 6345afd94fda8b8b5a45f635bf3fba6486c1998d: Resolution23, binary-ternary-refinement-commutes, circlePhaseRefinementDiamond. Refinement index diamond, not a cost-preserving reduction of arbitrary constraints.
- DASHI/Mathematics/Complexity/Karp21CliqueSetPackingExact.agda, blob ddffdd6e4276c263f3e96be129598c502005a3b2: cliqueToPacking, packingToClique. Witness equivalence, not an existing monotone selector compiler; supply actual monotone projection below.
- Earlier G13/G14/G15 and #1040 terminal, #1129 costed machine, #1006 SAT self-reduction and FactorsThrough, #1474/#1502 Karp/Cook-Levin, #123 JMD lowering, #1291 indexed geometry, #607/#678 Aristotle and #1546 sharing remain controlling donors. Previous heads ca442a027f3d / cb77c205529e, common blob 75267c821aa140e8f0dbb7e28ea9d068c3888e05.

### G16a — pairwise reconstruction equals median closure (known bijunctive characterization)

For m>=1 and R subset {0,1}^m, H2(R) is the intersection of inverse images of all nonempty unary and binary projections of R. Every binary Boolean relation is coordinatewise majority-closed: if a forbidden pair were the median of three allowed pairs, at least two rows match its first coordinate and two match its second, so one row matches both. Thus H2 is median-closed and contains R. Conversely if S is median-closed and a point has every unary/binary projection in S, induct on the number k of coordinates matched by a point of S. Base k<=2 holds by hypothesis. For k>=3 take three witnesses agreeing on the desired k coordinates except possibly three different single coordinates, one omitted per witness. Their median agrees on all k. Apply to S=median closure of R; its unary/binary projections equal those of R by binary closure. Hence H2(R)=medianClosure(R). Equivalently a Boolean relation is 2-CNF definable iff median-closed, because each excluded unary/binary pattern contributes a clause of width at most two. Empty relation included by contradictory units. This is classical Schaefer bijunctivity (https://doi.org/10.1145/800133.804350), not a claimed new dichotomy.

For a 3-clause excluding 000, all pair projections are full and H2(R) is the full cube; 100,010,001 are models with median 000. Literal complement transports all eight polarities. More generally, three satisfying assignments of a 3-CNF violate a clause in their coordinatewise median iff the three rows of truth values of that clause's literals form a 3x3 permutation matrix: every row must have at least one true literal; median failure means every column has at most one; hence exactly one per row and column. This identifies the minimal local ternary defect. It does not prove a global resource lower bound; Horn 3-CNF and ternary parity equations are tractable by other algebraic closures.

### G16b — actual support/sign witness bridge and projection no-go

For each active clause of width two use a Boolean antipodal witness choosing its satisfied literal; width three uses an actual balanced trit t in {-1,0,+1} labelling its three literal positions. Require t=label_i implies literal_i(x)=1 for each i. Then there exists a local witness iff clause is true. Inactive selectors may have arbitrary witness; for fixed input select only active clauses. For width two the implication on a witness bit and assignment bit is a 2-clause. For width three these constraints are binary RELATIONS on a mixed 3-element/2-element domain. The problem is still NP-complete: pairwise arity is not Boolean domain size. Encode the trit by the existing support/sign fibre, for example fixed two-bit codes zero=(0,0), positive=(1,0), negative=(1,1); the sign bit in the zero code is padding, not a sign of zero. The three-way local witness survives losslessly. There is no existential 2-CNF formula with original assignment bits as visible coordinates whose projection is this single 3-clause, for any number of Boolean auxiliaries or any encoding of the witness: existential projection preserves median closure (choose three lifts and take their median), contradiction to G16a. This is a genuine representation-transport no-go in the specified language, not a prohibition of polynomial algorithmic reductions to arbitrary Boolean circuits or a proof of P!=NP. A 3-ary witness domain and a width-three Boolean clause are not the same object.

### G17 — genuine superpolynomial bound on monotone selector computation

Use complementary selector bits t_C=1+s_C (one means clause absent), and G_m,w(t)=F_m,w(1+t), a monotone increasing function. Equivalently U_m,w(s)=1+F_m,w(s) is monotone unsatisfiability. AND/OR circuits for the two functions have equal complexity by swapping AND/OR and constants under Boolean duality.

Width two: build literal implication graph with edge bits given by selected clauses; a unit gives the implication not l -> l. Reachability on 2m vertices can be computed by Boolean Floyd-Warshall, R^h_ij=R^(h-1)_ij OR (R^(h-1)_ih AND R^(h-1)_hj). Unsatisfiability iff any variable and its negation are mutually reachable. This gives an O(m^3) monotone AND/OR circuit for U_m,2, and by duality for G_m,2. It does not claim that plain unit propagation on an arbitrary 2-CNF is complete.

Width three: explicit monotone projection from CLIQUE(n,k) to G_M,3. Use k slots and Boolean variables x_(i,v) for each slot and each graph vertex. Fixed clauses require exactly one vertex per slot (pairwise at-most-one, one at-least-one disjunction per slot) and different vertices in different slots. Convert each length-n positive at-least-one clause to width <=3 by the usual fresh-variable chain (a1 OR a2 OR y1), (not y1 OR a3 OR y2), ..., (not y_last OR a_(n-1) OR a_n). Existential equivalence follows by eliminating each auxiliary: exists y [(a OR y) AND (not y OR b)] iff a OR b, for disjunctions a,b. For n>=3 use n-3 fresh variables per slot, so M=k(2n-3). For each i<j and u!=v, include the 2-clause (not x_(i,u) OR not x_(j,v)) iff edge {u,v} is absent. With t-complementary selectors the fixed clauses have t=0, unused t=1, conditional nonedge clauses t=e_(u,v) (the graph edge input). Conditional clauses are distinct up to canonical order and never conflict with fixed clauses; repeated graph input wires are free fanout. Thus all target inputs are constants or unnegated graph inputs, and

    CLIQUE_n,k(e)=G_M,3(t(e)).

Both directions: a satisfying assignment chooses k distinct pairwise adjacent vertices; a clique can be ordered into the slots and all fresh chain variables chosen to satisfy fixed constraints. M=O(kn), N_M,3=Theta(M^3); no truth-table expansion, no additional circuit gate charged for the projection.

External theorem (not a new DASHI lower bound proof): Cavalar, Kumar and Rossman, Monotone Circuit Lower Bounds from Robust Sunflowers, Algorithmica, Theorem 5, https://pmc.ncbi.nlm.nih.gov/articles/PMC9705498/ : for fixed delta in (0,1/3) and k=n^(1/3-delta), monotone CLIQUE size is Omega(n^(delta^2*k/2)). Choose delta=1/12 and n along perfect fourth powers, k=n^(1/4). Restrict any monotone G_M,3 circuit by the explicit projection without increasing its gate count. Since N=N_M,3=Theta(n^(15/4)), this establishes on that subsequence

    MonotoneSize(G_M,3) >= 2^Omega(N^(1/15) log N).

This is a genuine superpolynomial lower bound on the SAME original selector family in the monotone circuit model, with standard shared DAGs and arbitrary monotone bypasses. It is imported by an explicit new projection construction here, not a new proof of the external theorem. It is NOT an unrestricted AND/XOR/NOT lower bound. In particular G14's MC>=N-1 remains the general lower bound. A monotone circuit size lower bound cannot be converted by declaring XOR free and monotone; XOR and NOT can create nonmonotone internal functions even for a monotone output.

### G18 — deterministic lift obstruction for fixed propagation-complete encodings

A useful corollary for G13/G15: let E_M(s,z) be any fixed finite CNF with auxiliaries z, where setting selected s_C=1 and leaving the remaining selectors unassigned makes E satisfiable exactly when the selected 3-CNF is satisfiable. For example E can encode the existential relation under total selector assignments; by monotonicity its existentially unassigned selectors have the same consistency property. Assume unit propagation on E under those positive partial selector assignments detects every unsatisfiable case. Let L count selector variables, auxiliary variables and clause literal occurrences, including empty clause overhead. Then simulate all unit derivations synchronously by monotone Boolean circuitry. For each literal l, d_l^0 is 1 for initially given units (positive selector l has input s_C; other literals start false unless forced by fixed units). Recur

    d_l^(r+1) = d_l^r OR OR_{K containing l} AND_{a in K minus {l}} d_(not a)^r.

Include contradiction if some clause has all its literals falsified or both l and not l are derived. Fixed empty clauses immediately trigger contradiction. This is monotone, and forward chaining of at most 2p literals (p variables) stabilizes by 2p rounds. Width may be arbitrary, using bounded-fanin gates with O(L^2) per round, O(L^3) overall. For satisfiable inputs the inference is sound; assumed completeness means output equals U_M,3. G17 implies L is superpolynomial, quantitatively at least 2^Omega(N^(1/15) log N) along the same subsequence (taking a cubic root changes only constants). This rules out polynomial-size fixed CNF encodings making unit propagation a complete decision procedure for every positive partial selector input, even with arbitrary auxiliary variables. This is the selector-specific application of established propagator/monotone circuit correspondence (Bessiere, Katsirelos, Narodytska, Walsh, IJCAI 2009, https://ijcai.org/Abstract/09/076). The proof does not require a uniform construction of E and does not apply to input-dependent preprocessing, branching, arbitrary resolution search or arbitrary nonmonotone circuit evaluation.

Width two has a polynomial propagation checker: encode the monotone reachability circuit for U_M,2 by forward Horn implications (AND: not a OR not b OR g; OR: not a OR g, not b OR g) and impose not output. When a positive partial input forces U=1, forward propagation derives output and contradiction. When U=0, choose unspecified inputs zero and assign gates actual values, yielding a satisfying checker. Thus there is a concrete polynomial vs superpolynomial separation for fixed complete propagation lifts, not a conclusion about arbitrary deterministic sections.

### G19 — chord control and remaining Clay obstruction

General monotone-to-unrestricted cost equivalence is false: bipartite perfect matching has polynomial algorithms and superpolynomial monotone circuit lower bounds (Razborov 1985; see https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/RAN/MATCHING/matching.pdf and https://eccc.weizmann.ac.il/report/2025/102/). This is the same-endpoint chord control for G17/G18. Neither median failure, ternary encoding, exponential labelled jet rank, nor monotonicity of target output implies an unrestricted lower bound. The P0 question is a width-three-specific charge on all nonmonotone triangular lifts, or a direct standard-machine proof; no generic monotonicization lemma is admissible.

Precise potential crosswalk: let U be the actual monotone unsat function and let C range over all bounded-fanin circuits, including nonmonotone. G17 gives lower bound L(N) only for circuits with AND/OR and monotone input coordinates. A sufficient but unproved target-specific transport would map every correct general C for U to a monotone circuit of size poly(N,|C|), or more weakly at most 2^o(N^(1/15) log N) for polynomial-size C along the hard subsequence. No such transport asserted. Alternative G12 route remains any noncircular serial-safe measure separating actual 3-SAT and exceeding all polynomials in N. If proving transport, ensure all arbitrary nonmonotone internal functions, XOR, NOT, sharing, input-dependent branch choices and alternate encodings are allowed; matching refutes universal monotone transport. Do not assume canonicalization solves it.

### Executed local regression

Local Python integer/bitset execution (no CI or native kernel): all 276 Boolean relations on 1–3 coordinates tested for equality of explicit median closure and pair-projection hull (4+16+256). All 192 three-clause polarity / injective two-bit trit-label encoding combinations tested for exact projection and median failure. All 220 graph instances across (n,k)=(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3) tested by evaluating every assignment of the emitted fixed and conditional 3-CNF using integer bitsets, independently comparing with enumerated vertex subsets. All 260 width-two selector inputs at m=1,2 compared between Floyd-Warshall and brute-force SAT. No native proof or asymptotic test claim. Reproducer:

```python
from itertools import combinations, permutations

def med(a,b,c):return (a&b)|(a&c)|(b&c)
checks=0
for n in (1,2,3):
    for s in range(1<<(1<<n)):
        R={x for x in range(1<<n) if s>>x&1}; H=set(R)
        while True:
            W=H|{med(a,b,c) for a,b,c in combinations(H,3)}
            if W==H:break
            H=W
        scopes=[1<<i for i in range(n)]+[(1<<i)|(1<<j) for i,j in combinations(range(n),2)]
        ps=[{a&M for a in R} for M in scopes]
        assert H=={a for a in range(1<<n) if all(a&M in p for M,p in zip(scopes,ps))}
        checks+=1
assert checks==276
checks=0
for pol in range(8):
    for enc in permutations(range(4),3):
        R={(x<<2)|enc[i] for x in range(8) for i in range(3) if ((x^pol)>>i)&1}
        assert {x>>2 for x in R}==set(range(8))-{pol}
        assert med(((pol^1)<<2)|enc[0],((pol^2)<<2)|enc[1],((pol^4)<<2)|enc[2]) not in R
        checks+=1
assert checks==192

def clique_cnf(n,k):
    fixed=[]; conditional=[]; m=k*n
    for i in range(k):
        p=[1+i*n+v for v in range(n)]
        for a,b in combinations(p,2):fixed.append((-a,-b))
        while len(p)>3:
            m+=1;fixed.append((p[0],p[1],m));p=[-m]+p[2:]
        fixed.append(tuple(p))
    for i,j in combinations(range(k),2):
        for u in range(n):
            for v in range(n):
                c=(-(1+i*n+u),-(1+j*n+v))
                if u==v:fixed.append(c)
                else:conditional.append((tuple(sorted((u,v))),c))
    return m,fixed,conditional
checks=0
for n,k in [(2,1),(2,2),(3,1),(3,2),(3,3),(4,1),(4,2),(4,3)]:
    m,fix,cond=clique_cnf(n,k);full=(1<<(1<<m))-1
    v=[sum(1<<a for a in range(1<<m) if a>>i&1) for i in range(m)]
    def mask(c):
        t=0
        for a in c:t|=v[a-1] if a>0 else full^v[-a-1]
        return t
    base=full
    for c in fix:base&=mask(c)
    edges=list(combinations(range(n),2));constraints=[full]*len(edges)
    for e,c in cond:constraints[edges.index(e)]&=mask(c)
    for z in range(1<<len(edges)):
        a=base
        for i,b in enumerate(constraints):
            if not(z>>i&1):a&=b
        expected=any(all(z>>edges.index(e)&1 for e in combinations(S,2)) for S in combinations(range(n),k))
        assert bool(a)==expected
        checks+=1
assert checks==220
checks=0
for n in (1,2):
    clauses=[tuple(2*j+((p>>i)&1) for i,j in enumerate(I)) for w in (1,2) for I in combinations(range(n),w) for p in range(1<<w)]
    for s in range(1<<len(clauses)):
        chosen=[c for i,c in enumerate(clauses) if s>>i&1]
        R=[[int(i==j) for j in range(2*n)] for i in range(2*n)]
        for c in chosen:
            a=c[0];b=c[-1];R[a^1][b]=1;R[b^1][a]=1
        for h in range(2*n):
            R=[[R[i][j] or (R[i][h] and R[h][j]) for j in range(2*n)] for i in range(2*n)]
        ans=not any(R[2*i][2*i+1] and R[2*i+1][2*i] for i in range(n))
        brute=any(all(any(((x>>(a//2))&1)==a%2 for a in c) for c in chosen) for x in range(1<<n))
        assert ans==brute;checks+=1
assert checks==260
```

### Consolidated active frontier

| ID | Exact deliverable | Status and producer/consumer |
|---|---|---|
| G16a | pairHullEqualsMedianClosure / ternaryPermutationDefect | classical proof + finite check; Schaefer, FactorsThrough; G13 joint relation |
| G16b | signedTritClauseWitnessProjection / noExistential2CNFLift | proof + finite check; actual BalancedTritBitFibre / BinaryBalancedTernarySubcarrierExact; G13 existential lift |
| G17a | widthTwoMonotoneReachability | classical constructive proof + finite check; G15b |
| G17b | cliqueMonotoneSelectorProjection / monotoneSelectorSuperpoly | explicit projection and external Theorem 5; Karp owner #1474/#1502; restricted superpoly result |
| G18 | noPolynomialFixedCompletePropagationLift | proof via monotone unrolling; Bessiere et al.; G13/G15 restricted deterministic-lift obstruction |
| G19 | unrestrictedMonotoneShortcutNoGo | known matching counterexample; chord comparator |
| G12a/G6a/N4 | unrestrictedSerialCharge / targetSpecificCostedTransport | OPEN; no generic monotonicization; all legal nonmonotone triangular gates |
| G12b/G6b | unrestrictedSelectorGoalSeparation | OPEN; G17 applies only to monotone circuits |
| G12c/G6c/N5 | unrestrictedSuperpolynomialGrowth | OPEN; or direct uniform standard-machine failure |
| N6 | originalClayTransport | #1040 conditional terminal, #1129 standard machine coverage; unconditional endpoint unpaid |

Aristotle alpha priority: we now have a superpolynomial restricted resource obstruction on the exact NP-complete family, and a sharp propagation-lift no-go. Do not spend another round on finite geometry census or prove a generic monotone normalization which matching refutes. Attack the difference between unrestricted triangular lift and complete monotone propagation on the original selector carrier: either bound all nonmonotone shortcut use by a target-specific resource inequality, or pivot to direct uniform N4/N5 with actual machine work. Preserve both OR routes; neither new native certification nor a Langlands/Monster task is needed. No unconditional P!=NP claim.


## 15. P0-G20/G21 — inhabited zero fibres, hazard geometry and quantitative nonmonotone shortcut necessity (2026-11-24)

P0 remains literal Clay P vs NP. Inputs: user-provided G16–G19 packet and R21–R25 inhabited-zero/mediator packet from Agda #1549 / Lean #120 (reported heads 679397137e12 / fa917cfc5c58 in attachment). The controlling P0 PRs were read at a33655646b92 / ae18da2457eb, common blob 13695a138f7448770397cc004da199cfab8a7ca8. No Langlands, Monster, physics or other endpoint prerequisite. Reopened source bodies on default branch:
- DASHI/Core/GovernedIndexedResidualCubeExact.agda blob 42b70ebb7376813076934f2245ce6011b76f10c8: Cube, Faces, ExactFaces, ResidualFaces, six endpoint transports. Residual witnesses are not automatically commutation proofs.
- DASHI/Foundations/BalancedTernaryAntipodalResidualCodecExact.agda blob 2a5069418e25572f04941591dbc83334862c012d: OrientationResidual27, AntipodalCode27, encode27/decode27; centre has unit ORIENTATION residual, unlike the zero-difference VALUE residual below.
- DASHI/Codec/TriadicMaskSignFactorization.agda blob db62f5518adc7fd3815c56ead5e20a8071db4b5a: FactorizedTrit, encode/decode inverse. This is a lossless trit codec, not a licence to discard source-dependent value residuals.
- G11/G13/G14/G16/G17, #1291 indexed cube, #607/#678 Aristotle, #1006 FactorsThrough and SAT self-reduction, #123 JMD lowering, #1546 sharing, #1129 standard machine, #1040 terminal, #1474/#1502 reductions remain active.

### G20a — typed zero fibre and partial information

For child feasibility a,b in {0,1}, integer d=b-a in {-1,0,1}. The fibre over d=0 has two distinct inhabitants (0,0) and (1,1); the other fibres each have one. Retain r=a on the zero fibre. Parent feasibility is |d|+(1-|d|)r. This is an exact bijective dependent codec, not the antipodal orientation codec. It grants no lower bound by counting unresolved branches: computing a,b together or computing their OR without explicitly producing them is legal.

A separate useful ternary carrier is partial Boolean information {0,?,1}, with ? denoting both possible completions, not signed difference zero or balanced arithmetic zero. Use rails (p,q) with p=1 meaning definitely true and q=1 meaning definitely false. Allowed values 0=(0,1), ?=(0,0), 1=(1,0), with (1,1) inconsistent. For AND, p=p1 AND p2, q=q1 OR q2; for OR, p=p1 OR p2, q=q1 AND q2; NOT swaps rails. These local rules are sound under every common completion, but not complete with reconvergent correlated inputs: x OR NOT x evaluates to ? for unknown x, yet every Boolean completion yields 1. Exact joint completion retains the dependency; independent rail abstraction loses it. This is the inhabited-zero/correlation version of the existing chord warning. Do not conflate the 15-state common-source difference image with the partial-information rails.

For monotone selector G=G_m,3 on absent-clause bits, its exact partial semantics on a cube [l,u] is determined by G(l),G(u) (monotonicity). Local evaluation of an arbitrary correct Boolean circuit can be strictly less informative. Hazard-free circuits for monotone functions are known to have the same minimum size as monotone circuits (Ikenmeyer et al., https://arxiv.org/abs/1711.01904 ; Jukna, Notes on Hazard-Free Circuits, https://arxiv.org/abs/2012.10976). G17 therefore already excludes polynomial-size hazard-free selector circuits. A direct one-sided proof and stronger quantitative symmetry statement follow.

### G20b — dual-rail mask transport, shared DAGs retained

Let C be an arbitrary bounded-fanin Boolean AND/OR/NOT circuit for G. Convert to De Morgan form D(p,q) with positive and negative input rails using both polarities of every intermediate gate, constant-factor overhead (at most two AND/OR gates per original binary AND/OR gate; NOT swaps rails, XOR if present first expands to constant-size AND/OR/NOT). D is monotone as a function of its 2N independent rails and D(t,1-t)=G(t). Do not unroll the DAG. Denote its gate size by s.

For a mask A subset [N], define the monotone underapproximation
    H_A(t)=D(t AND 1_A, 1_(complement A)).
Proof: set v=t AND 1_A; 1_(complement A)<=1-v, so H_A(t)<=D(v,1-v)=G(v)<=G(t). This covers all nonmonotone internal functions in C; only the masked approximation is monotone. Each H_A is obtained by wire substitution, size <=s. At A=all coordinates, H_A(t)=D(t,0), the definite-positive rail on input t_j=1 for j in support(t), ? otherwise. This rail is exactly the strong Kleene definite-true output, proved by gate induction using the two rails.

G13 gives exactly 2^m minimal true supports P_x=Z_x in the absent-clause coordinates, all of size b=sum_{j=1}^3 binom(m,j). Every true input contains one. These supports form a transitive orbit under assignment translations h in F2^m acting as clause-polarity permutations g_h. The target is invariant under those permutations, so H_A(g_h(t))<=G(t). For a hazard-free C, D(1_P,0)=1 at every minterm P (all completions true), hence D(t,0)=G(t); this is a direct no-overhead monotone transfer. Even one-sided preservation on all minterms suffices, not general three-valued exactness.

### G21a — exact width of negative evidence on minterm traces

Consider the formal DNF of D (conceptual expansion only, no runtime or storage charge assigned to C). Each trace is a pair of sets (P,Q) of positive and negative literal coordinates. At the total minterm input 1_Px, every accepting trace has positive set contained in P_x and negative set disjoint from P_x. Its positive set must equal P_x: otherwise the smaller positive support itself satisfies that same trace, contradicting minimality. Define w_C(x) as the least |Q| over accepting traces at 1_Px. This is well-defined even with arbitrary reconvergence, cancellation, shared gates and repeated literal use. A formal DNF term with contradictory literals never accepts a total input. w_C(x)=0 iff D(1_Px,0)=1, i.e. no hazard on this particular definite-true partial input. This is the pointwise form of the negation-width notion of Jukna–Lingas, Lower bounds for Boolean circuits of bounded negation width (JCSS 129, 2022), https://web.vu.lt/mif/s.jukna/papers/negwidth_abs.html . Their theorem gives a general monotone simulation from bounded worst-case width. The following proof derives a selector-specific distributional variant via transitivity; no claim of literature novelty.

Let alpha_w = fraction of the 2^m minterms with w_C(x)<=w. For each good minterm choose one trace (P_x,Q_x) of negative width <=w. Draw A by independent inclusion of each coordinate with probability p=b/(b+w) for w>=1. Probability that P_x subset A and Q_x disjoint A is p^b(1-p)^|Q_x| >= q_w=p^b(1-p)^w. On this event H_A(1_Px)=1. For w=0 set p=q_w=1. For independently uniform translation h, g_h(P_x) is uniform among all minterms. Hence for every fixed minterm, a random masked/translated H_A(g_h(t)) accepts it with probability >=alpha_w q_w.

If alpha_w>0, choose K=ceil((m ln 2+1)/(alpha_w q_w)) independent copies. Probability some minterm is missed by all copies is <=2^m exp(-K alpha_w q_w)<1. Therefore there exist K specific masks and translations such that OR of their underapproximations accepts ALL minterms and, by monotonicity, exactly computes G. Its size <=K(s+1). Denote actual monotone circuit complexity by L_m. Consequently, also trivially for alpha_w=0,

    alpha_w q_w <= (m ln 2+2)(s+1)/L_m.

Proof of constant: K<= (m ln2+1)/(alpha_w q_w)+1 <=(m ln2+2)/(alpha_w q_w). This is a global shared-circuit statement, not a sum of independently charged branch costs. Mask/translation choice is existential nonuniform; no algorithm for finding them is needed for the contradiction to a nonuniform lower bound. Orbit argument applies to actual selector minterms, not an assumed transitive orbit of arbitrary internal states.

### G21b — quantitative consequence for any putative polynomial selector circuit

G17 is based on Cavalar–Kumar–Rossman, Monotone Circuit Lower Bounds from Robust Sunflowers, Theorem 5 (verified exact statement this turn, https://pmc.ncbi.nlm.nih.gov/articles/PMC9705498/): for fixed delta in (0,1/3), k=n^(1/3-delta), monotone CLIQUE complexity Omega(n^(delta^2 k/2)). The G17 monotone projection at delta=1/12 gives L_m>=exp(c N^(1/15) ln N) for some c>0 and all sufficiently large m on the specified subsequence, N=N_m,3. This is the source of the following inequalities; not a new proof of CLIQUE hardness.

For w>=1, q_w=(b/(b+w))^b (w/(b+w))^w >= exp(-w) (w/(b+w))^w by ln(1+w/b)<=w/b. For 1<=w<=N, -ln q_w <= w(1+ln(2N)), using b<=N. Suppose s is polynomial in N. Choose a sufficiently small fixed epsilon>0 depending on c, w=floor(epsilon N^(1/15)). Then

    alpha_w <= exp(-Omega(N^(1/15) ln N)).

Thus, conditional on a polynomial-size unrestricted selector circuit existing, all but an exponentially small FRACTION of assignment-minterms require more than epsilon N^(1/15) distinct negative literal conditions in EVERY accepting formal trace. In particular the fraction of hazard-free minterm partial evaluations (w=0) is at most (m ln2+2)(s+1)/L_m. This strengthens the worst-case negation-width consequence to an almost-every-minterm requirement for the actual target. It concerns minterm traces and partial information, not the number of NOT gates, number of actual execution steps, or complexity of computing a witness. It holds on the hard subsequence. Width-two monotone reachability yields a hazard-free circuit with alpha_0=1; G15 width-two full-jet-rank control is retained.

### G21c — precise remaining unrestricted obstruction; width cannot be charged naïvely

Even a simple monotone f(t)=t_1 can be represented as t_1 AND product_{i>1}(t_i OR NOT t_i), using O(N) gates; its sole minterm trace requires N-1 distinct negative literals. More generally appending all coordinate tautologies to a correct monotone circuit for G forces w_C(x)=N-b at every minterm with only O(N) added gates. This shows that high formal width and local hazard can be created cheaply, and even if avoidable padding is removed there is no established upper bound on width for size-optimal general circuits. Do not confuse a necessary property of small circuits with a superpolynomial charge. A single unknown gate can also affect many partial inputs; counting hazards cannot be summed as execution costs. Matching remains a generic nonmonotone shortcut control.

The genuine remaining alternative: a target-specific transformation or inequality that bounds the cost of genuine correlation-dependent shortcuts (not removable tautology hazards) enough to contradict G21b, or a direct uniform-machine lower bound. For example, a polynomial-size correct general circuit admitting a polynomial-overhead alternate realization with alpha_w>=exp(-o(N^(1/15) ln N)) and w=o(N^(1/15)) would contradict G21a on the hard subsequence. This is sufficient but OPEN and must not be assumed. Full hazard-free conversion is not needed, and is generically impossible at polynomial cost. No unrestricted separation has been established.

### Executed local checks, no CI/kernel

Local Python integer and Fraction run: 4 dependent zero reconstructions; 1040 Boolean evaluations of guarded minterm circuits (m=1,2, four guard widths 0..3); 262208 mask/input underapproximation comparisons; 24 exact minimum negative-width and 24 hazard-rail checks, plus exact mask-event probability and translation orbit membership for the corresponding cases. These test local formulas, not the asymptotic distribution theorem. Guarded DNF circuits are small controls, not polynomial-size constructions for all selector lengths. Reproducer:
```python
from itertools import product, combinations
from fractions import Fraction
from random import Random

def masks(m,w):
    C=[(I,p) for j in range(1,min(w,m)+1) for I in combinations(range(m),j) for p in range(1<<j)]
    Z=[sum(1<<i for i,(I,p) in enumerate(C) if p==sum(((x>>j)&1)<<k for k,j in enumerate(I))) for x in range(1<<m)]
    return C,Z
for a,b in product((0,1),repeat=2):
    d=b-a;r=a if d==0 else 0
    assert abs(d)+(1-abs(d))*r==a|b
def terms(Z,N,style):
    rng=Random(4387+style);out=[]
    for P in Z:
        outside=[i for i in range(N) if not(P>>i&1)]
        Q=sum(1<<i for i in rng.sample(outside,min(len(outside),style)))
        a=Q
        while True:
            out.append((P|a,Q^a))
            if a==0:break
            a=(a-1)&Q
    return out
def ev(T,P,Q):return any(not(A&~P or B&~Q) for A,B in T)
def complete(Z,t):return any(not(P&~t) for P in Z)
checks=maskchecks=hazards=widthchecks=0
for m in (1,2):
    C,Z=masks(m,3);N=len(C);U=(1<<N)-1
    for style in (0,1,2,3):
        T=terms(Z,N,style)
        for t in range(1<<N):
            assert ev(T,t,U^t)==complete(Z,t);checks+=1
            for A in range(1<<N):
                assert not ev(T,t&A,U^A) or complete(Z,t);maskchecks+=1
        for P in Z:
            w=min(B.bit_count() for A,B in T if A==P and not B&P)
            assert w==min(style,N-P.bit_count());widthchecks+=1
            assert ev(T,P,0)==(w==0);hazards+=1
            if w:
                b=P.bit_count();p=Fraction(b,b+w)
                W=next(B for A,B in T if A==P and B.bit_count()==w and not B&P)
                prob=sum(p**a.bit_count()*(1-p)**(N-a.bit_count()) for a in range(1<<N) if P&a==P and not(a&W))
                assert prob==p**b*(1-p)**w
            for h in range(1<<m):
                perm=[C.index((I,pol^sum(((h>>j)&1)<<k for k,j in enumerate(I)))) for I,pol in C]
                assert sum(((P>>i)&1)<<j for i,j in enumerate(perm)) in Z
assert (checks,maskchecks,hazards,widthchecks)==(1040,262208,24,24)
```

### Updated active P0-C/D ledger

| ID | Exact deliverable | Status / producer and consumer |
|---|---|---|
| G20a | dependentZeroFeasibilityCodec / partialRailSoundness | derived and typed; #1291, R23/R24, FactorsThrough; G15 section consumer |
| G20b | maskedDualRailMonotoneUnderapprox / mintermHazardFreeTransport | derived, local exact tests; hazard-free theory, G17 |
| G21a | mintermNegativeWidthOrbitCover | derived by probabilistic cover; G11/G13 minterms, G17, Jukna–Lingas bounded width |
| G21b | smallCircuitAlmostEveryMintermNeedsNegativeEvidence | conditional theorem on small circuit, quantitative; G17 and G21a; NOT a separation |
| G21c | cheapNegativeWidthPaddingCounterexample | derived; #1546 sharing and chord control |
| G12a/G6a/N4 | unrestrictedSerialCharge / genuineCorrelationShortcutBound | OPEN; all legal arbitrary triangular gates, not just local uncertainty |
| G12b/G6b | selectorGoalSeparationBeyondMonotone | OPEN; actual original selector semantics |
| G12c/G6c/N5 | unrestrictedSuperpolynomialGrowth | OPEN; alternative direct uniform machine route |
| N6 | originalClayTransport | #1040 conditional terminal, #1129 coverage; unconditional endpoint unpaid |

Next Aristotle BIDI action: study unavoidable correlation dependencies of accepting traces across the actual width-three clause-overlap geometry. Reverse from G21a's explicit sufficient threshold, seek a target-specific low-width realization or direct cost obstruction for the necessary widespread negative evidence. Do not assume negative width, local unknowns, phase defects, cube flatness, or branch count charge time. Use exact minterm orbits only for sound cover/transport, no forced symmetric intermediate states. Keep direct uniform N4/N5 in parallel, and distinguish this stronger nonuniform route. No new infrastructure/certification prerequisite and no P!=NP claim.


## 16. P0-G22–G24 — same-object clause projectors, compressed CLIQUE projection and transversal-width obstruction (2026-11-24)

P0 remains literal Clay P vs NP; no Monster or Langlands endpoint work. User-provided #1545 character-projector construction motivates extracting components from the original carrier before classifying a realization. Attached #1549/#120 R28–R33 demonstrates positive fixed-type representation support transport and genuine quotient NOT; retain both and do not assume monotone normalization. G20/G21 remains controlling. Previous P0 heads e8afe2cba4e3 / 05642355ac3e, common blob 2fe3215cc3fc71bbeb662b30bc4ce735d7dbe716. Existing producers: G13 original selector, G17 monotone projection, G21 mask cover, #1291 indexed overlaps, #607/#678 Aristotle, #123 JMD lowering, #1546 shared DAG, #1006 FactorsThrough/self-reduction, #1129 machine coverage, #1040 terminal, #1474/#1502 reductions. Reopened DASHI/Mathematics/Complexity/Karp21NativeBinaryAdderWidthBoundExact.agda (blob 4016924f3bfc88bf850410e983a74bea9e996088, actual addCarry/addBits width bound; not a population-counter compiler), DASHI/Core/ConsumerFibreRepairExact.agda (blob 5bab8f89861559c14f3877acd5e11424b21a6a6d, refinementRepairSeparatesWitness and factorizationRepairSeparatesWitness; necessary not sufficient). Existing Karp21CliqueVertexCoverExact and SATDecisionToWitnessSelfReductionExact were located. Reuse rather than claiming native source weld already paid.

### G22 — linear-variable monotone CLIQUE projection

For graph on n vertices use one chosen-bit x_v per vertex. Fixed constraints require sum x_v >= k. Each absent edge {u,v} enables the binary clause (not x_u OR not x_v). Thus satisfying assignment selects a clique of size >=k, and a k-clique supplies an assignment. Construct the fixed threshold circuit by a balanced tree of ripple additions, padding n to next power of two if needed with zero bits; at level j add j-bit operands in O(j) gates, at most O(n/2^j) adders. Total O(n sum j/2^j)=O(n), then O(log n) comparison to the fixed integer k. For n power of two the first bit uses two half-adder gates and each further bit uses at most five full-adder gates (h=a XOR b, sum=h XOR carry, next=(a AND b) OR (h AND carry)); at most 5j-3 per addition. Encode every binary gate by four clauses forbidding its wrong output truth triples, with a distinct fresh output variable. Unit clause requires the threshold output. Unique auxiliary values follow by topological induction; fixed gate clauses width <=3 and contain fresh outputs, so do not overlap the conditional nonedge binary clauses. For n power of two and k power of two, the comparator is OR of sum bits at positions >= log2 k. General k comparison also has O(log n) size. Let M=n+number of auxiliary variables, hence M=Theta(n), and N=N_M,3=Theta(n^3). In absent-clause selectors t_C: fixed clauses t=0, unused clauses t=1, nonedge clauses t=e_uv. This is an exact monotone projection CLIQUE_n,k(e)=G_M,3(t(e)), including arbitrary shared DAGs; no gate charged for projection.

External CKR Theorem 5 verified (https://pmc.ncbi.nlm.nih.gov/articles/PMC9705498/): for fixed delta in (0,1/3) and k=n^(1/3-delta), monotone CLIQUE complexity Omega(n^(delta^2 k/2)). Use rational delta and appropriate powers of n to ensure integral k; for arbitrary desired exponent below 1/9 choose rational delta sufficiently small. Therefore L_M >= exp(Omega(N^(1/9-delta/3) ln N)) along the resulting subsequence. For delta=1/12 choose n=16^j, k=2^j, improving G17's exponent 1/15 to 1/12. This strengthens G18 propagation and R32 fixed-type positive support bounds through their existing polynomial overheads. For each fixed epsilon>0, the lower bound with exponent 1/9-epsilon follows on a suitable subsequence (for epsilon>=1/9 the statement is weaker). This is NOT a new external clique lower bound or unrestricted SAT lower bound.

### G23 — exact original-coordinate mask and transversal

Use G13 clause labels (I_C,p_C), where p_C is its falsifying assignment pattern on I_C, 1<=|I_C|<=3. For minterm P_x=Z_x define D_C(x)={i in I_C : x_i differs from p_C,i}. Thus C in P_x iff D_C(x) empty; every negative literal Q on an accepting formal trace has D_C(x) nonempty. For a partial assignment (T,z) define actual fibre X(T,z)={y:y|T=z} and A(T,z)=union_{y in X(T,z)} P_y, a subset of original selector coordinates. Then P_x subset A(T,x|T) and

    C not in A(T,x|T) iff T intersects D_C(x).

Proof: a clause falsifying pattern extends the specified partial assignment iff they agree on the intersection of scopes. This is exact projection from the original object, not independent synthetic states. Retain literal polarity, actual scope and shared source x. Repeated clauses with identical mismatch sets impose the same hit requirement; no independent charge. The empty mismatch set is the actual positive minterm coordinate, not a negative witness.

For negative set Q of an accepting trace let tau_x(Q) be the minimum |T| hitting all D_C(x), including zero for empty Q. Then tau<=min(m,|Q|). Any such T produces a G21 mask that admits the entire accepting trace: all its positive coordinates equal P_x by G21, and all Q are outside A. Conversely every mask from a fibre containing x that admits the trace must hit every mismatch set. Thus this minimum is exact within the source-coordinate fibre mask class. Define geometric width as minimum tau_x(Q) over accepting traces at P_x. No need to calculate the trace DNF or solve a hitting-set instance as part of the original circuit.

### G24 — distributional transversal-width inequality

For 0<=h<=m let beta_h be fraction of minterms whose geometric width <=h. There are K_h=2^h binom(m,h) partial assignments of size h. For each good x one of these masks works, because a hitting set of size <=h can be extended to h coordinates and still hits every mismatch. With D the dual-rail circuit of G21 (size s), each H_A(t)=D(t AND 1_A,1_(A^c)) is a monotone underapproximation of G. Sample (T,z) uniformly from K_h masks, and independently translate the input by an assignment translation h0 in F2^m inducing the actual clause polarity permutation. For any given minterm, probability of acceptance >=beta_h/K_h. The G21 union bound over 2^m minterms, followed by OR of at most ceil((m ln2+1)K_h/beta_h) masked/translated circuits, yields

    beta_h <= (m ln2+2)(s+1) K_h / L_m.

This also holds for beta_h=0. Shared DAGs remain within each copy; no claim that copies must be independently paid by original C. Since K_h <= (2em/h)^h for h>=1, and G22 gives L_m>=exp(c N^(1/12) ln N) on its delta=1/12 subsequence, polynomial s implies beta_floor(epsilon N^(1/12)) <= exp(-Omega(N^(1/12) ln N)) for sufficiently small fixed epsilon>0. In particular almost every minterm of a putative polynomial circuit has EVERY accepting trace needing a transversal of more than epsilon N^(1/12) original variables. Same result with any fixed exponent 1/9-delta/3 on its G22 subsequence. This is stronger than G21's literal-count necessity because beta_h >= alpha_h at the same threshold, and because G22 strengthens L_m. No claim about efficient trace extraction.

Let nu_x(Q) be maximum number of pairwise disjoint mismatch sets from Q. Then nu<=tau<=3nu: a maximum disjoint family is maximal, its union hits every edge, each edge has size <=3. Thus for almost every minterm of any putative polynomial circuit EVERY accepting trace contains more than h/3 pairwise disjoint nonempty mismatch sets (their full clause scopes may still overlap). This is a true independence property of original variable mismatches, not independence of circuit resources. It does not prove those mismatches require independently paid gates. G21 tautology-padding control persists: append all input tautologies to a correct circuit; for each minterm this forces all outside-P negative literals in every accepting trace, including the opposite unit clauses with singleton mismatch sets on all m variables. Then tau=nu=m, at only O(N) extra gates. Even stripping this explicit padding is not an established general low-transversal realization. Width-two polynomial monotone circuit has tau=0. Positive representation model still inherits G22; quotient NOT escapes. Do not assert that symmetry, minterm identity or exact geometric width makes the required resource inequality automatic.

### Executed local regression (Python integer arithmetic, no CI/kernel)

Balanced adder + fixed gate CNF: all 1080 assignments across n=2,4,8 and all powers-of-two thresholds checked against integer popcount; fixed gate truth clauses and no conditional/fixed overlap checked. 196 graph/threshold instances at n=2,4 compared emitted CNF under uniquely extended chosen-bit assignments against explicit k-clique enumeration. 18,184 fibre-mask coordinate comparisons for m=1..4, every x,T, every clause. 8,038 transversal/matching inequalities for families of up to three distinct nonempty mismatch sets on the same carriers. General results follow from proofs, not finite extrapolation. Reproducer:

```python
from itertools import combinations,product

def compile_count(n,k):
    gates=[]; clauses=[]
    def gate(op,a,b):
        y=n+len(gates)+1;gates.append((op,a,b,y))
        for x,z in product((0,1),repeat=2):
            v={'xor':x^z,'and':x&z,'or':x|z}[op]
            clauses.append(tuple(-i if bit else i for i,bit in zip((a,b,y),(x,z,1-v))))
        return y
    level=[[i+1] for i in range(n)]
    while len(level)>1:
        nxt=[]
        for a,b in zip(level[::2],level[1::2]):
            assert len(a)==len(b)
            s=[gate('xor',a[0],b[0])];c=gate('and',a[0],b[0])
            for u,v in zip(a[1:],b[1:]):
                h=gate('xor',u,v);s.append(gate('xor',h,c));c=gate('or',gate('and',u,v),gate('and',h,c))
            nxt.append(s+[c])
        level=nxt
    assert k and k&(k-1)==0
    bits=level[0][k.bit_length()-1:];y=bits[0]
    for b in bits[1:]:y=gate('or',y,b)
    clauses.append((y,));return gates,clauses,y
def evaluate(n,gates,x):
    a=[None]+[(x>>i)&1 for i in range(n)]
    for op,u,v,y in gates:
        assert len(a)==y
        p,q=a[u],a[v];a.append({'xor':p^q,'and':p&q,'or':p|q}[op])
    return a
def sat(c,a):return any(a[abs(i)]==int(i>0) for i in c)
count=graphchecks=0
for n in (2,4,8):
  for k in [1<<i for i in range(n.bit_length())]:
    g,c,y=compile_count(n,k); assert n+len(g)<=12*n
    edges=list(combinations(range(n),2)); fixed={tuple(sorted(z)) for z in c}; conditional={tuple(sorted((-i-1,-j-1))) for i,j in edges};assert not fixed&conditional
    a=[evaluate(n,g,x) for x in range(1<<n)]
    for x,v in enumerate(a):
        assert all(sat(z,v) for z in c[:-1]); assert bool(v[y])==(x.bit_count()>=k);count+=1
    if n<=4:
        for E in range(1<<len(edges)):
            formula=c+[(-i-1,-j-1) for h,(i,j) in enumerate(edges) if not E>>h&1]
            actual=any(all(sat(z,v) for z in formula) for v in a)
            expected=any(all(E>>edges.index(e)&1 for e in combinations(S,2)) for S in combinations(range(n),k))
            assert actual==expected;graphchecks+=1
assert (count,graphchecks)==(1080,196)
maskchecks=transchecks=0
for m in range(1,5):
    C=[(I,p) for w in range(1,min(3,m)+1) for I in combinations(range(m),w) for p in range(1<<w)]
    def mm(x,I,p):return sum(1<<j for i,j in enumerate(I) if (x>>j&1)!=(p>>i&1))
    Z=[sum(1<<i for i,(I,p) in enumerate(C) if mm(x,I,p)==0) for x in range(1<<m)]
    for x in range(1<<m):
      dif=[mm(x,I,p) for I,p in C]
      for T in range(1<<m):
        A=0
        for y in range(1<<m):
            if (y^x)&T==0:A|=Z[y]
        assert A&Z[x]==Z[x]
        for i,d in enumerate(dif):
            assert bool(A>>i&1)==(d&T==0);maskchecks+=1
      D=sorted(set(dif)-{0})
      for Q in [(d,) for d in D]+list(combinations(D,2))+list(combinations(D,3)):
        tau=min(T.bit_count() for T in range(1<<m) if all(T&d for d in Q))
        nu=max(len(S) for l in range(len(Q)+1) for S in combinations(Q,l) if all(not a&b for a,b in combinations(S,2)))
        assert nu<=tau<=3*nu
        transchecks+=1
assert (maskchecks,transchecks)==(18184,8038)
```

### Active P0-C/D frontier (no new mandatory phase)

| Gate | Deliverable | Status |
|---|---|---|
| G22a | balancedCountThresholdCNFLinearVariables / cliqueMonotoneProjectionLinearVariables | derived and tested; G17, Karp native adder donor; native source attachment open |
| G22b | strengthenedSelectorMonotoneLowerBound | external CKR transfer with new projection; restricted model |
| G23 | originalAssignmentFibreMaskIff / traceTransversalExact | derived and tested; G13/G21, #1291, FactorsThrough |
| G24a | mintermTransversalOrbitCover | derived by probabilistic cover |
| G24b | almostEveryMintermDisjointMismatchNecessity | derived conditional on small unrestricted circuits; not a size lower bound |
| G24c | transversalPaddingNoGo | derived; actual shared-resource overlap unpaid |
| G12a/G6a/N4 | genuineCorrelationShortcutBound | OPEN: charge the necessary disjoint mismatch information to actual shared gates, or find a same-object low-transversal equivalent realization at controlled cost, or direct uniform lower bound |
| G12b/G6b | unrestrictedSelectorGoalSeparation | OPEN |
| G12c/G6c/N5 | unrestrictedSuperpolynomialGrowth | OPEN |
| N6 | originalClayTransport | #1040 conditional consumer; unconditional endpoint unpaid |

Aristotle BIDI: the explicit sufficient threshold is a correct polynomial-size alternate realization with beta_h>=exp(-o(N^(1/12) ln N)) and h=o(N^(1/12)), which would contradict G24 on the G22 subsequence. Do not assume this exists; generic monotonicization is false. Need an actual resource inequality that survives quotient/negation, sharing, bypass and recomputation. Prioritize proving or disproving such a target-specific transport and keep the direct uniform N4/N5 route active. A large transversal alone is not a resource lower bound; no further finite census or generic certification prerequisite. No P!=NP claim.


## 17. P0-G25–G27 — actual limited negation, shared global inversion and exact minterm-layer obstruction (2026-11-24)

Controlling endpoint remains Clay P vs NP, P0-C/D. User continuation from G22–G24 (heads 3245b317cb3f / bf7785458979, common blob f5dc95814f0c6d6cc1136889a87eb12f36ed3331, both read live). This packet attacks the gap between geometric mismatch independence and actual paid nonmonotone operations. No external programme or certification prerequisite. Reuse G13/G14/G17/G20–G24, #1291 indexed residuals, #1546 shared intermediates, #123 JMD lowering, #1006 FactorsThrough/self-reduction, #1129 standard-machine coverage, #1040 terminal, #1474/#1502 encoding, #607/#678 Aristotle. G22's compressed threshold circuit and actual Karp adder donor are relevant; do not count abstract term expansions as gates.

### G25 — transport a genuinely nonmonotone restricted-model lower bound

Amano and Maruoka, SIAM J. Comput. 35(1), 201–216 (2005), DOI 10.1137/S0097539701396959, https://epubs.siam.org/doi/10.1137/S0097539701396959 (publisher abstract inspected): for their specified growing clique size k=(log n)^(3 sqrt(log n)), circuits on n-vertex graphs with at most floor((1/6) log log n) NOT gates require at least 2^((1/5)(log n)^sqrt(log n)) gates (use the theorem's integer conventions and sufficiently large n). This is an established external result, not a new proof here. G22 works for arbitrary k<=n, using O(log n) comparison with the fixed threshold (not just power-of-two k). Its projection substitutes only constants or unnegated edge bits into G_M,3; hence neither total gate count nor number of NOT gates increases. With M=Theta(n), N=Theta(n^3), the same lower bound transfers to selector circuits along the resulting lengths whenever their NOT budget is <= floor((1/6) log_2 log_2 n), equivalently a sufficient asymptotic budget (1/6) log_2 log_2 N-O(1). Superpolynomial size follows since (log n)^sqrt(log n) grows faster than log N. This extends G22's monotone model to genuine but limited nonmonotonicity. Does not apply to free XOR or arbitrary nonmonotone gates without counting their basis expansion. G14 remains the unrestricted MC lower bound N-1. G24 remains a conditional geometric statement.

### G26 — explicit shared logarithmic inversion mechanism (classical Markov–Fischer scope)

Every general AND/OR/NOT circuit with N input bits and size S can be transformed into a circuit of size O(S+N^3) with <=ceil(log_2(N+1)) actual NOT gates. This classical polynomial-overhead phenomenon is known as Fischer's theorem (see Jukna, Boolean Function Complexity, section 10.4, https://web.vu.lt/mif/s.jukna/boolean/bool-V7.pdf, search excerpt inspected). The following explicit elementary construction is useful as a same-object shared-resource counterexample, not claimed novel.

Use input bits t_i and weight w=sum t_i. For any input list, all monotone threshold wires T_k=[sum>=k] can be computed by triangular dynamic programming T_{j,k}=T_{j-1,k} OR (t_j AND T_{j-1,k-1}), constants T_{j,0}=1, T_{j,k}=0 for k>j. All thresholds for full list cost O(N^2). Let ell=ceil(log_2(N+1)) and z_j=1-bit_j(w). Compute z_j in descending j. For each possible high prefix H (a multiple of 2^(j+1) not exceeding N), include the monotone term

    T_(H+2^j) AND product_{i>j: bit_i(H)=0} z_i

when H+2^j<=N. OR all these terms and negate once to obtain z_j. Proof: any term whose prefix factors are true has H's high set bits containing all actual high set bits of w, thus H>=actual high prefix. If H is strictly larger, its threshold exceeds w; if equal, its threshold is true exactly when bit_j(w)=1. The actual high prefix is among the candidates whenever the bit is one. Induction gives exact complemented weight bits with ell NOT gates. Total number of high-prefix terms across j is O(N), each O(log N) gates.

For each i compute monotone thresholds U_(i,k)=[sum_{j!=i}t_j>=k] with O(N^2) gates per list, U_(i,0)=1. Then

    not t_i = OR_{k=0}^{N-1} [ U_(i,k) AND product_{j: bit_j(k)=0} z_j ].

If all prefix factors hold, set bits of k contain those of w so k>=w. The threshold requires k<=w-t_i. Thus success iff t_i=0, with k=w then available (w<=N-1). Each output costs O(N^2+N log N), giving O(N^3) across all outputs. The only NOTs in the entire complement generator are the ell shared weight-bit negations. Convert an arbitrary circuit to dual polarities using G20b (linear overhead), then connect positive and complemented input wires from the generator. This supplies the claimed cost bound. The exact complement-vector computation is on the original input carrier; it is not a virtual signed operation or free oracle.

Consequences: (i) a lower bound solely on the number of NOT gates larger than ell cannot prove unrestricted superpolynomial complexity; every function admits this many NOTs, and if its unrestricted size is polynomial so is the transformed size. (ii) Large G24 transversal/matching width does not imply a proportional number of NOT gates: all N complements share the same ell-bit mechanism. The number of actual NOTs can be far smaller than the number of independent original assignment mismatches. (iii) the gap between the G25 budget ~log log N and this log N ceiling is real. A superpolynomial size lower bound for selector circuits allowing ell NOT gates would suffice for NP not subset P/poly via this polynomial transport; no such bound is known/proved here. This is an exact alternative endpoint sufficient condition, not a new mandatory phase. Do not count NOT operations in free-XOR circuits without converting basis.

### G27 — the actual minterm layer is cheap; upward closure is the hard extension

For selector absent-clause bits t indexed by scopes I (1<=|I|<=3) and falsifying patterns p on I, define the monotone circuit

    H(t) = AND_I OR_{p in {0,1}^I} [ t_(I,p) AND product_{i in I} t_({i},p_i) ].

This is O(N) bounded-fanin gates. For every satisfying selector G(t)=1, a witness x supplies the local p=x|I in every term; hence G<=H. Conversely if H(t)=1 and |t|<=b=sum binom(m,j), at least one allowed pattern in each of the b scopes is required, so there is exactly one pattern per scope. Singleton scopes determine a unique x; every chosen local pattern must agree with these singleton choices. Thus t=P_x, an actual minterm. Therefore H=G on the ENTIRE region |t|<=b, including all minterms and all inputs immediately below them. H is a monotone overapproximation, not the G21 underapproximation, so this does not contradict G22 or pay G24.

Sharp escape: for every m>=3, take singleton variable 1 with both allowed values, all other singleton variables fixed zero. Choose exactly one pattern per nonsingleton scope, all zero except scope {1,3}, where the pattern demands x_1=1 and x_3=0. Scope {1,2} demands x_1=0 and x_2=0. Every chosen pattern is locally compatible with the singleton supports, H=1, but there is no global witness, G=0. This has |t|=b+1. Therefore agreement with all minterms, all their lower neighbours, or every selector of weight <=b is insufficient for the hard upward closure. Even the pair-only family admits the same local-consistency false positive, but its global implication reachability is cheap. Distinguish width-three global consistency, not merely any local conflict.

Define B(t)=H(t) AND NOT [|t|>=b+1]. This exact minterm recognizer has O(N^2) size and one actual NOT gate. It accepts all and only original minterms; G is its upward closure (exists u<=t with B(u)=1). Since G22 is superpolynomial monotone, minterm recognition + upward closure cannot be assumed to be a free or polynomial monotone operation. A general circuit for G can be ORed with B while retaining correctness at polynomial overhead, but no cheap monotone underapproximation covering every minterm follows. This is a strong same-object control against charging negation, witness count or correctness on selected boundary samples. The global selection task is exactly the missing part; no conclusion about the size of arbitrary circuits implementing upward closure.

### Local exact regression, no CI/kernel

Executed the following Python integer gate-DAG implementation: all 2046 input assignments for N=1..10 verified both complemented weight bits and every output complement. Gate counts (N,size,NOTs): (1,8,1),(2,31,2),(3,69,2),(4,147,3),(5,248,3),(6,380,3),(7,554,3),(8,840,4),(9,1143,4),(10,1499,4). Independently checked H>=G on all 260 selector inputs for m=1,2, and equality on their entire weight<=b region. Six explicit sharp false positives m=3..8 passed. These are finite checks of the formulas, not asymptotic experiments or native certification.

```python
from itertools import combinations
class Circuit:
 def __init__(self,n): self.n=n;self.g=[]
 def gate(self,op,a,b=None):
  self.g.append((op,a,b));return self.n+1+len(self.g)
 def AND(self,a,b):return self.gate('&',a,b)
 def OR(self,a,b):return self.gate('|',a,b)
 def NOT(self,a):return self.gate('!',a)
 def all(self,op,xs):
  r=1 if op=='&' else 0
  for x in xs:r=self.gate(op,r,x)
  return r
 def thresholds(self,xs):
  T=[1]
  for x in xs:
   T=[1]+[self.OR(T[j] if j<len(T) else 0,self.AND(T[j-1],x)) for j in range(1,len(T)+1)]
  return T
 def eval(self,x):
  a=[0,1]+[(x>>i)&1 for i in range(self.n)]
  for op,u,v in self.g:a.append(1-a[u] if op=='!' else a[u]&a[v] if op=='&' else a[u]|a[v])
  return a
def compile_neg(n):
 C=Circuit(n);xs=list(range(2,n+2));L=n.bit_length();T=C.thresholds(xs);z={}
 for j in reversed(range(L)):
  terms=[]
  for H in range(0,n+1,1<<(j+1)):
   k=H+(1<<j)
   if k<=n:terms.append(C.all('&',[T[k]]+[z[i] for i in range(j+1,L) if not(H>>i&1)]))
  z[j]=C.NOT(C.all('|',terms))
 out=[]
 for i in range(n):
  Ti=C.thresholds(xs[:i]+xs[i+1:]);terms=[]
  for t in range(n):terms.append(C.all('&',[Ti[t]]+[z[j] for j in range(L) if not(t>>j&1)]))
  out.append(C.all('|',terms))
 assert sum(op=='!' for op,*_ in C.g)==L
 return C,z,out
checks=0
for n in range(1,11):
 C,z,out=compile_neg(n)
 for x in range(1<<n):
  a=C.eval(x);w=x.bit_count()
  assert all(a[z[j]]==1-(w>>j&1) for j in z)
  assert all(a[v]==1-(x>>i&1) for i,v in enumerate(out));checks+=1
assert checks==2046
def carrier(m):
 I=[I for w in range(1,min(3,m)+1) for I in combinations(range(m),w)]
 C=[(I0,p) for I0 in I for p in range(1<<len(I0))]
 idx={c:i for i,c in enumerate(C)}
 def G(t):
  return any(all(t>>idx[I0,sum((x>>j&1)<<k for k,j in enumerate(I0))]&1 for I0 in I) for x in range(1<<m))
 def H(t):
  return all(any(t>>idx[I0,p]&1 and all(t>>idx[(j,),p>>k&1]&1 for k,j in enumerate(I0)) for p in range(1<<len(I0))) for I0 in I)
 return I,C,idx,G,H
checks=0
for m in (1,2):
 I,C,idx,G,H=carrier(m)
 for t in range(1<<len(C)):
  g,h=G(t),H(t);assert not g or h
  if t.bit_count()<=len(I):assert g==h
  checks+=1
assert checks==260
for m in range(3,9):
 I,C,idx,G,H=carrier(m)
 t=sum(1<<idx[I0,1 if I0==(0,2) else 0] for I0 in I)|(1<<idx[(0,),1])
 assert t.bit_count()==len(I)+1 and H(t) and not G(t)
```

### Updated endpoint-first ledger (no extra phase)

| Gate | Deliverable | Status |
|---|---|---|
| G25 | selectorLimitedNegationSuperpoly | external Amano–Maruoka theorem transported by G22; restricted genuine nonmonotonicity |
| G26 | sharedLogarithmicInputInversion / polynomialLogNegationNormalization | explicit proof and executed gate DAG; classical scope, #1546 sharing, G20 dual rails |
| G27 | selectorMintermLayerExact / sharpLocalHullEscape / oneNegationMintermRecognizer | derived and checked; G13/G14 and same-object G23 |
| G12a/N4 | unrestrictedSerialCharge | OPEN: actual total work including shared inversion and arbitrary nonmonotone bypasses |
| G12b/N5 | selectorUnrestrictedSuperpoly | OPEN: alternatively show superpoly size even with ceil(log_2(N+1)) NOT gates; sufficient by G26 |
| N6 | originalClayTransport | #1040 conditional terminal, #1129 costed machine coverage |

Next Aristotle BIDI: distinguish the hard global upward closure of the explicit minterm relation from its easy exact layer recognition. Invert from G25's actual NOT-budget lower bound toward G26's logarithmic cap, but only by proving size bounds, never by assuming many disjoint mismatches mean many NOT gates. General matching shortcut and G21/G24 padding remain controls. The direct uniform N4/N5 route remains a weaker sufficient OR route; no need to solve a stronger nonuniform endpoint if direct machine proof succeeds. No claim of P!=NP, no CI or kernel detour.


## 18. P0-G28–G32 — exact ambiguity budget, hard near-minterm bands and fixed-weight gluing (2026-11-24)

Controlling endpoint remains literal Clay P vs NP, P0-C/D. Input: G25–G27 and attached Langlands R36–R39 (reported Agda #1549 / Lean #120 heads 464691089a12 / 9c181a9fd0ef). Use only original assignment projectors and weight-slice transport, no Langlands/Monster closure. Both P0 roadmaps read at ead847b32e6a / 8a8f77430e62, common blob 790854f6eb326974377356c840c10d38945bf1c8. Existing producers: G13/G14 exact selector incidence and overlap, G17/G22 CLIQUE projection, G20 dual rails, G21/G24 orbit masks, G25–G27 actual limited negation and minterm layer, #1291 indexed geometry, #1006 FactorsThrough/self-reduction, #123 JMD lowering, #1546 shared intermediates, #1474/#1502 encoding, #1129 standard-machine coverage, #1040 terminal, #607/#678 Aristotle. All new derivations below are classical mathematical arguments, not claims of new kernel proof or literature novelty.

### G28 — sharp ambiguity budget and monotone exact near-layer checker

Use t_(I,p)=1 for available local falsifying patterns, all nonempty scopes I of size <=3. G_m(t)=1 iff some x has every pattern t_(I,x|I)=1. Write b(m)=sum_{j=1}^3 binom(m,j), N_m=sum_{j=1}^3 2^j binom(m,j), e=|t|-b(m). If some scope has no available pattern then G=0; otherwise e>=0. For each variable i, let R_i(t) be intersection, over all I containing i, of the projection to i of the available patterns in that scope. These are necessary value domains; each of the two membership bits is a monotone AND of small ORs. Let A={i:R_i={0,1}}, a=|A|. Every scope meeting A has >=2 available patterns, since a singleton pattern would resolve all its coordinates. Thus

    e >= B_m(a) := b(m)-b(m-a).
    a D_m <= 3e, D_m=b(m)-b(m-1)=1+(m-1)+binom(m-1,2).

The second inequality counts incidences between ambiguous variables and scopes; each ambiguous variable has D_m incidences and a scope has at most three. First inequality is sharp for every a: choose two assignments x,y differing in exactly a coordinates and take t=P_x union P_y; each affected scope contributes exactly one extra pattern, and the viable domains are both values precisely on the differing coordinates. This is the original G14 overlap identity, now used as a tight input-budget constraint rather than a computational lower bound.

Define H_*(t)=AND_I OR_p [t_(I,p) AND AND_{i in I} [p_i in R_i(t)]]. Size O(N_m) in bounded-fanin monotone gates: sum of incidences <=3b(m), <=8 patterns per scope; all domain rails can be shared. G<=H_* globally. If H_*=1 then all scopes and all domains are nonempty. If |t|<b(m)+D_m, a=0, so the singleton domains specify x, and each scope has its pattern; hence G=H_* on the entire band. Sharp for THIS one-round checker: for m>=3 allow both singleton values of variable 1, fix all other singleton variables to zero. For scopes containing 1 use two patterns with both values of 1 and other bits zero, except scope {1,2} use (0,0),(1,1) and {1,3} use (1,0),(0,1). Other scopes allow just zero. Then R_1={0,1}, others {0}; H_*=1, G=0 by conflicting demands on variable 1, |t|=b+D_m. This is not a hardness proof at the boundary; further constraint propagation can solve this example.

### G29 — exact parameterized shortcut and monotone band gluing

Reject empty domains or scopes, then enumerate the a ambiguous variables, fixing all singleton domains and checking each completed assignment against every scope. Time O(N_m*2^a) indexed Boolean operations, with ordinary polynomial overhead on standard machines. In particular e=O(m^2 log m) gives a=O(log m) and polynomial time on that promise. No claim that optimal running time must grow like this. This is a legitimate shared-computation shortcut.

For fixed h in 0..m define R_{T,z} as wire restriction to patterns agreeing with assignment z on T, deleting inconsistent pattern coordinates. Let

    J_h(t) = AND_{T subset [m], |T|=h} OR_{z in {0,1}^T} H_*(R_(T,z)(t)).

This is monotone, size O(N_m * binom(m,h) * 2^h). If G=1, every T has a matching z from a witness, hence J_h=1. If G=0 and all scopes nonempty and a<=h, choose T containing all ambiguous variables. Under each z on T, every surviving domain has <=1 value: outside T domains only shrink, inside T the restriction fixes the value. If H_* accepts, these singleton domains provide a witness, contradiction. Thus J_h=0. If a scope empty, all restricted checkers reject. Consequently for h<m, J_h=G on |t|<b(m)+B_m(h+1); for h=m it computes G everywhere (exponential upper bound). For constant h the band has polynomial monotone circuits. Important quantifier order AND_T OR_z, not OR_T OR_z (a bad T could miss ambiguity). This is exact cross-restriction gluing for a controlled band, not a universal per-gate lower-bound potential.

### G30 — sharpen the G22 external monotone bound (CCC 2025)

Retrieved and checked Błasiok and Meierhöfer, Hardness of Clique Approximation for Monotone Circuits, CCC 2025, Corollary 5, DOI 10.4230/LIPIcs.CCC.2025.4, https://drops.dagstuhl.de/storage/00lipics/lipics-vol339-ccc2025/html/LIPIcs.CCC.2025.4/LIPIcs.CCC.2025.4.html (explicit corollary on exact CLIQUE). For fixed delta>0 and k<=n^(1/2-delta)/log^2 n the monotone complexity is n^Omega(delta^2 k). Take delta=1/24 and k=floor(n^(5/12)); for sufficiently large n it satisfies the bound, since 5/12<11/24. G22 uses arbitrary fixed k, O(n) variables and a monotone projection, so N=Theta(n^3) yields

    MonSize(G_M,3) >= 2^Omega(N^(5/36) log N).

More generally for any fixed 0<eta<1/6 choose a fixed delta sufficiently small and k=floor(n^(1/2-3eta)); gives exponent 1/6-eta on the corresponding selector lengths. This replaces the older CKR exponent 1/12 in G21/G24 consequences (same proofs), for example hypothetical polynomial circuits need transversal >epsilon N^(5/36) on almost every minterm. This is external theorem transport, not an unrestricted lower bound. G25 limited-negation bound is separate; do not promote this strengthened monotone result to that model.

### G31 — hard bands by same-object monotone padding

Embed arbitrary selector on r active variables into m>=r variables, with m-r dummy variables fixed to zero by singleton scopes. For pure-active scopes copy original input t_(I,p); for every other scope allow exactly those patterns whose dummy bits are all zero, without constraining their active bits. Denote this projection P_{r,m}. Each target coordinate is a constant or one original unnegated selector input. Therefore no gate/NOT overhead for monotone projection. G_m(P_{r,m}(t))=G_r(t): a target witness restricts to an original witness, and original witness extends by zero dummy values. The active variables are original carrier coordinates, not an independently synthesized object.

Let B be the number of fixed 1 coordinates outside pure-active scopes. Then |P(t)|=B+|t| and maximum weight is B+N_r=b(m)+E_{m,r}, where

    E_{m,r}=sum_{j=1}^3 sum_{l=1}^j binom(r,l)binom(m-r,j-l)(2^l-1)
          <=7[b(m)-b(m-r)] <=7r D_m=O(r m^2).

Use binom outside valid ranges =0. This includes the pure-active scopes and is exact at full input. Thus any circuit correct on all |t|<=b(m)+E_{m,r}, even if arbitrary outside the promise, computes full G_r after restriction. Set m=3r^d for fixed integer d>=2. Output input length N=Theta(r^(3d)) polynomial in original input size; E=O(N^(2/3+1/(3d)))=o(N). The promised band is NP-hard under polynomial deterministic reduction, and its accepted language (check the promise and a witness) is in NP. By composing G30 at active r with the padding, any monotone circuit correct on the whole band requires size

    2^Omega(N^(5/(36d)) log N)

on the hard subsequence. For d fixed, still superpolynomial. For any fixed epsilon>0 choose d large enough that 1/(3d)<=epsilon; hence a band of excess O(N^(2/3+epsilon)) can retain NP-hardness and a superpolynomial monotone bound. No unrestricted lower bound follows, and the reduction does not put hard instances in the proven polynomial region e=O(m^2 log m). This is a precise distinction between thin relative width and genuinely small ambiguity.

### G32 — single fixed-weight NP-hardness and unrestricted equivalence

In the same padding, take m>=3r. There are >=N_r distinct dummy-only non-singleton patterns having at least one dummy bit 1 (e.g. for r>=2 there are 3 binom(2r,2)+7 binom(2r,3) such coordinates, >=N_r; r=1 already has three such pair patterns). They are currently zero and cannot become part of any witness because dummy singleton domains force zero. Choose N_r of these slack coordinates and place 1-t_j in the j-th slack coordinate. Weight is now exactly B+N_r=b(m)+E_{m,r} for every input, and satisfiability unchanged. This is a polynomial general Boolean projection with complemented inputs, NOT a monotone projection. Thus even a single specified weight layer at that excess is NP-hard (ordinary polynomial reduction), and the associated exact-weight language is in NP; one can choose m=3r^d and reject other lengths to define a uniform language. It does not have the G31 monotone lower bound by that reduction.

More generally for any Boolean circuit C on N bits, dual rail D(t,u) has O(size(C)) monotone size and agrees with C on u=1-t. Define L_k(t)=D(t,([sum_{j!=i}t_j>=k])_i). Threshold banks have polynomial size (G26). On |t|=k negative rails are exact; on |t|<k all negative rails zero, on |t|>k all one. Thus L_k agrees with C on its slice, underapproximates below and overapproximates above (relative to C; no target monotonicity needed for the comparison). For monotone G, define T_k=[|t|>=k] and

    S_k(t)= T_(k+1)(t) OR (T_k(t) AND L_k(t)).
    S_k(t)= T_(k+1)(t) OR (T_k(t) AND G(t)).

First form monotone; equality by weight cases. It is the monotone sandwich extension of the exact slice (all lower points false, all upper points true). This provides polynomial-size monotone sandwich circuits for every k if general C is polynomial. Conversely if all these monotone sandwich circuits have a common polynomial size bound, compute G(t)=OR_k ([|t|=k] AND S_k(t)) with polynomial overhead and shared weight bank. Uniform version requires polynomially constructible circuits; nonuniform version alone is equivalent to polynomial circuit families, not to P. Therefore a general nonuniform selector lower bound is equivalent to superpolynomial growth of worst-case monotone sandwich-extension complexity over k; merely proving a globally sound monotone extension expensive is insufficient. The latter extension is a different function. G31 band has comparisons between different weights and a monotone projection; G32 single slice erases these comparisons and can express general negation through padding. That is the precise cross-weight gluing boundary. Do not transfer G31 lower bound to G32 by treating complemented rails as free monotone inputs. Attached R37 rank-one Fourier detector remains exact but W(t)/2^m may be 2^-m; extracting it is not a free primitive and no precision/representation lower bound here.

### Local execution (Python integer masks, no CI/native kernel)

Executed 1260 selector inputs (all 260 at m=1,2; 250 seeded inputs for each m=3..6), checking H_* sound overapproximation, exact ambiguity budget, viable-domain witness restriction, near-band exactness and J_h on promised inputs for h<=2. Eight sharp boundary counterexamples m=3..10 verified. 920 semantic padding comparisons (monotone band and balanced fixed slice) for (r,m)=(1,3),(2,6),(3,9), all original selectors at r=1,2 and 200 seeded r=3 selectors. All passed. Reproduction core:

```python
from itertools import combinations
from random import Random
from math import comb
def b(m):return sum(comb(m,j) for j in range(1,min(3,m)+1))
def carrier(m):
    S=[I for j in range(1,min(3,m)+1) for I in combinations(range(m),j)]
    C=[(I,p) for I in S for p in range(1<<len(I))]
    ix={c:i for i,c in enumerate(C)}
    P=[sum(1<<ix[I,sum((x>>i&1)<<j for j,i in enumerate(I))] for I in S) for x in range(1<<m)]
    return S,C,ix,P
def support(t,m,S,ix):
    R=[3]*m
    for I in S:
        pats=[p for p in range(1<<len(I)) if t>>ix[I,p]&1]
        for j,i in enumerate(I):R[i]&=sum(1<<a for a in {p>>j&1 for p in pats})
    return R
def H(t,m,S,ix):
    R=support(t,m,S,ix)
    return all(any(t>>ix[I,p]&1 and all(R[i]>>(p>>j&1)&1 for j,i in enumerate(I)) for p in range(1<<len(I))) for I in S)
def restrict(t,C,T,z):
    return t & sum(1<<k for k,(I,p) in enumerate(C) if all(i not in T or (p>>j&1)==(z>>i&1) for j,i in enumerate(I)))
def glue(t,m,S,C,ix,h):
    return all(any(H(restrict(t,C,T,z),m,S,ix) for z in range(1<<m) if z&~sum(1<<i for i in T)==0) for T in combinations(range(m),h))
def check(t,m,S,C,ix,P):
    g=any(t&p==p for p in P);R=support(t,m,S,ix);a=R.count(3);hh=H(t,m,S,ix)
    assert not g or hh
    if all(any(t>>ix[I,p]&1 for p in range(1<<len(I))) for I in S):
        assert t.bit_count()-b(m)>=b(m)-b(m-a)
    if t.bit_count()<2*b(m)-b(m-1):assert hh==g
    assert any(t&p==p and all(R[i]>>(x>>i&1)&1 for i in range(m)) for x,p in enumerate(P))==g
    for h in range(min(2,m)+1):
        if h==m or t.bit_count()<2*b(m)-b(m-h-1):assert glue(t,m,S,C,ix,h)==g
rng=Random(369);count=0
for m in (1,2,3,4,5,6):
    S,C,ix,P=carrier(m)
    if m<=2: inputs=range(1<<len(C))
    else:
        inputs=[]
        for _ in range(250):
            t=P[rng.randrange(1<<m)]
            for i in rng.sample(range(len(C)),rng.randrange(len(C)+1)):t^=1<<i
            inputs.append(t)
    for t in inputs:check(t,m,S,C,ix,P);count+=1
assert count==1260
for m in range(3,11):
    S,C,ix,P=carrier(m);t=0
    for I in S:
        pats=[0] if 0 not in I else [0,3] if I==(0,1) else [1,2] if I==(0,2) else [0,1]
        for p in pats:t|=1<<ix[I,p]
    assert t.bit_count()==2*b(m)-b(m-1) and H(t,m,S,ix) and not any(t&p==p for p in P)
def pad(t,r,m,balanced):
    S,C,ix,P=carrier(m);s,c,jx,ps=carrier(r);v=0
    for j,(I,p) in enumerate(C):
        take=(t>>jx[I,p]&1) if I[-1]<r else all(not(p>>k&1) for k,i in enumerate(I) if i>=r)
        if take:v|=1<<j
    if balanced:
        slack=[j for j,(I,p) in enumerate(C) if len(I)>1 and all(i>=r for i in I) and p!=0]
        assert len(slack)>=len(c)
        for j,k in enumerate(slack[:len(c)]):
            if not(t>>j&1):v|=1<<k
    return v
count=0
for r,m in ((1,3),(2,6),(3,9)):
    s,c,jx,ps=carrier(r);S,C,ix,P=carrier(m)
    E=pad((1<<len(c))-1,r,m,False).bit_count()-b(m)
    assert E<=7*(b(m)-b(m-r))
    inputs=range(1<<len(c)) if r<=2 else [rng.getrandbits(len(c)) for _ in range(200)]
    for t in inputs:
        g=any(t&p==p for p in ps)
        for bal in (False,True):
            v=pad(t,r,m,bal)
            assert any(v&p==p for p in P)==g and v.bit_count()<=b(m)+E
            if bal:assert v.bit_count()==b(m)+E
            count+=1
assert count==920
```

### Active endpoint ledger (no additional prerequisite phase)

| Gate | Deliverable | Status / producer and consumer |
|---|---|---|
| G28 | sharpAmbiguityBudget / nearMintermMonotoneExact | proof + finite checks; G13/G14/G27 |
| G29 | ambiguityParameterizedDecision / boundedBandMonotoneGluing | proof + finite checks; G28, #1291, #1006 |
| G30 | strengthened2025CliqueSelectorMonotoneBound | external Corollary 5 via G22; restricted; updates G21/G24 |
| G31 | monotoneDummyPadding / hardShrinkingWeightBand | proof + finite checks; G22/G30 |
| G32 | fixedWeightNPCompleteProjection / sliceSandwichCircuitEquivalence | proof + padding checks; G26 dual rails, attached R39 |
| N4/G12a | unrestrictedSerialCharge | OPEN: bound actual cross-weight/same-layer nonmonotone computation, permit G29 and G32 shortcuts |
| N5/G12c | unrestrictedSuperpolynomialGrowth | OPEN: e.g. superpoly worst slice sandwich monotone complexity, or direct uniform machine route |
| N6 | originalClayTransport | #1040 conditional terminal / #1129 costed machine coverage |

Aristotle BIDI: prioritize the explicit hardest promise bands between e=O(m^2 log m) and e=O(m^(2+epsilon)), not further local rank census. A new sufficient nonuniform endpoint is lower bounding the actual sandwich S_k rather than the full monotone extension G (G32 makes their polynomial-family complexity equivalent to general circuits). G31 is insufficient for S_k since the monotone projection spans multiple layers. Fixed-weight complemented padding demonstrates exactly where the ordinary monotone argument fails. Need a lower bound surviving that shortcut, or pivot to direct uniform N4/N5; no additional formal certification prerequisite or unrestricted separation claim.
