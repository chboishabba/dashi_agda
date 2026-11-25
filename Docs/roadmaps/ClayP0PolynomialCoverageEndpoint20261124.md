# Clay P vs NP P0 — polynomial semantic coverage and universal resource obstruction

Date: 2026-11-24. Shared Agda/Lean roadmap, independently based on their default branches. Priority: solve the literal Clay P vs NP endpoint (P0). Endpoint mathematics before additional certification; no other programme is a prerequisite. This document records research obligations, not a separation proof. Proposed lemma identifiers below are not existing declarations unless explicitly marked.

## Controlling P0 directive — literal Clay solution, 2026-11-25

**Current controlling frontier (2026-11-25): Section 57 — target-conditioned cut-syndrome contraction and witness reopening.** Paid bounded Boolean/syndrome interface algorithm removes full character rank cost. General polynomial selector, unrestricted obstruction, full-code deadline remain open; no compulsory rank or width representation. Prize endpoint mathematics first.


User explicitly confirmed: the objective is to win the Clay Millennium Prize by solving P vs NP, NOT to formalise everything encountered. These three parallel mathematical routes supersede older phase labels and serial infrastructure priorities wherever they conflict. P vs NP is the exclusive scope of these branches.

| Controlling route | Mathematical exit criterion |
|---|---|
| P0-S — separation | Unconditionally prove that for every fixed c there exists an original satisfiable F with J(F) > c log2(|F|+2), or equivalently the Section47 unrestricted kappa obstruction up to the Section49 BIDI constants. |
| P0-C — construction | Give a uniform deterministic polynomial-time isolating seed/portfolio constructor AND a uniform polynomial-time promised singleton witness producer, with all source compilation, verification and decoding costs paid; alternatively give a direct uniform polynomial SAT algorithm. |
| P0-R — reverse endpoint | Prove existence of a total computable full-code deadline B(e) bounding the first genuine gain of every incomplete valid clocked candidate, with the G128 standard-machine coverage and totality proof. No polynomial-time deadline finder is required. |

Any one completed route suffices for the corresponding literal Clay conclusion. None is established as of this directive. In particular an RP algorithm, nonuniform advice, finite tests, a restricted affine/query/representation lower bound, and partial counterexample enumeration do not pay these exits. Do not presume P!=NP while attempting P0-S/P0-R or presume P=NP while attempting P0-C.

Work geometry-forward from original sources, steelman both possible outcomes, BIDI and reverse-solve from the endpoint. Preserve zero mode, inhabited neutral fibres, signed residual, independent source/time/refinement/precision/resource indices and original attribution. Take substantial theorem-level cuts rather than incremental formalisation gates. Permit arbitrary ordinary computation, sharing, nonlinear charts, recomputation and source re-access in unrestricted claims. Use existing standard-machine fallback rather than make exotic compilers compulsory.

Use FRACTRAN, earth/wheel/spoke, Langlands, prime residues and the indexed hyperfabric only when they supply a concrete mathematical lever on one of the three exits. Reuse existing owners; no new generic infrastructure or unrelated programme work. Local exact computation (SymPy where useful, no GitHub CI) is a falsification/validation aid, not proof of an asymptotic universal claim. Agda/Lean formalisation is downstream of the decisive mathematical argument except where a specific proof obligation requires it. Record actual proofs, failed hypotheses and exact remaining lemmas; do not count commits, passing finite checks or added declarations as progress toward separation by themselves. Prepare a self-contained standard-model mathematical argument for independent expert scrutiny once an endpoint is genuinely paid; no claim of solvedness or prize eligibility before that.

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


## 19. P0-G33–G37 — signed component compression, slice projection obstruction, literature reconciliation (2026-11-24)

Controlling endpoint: literal Clay P vs NP. User attachments: G28–G32 and Langlands R43–R46 (reported #1549/#120 heads 07ced79e5be4 / 1568c2c4738b). Reuse exact source-selected fibre compression, not a new arithmetic programme. Both P0 roadmaps read live at 9cc331b5ae03 / 4f8af7050230, common blob 777a62b796d53f3c753b79ee0bb038e566888a37. Producers/consumers: G13 original scopes, G14 overlap, G16 median closure, G17 2-SAT reachability, G22/G30 CLIQUE projection, G28/G29 ambiguity and G31/G32 padding/slices; existing BalancedTritBitFibre and #1291 signed indexed residuals, ConsumerFibreRepairExact (#1006), #123 JMD lowering, #1546 sharing, #1474/#1502 reductions, #1129 standard machine, #1040 terminal, #607/#678 Aristotle. No native kernel execution or new prerequisite phase.

### G33 — signed component quotient with exact inverse

Compute G28's necessary value domains R_i, reject any empty domain, and let A={i:R_i={0,1}}, a=|A|, f=m-a. Fix every nonambiguous variable to its singleton value. The attachment's singleton-scope compression is a valid weaker choice; G28 uses all unary projections. For any original scope I and pair i,j in I intersect A, inspect the projection of its original allowed-pattern set onto i,j. If exactly two pairs occur, each coordinate has both values (by R_i=R_j={0,1}), so the relation is either equality or disequality. Add a signed graph edge with label epsilon=x_i XOR x_j. This includes every pair in a two-pattern scope and can also detect additional pair correlations in larger pattern sets. All edges are necessary for every original witness. If any signed cycle has nonzero XOR, reject. Otherwise choose a root per connected component, assign orientation eta_i by path XOR with root orientation zero, and write x_i=y_{component(i)} XOR eta_i. Every original witness has unique component-bit coordinates; conversely a component assignment gives one original assignment with the prescribed fixed bits and orientations. For every original scope I substitute these affine expressions (including repeated component labels); enumerate its at most 8 possible residual patterns and intersect masks on identical residual scopes J. Keep empty scope: rejection if its unique empty pattern is forbidden. Result has at most 1+b(c) scopes and 1+N_c forbidden patterns, c number of components. The map between original and residual witnesses is bijective, so exact counting and witness reconstruction are preserved. Indexed work polynomial in N, followed by O((c+1)^3 2^c) enumeration. This is a deterministic upper bound, not independent work charge. In the attached projector notation this is a coordinate isometry onto the parity-consistent subcube and hence preserves the same diagonal satisfying projector, not a free rank oracle.

### G34 — exact component excess bound

Assume nonempty domains and consistent signs. Let n_1,...,n_c be component sizes, sum=a. Put B=b(m)-b(f), e=|t|-b(m). Every scope touching A has at least two available patterns. Every scope touching >=2 distinct components has at least three, since otherwise its two patterns would induce a signed edge across components. This remains true with the stronger pair-projection graph. The number X of crossing scopes is exactly

    X=B-sum_j (b(f+n_j)-b(f)).
    e >= B+X.

For given a,c>=1, discrete convexity of b (its first differences increase) maximizes sum_j b(f+n_j) at sizes a-c+1,1,...,1, by repeatedly moving a unit from a smaller nonsingleton to a largest component. Thus

    e >= 2B - b(m-c+1)+b(f) -(c-1)(b(f+1)-b(f)).

The bound is sharp for every 1<=c<=a<=m even for the stronger pair-projection graph. Take this unbalanced partition, fixed variables zero, and in each scope with d distinct component labels use the following allowed patterns on those labels: d=0: empty pattern; d=1: 0,1; d=2: 00,01,10; d=3: 000,011,101 (little-endian integer patterns 0,3,5). Expand onto repeated component coordinates and fixed zero variables. Each active variable has both values in every containing scope; cross-component pair projections contain three pairs, within-component projections contain only equality pairs. All-zero assignment satisfies. Each crossing scope contributes exactly one extra unit beyond B, and the component partition is exactly as chosen. This is an explicit sharp witness on the original carrier.

For a simpler bound, number of cross-component pairs X2 = sum_{i<j} n_i n_j >= (c-1)(a-c/2) >= a(c-1)/2. Each pair belongs to m-2 triples, each triple counts at most three pairs. Hence X>=X2(1+(m-2)/3) for m>=2, with m=1 trivial, so

    c <= min(a, 1+6(e-B)/(a(m+1)))   for a>0.

At e=B, all ambiguous variables belong to at most one component (or instance rejected for contradictory signs); huge a can coexist with only one free bit. For a=0 no branch needed. This corrects the impression that raw residual dimension must be exponential in raw ambiguity. Both parameter bounds are upper bounds on possible independent choices, not lower bounds on time.

### G35 — exact binary/ternary residual backdoor

For each merged residual relation on three distinct component variables, test its finite majority closure (G16). Relations on <=2 variables and majority-closed ternary relations are all exactly 2-CNF expressible by excluding absent unary and binary patterns. Empty residual scope must be checked separately. Let bad scopes be the ternary ones that fail majority closure. Greedily take any maximal disjoint family of p bad scopes. Its union T has <=3p variables and intersects every bad scope. Branch on T, restrict each residual mask, and convert all remaining constraints to 2-CNF: originally majority-closed relations stay closed under restriction and projection of fixed coordinates; every bad ternary scope loses at least one variable. Apply G17 implication graph reachability. Decision time poly(N)*2^(3p), also reconstruct one witness by normal 2-SAT methods. This is a strong-backdoor upper bound, not a claim that counting satisfying assignments of arbitrary 2-CNF is polynomial or that p measures unavoidable work. Retain G33 counting route, and distinguish fixed labels versus dynamic input-derived contraction (not free monotone projection). Tests below cover G33/G34; G35 proved directly without claiming extra algorithm tests.

### G36 — exact obstruction to importing ordinary CLIQUE lower bounds into a single slice

Attribution correction: G32 sandwich is the classical slice-function construction of Berkowitz (1982), not new general circuit equivalence. Valiant, Negation is Powerless for Boolean Slice Functions, SIAM J. Comput. 15 (1986) 531–535, https://doi.org/10.1137/0215037 (publisher abstract checked), improves overhead to constant-factor size plus O(N log^2 N); see also Wegener, The complexity of central slice functions, https://doi.org/10.1016/0304-3975(86)90122-2. G32's application to actual selector carrier and fixed-weight padding is retained. Literature even has polynomial-size canonical CLIQUE slice; distinguish slice from the original monotone target.

New explicit discriminator: let S_l be ANY sandwich/slice function, false below weight l and true above l, arbitrary on l. Suppose a monotone projection phi (constants, positive edge inputs with arbitrary repeated wires) maps CLIQUE(n,k) exactly to S_l, for 3<=k<=n/2. Write w(phi(e))=C+sum_edge a_edge e_edge, a_edge>=0 integers. Every positive graph must map to weight>=l; every negative graph to weight<=l. Choose a random k-element vertex subset and put exactly its clique edges, positive distribution P. For negative distribution Q color each vertex independently uniformly in k-1 colors and put every cross-color edge; always no k-clique. Each edge has positive marginal q=k(k-1)/(n(n-1)) and negative marginal 1-r, r=1/(k-1). For this parameter range q<1-r. Hence expected mapped weight on P strictly less than on Q if any a_edge>0, contradicting required inequalities. If all a_edge=0, image is constant, also impossible. Thus no monotone coordinate projection of this CLIQUE family to any slice function, regardless of target dimension, weight, repetition or choice of slice truth table. This closes a tempting G32 proof route negatively; G22/G30 cannot be used by that kind of transfer.

Stronger no-go for preprocessing by small-support monotone functions: permit each output coordinate phi_j to be an arbitrary monotone Boolean function of at most d graph edges, not just a wire. Constants cancel in expected weights. A nonconstant such function vanishes at all-zero and is true at all-one of its support. Thus P(phi_j=1)<=d q by union bound on at least one present supported edge; Q(phi_j=1)>=1-d r by union bound on absence of any supported edge. If d(q+r)<1, each nonconstant coordinate has strictly smaller expected value under P than Q. Therefore the same weight contradiction holds for any such preprocessing, even if the coordinate functions share intermediate computations and even if the target slice length is unrestricted. In the G30 regime k=n^(5/12), q=o(1/k), so d below a constant fraction of k is excluded. This forces some output coordinate to depend on many graph edges in any monotone preprocessing reduction, but does NOT prove large size (e.g. an OR can have large support cheaply). No restriction on nonmonotone reductions: G32 balanced complementary padding is a legal shortcut. This is a self-contained expectation argument, not a literature novelty claim, and does not exclude arbitrary global monotone preprocessing. Exact small-support distribution checks below.

### G37 — current subexponential SAT literature: reported algorithm, not a lower-bound premise

Current web source check found the OpenAI preprint The Exponential Time Hypothesis is False, 17 Oct 2026 revised 25 Oct, https://github.com/openai/math/tree/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026 (Theorem 1.1 and abstract inspected), which reports deterministic exact fixed-width #SAT in polynomial space and time (n+clauses)^O(1) * 2^(n/(log n)^(1/2+o(1))). Anthropic independently reports a subexponential 3SAT algorithm; see current discussion and https://www.cslib.io/complexitylib/abstracts/subexponential-sat.pdf (formal abstracts search result) and https://newruntime.com/analysis/research-anthropic-s-lean-proof-that-eth-is-false-is-public-and-machine-checked-but-no/ (external verification caveat). Do not assume ETH as a valid unconditional or accepted premise, and do not claim this roadmap independently verified either preprint or its Lean boundary. If the stated theorem is accepted, G33's exact residual 3-CNF on c variables and O((c+1)^3) clauses can use that algorithm unchanged. Reported upper bound then poly(N)*2^(c/(log c)^(1/2+o(1))) (small c handled directly); includes exact counts, decision and witness via polynomial self-reduction. In particular for any fixed 0<delta<1/2, c=O(log m*(log log m)^(1/2-delta)) is polynomial-time on the promise, and by G28 so is e=O(m^2 log m*(log log m)^(1/2-delta)). This is an external-theorem-dependent improvement, not claimed kernel-verified or unconditional here. Subexponential is not polynomial and does not settle Clay. A proof of P!=NP must permit the reported faster algorithm if correct. Do not cite ETH to claim a lower bound on the compressed residual. The preprint also reports an E^NP circuit lower bound; that class is not NP and cannot pay N5. Direct uniform route remains active.

### Executed local regression (integer masks and exact rational probabilities; no CI/kernel)

Actually executed 1,260 selector cases (260 exhaustive m=1,2 and 250 each at m=3..6, mixed planted/constrained/random), checking exact witness-set reconstruction, parity contradictions and component excess inequalities. 165 sharp partitions across all 1<=c<=a<=m<=9 checked, using the explicit patterns above; all passed. 800 exact comparisons of positive/negative acceptance probabilities on small support monotone truth tables passed (n,k in (6,3),(8,4),(10,4),(12,5),(15,6),(20,7), 20 seeded supports for each d=1..3 satisfying d(q+r)<1). No asymptotic numerical extrapolation. Reproduction core:
```python
from itertools import combinations, product
from math import comb
from random import Random
from fractions import Fraction
def b(n):return sum(comb(n,j) for j in (1,2,3))
def scopes(n):return [I for j in range(1,4) for I in combinations(range(n),j)]
def pattern(x,I):return sum(((x>>i)&1)<<j for j,i in enumerate(I))
def check(m,S,L):
 R=[3]*m
 for I,ps in zip(S,L):
  for j,i in enumerate(I):R[i]&=sum(1<<v for v in {p>>j&1 for p in ps})
 brute={x for x in range(1<<m) if all(pattern(x,I) in ps for I,ps in zip(S,L))}
 if 0 in R:assert not brute;return
 A={i for i in range(m) if R[i]==3};a=len(A);f=m-a
 e=sum(len(ps)-1 for ps in L);B=b(m)-b(f);assert e>=B
 adj={i:[] for i in A}
 for I,ps in zip(S,L):
  for j,k in combinations(range(len(I)),2):
   i,l=I[j],I[k]
   if i not in A or l not in A:continue
   q={((p>>j)&1,(p>>k)&1) for p in ps}
   if len(q)==2:
    z={u^v for u,v in q};assert len(z)==1
    h=z.pop();adj[i].append((l,h));adj[l].append((i,h))
 lab={};eta={};c=0;ok=True
 for i in sorted(A):
  if i in lab:continue
  lab[i]=c;eta[i]=0;Q=[i]
  for j in Q:
   for k,h in adj[j]:
    v=eta[j]^h
    if k in lab:
     if eta[k]!=v:ok=False
    else:lab[k]=c;eta[k]=v;Q.append(k)
  c+=1
 if not ok:assert not brute;return
 X=sum(len({lab[i] for i in I if i in A})>=2 for I in S)
 assert X==B-sum(b(f+list(lab.values()).count(j))-b(f) for j in range(c))
 assert e-B>=X
 if c:
  assert X>=B-(b(m-c+1)-b(f))-(c-1)*(b(f+1)-b(f))
  assert 6*(e-B)>=(c-1)*a*(m+1)
 base=sum((R[i]==2)<<i for i in range(m) if i not in A);res={}
 for I,ps in zip(S,L):
  J=tuple(sorted({lab[i] for i in I if i in A}));vals=set()
  for z in range(1<<len(J)):
   x=base|sum((((z>>J.index(lab[i]))&1)^eta[i])<<i for i in I if i in A)
   if pattern(x,I) in ps:vals.add(z)
  res[J]=res.get(J,set(range(1<<len(J))))&vals
 got={base|sum((((y>>lab[i])&1)^eta[i])<<i for i in A) for y in range(1<<c) if all(pattern(y,J) in ps for J,ps in res.items())}
 assert got==brute
 return a,c,e,X
rng=Random(369);count=0
for m in range(1,7):
 S=scopes(m)
 if m<=2:
  for t in range(1<<sum(1<<len(I) for I in S)):
   L=[];v=0
   for I in S:L.append({j for j in range(1<<len(I)) if t>>(v+j)&1});v+=1<<len(I)
   check(m,S,L);count+=1
 else:
  for trial in range(250):
   x=rng.randrange(1<<m);y=rng.randrange(1<<m);L=[]
   for I in S:
    ps={p for p in range(1<<len(I)) if rng.random()<(.2 if trial%3==0 else .65)}
    if trial%3!=0:ps.add(pattern(x,I))
    if trial%3==2:ps.add(pattern(y,I))
    L.append(ps)
   check(m,S,L);count+=1
assert count==1260
count=0
for m in range(1,10):
 S=scopes(m)
 for a in range(1,m+1):
  for c in range(1,a+1):
   classes={i:max(0,i-(a-c)) for i in range(a)};L=[]
   for I in S:
    J=sorted({classes[i] for i in I if i<a});d=len(J)
    pats=[0] if d==0 else [0,1] if d==1 else [0,1,2] if d==2 else [0,3,5]
    L.append({sum(((z>>J.index(classes[i]))&1)<<j for j,i in enumerate(I) if i<a) for z in pats})
   aa,cc,e,X=check(m,S,L);assert (aa,cc)==(a,c)
   f=m-a;B=b(m)-b(f);assert e-B==X==B-(b(m-c+1)-b(f))-(c-1)*(b(f+1)-b(f));count+=1
assert count==165
count=0
for n,k in ((6,3),(8,4),(10,4),(12,5),(15,6),(20,7)):
 E=list(combinations(range(n),2));q=Fraction(k*(k-1),n*(n-1));r=Fraction(1,k-1)
 for d in range(1,4):
  if d*(q+r)>=1:continue
  for _ in range(20):
   es=rng.sample(E,d);V=sorted({i for e in es for i in e});pp=[0]*(1<<d);nn=[0]*(1<<d)
   for bits in range(1<<len(V)):
    X={v for j,v in enumerate(V) if bits>>j&1};h=len(X)
    if 0<=k-h<=n-len(V):pp[sum((u in X and v in X)<<j for j,(u,v) in enumerate(es))]+=comb(n-len(V),k-h)
   for z in product(range(k-1),repeat=len(V)):
    c=dict(zip(V,z));nn[sum((c[u]!=c[v])<<j for j,(u,v) in enumerate(es))]+=1
   for F in range(1<<(1<<d)):
    if F&1 or not(F>>(2**d-1)&1):continue
    if not all(not(F>>x&1) or F>>y&1 for x in range(1<<d) for y in range(1<<d) if x&y==x):continue
    u=Fraction(sum(p for j,p in enumerate(pp) if F>>j&1),comb(n,k));v=Fraction(sum(p for j,p in enumerate(nn) if F>>j&1),(k-1)**len(V));assert u<v;count+=1
assert count==800
```

### Active endpoint-first ledger

| Gate | Deliverable | Status |
|---|---|---|
| G33 | signedParityComponentResidualBijection | derived and tested; original scopes, #1291 signed residuals |
| G34 | sharpComponentExcessBudget / sharpPartitionWitness | derived and tested |
| G35 | nonBijunctiveResidualBackdoorDecision | derived; G16/G17 |
| G36 | cliqueToAnySliceMonotoneProjectionNoGo / boundedSupportPreprocessingNoGo | derived and exact checks; G32 attribution Berkowitz–Valiant |
| G37 | reportedSubexponentialSATResidualTransport | external preprint theorem conditional; no independent proof audit |
| N4/G12a | unrestrictedSerialCharge | OPEN: cannot charge raw c, a, p or e; must allow exact contraction and shared inversion |
| N5/G12c | actualSliceOrUnrestrictedSuperpoly | OPEN: ordinary monotone CLIQUE projection cannot pay it; general monotone preprocessing not excluded |
| N6 | originalClayTransport | existing conditional #1040, #1129 coverage |

Highest alpha: rather than attempting another unnegated CLIQUE projection into a sandwich (G36 rules it out even with small-support preprocessing), inspect genuinely global monotone reductions or direct lower-bound methods on the original balanced hard slice. In parallel, audit the reported 2026 #SAT algorithm's actual paid operations (including any field/rank/tensor work) as a necessary shortcut control and potential source of a different uniform-time endpoint. Do not infer lower bounds from ETH or from restricted proof-search complexity. No assertion of P!=NP or extra mandatory kernel phase.


## 20. P0-G38–G41 — canonical central slice, exponential formal arithmetic bound and the exact squarefree-trace gap (2026-11-24)

Controlling endpoint remains literal Clay P vs NP, P0-C/D. Inputs: attached Langlands R50–R53 (reported #1549/#120 heads d52220233312 / afa8a6d16ac7) and P0 G33–G37. No new Langlands/Monster work. Both P0 roadmaps read at d0d7d2187306 / 48f329a5b3ae, common blob 59fae07307670ad14bada57b7eb6c8cd6cd17ee3. Existing producers: G13 original clause scopes, G14 parity degree, G16/G17 width-two median/reachability, G22/G30 monotone CLIQUE, G26/G32 dual rails and slices, G31 padding, G33 signed contraction, G36 projection no-go, #1291 joint residuals, #1006 FactorsThrough/self-reduction, #123 JMD lowering, #1546 sharing, #1129 standard machine coverage, #1040 terminal, #1474/#1502 original reductions, #607/#678 Aristotle. Classical arithmetic balanced-decomposition method attribution: Schnorr/Hyafil/Valiant and the exposition https://web.vu.lt/mif/s.jukna/boolean/minkowski.html ; see also Cavalar–Kumar–Rossman https://pmc.ncbi.nlm.nih.gov/articles/PMC9705498/ (monotone decomposition). Distinguish formal polynomial computation, counting on Boolean inputs, and decision; Jukna, Lower Bounds for Monotone Counting Circuits, https://arxiv.org/abs/1502.01865 ; Notes on Boolean Read-k and Multilinear Circuits, https://arxiv.org/abs/2207.08701. The source-specific bounds below are derived, not a claim of literature novelty or native kernel certification.

### G38 — canonical central-slice transport with slack budget

For q active variables take m=4(q+1), d=m-q dummies forced zero by singleton scopes, K=N_m/2 (N_m even). For every non-pure-active scope permit exactly patterns with dummy bits zero. Write B for number of fixed 1 coordinates outside pure-active scopes. Their contribution is at most half the number of those coordinates, because each such scope has >=1 dummy. The deficit from half is at least binom(d,2)+3 binom(d,3) from dummy-only pair/triple scopes; this is >=N_q/2=q+2 binom(q,2)+4 binom(q,3) (d>=3q+4; pair term >=q^2, triples contain at least two disjoint q-subsets). Hence B+N_q<=K. There are N_m-N_q-B-d inactive outside-active coordinates excluding the d forbidden singleton patterns, which must remain zero. Since K<=N_m-d, there are enough slack coordinates for N_q complements and K-(B+N_q) further ones. Assign one separate slack coordinate 1-t_j to every active input t_j, and the remaining constants to reach K. All original witnesses extend uniquely by dummy zero, no new witness is introduced, and output weight is K. Thus exact witness-count-preserving general projection (not monotone). G32's Berkowitz–Valiant slice simulation plus this explicit polynomial padding yields equivalence of polynomial general circuit families for G_q and polynomial monotone circuit families for the single canonical central sandwich S_m. Uniform P endpoint additionally requires efficient uniform construction. No assumption that arbitrary monotone projection can implement this: G36 forbids the proposed CLIQUE route.

### G39 — direct exponential nonnegative arithmetic lower bound on source witness polynomial

For w=2 or 3 use all scopes I of 1..w variables. b_w(m)=sum binom(m,j), N_w(m)=sum 2^j binom(m,j). Let
    W_m(t)=sum_x prod_I t_(I,x|I).
This is a homogeneous multilinear formal polynomial of degree b=b_w(m), with 2^m distinct monomials. More generally allow any nonempty subset X of its monomials, with arbitrary strictly positive coefficients. Claim for m>=3: every bounded-fanin nonnegative (+,times) arithmetic DAG for such a formal polynomial has size at least |X|*2^(-(m-r0)), where r0=min{r:b_w(r)>=b_w(m)/3}. In particular W_m requires >=2^r0>=2^(m/3) gates, hence exp(Omega(N_w(m)^(1/w))). Constants arbitrary nonnegative; zero/dead gates discarded.

Proof: use the classical balanced-product decomposition. For completeness, in a live monotone circuit for a homogeneous multilinear output, every gate is homogeneous/multilinear because any gate monomial can be extended by a fixed nonzero context monomial along a live path to the output; no cancellation. For each output monomial choose a parse tree, descend through plus gates and the larger-degree child of products until first degree <=2b/3; the selected gate has degree >=b/3 (unless at root, which has degree b). For each such gate g, collect all context monomials from parse trees with a distinguished occurrence of g. Replacing that occurrence by any monomial of g still yields an output monomial. Thus the products of the gate polynomial A_g with a nonnegative context polynomial B_g have support contained in output and together cover output; at most one product per gate. This does not unroll or charge the original DAG per parse tree. A,B have complementary degrees in [b/3,2b/3].

In any nonzero balanced product AB supported within W, fixing a monomial of B forces every monomial of A to choose exactly one pattern from the same complementary set of scopes; similarly for B. Write the resulting partition of scopes as S_A,S_B, and U,V for their unions of original assignment variables. If there is i in U minus V and j in V minus U, the pair scope {i,j} cannot belong to either side, contradiction. Thus U=[m] or V=[m]. Each side has >=b/3 scopes, so each union has size >=r0. For any shared coordinate i in U intersect V, all monomials of A and B must agree on its value: all cross products are valid assignment monomials. Thus all product monomials have fixed bits on at least r0 original coordinates. At most 2^(m-r0) distinct assignment monomials per product. Covering |X| proves the bound. Finally b_w(r)<=r b_w(m)/m by binomial ratios, so r0>=m/3. This is a direct same-object geometric resource lower bound for formal nonnegative arithmetic with arbitrary sharing, stronger in its own model than counting expanded terms. It holds for width two as well; that fact is a mandatory shortcut control. It is NOT an unrestricted circuit lower bound or an assertion about arbitrary arithmetic circuits with subtraction, or about all circuits counting on Boolean inputs (powers can collapse on the Boolean cube).

### G40 — lift the formal arithmetic bound to the actual central exterior polynomial

For w=3 define the homogeneous polynomial
    W_K(t)=sum_{L subset [N_m], |L|=K} W_m(1_L) prod_{j in L} t_j,
and F_K=W_K+e_(K+1)(t), where e_j is the elementary symmetric polynomial. This is exactly the attachment R51/R52 exterior multiplicity on Boolean inputs; F_K support equals S_m. On Boolean t, W_K(t)=W_m(t)*binom(|t|-b_m,K-b_m), interpreted zero if |t|<b_m. The formal polynomial is not merely the Boolean support.

Suppose a nonnegative arithmetic circuit of size s computes F_K (or W_K) formally. Homogeneous degree-K extraction retains W_K with polynomial overhead O(s*(K+1)^2): track each gate's homogeneous components up to K, addition componentwise and multiplication by truncated convolution. Set all nonactive selector coordinates to 1 except forbidden dummy singleton patterns (zero); leave pure-active q-variable inputs as indeterminates. Denote T=N_m-N_q-d the number of available nonactive coordinates. Extract the homogeneous degree-b_q part in the active variables, again by truncated convolution. Every surviving W_K monomial has a witness with all dummies zero. At active degree b_q it contains precisely one original minterm P_x, since the witness forces all b_q coordinates and there are no extra active coordinates. Every original x contributes exactly binom(T-(b_m-b_q),K-b_m) choices of additional outside-active coordinates, the same positive integer lambda for every x. This is because the remaining b_m-b_q padded witness coordinates are fixed, and the extra K-b_m may be chosen anywhere among the remaining available outside-active coordinates. K>=b_m and T+b_q>=K (follows from the G38 slack budget; its balanced padding gives a central input extending each original minterm). Hence the extracted polynomial is lambda W_q. G39 gives s*poly(N_m)>=2^(q/3); m=4(q+1), so s>=exp(Omega(N_m^(1/3))) on this padded subsequence. This directly bounds the formal nonnegative exterior multiplicity computation, without charging its representation dimension or assuming #P!=FP. It does not give a lower bound for Boolean support, or for an arithmetic algorithm whose output only agrees with F_K on Boolean inputs but uses nonmultilinear powers or cancellation.

### G41 — exact Boolean trace obstruction, including arbitrary shared DAGs

Let C be an arbitrary monotone AND/OR circuit computing S_m with size s. Replace AND by formal multiplication, OR by formal addition, Boolean constants by 0,1. The resulting nonnegative polynomial P_C agrees in SUPPORT on total Boolean inputs; it need not equal F_K or be multilinear. Every monomial's support is an accepting input (set its variables 1), hence has cardinality >=K. Therefore the degree-K homogeneous part is squarefree, and each of its monomials corresponds to a true central input. Conversely a true central input t appears in that degree-K part iff C has some accepting formal parse monomial of degree K, equivalently a trace that uses each of the K coordinates exactly once. It is legal for an arbitrary monotone circuit to lack such a trace.

Perform the same degree-K extraction, outside-active restriction and degree-b_q extraction as G40. The result has nonnegative coefficients, and support a subset X of W_q's monomials. Indeed every degree-K surviving monomial is a true central input, with dummy singleton constraints forcing dummies zero; at active degree b_q its active support must be exactly a minterm. Conversely every central true input with active support exactly P_x, dummies forced by singleton restrictions, and a squarefree accepting trace contributes that original monomial. In particular this applies to the canonical padding E(P_x) from G38. G39's subset bound yields

    |X| / 2^q <= poly(N_m)*(s+1) * 2^(-r0(q)).

This also holds if X is empty. Thus if central sandwich circuits have polynomial size, all but an exp(-Omega(q)) fraction of original assignments x have NO squarefree accepting trace at their padded minterm, in fact at ANY central completion of P_x respecting the dummy singleton zeros. This is a necessary property of hypothetical small circuits, not a contradiction. Conversely any family of correct central-sandwich monotone circuits in which a non-negligible exp(-o(q)) fraction of original padded minterms has a squarefree trace must have exponential size. Syntactically multilinear monotone circuits (disjoint variable supports at every AND) meet the trace requirement automatically; indeed the more general read-1 property on just these padded positives suffices. This bound is on actual central slice, not a transfer of the ordinary CLIQUE bound through the forbidden projection G36.

Decisive width-two control: all proofs G38–G41 apply with w=2 (K>=b, same dummy pair deficit >=q^2=N_q/2, central padding valid); the G39 formal polynomial is exponentially hard in q, yet G17's monotone reachability decision and the cheap sandwich gate wrapper give polynomial-size monotone circuits for width-two central sandwich. Therefore these small circuits necessarily bypass formal squarefree arithmetic traces on almost every padded minterm. One cannot infer a universal cheap trace-preserving normalization, even for a tractable SAT subclass. Absorption and multiplicative idempotence on Boolean inputs are essential legal shortcuts. G39/G40 do not prove that exact counting or recovering the attachment's #P-hard coefficient is necessary for decision; they directly separate the specified positive formal arithmetic resource model from Boolean support, and G41 states precisely what remains missing. Repeated variable use alone cannot be charged to time (e.g. x AND x=x, shared repeated squaring in formal arithmetic). No claim that width-three circuits have more unavoidable repeat work than width-two.

### Executed local regression (exact Python integers, no CI/kernel)

Executed 14,246 balanced scope partitions (width 2/3, m=2..4, including every balanced partition), checking one union covers all m, shared-coordinate lower bound, and exact fibre cardinalities. Executed 436 central-padding instances for q=1..5 (all 260 small original inputs, 40 seeded plus all minterms for each q=3..5), checking weight, dummy singleton zeros and complete witness-set equivalence. Independently enumerated all 70 K-subsets in the small m=2,q=1 central formal lift; extracted coefficients equal 3 times W_1. No actual general circuit synthesis or unrestricted asymptotic numerical extrapolation claimed. Reproducer:

```python
from itertools import combinations
from math import comb
from collections import defaultdict
from random import Random
def scopes(m,w=3):return [I for j in range(1,min(w,m)+1) for I in combinations(range(m),j)]
def pattern(x,I):return sum(((x>>i)&1)<<j for j,i in enumerate(I))
def b(m,w=3):return len(scopes(m,w))
checks=0
for w in (2,3):
 for m in range(2,5):
  S=scopes(m,w);B=len(S);allv=set(range(m))
  for z in range(1<<B):
   d=z.bit_count()
   if 3*d<B or 3*d>2*B:continue
   A=set().union(*(set(I) for i,I in enumerate(S) if z>>i&1))
   C=set().union(*(set(I) for i,I in enumerate(S) if not(z>>i&1)))
   R=A&C
   assert A==allv or C==allv
   assert 3*len(R)>=m
   f=defaultdict(int)
   for x in range(1<<m):f[pattern(x,sorted(R))]+=1
   assert len(f)==1<<len(R) and set(f.values())=={1<<(m-len(R))}
   checks+=1
assert checks==14246
rng=Random(369);count=0
for q in range(1,6):
 m=4*(q+1);S=scopes(q)
 C=[(I,p) for I in S for p in range(1<<len(I))];ix={c:i for i,c in enumerate(C)}
 L=[(I,p) for I in scopes(m) for p in range(1<<len(I))];J={c:i for i,c in enumerate(L)}
 B=0;slack=[]
 for j,(I,p) in enumerate(L):
  if I[-1]<q:continue
  if all(not(p>>k&1) for k,i in enumerate(I) if i>=q):B|=1<<j
  elif len(I)>1:slack.append(j)
 K=len(L)//2;n=len(C);e=K-B.bit_count()-n
 assert 0<=e<=len(slack)-n
 const=B|sum(1<<j for j in slack[n:n+e])
 P=[sum(1<<ix[I,pattern(x,I)] for I in S) for x in range(1<<q)]
 P2=[sum(1<<J[I,pattern(x,I)] for I in scopes(m)) for x in range(1<<q)]
 inputs=range(1<<n) if q<=2 else [rng.getrandbits(n) for _ in range(40)]+P
 for t in inputs:
  u=const|sum(1<<(J[c] if t>>i&1 else slack[i]) for i,c in enumerate(C))
  assert u.bit_count()==K and all(not(u>>J[((i,),1)]&1) for i in range(q,m))
  assert [x for x,p in enumerate(P) if t&p==p]==[x for x,p in enumerate(P2) if u&p==p]
  count+=1
assert count==436
q=1;m=2;L=[(I,p) for I in scopes(m) for p in range(1<<len(I))]
K=len(L)//2;bq=b(q);bm=b(m);ix={c:i for i,c in enumerate(L)}
P=[sum(1<<ix[I,pattern(x,I)] for I in scopes(m)) for x in range(1<<m)]
active=sum(1<<i for i,(I,p) in enumerate(L) if I[-1]<q)
forbidden=1<<ix[((1,),1)];coef=defaultdict(int);checked=0
for S in combinations(range(len(L)),K):
 z=sum(1<<i for i in S);w=sum(z&p==p for p in P)
 if not(z&forbidden) and (z&active).bit_count()==bq and w:coef[z&active]+=w
 checked+=1
T=len(L)-active.bit_count()-1;kappa=comb(T-(bm-bq),K-bm)
assert checked==70 and kappa==3
assert dict(coef)=={1<<ix[((0,),p)]:kappa for p in (0,1)}
```

### Consolidated endpoint ledger

| Gate | Deliverable | Status |
|---|---|---|
| G38 | canonicalCentralSliceWitnessProjection | derived and checked, R50/G32, Berkowitz–Valiant |
| G39 | balancedScopeProductCoverBound / witnessFormalArithmeticExponential | derived and checked geometric lemmas; arbitrary nonnegative arithmetic DAG |
| G40 | centralMultiplicityFormalArithmeticLowerBound | derived via positive homogeneous extraction; R51/R52 |
| G41 | centralSquarefreeTraceFractionBound / widthTwoTraceShortcut | derived; restricted central sandwich lower bound and decisive cheap-width-two control |
| N4/G12a | unrestrictedSerialCharge | OPEN: genuine width-three-specific resource obstruction, permit arbitrary Boolean idempotence/absorption and signed arithmetic |
| N5/G12c | canonicalCentralSliceUnrestrictedSuperpoly | OPEN; G38 equivalence stronger nonuniform route |
| N6 | originalClayTransport | conditional #1040 terminal / #1129 costed coverage; direct uniform N4/N5 stays OR |

Highest-alpha Aristotle BIDI: do not try to lift G39 by generic arithmetic normalization: G41's tractable width-two control explicitly rules that out. The central-slice problem is whether width-three-specific correlations make the unrestricted repeated-variable/absorption shortcuts expensive in total work, not whether an exponential formal polynomial or #P-hard coefficient exists. Investigate Boolean product-support overlap at a balanced scope cut (which can duplicate shared scope coordinates and permit supersets on upper weight layers) and require a charge that accounts for those overlaps without ruling out G17 reachability. Keep direct uniform-machine route and the G37 reported subexponential algorithm audit alive; no assumption of ETH or a new certification prerequisite. No unrestricted separation claimed.


## 21. P0-G42–G44 — conditioned repeat traces, paired central slice and the sharp linear-repeat shortcut (2026-11-24)

Controlling endpoint remains literal Clay P vs NP. Inputs: attached G38–G41 and Langlands R57–R60 (reported #1549/#120 heads 75fe88e1e1d8 / b0c59146024c). Only P0 roadmaps modified. Both read live at e25853446aac / e0e150cde49a, common blob 4ace4df1bf48d96d9dd51ac2d125d609762ea761. Reuse G13 original selector scopes, G16/G17 binary control, G26 shared inversion, G32/G38 central padding, G39/G41 balanced arithmetic extraction, G28/G33 parity compression, #1291 signed residuals, #1006 FactorsThrough/self-reduction, #123 JMD lowering, #1546 sharing, #1129 standard-machine coverage, #1040 terminal, #1474/#1502 reductions, #607/#678 Aristotle. The formal polynomial / Boolean support distinction and classical slice-function and arithmetic-decomposition attribution remain as in sections 19–20. New derivations are internal mathematical arguments, not independent native-kernel proofs or claims of literature novelty.

### G42 — recover squarefree traces by conditioning, not prohibiting reuse

Let C be any correct monotone Boolean circuit for central sandwich S_m, gate size s; replace AND by formal product and OR by formal sum as in G41. Denote resulting nonnegative polynomial P. Every monomial support is a true input, so has at least K coordinates. For a set R of r<=K distinct input coordinates define

    E_R(P) = (prod_{i in R} t_i) * [homogeneous degree K-r] P|_{t_i=1 for i in R}.

Every surviving conditioned monomial has support size at least K-r, since adjoining R produces a true input of C. With formal degree exactly K-r, it must be squarefree, disjoint from R. Thus E_R is squarefree homogeneous degree K, and its monomials are all true central inputs. If a true central input L admits a formal accepting trace whose repeated-variable set is contained in R subset L, that trace contributes the monomial of L to E_R. This remains true with arbitrary shared DAGs, because only the formal polynomial is used and no parse-tree expansion is charged to the circuit. Homogeneous extraction has O((s+1)(K+1)^2+N) gate overhead by truncated convolution.

Sum E_R over all R of cardinality r. Any positive central L with a trace using at most r distinct repeated variables is represented (extend the repeated set to r coordinates inside L). Use the same dummy singleton zeros and outside-active substitution as G40/G41, then extract active degree b_q. Result is supported on a subset X of W_q's original monomials. In particular it includes every x whose canonical padded minterm E(P_x) has such a trace, or even any central completion of P_x respecting dummy singleton zeros with such a trace. G39 gives

    fraction of such x <= poly(N)*(s+1)*binom(N,r)*2^(-r0(q)),

where r0(q)>=q/3 from G39, N=Theta(q^3), q original assignment count, m=4(q+1). Thus for polynomial s, r<=epsilon*q/log N with sufficiently small fixed epsilon gives exponentially small fraction. This strengthens G41 beyond r=0, still only a necessary property of small circuits.

### G43 — exploit original scope labels to obtain linear, rather than q/log N, repeat necessity

Use exactly G38's canonical central padding. Its active input t has n=N_q bits, paired slack rails u_j are 1-t_j in the encoding; they occupy distinct inactive selector coordinates. Other coordinates are fixed constants of total weight K-n. Fix all these constants in C, leaving t,u independent. In particular all forbidden dummy singleton patterns stay zero, and all fixed compatible patterns involving dummies remain one. Because every u_j is an inactive coordinate, original SAT semantics is G_q(t) for ALL t,u, not just paired encodings. The restricted circuit C' therefore computes the exact monotone two-rail sandwich

    J_q(t,u) = [|t|+|u|>n] OR ([|t|+|u|=n] AND G_q(t)).

This is a same-object restriction, no added gates. A canonical positive encoding for minterm P_x is v_x=(1_Px,1-1_Px), of weight n. For any trace at v_x define its source repeat set T_trace as the union of original assignment scopes I of repeated rail variables t_(I,p) or u_(I,p). Repetitions of fixed constants in C have already been eliminated by restriction.

For T subset [q] of size h and z in F2^T, define R(T,z) as follows: for each original scope I contained in T, retain exactly the selected rail for each of its pattern coordinates. That is t_(I,z|I) and all u_(I,p) for p != z|I. Then |R|=N_h and R(T,x|T) subset support(v_x). If T_trace subset T, the mask contains every repeated rail of that trace. Apply G42 to C' with threshold n and mask R; the result is a squarefree polynomial supported on true layer-n inputs of J_q. Substitute all u rails by 1 and extract homogeneous active degree b_q. Each remaining monomial is an actual original witness monomial: its active support has size b_q, and G_q(t)=1 requires one full minterm. Any v_x with a trace satisfying T_trace subset T contributes its W_q monomial.

Sum over all masks with |T|=h. There are exactly 2^h binom(q,h) masks (or at most this many distinct masks). If gamma_h is the fraction of original assignments x with any accepting trace at v_x whose source repeat set has size <=h, the preceding extraction and G39 prove

    gamma_h <= poly(N)*(s+1)*2^h*binom(q,h)*2^(-r0(q)).

For h=floor(q/32), binary entropy H_2(1/32)+1/32 < 1/3, so any polynomial s implies gamma_h <=2^(-Omega(q)). This is a linear original-coordinate repeat-span requirement on almost every canonical padded minterm, and implies Omega(q) distinct repeated rail variables (each rail involves at most 3 source variables). It does not count repetitions of dummy constants, expanded multiplicities, or separate costs per trace. The conditioning masks are chosen independently of the original execution; their construction overhead is charged in the comparison arithmetic circuit. Width-two also satisfies this theorem, so it is not a width-three-specific lower bound. No inference that a single gate cannot serve many such repeats.

### G44 — explicit sound linear-size underapproximation on the SAME canonical minterms

The following construction establishes why G43 alone cannot pay N4. For the independent active/paired rails t,u define

    A(t,u)=AND_I OR_p [
        t_(I,p) AND (AND_{r != p} u_(I,r))
                 AND (AND_{i in I} t_({i},p_i))
    ].

Each scope has <=8 patterns; all operations bounded arity or reducible to constant-size gates per pattern. Size O(n). Any accepting formal trace selects one positive pattern rail and the other negative rails for every scope, hence contains at least n distinct coordinates, one per input pair. If the total rail weight is exactly n, every pair contains exactly one selected rail; for each scope the chosen pattern is its unique available positive pattern. The singleton consistency factors ensure that these unique patterns agree with a single original assignment. Thus A=1 on the layer n iff (t,u)=(P_x,1-P_x) for some x. In particular A<=J_q on ALL inputs: below layer n A cannot accept, on layer n it accepts only original minterms, above layer n J_q=1. This is exact soundness, not a local overapproximation.

At v_x choose the unique pattern p=x|I in every scope. The resulting trace uses each selected rail once except the q selected singleton positive rails, which may be repeated by the consistency factors. Exactly those q rails repeat (including the singleton's own support factor). Thus repeat-coordinate count is q, source repeat union is all q coordinates. This is O(q) distinct repeated rails, not a claim about the expanded multiplicity total.

Lift A to the actual central sandwich S_m by ANDing it with every fixed-one coordinate of G38's padding (K-n coordinates, disjoint from rails). Leave all other coordinates unrestricted. Every accepting input has weight >=K. If weight=K, no other coordinates can be 1, the paired rails have weight n, and the exact minterm property supplies an original assignment extending by dummy zero. If weight>K, S_m accepts automatically. Therefore the lifted checker is a globally sound monotone underapproximation of S_m, size O(N), covering EVERY canonical padded minterm. Its chosen accepting traces on those inputs have exactly q repeated rail coordinates; fixed ones appear once. If C is any correct central circuit, ORing this checker into C preserves exact output, adds only O(N) gates, and ensures those traces on all canonical padded minterms. So a proposed lower bound demanding more than q repeated coordinates there cannot follow from correctness alone at polynomial overhead, unless the general circuit lower bound has already been proved. G43's linear scale is tight up to constants for this selected positive family. Crucially the checker is not a circuit computing the whole sandwich: for example at a paired encoding of the full active selector t=1, u=0, the target accepts but A rejects as long as some scope has >=2 patterns. It accepts minterms, not all satisfying active selectors and not all true central inputs.

This isolates a precise hard operation: decide global existence of a compatible minterm on general central inputs, including paired encodings of nonminimal active selectors, not merely recognize canonical encodings of witnesses or count repeated coordinates there. The low-repeat obstruction is real but the same-object checker gives its exact shortcut boundary. No generic normalization from Boolean circuits to formal arithmetic can hold (G41 width-two control). No claim of a lower bound for arbitrary Boolean support.

### Affine and signed contraction reconciliation

R57/R58's affine-hull compression, primal/dual character contraction and independent block sum are admissible upper-bound methods. In particular affine rank/nullity and number of independent original coordinates cannot themselves charge time. Arbitrary affine substitution may increase clause width; keep the original bounded-width formulas or charge a re-encoding before applying any fixed-width SAT algorithm. R59/R60's interpolation recovery has signed coefficients; its support-only counterexample H_0(T)=T, H_1(T)=1+T is an additional exact FactorsThrough obstruction, not a work lower bound. The previously reported subexponential #SAT algorithm in G37/R60 remains an external theorem boundary, not independently proved here. No reliance on ETH or on exponential search necessity. No new Langlands or Monster task.

### Executed local regression (Python integer masks, no CI/kernel)

Executed 13,884 paired layer inputs: exhaustive q=1 (6) and q=2 (12,870), plus q=3 (8 planted canonical positives and 1,000 seeded layer samples); independently compared the G44 checker with the exact property u=1-t and t=P_x. All 14 canonical positive traces had exactly the asserted q repeated singleton rails. Executed 39 source-coordinate mask/homogeneous extraction comparisons on explicit expansions of the original G27 H checker for q=1,2,3 (2,16,4096 formal terms respectively). This independently verifies the conditioning principle on those small layer checkers, not an exhaustive test of all arbitrary circuits. Also checked the central slack inequalities for q=1..20. All passed. Reproducer:

```python
from itertools import combinations
from collections import Counter
from random import Random
from math import comb

def carrier(q):
    S=[I for j in range(1,4) for I in combinations(range(q),j)]
    C=[(I,p) for I in S for p in range(1<<len(I))]
    ix={v:i for i,v in enumerate(C)}
    def pat(x,I):return sum(((x>>i)&1)<<j for j,i in enumerate(I))
    P=[sum(1<<ix[I,pat(x,I)] for I in S) for x in range(1<<q)]
    return S,C,ix,P,pat

def check_pairs(q):
    S,C,ix,P,pat=carrier(q);n=len(C);full=(1<<n)-1
    def checker(t,u):
        return all(any(t>>ix[I,p]&1 and
            all(u>>ix[I,r]&1 for r in range(1<<len(I)) if r!=p) and
            all(t>>ix[(i,),p>>j&1]&1 for j,i in enumerate(I))
            for p in range(1<<len(I))) for I in S)
    count=pos=0
    if q<=2:
        inputs=((z&full,z>>n) for J in combinations(range(2*n),n)
                for z in [sum(1<<j for j in J)])
    else:
        rng=Random(369)
        inputs=[(t,full^t) for t in P]+[(z&full,z>>n)
            for _ in range(1000)
            for z in [sum(1<<j for j in rng.sample(range(2*n),n))]]
    for t,u in inputs:
        v=checker(t,u)
        assert v==(u==full^t and t in P)
        pos+=v;count+=1
    for x,t in enumerate(P):
        u=full^t;assert checker(t,u)
        trace=[]
        for I in S:
            p=pat(x,I);trace.append(ix[I,p])
            trace.extend(n+ix[I,r] for r in range(1<<len(I)) if r!=p)
            trace.extend(ix[(i,),p>>j&1] for j,i in enumerate(I))
        counts=Counter(trace)
        assert set(counts)=={i for i in range(n) if t>>i&1}|{n+i for i in range(n) if u>>i&1}
        assert {i for i,k in counts.items() if k>1}=={ix[(i,),x>>i&1] for i in range(q)}
    return count,pos,len(P)
assert [check_pairs(q) for q in (1,2,3)]==[(6,2,2),(12870,4,4),(1008,8,8)]

def masks(q):
    S,C,ix,P,pat=carrier(q);b=len(S);terms=[()]
    for I in S:
        F=[tuple([ix[I,p]]+[ix[(i,),p>>j&1] for j,i in enumerate(I)])
           for p in range(1<<len(I))]
        terms=[a+f for a in terms for f in F]
    checks=0
    for Tbits in range(1<<q):
        T={i for i in range(q) if Tbits>>i&1}
        for z in range(1<<q):
            if z&~Tbits:continue
            R={ix[I,pat(z,I)] for I in S if set(I)<=T}
            out=set()
            for a in terms:
                rem=[i for i in a if i not in R]
                if len(rem)==b-len(R):
                    assert len(set(rem))==len(rem)
                    t=sum(1<<i for i in set(rem)|R)
                    assert t in P;out.add(t)
            expected={p for x,p in enumerate(P) if
                all(p>>i&1 for i in R) and
                all(ix[(i,),x>>i&1] in R for i in range(q))}
            assert out==expected
            checks+=1
    return checks,len(terms)
assert [masks(q) for q in (1,2,3)]==[(3,2),(9,16),(27,4096)]

for q in range(1,21):
    m=4*(q+1);d=m-q
    b=lambda x:sum(comb(x,j) for j in (1,2,3))
    N=lambda x:sum((1<<j)*comb(x,j) for j in (1,2,3))
    B=sum(comb(q,l)*comb(d,j-l)*(1<<l)
          for j in (1,2,3) for l in range(j))
    K=N(m)//2
    assert B+N(q)<=K<=N(m)-d
    assert B<=K-b(q)<=N(m)-N(q)-d
```

### Consolidated endpoint-first ledger

| Gate | Deliverable | Status |
|---|---|---|
| G42 | conditionedHomogeneousRepeatTraceExtraction | derived; general central circuit, polynomial cost per mask |
| G43a | exactPairedRailCentralRestriction | derived; same-object G38 |
| G43b | sourceRepeatMaskCover / linearRepeatSpanNecessity | derived; conditional on polynomial size; G39/G42 |
| G44 | canonicalMintermSoundPairedChecker / linearRepeatShortcut | derived and locally tested; explicit O(N) sound underapproximation; NOT complete decision |
| N4/G12a | unrestrictedSerialCharge | OPEN: actual total work on general active selector inputs, permit repeat/absorption, affine and signed contraction, shared interpolation |
| N5/G12c | canonicalCentralSliceUnrestrictedSuperpoly | OPEN; G38 nonuniform equivalence; direct uniform route remains OR |
| N6 | originalClayTransport | conditional #1040 terminal / #1129 standard-machine coverage |

Aristotle BIDI: G44 proves that studying only canonical padded minterm acceptance, even with a stronger linear repeat-span theorem, cannot close the unrestricted endpoint by demanding more repeat coordinates. Shift the mathematical discriminator to nonminimal selectors on the paired slice and require globally correct support, not just witness recognition. Analyze actual signed arithmetic/interpolation costs from the reported G37/R59 algorithm and target-specific width-three correlations; no inference from #P-hard exact multiplicity, independent rank, trace size or restricted circuit complexity alone. No new certification prerequisite; no unconditional P!=NP claim.


## 22. P0-G45–G48 — globally rigid locally full ternary constraints and the exact global-compression endpoint (2026-11-24)

Controlling endpoint: literal Clay P vs NP, no Langlands/Monster endpoint work. Inputs: user G42–G44 and Langlands R64–R67 (reported #1549/#120 d70f6ff3ec7f / ec3e8df4f153). Read both original pasted files in the local container; read both P0 roadmaps live at cbc4dd1496c0 / 003733c92e00, common blob 85df78165b31c999e23568155b94480c517600bf. Reuse G13 original selector carrier, G16 median and pair-hull obstruction, G22/G30 monotone CLIQUE projection, G25 actual NOT count, G28/G33/G34 local unary and signed component contraction, G38/G43 central paired encoding, G44 cheap minterm checker, and attached R57 affine-hull contraction. Existing #1006 FactorsThrough/decision-to-witness and ConsumerFibreRepairExact, #1291 signed indexed residual, #123 JMD lowering, #1546 shared DAG, #1474/#1502 Karp/Cook-Levin, #1129 standard machine, #1040 terminal, #607/#678 Aristotle remain source owners/consumers. No new native theorem attachment or kernel check claimed. This packet shifts from accepting traces to actual nonminimal general selectors and asks what local contraction can and cannot remove. No novelty claim about general CSP rigidity or reductions to restricted 3-SAT.

### G45 — explicit constant-size, globally unique, locally full forcing gadget

Let Z have six Boolean variables indexed 0..5. List the 20 triples I in lexicographic order; on each triple forbid exactly one pattern, encoded little-endian by the digit of

    16763747126132141175

in that order. All digits nonzero, hence all-zero assignment allowed. Exact enumeration of all 64 assignments proves it is the unique witness (reproducer below); this finite exhaustive proof suffices for a fixed gadget. Each local triple relation has 7 of 8 patterns. Every unary and binary projection is full, and every nonzero linear functional on F2^3 takes both values (each of its two fibres has size 4 before one deletion). Therefore every local affine hull is full. All remaining scopes, including unary and binary scopes, are unrestricted. G28 unary domain reduction, G33 pair parity contraction, and R57 local affine equations discover no fixed coordinate or equality, yet global solution space is {0}. The exact joint affine hull has dimension zero rather than six. More generally any two disjoint copies of this gadget force all their coordinates zero; add a cross-block clause forbidding 000 to obtain UNSAT, or forbid 111 on the same scope to retain the unique zero witness. These two examples have identical scope cardinalities, local unary/pair projections and local affine hulls, but distinct global decision. This is a precise FactorsThrough collision for that observer, not an assertion of large computational work: the gadget itself is constant size.

### G46 — parsimonious locally-full compiler, with arbitrary selector inputs and fixed-weight option

Define promise L_m: all unary and binary selector patterns available, and each ternary scope either has all 8 patterns or exactly 7. In particular every local unary and pair projection and every affine hull is full; every assignment on at most two variables extends to any third variable while respecting all constraints on those three variables (not a claim of global 3-consistency closure beyond these original scopes).

For arbitrary input selector on q variables, list its N_q possible nonempty width<=3 clauses C_j. Introduce one distinct new occurrence variable a for each literal occurrence in this whole list, whether or not the clause is selected. Add one G45 zero block Z, disjoint from all original and occurrence variables. For every occurrence variable a corresponding to original x, add the two distinct 3-clauses

    (not x OR a OR z_0), (x OR not a OR z_1).

The zero gadget forces z_0=z_1=0 globally, so exactly a=x. For each original clause, use its occurrence copies with the same literal signs, padding a clause of width two with z_0 and a unit with z_0,z_1. Include this new width-three clause iff the original clause is selected. Its triple scope is unique: copies are private to each original clause, the equality triples contain one original and one copy, and zero-block triples contain neither. All clauses have three distinct variables, with at most one clause on any triple. Every target selector coordinate is constant or one original absent-clause bit t_j. Thus this is an explicit monotone coordinate projection into L_m, m=q+6+sum_j |C_j|=O(N_q). All original witnesses extend uniquely by copied values and zero gadget, and every target witness restricts to an original one. W_m(E(t))=W_q(t) exactly. General 3-CNF input with any clause list can use the same compiler with O(number of literal occurrences) variables, including repeated original scopes (normalize literals/tautologies first; empty clause can be mapped to the fixed UNSAT cross-block gadget).

Fixed-weight option: for each C_j add an alternative inert width-three clause on {its first occurrence a,z_2,z_3}, namely (a OR not z_2 OR z_3), selected iff C_j is NOT selected. Since z_2=0 globally this constraint is always satisfied. Scope distinct from all others; even for a unit main scope {a,z_0,z_1} is different. Now every input has exactly 20+2*sum_j|C_j|+N_q forbidden patterns, and exact witness count unchanged. The two conditional available bits are t_j and 1-t_j, so this fixed-weight reduction is a general Boolean projection, NOT monotone. It places the hard instances at one explicitly prescribed weight near the full selector layer; no claim they lie at the central weight or in the near-minterm tractable band. Combining with G38's separate central embedding preserves all witness counts but that embedding does not preserve local fullness of all the added scopes.

Consequences: selector decision on L_m is NP-complete (and exact counting #P-hard by the parsimonious projection from #3SAT); the same holds with the above fixed-weight promise along the compiler lengths. All G28/G33/R57 contractions return the maximal local ambiguity/rank residual even on these instances. This is a target-specific width-three hard core after the previously used local contraction stages. It does not show no other global or arithmetic algorithm can solve the core in polynomial time.

### G47 — retain the strongest monotone bound on the locally-full core without variable blowup

The generic G46 projection from full q-variable selector adds O(N_q) variables and would weaken G30's exponent. Instead apply the local-full compiler directly to G22's original CLIQUE construction: n vertex-choice bits, O(n) fixed threshold circuit auxiliaries and O(n) fixed width<=3 clauses from bounded-fanin Tseitin encoding. Split occurrences and add zero block ONLY for the fixed threshold clauses, adding O(n) variables. For each graph pair {i,j} keep the direct conditional clause (not x_i OR not x_j OR z_0), selected iff the original edge is absent. Each conditional triple distinct and contains two original vertex variables, whereas every fixed compiler triple with an original variable also contains a private copy. All are in L_m, m=Theta(n), and number of forbidden coordinates is O(n^2), even on negative graphs. Projection maps each conditional absent bit directly to positive graph edge; no gates or NOTs added. Witness bijection to chosen cliques of size >=k, with fixed auxiliary gates uniquely determined by choice bits. Thus the external Błasiok–Meierhöfer CCC 2025 Corollary 5 (https://drops.dagstuhl.de/storage/00lipics/lipics-vol339-ccc2025/html/LIPIcs.CCC.2025.4/LIPIcs.CCC.2025.4.html, rechecked this turn) transfers exactly as G30: any AND/OR circuit correct on the locally-full promised inputs (even with at most O(m^2) forbidden coordinates) has size >=2^Omega(N^(5/36) log N) on the chosen hard subsequence, exponent can approach 1/6 from below by G30. Same monotone projection preserves the G25 limited actual-NOT lower bound on its own hard lengths. This is a restricted-model gate lower bound on a nonminimal locally-full promise family, not the central sandwich: G36 forbids the direct monotone slice projection, and the fixed-weight variant of G46 uses complements. No unconditional unrestricted separation.

### G48 — exact global affine compression is Clay-equivalent, even on satisfiable locally-full formulas

Let F(x) be arbitrary width<=3 CNF on q variables. Introduce flag b and enforce b=>F(x) via clauses (not b OR C). For a three-literal C=(l1 OR l2 OR l3), introduce fresh a with a=l1 OR l2, encoded by (not l1 OR a),(not l2 OR a),(l1 OR l2 OR not a), and (not b OR a OR l3). For shorter C, no extra bit needed. This is width<=3 and all auxiliaries uniquely determined for each (x,b). Now apply G46 with all clauses selected. Result is satisfiable (every x extends at b=0) and belongs to L_m. Exact counts on flag fibres:

    W(b=0)=2^q, W(b=1)=W(F).

Hence the distinguished coordinate b is globally forced zero iff F is UNSAT. Deciding whether b can take value one is NP-hard, even given a known satisfying witness at b=0 (construct from x=0, the gate definitions and G46 copies). Deciding globally forced zero is coNP-hard under the same promise. Computing the exact global affine hull, or even its projection to this single flag coordinate, would solve original SAT. Conversely if P=NP, compute a basis of the true affine hull in polynomial time: find one witness by SAT self-reduction; iteratively find a witness outside current affine span by adding a polynomial circuit for violation of at least one of its defining linear equations (XOR and OR gates, encoded with uniquely defined Tseitin auxiliaries). Each successful query increases affine dimension, so at most m+1 iterations, and termination certifies that all witnesses lie in the current span. Unsatisfiable case detected by initial query. Therefore polynomial-time exact global affine-hull construction on satisfiable locally-full promise instances is equivalent to P=NP. The one-bit global support query suffices for the hard direction; no counting assumption. This explains precisely why replacing local affine contraction by exact joint affine contraction cannot be assumed polynomial as an enabling lemma. It is an equivalent endpoint, not a proof of lower bound. The flag construction is distinct from original signed occurrence counts and allows all unrestricted computations.

### Actually executed local regression (exact integer arithmetic, no CI/kernel)

Local Python /tmp/p0_global_rigidity.py: 64 assignments of G45 checked, unique zero; 20 local scopes checked for full pair projections and all 7 nonzero linear directions. All original selectors q=1,2 (260), both ordinary and fixed-weight compilers (520 total), verified by independent exact DPLL model counting of the full emitted formula, with no forced-zero assumption passed to DPLL; 25,804 emitted clauses checked individually for width, unique triple scope and full projections. 36 seeded flag instances q=1,2,3, both flag fibres (72 model-count comparisons), plus local checks on all emitted flag constraints; total compiler local checks including flags 28,700. All passed. The G47 asymptotic transport follows from explicit construction and external theorem, not a new graph-family execution or numerical extrapolation. Reproducer core:
```python
from itertools import combinations,product
from functools import lru_cache
from collections import Counter
from random import Random
D='16763747126132141175'
F0=[tuple((i,1-(int(p)>>j&1)) for j,i in enumerate(I))
    for I,p in zip(combinations(range(6),3),D)]
def brute(q,F):
 return [x for x in range(1<<q) if all(any((x>>i&1)==v for i,v in C) for C in F)]
assert brute(6,F0)==[0]
def local(F):
 seen=set()
 for C in F:
  assert len(C)==3 and len({i for i,v in C})==3
  I=tuple(sorted(i for i,v in C));assert I not in seen;seen.add(I)
  p=sum((1-dict(C)[i])<<j for j,i in enumerate(I));A=set(range(8))-{p}
  for j,k in combinations(range(3),2):assert {(a>>j&1,a>>k&1) for a in A}==set(product(range(2),repeat=2))
  for h in range(1,8):assert {(a&h).bit_count()%2 for a in A}=={0,1}
 return len(F)
assert local(F0)==20
def compile_(q,clauses,t,balanced=False):
 z=list(range(q,q+6));F=[tuple((q+i,v) for i,v in C) for C in F0];m=q+6
 for j,C in enumerate(clauses):
  assert 1<=len(C)<=3
  cc=[]
  for i,v in C:
   a=m;m+=1;cc.append((a,v))
   F.extend([((i,0),(a,1),(z[0],1)),((i,1),(a,0),(z[1],1))])
  if not(t>>j&1):F.append(tuple(cc+[(z[k],1) for k in range(3-len(cc))]))
  elif balanced:F.append(((cc[0][0],1),(z[2],0),(z[3],1)))
 return m,F
@lru_cache(None)
def count(F,free):
 if not F:return 1<<free.bit_count()
 if any(not C for C in F):return 0
 def sub(i,v):return tuple(sorted(set(tuple(l for l in C if l[0]!=i) for C in F if (i,v) not in C)))
 for C in F:
  if len(C)==1:
   i,v=C[0];return count(sub(i,v),free^(1<<i))
 freq=Counter(i for C in F for i,v in C);i=max(freq,key=freq.get)
 return sum(count(sub(i,v),free^(1<<i)) for v in (0,1))
def cnt(m,F):return count(tuple(sorted(set(tuple(sorted(C)) for C in F))),(1<<m)-1)
def clauses_(q):
 return [tuple(zip(I,p)) for w in range(1,min(3,q)+1) for I in combinations(range(q),w) for p in product(range(2),repeat=w)]
checks=localchecks=0
for q in (1,2):
 C=clauses_(q);L=sum(map(len,C))
 for t in range(1<<len(C)):
  expected=len(brute(q,[c for j,c in enumerate(C) if not t>>j&1]))
  for bal in (False,True):
   m,F=compile_(q,C,t,bal);localchecks+=local(F)
   if bal:assert len(F)==20+2*L+len(C)
   assert cnt(m,F)==expected;checks+=1
assert (checks,localchecks)==(520,25804)
def flag_formula(q,F):
 b=q;m=q+1;A=[]
 for C in F:
  if len(C)<=2:A.append(((b,0),)+C)
  else:
   a=m;m+=1;l,r,s=C
   A.extend([((l[0],1-l[1]),(a,1)),((r[0],1-r[1]),(a,1)),(l,r,(a,0)),((b,0),(a,1),s)])
 return m,A,b
rng=Random(369);fc=0
for q in (1,2,3):
 C=clauses_(q)
 for trial in range(12):
  F=rng.sample(C,rng.randrange(len(C)+1));m,A,b=flag_formula(q,F)
  mm,B=compile_(m,A,0);localchecks+=local(B)
  assert cnt(mm,B+[((b,0),)])==1<<q
  assert cnt(mm,B+[((b,1),)])==len(brute(q,F))
  fc+=1
assert (2*fc,localchecks)==(72,28700)
```

### Endpoint-first ledger

| Gate | Deliverable | Status |
|---|---|---|
| G45 | locallyFullGloballyUniqueTernaryGadget / localObserverCollision | exact finite construction and proof |
| G46 | parsimoniousLocallyFullSelectorProjection / fixedWeightLocallyFullHardness | derived and exact DPLL checks |
| G47 | locallyFullSparseForbiddenMonotoneLowerBound | G30 external theorem via compressed projection, restricted AND/OR; G25 separate limited NOT |
| G48 | globalForcedFlagHardness / exactGlobalAffineHullClayEquivalence | derived and flag checks, original decision-to-witness consumer |
| N4/G12a | unrestrictedSerialCharge | OPEN: arbitrary global shortcuts including signed/affine/character/interpolation; no local observer invariant suffices by itself |
| N5/G12c | unrestrictedSuperpolynomialGrowth | OPEN: full locally-full promise, canonical central slice, or direct uniform route |
| N6 | originalClayTransport | conditional #1040 / #1129 coverage |

Aristotle BIDI: the exact new residual core is locally full yet globally rigid. No need to invent more local affine/median measurements or require expensive count extraction; the one-bit global support query is already equivalent to Clay decision. Next examine global contraction algorithms on this actual core, including the reported 2026 subexponential tensor contraction (G37; not independently audited in this packet). A bound merely on local projections, cardinalities, raw rank, repeat counts, or closure stages would fail to charge arbitrary standard-machine work; the global affine-hull equivalence is an alternative mathematical endpoint, not an established lower bound. No extra phase, no CI/kernel detour, no P!=NP claim.


## 23. P0-G49–G52 — exact joint selector contraction, Smith-channel amplification and consumer-specific resource boundary (2026-11-24)

Controlling endpoint: literal Clay P vs NP, P0-C/D. Inputs: attached G45–G48 and Langlands R71–R74 (reported #1549/#120 b5b345e833d9 / e3e6d6a66349); user #1545 same-phase degree-12 to dual Sym^2 producer suggests using the authentic source interface before constructing larger matrices. Both pasted files inspected; no Monster or Langlands endpoint work. Both P0 roadmaps read at 08dad6fd61b5 / 20bb8b46381b, common blob b59cb2b86687bcfd4495533b52b6c10c6acf7ef4. Existing source producers/consumers: G13 selector incidence, G14 overlap, G16/G17 binary/ternary and monotone reachability, G22/G30 linear-variable CLIQUE, G38/G43 central paired slice, G45/G46 zero gadget and local-full compiler, G48 global forced flag; #1006 FactorsThrough and ConsumerFibreRepairExact, #1291 indexed signed residuals, #123 JMD lowering, #1546 shared computation, #1129 standard machine, #1040 original SAT terminal, #1474/#1502 encoding, #607/#678 Aristotle. Classical meet-matrix zeta/Mobius factorization (Wilf–Lindstrom; see https://doi.org/10.1016/j.jalgebra.2022.01.040), classical communication matrix rank and rectangle methods (e.g. https://www.cs.toronto.edu/~toni/Courses/CommComplexity2022/Lectures/deterministic-cc.pdf). New statements concern the specific original selector carrier and explicit locally-full restriction; no claim of general literature novelty or native kernel proof.

### G49 — same-object conjunction kernel and exact minimum linear count channels

For m>=1, N=N_m, let t,u be arbitrary original absent-clause selectors on the same assignment variables. P_x is the G13 minterm. Define V(t)={x:P_x subset t}. Then V(t AND u)=V(t) intersect V(u), so the matrix of exact counts K_W(t,u)=W(t AND u)=BB^T where B_(t,x)=[x in V(t)]. Its rows at the 2^m actual minterms P_x give an identity matrix, since distinct minterms have equal size and differ at a singleton scope. Subtract from each other row of B its combination of these identity rows; this is an integer unimodular operation U with UB equal to an identity block and zero rows. Thus U K_W U^T has 2^m diagonal ones and remaining zero entries. In particular the exact count kernel over every field has rank 2^m; its integer Smith form has 2^m units. Over Z/(p^H) for H>=1, the minimal scalar channel count for linear matrix factorization is exactly 2^m: upper bound from B, lower bound by reducing modulo p. This does NOT count channels of the actual small local Cauchy tile in R74, and is a statement about the entire two-sided count interface on all selectors, not a complexity lower bound for computing an entry or the SAT output. A rank-one consumer for any specified single pair need not reproduce this entire matrix.

Decision kernel K_G(t,u)=G(t AND u)=[K_W(t,u)>0]. For any integer-valued f on subsets of N coordinates, let d(A)=sum_{B subset A}(-1)^(|A|-|B|) f(B), with f(T)=sum_{A subset T}d(A). The matrix K_f(t,u)=f(t AND u) is exactly Z diag(d) Z^T for subset-zeta matrix Z_(t,A)=[A subset t]. Z is integer unimodular (order by inclusion). Hence the complete p-adic precision-relative channel count for K_f modulo p^H is # {A:v_p(d(A))<H}, with zero having infinite valuation. To justify lower bound over the finite local ring even for nonunit diagonal factors: image module of diagonal form is direct sum of nonzero cyclic ideals, requiring that many generators (reduce the image modulo p times the image); a submodule of an r-generated module over Z/(p^H) is at most r-generated by principal ideal ring structure, so a factorization through r channels cannot have image requiring more. Upper bound follows from the diagonal form. For a field this is exactly the number of nonzero Mobius coefficients over that field, not the number of original assignment monomials. This is the global meet-kernel analogue of the attachment's tile Smith spectrum. It is not a cost-free way of calculating d, since the matrix has exponentially many rows in N.

### G50 — exponentially greater exact support channel count on an easy, locally-full same-object subfamily

For integer r>=1 use three disjoint groups each of r original choice variables, total 3r. Force exactly one true variable per group: pairwise at-most-one constraints, and a fixed OR chain of O(r) binary gates plus a true output per group (unique auxiliary extensions). Use G45's six-variable unique-zero gadget. Pad pairwise clauses (not x_i OR not x_j OR z_0). Compile only the O(r) fixed OR-chain clauses via G46's private copies, padding shorter clauses with z_0,z_1, and padded equalities (not x OR a OR z_0),(x OR not a OR z_1). Total m=Theta(r), each emitted ternary scope distinct, all unary and binary scopes unrestricted, every ternary scope allows 7 or 8 patterns. Fixed choice constraints have r^3=M witnesses, one for each cross-group triple, all auxiliaries uniquely determined. For each cross-group triple I, independently select the clause forbidding 111 iff A_I=0, with A a free M-bit vector. These scopes contain three original choice variables and cannot overlap the fixed clauses (padded pairs have a zero-block variable, compiled clauses have private copies). The original selector projection E(A) is monotone and every coordinate is a constant or one positive A bit. It respects intersection E(A AND B)=E(A) AND E(B). Exact witness count W(E(A))=|A|, with exactly one authentic witness per enabled triple. This is a promise subfamily, not a hard decision reduction. Since N_m=Theta(r^3)=Theta(M), the projection has linear input dimension up to constant factors.

Consequently the joint count submatrix is C_(A,B)=|A intersect B|; joint decision submatrix is D_(A,B)=[A intersect B nonempty]. Their Mobius coefficients on M free bits are:
- count: 1 at singleton subsets, zero elsewhere;
- support: (-1)^(|T|+1) at every nonempty subset T, zero at empty.
By G49 the exact Smith forms have respectively M and 2^M-1 unit factors. This holds over EVERY prime field and modulo EVERY prime power p^H (the retained factors are units, so no precision change eliminates them). Thus the full original decision kernel, even restricted to the locally-full promise on both sides and their conjunction, needs >=2^M-1=2^Omega(N_m) scalar channels for complete linear factorization; trivial dimension upper bound 2^N_m. In contrast the full count kernel has 2^m=2^Theta(N_m^(1/3)) channels, and the submatrix count has only M. This is an exponential support-rank amplification within exactly the same original witness objects. The original decision kernel is NOT a bilinear witness contraction simply because counting is.

Decisive computational control: on this very subfamily D(A,B)=OR_i(A_i AND B_i) is a circuit of at most 2M-1 binary gates, and a count can be accumulated in polynomial time (indeed linear-size Boolean population counter by G22). The low-rank count contraction followed by ONE nonlinear nonzero test computes the high-rank decision kernel. Therefore one cannot infer superpolynomial decision work from the exact Smith channel requirement, even when there is no loss of information at any modular precision. The example works for any finite number of sides as well: multilinear product count sum_i prod_j A^(j)_i, support OR_i AND_j A^(j)_i. Across every nontrivial split of sides fix all but one side in each group to all-one; the same exponential support matrix rank lower bound holds, while direct gates O(number_of_sides*M). This refutes charging each surviving support channel, each cut rank, or a product of such ranks independently in unrestricted computation. The actual R71–R74 source packet and Smith factorization may still improve the reported algorithm; no end-to-end asymptotic improvement or lower bound is inferred here.

### G51 — exact universal consumer quotient and certificate asymmetry

Define two original selectors equivalent if their decision responses to EVERY conjunctive context u agree. Then

    t ~ u iff V(t)=V(u).

Proof: equality of witness sets implies all future intersection-nonempty responses equal. Conversely if witness x belongs to exactly one set, choose the authentic minterm context P_x; its witness set is {x}, giving different results. Thus the same quotient governs exact count and decision against all conjunctive contexts (the count response to P_x is already 0 or 1).

Canonical representative sigma(t)=union_{x in V(t)} P_x, empty union zero. This is a monotone interior map: sigma(t) subset t, V(sigma(t))=V(t), sigma(sigma(t))=sigma(t); it is the inclusion-minimal selector preserving the exact witness set. Further sigma(t AND u)=sigma(sigma(t) AND sigma(u)), since the witness sets on both sides are equal. This is the same-object exact consumer quotient, no independent synthetic reconstruction. G50 realizes all 2^M subsets of its M authentic witnesses. Hence any deterministic summary of one side permitting all future conjunctive decision queries must use >=M bits worst-case (>=2^M states), even if its summary and decoder are nonlinear; the full t itself uses N bits. This is a tight asymptotic Theta(N) bit budget along compiler lengths, NOT an exponential bit or running-time lower bound. On the easy subfamily the identity summary A is optimal and direct decoding costs O(M). Computing sigma(t) on arbitrary inputs is itself Clay-equivalent: G(t)=1 iff sigma(t) nonempty (m>=1); conversely each coordinate membership is a SAT query asking for a witness agreeing with that scope pattern, so N polynomially sized queries suffice under P=NP. G48 shows even a single global flag support query can be NP-hard with known satisfying witness. Do not assume canonical quotient construction is a paid polynomial preprocessing lemma.

For the entire K_G, a positive monochromatic rectangle cover needs exactly 2^m rectangles: upper via one rectangle {t:P_x subset t} times itself per witness; lower via diagonal true pairs (P_x,P_x) whose off-diagonal pairs are false. For the negative cover, G50 supplies 2^M distinct zero pairs (A, complement A). For distinct A,B, at least one of (A, complement B) or (B, complement A) is positive, since at least one of A minus B, B minus A is nonempty. No all-zero rectangle can cover two of these pairs. Therefore negative rectangle cover number >=2^M on this restricted promise; upper <=2^N by taking a rectangle for each row and all its false columns. This is an exact separation of positive witness certificate length m bits versus negative rectangle certificate length Theta(N) bits (log of cover number, up to rounding). It is communication/rectangle complexity in a specified two-party split, not coNP hardness of that easy subfamily or a superpolynomial standard-machine lower bound. All proof paths allow arbitrary sharing; only the specified intermediate interface is restricted.

### G52 — resource conclusion and next attack

The prior arithmetic lower bounds and the new Smith/certificate theorems identify the model in which an obstruction actually applies. They do not prove that the actual computation ever materializes the joint kernel, a universal context quotient, or a rectangle cover. A Boolean consumer may contract via low-rank counts, use nonzero tests, retain a compact input description and perform global adaptive computation. The OR-of-intersections subfamily shows even exponential support rank over every modulus and exponential negative rectangle count are compatible with linear-size Boolean circuits. This is a stronger explicit control against converting R74's channel count to total time merely by changing the target from count to support. To obtain N4, need target-specific cost of PRODUCING suitable intermediate factors on arbitrary selectors, including the nonminimal locally-full hard family, or direct uniform standard-machine work. Neither exact global quotient nor large rank is itself the missing theorem. In particular G49 count channel lower bound is not a lower bound for actual #SAT algorithms with interpolation and shared tensor operations; G37 external reported subexponential algorithms remain admissible. No assumption of ETH or external theorem audit in this packet.

### Actually executed local regression (exact integer/SymPy; no CI/native kernel)

Local /tmp/p0_meet.py executed: 258 complete model-count comparisons on emitted locally-full one-hot triple formulas r=1,2 by independent exact DPLL (without pre-setting zero block), distinct triple scope checks; 65,540 compiled conjunction and negative fooling-set pair checks; 174,760 exact Mobius diagonal matrix entries for count and support at M=1..8, including eight independent SymPy Smith normal forms at M<=4; 65,552 full original selector closure/intersection comparisons at m=1,2; 65,552 full original count-kernel entries and explicit integer elimination at m=1,2. All passed after fixing test-harness SymPy Integer conversion (not a mathematical failure). No asymptotic extrapolation. Core reproducer (Python, NumPy integer arithmetic and SymPy; sizes limited to exact int64-safe values):

```python
from itertools import combinations,product
from collections import Counter
from functools import lru_cache
import numpy as np
import sympy as sp
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ
D='16763747126132141175'
Z=[tuple((i,1-(int(p)>>j&1)) for j,i in enumerate(I)) for I,p in zip(combinations(range(6),3),D)]
def compile_(r,mask):
 q=3*r;z=list(range(q,q+6));m=q+6
 F=[tuple((q+i,v) for i,v in C) for C in Z]
 groups=[list(range(g*r,(g+1)*r)) for g in range(3)];fixed=[]
 for G in groups:
  for i,j in combinations(G,2):F.append(((i,0),(j,0),(z[0],1)))
  cur=G[0]
  for j in G[1:]:
   a=m;m+=1;fixed.extend([((cur,0),(a,1)),((j,0),(a,1)),((cur,1),(j,1),(a,0))]);cur=a
  fixed.append(((cur,1),))
 for C in fixed:
  cc=[]
  for i,v in C:
   a=m;m+=1;cc.append((a,v));F.extend([((i,0),(a,1),(z[0],1)),((i,1),(a,0),(z[1],1))])
  F.append(tuple(cc+[(z[k],1) for k in range(3-len(cc))]))
 for h,I in enumerate(product(*groups)):
  if not(mask>>h&1):F.append(tuple((i,0) for i in I))
 assert len({tuple(sorted(i for i,v in C)) for C in F})==len(F)
 assert all(len(C)==len({i for i,v in C})==3 for C in F)
 return m,F
@lru_cache(None)
def cnt(F,free):
 if not F:return 1<<free.bit_count()
 if any(not C for C in F):return 0
 def sub(i,v):return tuple(sorted(set(tuple(l for l in C if l[0]!=i) for C in F if (i,v) not in C)))
 for C in F:
  if len(C)==1:
   i,v=C[0];return cnt(sub(i,v),free^(1<<i))
 freq=Counter(i for C in F for i,v in C);i=max(freq,key=freq.get)
 return sum(cnt(sub(i,v),free^(1<<i)) for v in (0,1))
checks=meet=0
for r in (1,2):
 M=r**3;n=1<<M;clauses=[]
 for A in range(n):
  m,F=compile_(r,A);clauses.append(set(F))
  assert cnt(tuple(sorted(set(tuple(sorted(C)) for C in F))),(1<<m)-1)==A.bit_count()
  cnt.cache_clear();checks+=1
 for A in range(n):
  for B in range(n):
   assert clauses[A]|clauses[B]==clauses[A&B]
   assert bool(A&(n-1-B)) or bool(B&(n-1-A)) or A==B
   meet+=1
assert (checks,meet)==(258,65540)
checks=smith=0
for M in range(1,9):
 n=1<<M
 for mode in ('count','support'):
  def f(a,b):return (int(a)&int(b)).bit_count() if mode=='count' else int(bool(int(a)&int(b)))
  K=np.array([[f(a,b) for b in range(n)] for a in range(n)],dtype=np.int64)
  for i in range(M):
   for a in range(n):
    if a>>i&1:K[a,:]-=K[a^(1<<i),:]
  for i in range(M):
   for b in range(n):
    if b>>i&1:K[:,b]-=K[:,b^(1<<i)]
  ds=[int(a.bit_count()==1) if mode=='count' else ((-1)**(a.bit_count()+1) if a else 0) for a in range(n)]
  assert np.array_equal(K,np.diag(ds));checks+=n*n
  if M<=4:
   Dm=smith_normal_form(sp.Matrix(n,n,f),domain=ZZ)
   assert sorted(abs(int(Dm[i,i])) for i in range(n))==sorted(abs(x) for x in ds);smith+=1
assert (checks,smith)==(174760,8)
checks=0
for q in (1,2):
 S=[I for j in range(1,4) for I in combinations(range(q),j)]
 C=[(I,p) for I in S for p in range(1<<len(I))];ix={v:i for i,v in enumerate(C)}
 P=[sum(1<<ix[I,sum((x>>i&1)<<j for j,i in enumerate(I))] for I in S) for x in range(1<<q)]
 n=1<<len(C)
 V=[sum(1<<x for x,p in enumerate(P) if t&p==p) for t in range(n)]
 L=[0]*n
 for t in range(n):
  for x,p in enumerate(P):
   if V[t]>>x&1:L[t]|=p
  assert L[t]&t==L[t] and V[L[t]]==V[t]
 A=np.array([[int(t&p==p) for p in P] for t in range(n)],dtype=np.int64);K=A@A.T
 for t in range(n):
  for u in range(n):
   assert V[t&u]==V[t]&V[u] and L[t&u]==L[L[t]&L[u]]
   assert K[t,u]==sum((t&u)&p==p for p in P);checks+=1
 rows=[tuple(bool(v&w) for w in V) for v in V]
 assert len(set(rows))==len(set(V))==len(set(L))
 for a in range(n):
  if a not in P:
   for x,p in enumerate(P):
    if A[a,x]:K[a,:]-=K[p,:]
 for a in range(n):
  if a not in P:
   for x,p in enumerate(P):
    if A[a,x]:K[:,a]-=K[:,p]
 assert np.array_equal(K,np.diag([int(a in P) for a in range(n)]))
assert checks==65552
```

### Active endpoint-first ledger (no extra phase)

| Gate | Deliverable | Status |
|---|---|---|
| G49 | exactWitnessMeetKernelSmith / generalMeetMobiusChannels | derived, exact tests; R74 linear interface analogue |
| G50 | locallyFullTripleChoiceProjection / exponentialDecisionChannelAmplification | derived and tested; G45/G46, exact rank over every prime power |
| G51a | universalConjunctiveConsumerQuotient / canonicalWitnessUnionInterior | derived and tested; G13, FactorsThrough; polynomial construction Clay-equivalent |
| G51b | positiveNegativeRectangleAsymmetry | derived, exact small tests; communication not time |
| G52 | cheapNonlinearSupportChannelEscape | explicit linear-gate control; no general rank-to-work transport |
| N4/G12a | unrestrictedSerialCharge | OPEN: cost of producing actual usable contraction factors, not entire interface; all legal nonlinear/shared shortcuts |
| N5/G12c | unrestrictedSuperpolynomialGrowth | OPEN; G48 global flag uniform route or G38 central-slice nonuniform route |
| N6 | originalClayTransport | conditional #1040 / #1129 standard-machine coverage |

Aristotle BIDI: the next meaningful attack must constrain a paid algorithmic operation on the actual G48 flag or full nonminimal central-slice family. The rank of a joint response function, precision-relative Smith spectrum and context-equivalence classes are not independently chargeable; G50/G52 provide explicit cheap controls. Inspect shared signed tensor contraction as a legitimate upper-bound mechanism, and seek an unavoidable resource inequality for computing its useful factors (or a direct standard-machine contradiction) that does not require reconstructing all context responses. No new certification prerequisite, no unconditional P!=NP claim.


## 24. P0-G53–G55 — precision-sensitive zero test, weighted parity fingerprints, exact deterministic probe budget (2026-11-24)

Controlling endpoint remains literal Clay P vs NP, P0-C/D. Inputs: user pasted R78–R82 deterministic truth graph and signed scalar D=3M-4W (reported Langlands #1549/#120 heads 950852bf6615 / 64c2f1cd5091) plus G49–G52; both files read in container. Both P0 roadmaps read live at 57c5bc5fe260 / be4988049c2c, common blob 74a172e67e18677af55249b2fdd6ba688b2fe646. No Monster/Langlands endpoint edits. Existing producers/consumers: G13 original selector, G16/G17 binary control, G22 threshold circuits, G26 shared Boolean gates, G38/G43 central slice, G45/G46 locally-full parsimonious compiler, G48 global flag, G50 triple-choice witness subfamily, G51 canonical consumer quotient, G37 external reported SAT algorithm; #1006 FactorsThrough/self-reduction, #1291 signed residuals, #123 JMD lowering, #1546 shared computation, #1474/#1502 reductions, #1129 costed machine coverage, #1040 terminal, #607/#678 Aristotle. Classical sources: Valiant–Vazirani, NP is as easy as detecting unique solutions (1986), https://doi.org/10.1016/0304-3975(86)90135-0 (randomized parity-SAT hardness already known); Schwartz–Zippel polynomial identity testing, https://people.seas.harvard.edu/~salil/cs225/spring09/lecnotes/Chap2.pdf. New contributions here are the explicit same-object weighted truth-graph interface and exact deterministic probe budget on G50; no claim of novelty for randomized parity hardness or general polynomial identity testing.

### G53 — exact unweighted precision criterion and logarithmic-precision transport

Let original q assignment bits, M=2^q, W integer in [0,M], and D=3M-4W as in attached R82. For any fixed positive integer modulus a, observing D mod a is equivalent to observing W mod d=a/gcd(a,4), since 4(W-W')=0 mod a iff d divides W-W'. With several observations let L=lcm(d_1,...,d_l). Zero is distinguishable from every positive count iff L>M: if L<=M, W=L has precisely the zero transcript. This also holds for adaptive deterministic residue-only algorithms: follow the zero transcript, which fixes the queried moduli; if their effective lcm is <=M the positive count L follows the same path and receives the same decision. This is not a lower bound for algorithms that also inspect the original formula, change its weights or otherwise derive formula-dependent observations.

All integer counts c in [0,M] occur on the original carrier: the q-bit comparator [integer(x)<c] has O(q) bounded-fanin gates, with q+1-bit constant c (handle c=M separately). Its deterministic Tseitin graph has unique auxiliary extension per x, and G46 can hide all its locally visible affine/unary constraints while preserving exact flag counts. Thus the collision is realizable by succinct formulas, not merely by arbitrary integers. In particular for a single 2-adic residue D mod 2^H, H>=2, effective modulus 2^(H-2), and H>=q+3 is necessary and sufficient in this observer model. The zero-path joint effective modulus must have log2 L>q; this is a precision requirement, not independently paid time.

There is no need for high precision in any SINGLE contraction. Query D modulo 4j for j=2,...,2q+2, each O(log q) bits. Then L=lcm(1,...,2q+2)>2^q. Proof: put n=q+1. Each p-adic valuation of binom(2n,n) is sum over powers p^i<=2n of floor(2n/p^i)-2floor(n/p^i), each 0 or 1; hence binom(2n,n) divides lcm(1,...,2n). The central binomial coefficient is >=2^(2n)/(2n+1)>2^(n-1) for n>=2. So check whether all D residues agree with 3M; no CRT reconstruction of W is necessary. Can instead query only maximal prime powers <=2q+2 and multiply by 4 in the D modulus. Polynomial number of logarithmic-precision original contractions suffices, deterministically, with poly(q) preprocessing. If the reported tensor algorithm's exact count precision is a significant expense, this supplies an alternative consumer; it does NOT show its entire interpolation and division budget can be reduced to these digits. Intermediate denominators/valuation losses must still be charged. No claim of polynomial-time modular #SAT or end-to-end speedup.

### G54 — constant-precision randomized weighted parity fingerprint

Work over F=GF(2^k), k=ceil(log2(4q)) for q>=1, Q=2^k. A field description can be built uniformly in poly(q) time by enumerating monic degree-k binary polynomials and testing irreducibility (even naive divisor enumeration is polynomial in q). For original witness set V(t) define the multilinear polynomial

    P_t(z_1,...,z_q)=sum_{x in V(t)} prod_{i:x_i=1} z_i   in F[z].

Distinct original assignments give distinct monomials, all coefficients one, so P_t=0 identically iff UNSAT, even in characteristic 2. Degree <=q. Uniform independent z_i in F, by Schwartz–Zippel a satisfiable t gives P_t(z)!=0 with probability >=1-q/Q>=3/4. This is different from unweighted counting modulo 2, which may vanish on a nonempty even-cardinality fibre.

For each trial choose an independent uniform k-bit mask lambda and use the F2-linear bit functional ell_lambda(v)=dot(lambda, coordinate_vector(v)) over F2. For nonzero v exactly half masks give ell=1. Define original per-assignment deterministic flag

    b_(z,lambda)(x) = F_t(x) AND ell_lambda(prod_i z_i^x_i).

Then the parity of its 1-fibre W_(z,lambda) is exactly ell_lambda(P_t(z)), by linearity. The flag circuit is explicitly polynomial cost: start accumulator 1 in F; each assignment bit chooses either unchanged accumulator or multiplication by fixed z_i (a k-by-k binary linear map); use O(k^2) XOR/mux gates per original bit, plus O(k) gates for the final linear functional and O(N) original evaluation. Bounded-fanin gates encoded by their truth constraints (fresh output; unique extension for every x); G46 compiler preserves the exact truth-graph fibre counts and local fullness. The full graph remains always satisfiable with total M=2^q, including the rejected flag branch; only W_(z,lambda) changes. No exponential witness expansion is constructed.

The attached signed scalar for this modified graph is D_(z,lambda)=3M-4W_(z,lambda). A single residue modulo 8 returns exactly the parity bit: D-3M is 4 mod 8 iff flag-one count odd. UNSAT yields zero parity for every trial. SAT yields one with probability at least (3/4)*(1/2)=3/8. Three independent trials, OR the returned bits, miss with probability <=(5/8)^3<1/3. More trials exponentially reduce one-sided error. Alternatively use all k coordinate functionals per field evaluation and test the vector nonzero (miss <=1/4 per evaluation). This is randomized polynomial reduction to constant-precision signed contraction on polynomially enlarged locally-full deterministic graphs, with O(q log q) random bits per trial. It is a field-polynomial version of the known randomized parity-SAT hardness (Valiant–Vazirani); it need not isolate a unique witness. It does NOT imply P=NP from polynomial-time parity contraction: that would give NP=RP, not an unconditional deterministic equality. No equivalence of #P and NP is assumed; even P=NP alone is not known to give polynomial parity counting. Further, precision modulo 8 of the final scalar is not a proof of constant precision at every internal arithmetic division/interpolation step.

### G55 — sharp deterministic universal linear-probe budget

A probe is any F2-linear functional of the original witness incidence vector in F2^(2^q), with one output bit. Its coefficient function h(x) may be arbitrary, not just a product-weight linear functional from G54. Crucially the selection of probes is independent of the input selector t (may depend on q and previous answers, not on inspecting t). Decision can be an arbitrary nonlinear function of answers. For all selectors of length N=N_q there are <=2^N positive or negative inputs. G54 detects each positive input with probability >=3/8 and never detects a negative. Take L=2N+1 independent random seeds; union bound over positive selectors gives 2^N*(5/8)^L<1. Thus there EXISTS a common deterministic seed list of length 2N+1 detecting every satisfiable selector and no unsatisfiable selector. It is nonuniform advice of O(N q log q) bits, not a known polynomial uniform construction. In particular polynomial-size circuits for parity contraction on these compiled graphs would imply SAT in P/poly through this list, but no converse or unconditional lower bound.

For a matching worst-case lower bound in this probe model use G50's locally-full three-group construction at its original compiled variable count m. It realizes every subset A of M0=r^3=Theta(N_m) authentic fixed witnesses, with all other witness bits identically zero. Restrict any deterministic linear-probe decision procedure to this subfamily and follow its zero transcript. Fewer than M0 queried bits define a homogeneous linear system on M0 arbitrary incidence bits with a nontrivial kernel. Take a nonzero kernel vector A: it is an actual satisfiable compiled selector, and all its answers along this path are identical to empty A. Adaptivity cannot fix the collision because the path is fixed by the answers. Hence at least M0 probes are necessary in the worst case, even for arbitrary linear forms. This proves Theta(N) deterministic one-bit universal linear-probe complexity along G50's compiler lengths, versus O(1) randomized probes for bounded one-sided error. The input-independent condition is essential: a standard machine reads t and can choose probes or directly compute support using that information. In fact G50's easy family accepts iff some allowed triple bit is one, O(N) gates, illustrating why this optimal information bound is not N4. Do not count generating these probe responses as free, and do not sum their computation costs independently without controlling shared subgraphs.

### Actually executed local regression (Python integer, SymPy irreducibility, exact DPLL; no CI/kernel)

Local /tmp/p0_precision.py checked 1,049,616 field evaluation pairs: all arbitrary witness subsets for q=1,2,3 and every point in fields of sizes 4,8,16, using irreducible polynomials 0b111,0b1011,0b10011 (SymPy independently checked). For each nonempty subset verified the exact zero-count upper bound q Q^(q-1); 966,466 nonzero outputs each checked over every lambda for balanced bit functionals. For q=1..10 all 2,056 comparator target counts checked by evaluating every assignment; same 2,056 signed-scalar residue zero tests checked and central-binomial divisibility verified. For 24 seeded actual width<=3 selector formulas (8 each q=1,2,3), emitted deterministic Boolean truth graph for original evaluation AND weighted parity functional, then G46 local-full compiler. Independent exact DPLL counted both flag fibres (48 comparisons) and checked their sum 2^q, filtered count and modulus 8 parity. Initial counter hit Python recursion depth on unit propagation; replaced with iterative batched unit propagation, reran all and passed. No asymptotic extrapolation. Core reproduction code (the G46 compiler and exact model-count method from section 22 can be reused, with iterative unit propagation for the larger graphs):

```python
from itertools import product
from math import lcm,comb
from sympy import Poly,symbols
x=symbols('x')
def mul(a,b,k,irr):
 r=0
 while b:
  if b&1:r^=a
  b>>=1;a<<=1
  if a>>k:a^=irr
 return r
def ev(S,weights,k,irr):
 v=0
 for a in S:
  z=1
  for i,w in enumerate(weights):
   if a>>i&1:z=mul(z,w,k,irr)
  v^=z
 return v
checks=nonzero=0
for q,k,irr in [(1,2,7),(2,3,11),(3,4,19)]:
 Q=1<<k
 assert Poly(sum(((irr>>j)&1)*x**j for j in range(k+1)),x,modulus=2).is_irreducible
 zeros=[0]*(1<<(1<<q))
 for weights in product(range(Q),repeat=q):
  terms=[ev([a],weights,k,irr) for a in range(1<<q)]
  vals=[0]*len(zeros)
  for S in range(1,len(vals)):
   b=S&-S;vals[S]=vals[S^b]^terms[b.bit_length()-1]
  for S,v in enumerate(vals):
   zeros[S]+=v==0;checks+=1
   if S and v:
    assert sum((v&lam).bit_count()%2 for lam in range(Q))==Q//2
    nonzero+=1
 assert zeros[0]==Q**q
 assert all(z*Q<=q*Q**q for z in zeros[1:])
assert (checks,nonzero)==(1049616,966466)
checks=0
for q in range(1,11):
 M=1<<q
 def comparator(a,c):
  if c==M:return 1
  eq=1;lt=0
  for i in reversed(range(q)):
   b=a>>i&1;d=c>>i&1
   lt|=eq & (1-b) & d;eq&=1^(b^d)
  return lt
 L=lcm(*range(2,2*q+3))
 assert L>M and L%comb(2*q+2,q+1)==0
 for c in range(M+1):
  assert sum(comparator(a,c) for a in range(M))==c
  D=3*M-4*c
  assert all((D-3*M)%(4*j)==0 for j in range(2,2*q+3))==(c==0)
  checks+=1
assert checks==2056
```

Compiler reproduction detail: use gate truth-table encoding for AND/OR/XOR (for each consistent input bit pair forbid incorrect output, deleting constant wires and repeated identical input coordinates). Construct accumulator bit arrays acc initially [1,0,...,0]. For each i, derive rows[b]={j: bit_b(mul(1<<j,z_i,k,irr))=1}; calculate each v_b as XOR of acc[j] in row b, then new_acc[b]=OR(AND(not x_i,acc[b]),AND(x_i,v_b)). Final flag = AND(original CNF gate evaluation, XOR of accumulator bits selected by lambda). Leave flag unconstrained, compile entire gate graph by G46 using every gate clause selected. Count compiled formula with additional flag unit b=0 or b=1 via exact DPLL, batched unit propagation and cache cleared between cases; flag query units are tests, not part of locally-full source. Seed Random(53), q=1,2,3 as above, 8 trials each: C list all clauses ordered by width, lexicographic scope, lexicographic signs; F=rng.sample(C,rng.randrange(len(C)+1)); z_i=rng.randrange(Q); lambda=rng.randrange(Q). Compare true fibre with sum(ell_lambda(ev([a],z,k,irr)) for satisfying original a), false+true=2^q, and (D-3M) mod 8=4 iff true count odd. This spells out the emitted gate graph used in the executed test, not an independent claimed native kernel verification.

### Active endpoint-first ledger

| Gate | Deliverable | Status |
|---|---|---|
| G53 | exactUnweightedResidueZeroCriterion / logarithmicPrecisionModularCover | derived and checked; R82 |
| G54 | weightedWitnessFieldFingerprint / parityTruthGraph / constantPrecisionRandomizedDecision | derived and tested; classical Schwartz–Zippel, Valiant–Vazirani |
| G55 | universalLinearProbeDeterministicThetaN / nonuniformSeedCover | derived; G50 exact subfamily and union bound; restricted observer only |
| N4/G12a | unrestrictedSerialCharge | OPEN: must survive low-precision modular/weighted contractions, input-dependent probes, sharing and arbitrary direct decision |
| N5/G12c | originalUnrestrictedSuperpolynomialGrowth | OPEN: G48 uniform forced flag, G38 nonuniform central slice |
| N6 | originalClayTransport | conditional #1040 terminal / #1129 coverage |

Aristotle BIDI: exact count precision and explicit representation dimension cannot be required for decision. G53 gives deterministic low-precision cover; G54 constant final precision uses weights and changes the graph with paid polynomial overhead. Actual reported 2026 tensor/Hermite algorithm's internal valuation losses and mode costs must be analyzed for these modular consumers before claiming speedup. In particular low final precision does not bound intermediate denominators. To settle literal Clay, need a deterministic uniform resource lower bound for SAT itself (or a valid polynomial solver), not merely hardness of parity/counting or a universal linear-observer lower bound. No new certification or representation prerequisite, no P!=NP claim.


## 25. P0-G56–G59 — zero mode, signed residual, indexed Fourier horizon and inherited precision (2026-11-24)

P0 remains literal Clay P vs NP. User explicitly requires zero mode, signed residual and indexed hyperfabric. Read both attached pasted files (G53–G55 and Langlands R85–R89, reported #1549/#120 heads 8050f29facb1 / e8f8b31242d1). Both original P0 roadmaps read at 719d5ff1245d / e04e9a0a426b, common blob 6585482064f110e6e08afc3f7790ee4bffcf0b5a. Reopened actual DASHI/Core/GovernedIndexedResidualCubeExact.agda default-branch blob 42b70ebb7376813076934f2245ce6011b76f10c8: Index retains history,time,depth,iteration,version; IndexedCube has per-index vertices, faces, residual types; ExactFaces vs ResidualFaces; six paths. Reuse H05/#1291 but do not close H07/H14 or modify TOE/Monster/Langlands. Other producers G13 original width-three carrier, G14 scope incidence, G16/G17 binary control, G28/G33 signed reduction, G45–G48 locally-full flag, G49–G52 universal conjunction quotient, G53–G55 modular weighted consumers, R57–R60 affine/character/interpolation, R71–R74 tile Smith. #1006 FactorsThrough/self-reduction, #123 JMD lowering, #1546 sharing, #1474/#1502 reductions, #1129 standard-machine coverage, #1040 terminal, #607/#678 Aristotle. The elementary Fourier, linear-span and Hermite arguments below are derived here for these specific interfaces; no literature novelty or native kernel claim.

### G56 — low-degree signed source interface determines the original relation

Use q original assignment bits and actual absent-clause selector t. For a current original width<=3 relation b(x) in {0,1}, define unnormalized signed Fourier S(h)=sum_x b(x)(-1)^(h dot x). S(0)=W is integer zero mode; nonzero h retain signs. For an original scope I and pattern p, contextual count M_(I,p)=sum_{x:x|I=p} b(x) is

    2^|I| M_(I,p) = sum_{a subset I} (-1)^(a dot p) S(a).

The RHS is exact integer arithmetic (no division over F2 without precision accounting). In the other direction S(a)=sum_p (-1)^(a dot p) M_(I,p) for any containing scope I, including the count for a=0. Thus low-degree modes |h|<=3 and local counts are equivalent linear observations over Q. On original selector relations, the sign-preserving low-degree integer observations determine the ENTIRE original witness relation: set sigma(t)_(I,p)=[M_(I,p)>0] (G51 canonical witness union). Each witness satisfies these allowed patterns; every nonwitness violates some original allowed-pattern constraint, whose forbidden pattern has count zero, so is still rejected by sigma. For q>=1 include unary scopes and handle empty relation sigma=0. Exactly sum_{j=0}^{min(3,q)} binom(q,j) signed integers, each bounded in magnitude by 2^q, suffice to represent the source relation, O(q^4) bits. One could store canonical Boolean sigma in only N_q=Theta(q^3) bits. No independent reconstruction of all higher Fourier modes is necessary to specify the source. Producing low modes is at least as hard as SAT (S(0) exact count), and obtaining the support of all M is exactly the G51 canonicalization task, not a free operation. On arbitrary masks not defined by width<=3 clauses, or arbitrary weighted/signed distributions, this uniqueness does NOT hold. Retain source identity, exact selector and coefficient field; do not silently replace a signed residual by its support.

Quantitative same-object difference: let b,b' be two actual original width-three relations on the same q source coordinates, with contextual counts M,M'. For every x in V minus V', at least one forbidden pattern C in t' is hit. Such a pattern has M'_C=0. Hence |V minus V'|<=sum_{C forbidden by t'} M_C. Likewise reverse. A coordinate forbidden by both contributes zero; each other term is bounded by |M_C-M'_C|. Therefore

    |V symmetric_difference V'| <= sum_C |M_C-M'_C|.

In particular same zero mode does not imply same relation, but same exact signed low modes does. This is a joint-observer separation guarantee on actual sources, not a claim that arbitrary signed histories are determined by order-three marginals.

### G57 — exact update law and sharp linear future-horizon dimension

If Q is a new original clause filter excluding p on I, write d=|I|<=3. With H_a=(-1)^(a dot x) the character, Q=1-2^-d sum_{a subset I} (-1)^(a dot p)H_a. Multiplication b'=bQ gives

    2^d S'(h) = 2^d S(h) - sum_{a subset I} (-1)^(a dot p) S(h xor a).

Thus computing all modes of order <=r after one event requires at most order r+3 before it. This is exact signed convolution; all coincident frequencies combined before truncation. No free division in characteristic 2: over integers numerator is divisible by 2^d, modular result mod 2^H can be recovered from numerator mod 2^(H+d). For arbitrary sequences of <=ell such events, exact linear closure requires precisely the vector space spanned by characters of weight <=min(q,r+3ell). Upper by multiplying by at most ell clause filters, each Fourier support within a scope of size<=3. Lower: any h of weight <=r+3ell can partition its support into h0 of size<=r and <=ell disjoint nonempty scopes of size<=3. Each scope character is a linear combination of indicators of its full patterns, each indicator equals 1-Q_p. Expand products: H_h is a linear combination of observable kernels H_h0 times products of <=ell clause filters. Characters are linearly independent over Q and any odd-characteristic field. Therefore the exact rank of the future-observation linear family is

    D(q,r,ell)=sum_{j=0}^{min(q,r+3ell)} binom(q,j).

For a linear state with linear decoders, any summary valid on all original width-three sources must have >=D scalar channels: every singleton assignment is an original selector relation, so equalities on those sources enforce equality of observation row vectors. Even if only terminal count r=0 is requested, ell>=ceil(q/3) yields full 2^q linear dimension. On arbitrary signed distributions a linear summary with arbitrary decoder still needs this dimension over Q by kernel inclusion, but DO NOT extend this latter claim to nonlinear decoding only on the Boolean selector family. G56 shows nonlinear low-order source reconstruction is possible there. Actual arbitrary SAT algorithms may retain original input, adaptively recompute and exploit nonlinear sharing. This is a precise lower bound on a specified history-independent linear update/decoder model, not on arbitrary bit or gate complexity. Over characteristic two the character basis collapses; use integer/odd-characteristic formulation, not a spurious binary-rank claim.

### G58 — indexed hyperfabric with actual source labels, zero mode and signed loss retained

Use independent index (history,tau,k,j,version,coefficient ring,precision,consumer), with tau chronological event and k chart/refinement (ell above is future horizon, not k). Represent current mask in source coordinates; for an invertible chart C_k transport all masks and observation kernels simultaneously by permutation/pullback (or diagonal operator conjugation). Mode order always refers to ORIGINAL source scope labels, not arbitrary coordinates after permutation. Keep source selector and labels even when consumer reads only low modes or count. On a monotone event, L_tau=b_tau(1-Q_tau), b_tau=b_(tau+1)+L_tau. Loss masks disjoint over chronological deletions; b_0=b_T+sum L_tau. Apply each signed Fourier mode, the zero mode, or original weighted witness polynomial linearly. On revisions, gain=(1-b)b', loss=b(1-b'), b'-b=gain-loss; retain separate nonnegative masks or exact source descriptions rather than only net response. Equal counts can conceal both nonempty gain and loss; a modular zero can arise by cancellation or by coefficients divisible by p. If any scalar observation vanishes, do not label source empty without a sufficient consumer. G54 random weighted fingerprints remain one-sided tests with possible false negatives, not replacements for the signed source ledger.

For Q,R two commuting actual diagonal clause filters define A_ij=b Q^i(1-Q)^(1-i) R^j(1-R)^(1-j), i,j in {0,1}; disjoint source atoms with sum b. A00=b-bQ-bR+bQR is joint signed correction; first loss Q then R gives (A00+A01,A10), reverse gives (A00+A10,A01). With transported chart as third axis obtain eight vertices and six commuting mask faces by pointwise multiplication and conjugation. All modes and contextual kernels transform accordingly. Intermediate chronological histories are not identical even though endpoints commute; keep the named loss allocation. A noninvertible coarsening may identify distinct source masks and need not preserve multiplication; no exact chart transport asserted for it. Existing governed cube residual witness is not commutation proof. This is a finite source-mask realization, not a universal H05/H07/H14 closure or resource bound. No assumption that materializing the exponential masks or all Fourier coordinates is required for arbitrary decision; the symbolic source and paid algorithms remain admissible.

### G59 — inherited precision obstruction on an explicit clustered Hermite interface

G53/G54 reduce final output precision. For an actual clustered interpolation mechanism, small final precision does NOT in general imply small input precision. The following is a sharp restricted-interface theorem, independent of any claim that the reported SAT algorithm uses these exact nodes or arbitrary integral polynomials.

Fix prime p, spacing a=p^d with d>=1, Q>=1 distinct nodes t_i=u+p^d i, i=0,...,Q-1, p not dividing u. Suppose H(T) has integer coefficients and degree <QJ, and an observer receives Taylor coefficients [z^k]H(t_i+z), 0<=k<J, modulo p^P. Goal H(0) mod p^h, h>=1. Let

    L=J*(d*(Q-1)+v_p((Q-1)!)).
    F(T)=prod_{i=0}^{Q-2}(T-t_i)^J * (T-t_(Q-1))^(J-1).

F integral degree QJ-1, F(0) unit, all supplied jets zero except the last coefficient at the last node, which equals prod_{i<Q-1}(t_(Q-1)-t_i)^J and has valuation L. Compare 0 with p^(h-1)F. They have identical observed jets whenever P<=L+h-1, but different H(0) mod p^h. Therefore P>=h+L necessary, even for nonlinear reconstruction of those jets; holds for adaptive queries limited to these prescribed jet coordinates with that precision. This is a real integral-polynomial collision, not an arbitrary incompatible jet vector. For J=1 this bound is EXACT: Lagrange coefficient at zero has valuation -d(Q-1)-v_p(i!)-v_p((Q-1-i)!), because numerator products are units. Its most negative value is -L at the endpoints (binomial coefficient integrality). Thus P=h+L suffices to compute the linear combination modulo p^h. For general J, the ordinary Hermite basis L_i(T)=prod_{j!=i}((T-t_j)/(t_i-t_j))^J, inverse series truncated at J-1 gives sufficient P=h+L+(J-1)*(d+floor(log_p(Q-1))) for Q>=2. Indeed v_p(L_i(0))>=-L, each inverse-series coefficient of degree k has valuation >=-k*(d+floor log_p(Q-1)), by binomial integer numerators and the valuation of every node difference. For Q=1 no loss: Taylor translation is integral. Thus even final parity can require inherited precision Omega(QJ) for this generic cluster reconstruction with fixed d. If nodes include one congruent to zero mod p^h, direct evaluation there already determines H(0) mod p^h; if source class excludes F or admits special recurrences, this generic obstruction may disappear. Our collision is for unrestricted integral polynomials in the specified degree range, not proved to arise from actual Cauchy-deformed SAT contractions. No lower bound for the published algorithm, no end-to-end speedup, and no claim that internal precision is always unavoidable. Next inspect actual source deformation image and packet-node geometry before applying the bound. This also separates precision in a chosen observer from standard-machine work.

### Actually executed local regression (Python exact integers/Fraction and odd-field elimination; no CI/kernel)

Local /tmp/p0_indexed.py: 860 original selector source reconstructions (all 260 inputs at q=1,2 plus 150 seeded each q=3..6); 860 signed source difference inequalities; 19,032 individual Fourier update coefficients; 3,440 chart-transported atom comparisons; 60 actual horizon-span ranks by Gaussian elimination over GF(101) for q=1..5, r=0..q, ell=0..2; 192 integral Hermite collision polynomials for p=2,3,5, d=1,2, Q=1..8, J=1..4; 144 exact rational Lagrange reconstructions for J=1. All passed. Reproducer (same executed logic, helper implementations included):
```python
from itertools import combinations,product
from random import Random
from math import comb,factorial
from fractions import Fraction
rng=Random(369)
def carrier(q):
 S=[I for j in range(1,min(3,q)+1) for I in combinations(range(q),j)]
 C=[(I,p) for I in S for p in range(1<<len(I))]
 def pat(x,I):return sum((x>>i&1)<<j for j,i in enumerate(I))
 F=[sum(1<<x for x in range(1<<q) if pat(x,I)==p) for I,p in C]
 return C,F
def walsh(v,q):
 a=[v>>x&1 for x in range(1<<q)]
 for i in range(q):
  for x in range(1<<q):
   if not(x>>i&1):a[x],a[x|1<<i]=a[x]+a[x|1<<i],a[x]-a[x|1<<i]
 return a
def witness(t,F,q):
 v=(1<<(1<<q))-1
 for j,f in enumerate(F):
  if not(t>>j&1):v&=~f
 return v
cnt=diff=updates=faces=0
for q in range(1,7):
 C,F=carrier(q);n=len(C);U=(1<<(1<<q))-1
 ts=range(1<<n) if q<=2 else [rng.getrandbits(n) if j%2 else ((1<<n)-1)^sum(1<<i for i in rng.sample(range(n),rng.randrange(min(n,12)+1))) for j in range(150)]
 for t in ts:
  v=witness(t,F,q);s=walsh(v,q);m=[]
  for (I,p),f in zip(C,F):
   val=sum((-1)**((p&a).bit_count())*s[sum((a>>j&1)<<i for j,i in enumerate(I))] for a in range(1<<len(I)))
   assert val==(v&f).bit_count()*(1<<len(I));m.append(val//(1<<len(I)))
  sig=sum((x>0)<<i for i,x in enumerate(m));assert witness(sig,F,q)==v;cnt+=1
  u=rng.getrandbits(n);w=witness(u,F,q);mm=[(w&f).bit_count() for f in F]
  assert (v^w).bit_count()<=sum(abs(a-b) for a,b in zip(m,mm));diff+=1
  j,l=rng.randrange(n),rng.randrange(n);I,p=C[j];Q=U^F[j];R=U^F[l];ss=walsh(v&Q,q)
  for h in range(1<<q):
   a=sum((-1)**((p&z).bit_count())*s[h^sum((z>>j&1)<<i for j,i in enumerate(I))] for z in range(1<<len(I)))
   assert (1<<len(I))*ss[h]==(1<<len(I))*s[h]-a;updates+=1
  aa=[v&(Q if i else U^Q)&(R if j else U^R) for i,j in product((0,1),repeat=2)]
  assert sum(aa)==v and all(not(a&b) for a,b in combinations(aa,2))
  perm=list(range(1<<q));rng.shuffle(perm)
  def move(v):return sum((v>>x&1)<<y for x,y in enumerate(perm))
  for i,j in product((0,1),repeat=2):
   assert move(aa[2*i+j])==move(v)&(move(Q) if i else U^move(Q))&(move(R) if j else U^move(R));faces+=1
  assert sum(walsh(a,q)[0] for a in aa)==s[0]
assert (cnt,diff,updates,faces)==(860,860,19032,3440)
def basis(rows):
 piv={}
 for r in rows:
  r=[x%101 for x in r]
  for i in range(len(r)):
   if not r[i]:continue
   if i in piv:
    z=r[i];r=[(a-z*b)%101 for a,b in zip(r,piv[i])]
   else:
    z=pow(r[i],-1,101);piv[i]=[a*z%101 for a in r];break
 return list(piv.values())
rankchecks=0
for q in range(1,6):
 C,F=carrier(q);n=1<<q
 for r in range(q+1):
  B=basis([[(-1)**((x&h).bit_count()) for x in range(n)] for h in range(n) if h.bit_count()<=r])
  for ell in range(3):
   assert len(B)==sum(comb(q,j) for j in range(min(q,r+3*ell)+1));rankchecks+=1
   if ell==2 or len(B)==n:continue
   B=basis(B+[[a*(1-(f>>x&1)) for x,a in enumerate(b)] for b in B for f in F])
assert rankchecks==60
def vp(x,p):
 if not x:return 10**9
 v=0
 while x%p==0:x//=p;v+=1
 return v
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def jet(f,a,k):return sum(f[i]*comb(i,k)*a**(i-k) for i in range(k,len(f)))
hermite=lagrange=0
for p,d,Q,J in product((2,3,5),(1,2),range(1,9),range(1,5)):
 nodes=[1+p**d*i for i in range(Q)];f=[1]
 for i,a in enumerate(nodes):
  for _ in range(J-(i==Q-1)):f=mul(f,[-a,1])
 L=J*(d*(Q-1)+vp(factorial(Q-1),p))
 assert len(f)==Q*J and f[0]%p!=0
 vals=[jet(f,a,k) for a in nodes for k in range(J)]
 assert min(vp(x,p) for x in vals)==L;hermite+=1
 if J==1:
  coeff=[]
  for a in nodes:
   c=Fraction(1)
   for b in nodes:
    if a!=b:c*=Fraction(-b,a-b)
   coeff.append(c)
  assert max(vp(c.denominator,p)-vp(c.numerator,p) for c in coeff)==L
  for _ in range(3):
   g=[rng.randrange(-100,101) for _ in nodes]
   assert sum(c*jet(g,a,0) for c,a in zip(coeff,nodes))==g[0];lagrange+=1
assert (hermite,lagrange)==(192,144)
```

### Active P0 endpoint ledger

| Gate | Deliverable | Status |
|---|---|---|
| G56 | lowDegreeSourceRelationDetermination / signedLocalDifferenceBound | derived and tested; original width-three carrier only |
| G57 | signedClauseFourierUpdate / exactLinearFutureHorizonRank | derived and tested; Q/odd-field linear model, not time |
| G58 | indexedSourceResidualHyperfabric | derived and chart atoms tested; H05 source labels, zero mode, signed loss/gain preserved |
| G59 | clusteredHermitePrecisionCollision / simpleNodeSharpPrecision | derived and tested for stated integral-polynomial observer; actual source-image attachment open |
| N4/G12a | unrestrictedSerialCharge | OPEN: all legitimate nonlinear, signed and shared computation, no imposed linear summary or interpolation representation |
| N5/G12c | unrestrictedSuperpolynomialGrowth | OPEN: G48 uniform flag / G38 nonuniform central slice |
| N6 | originalClayTransport | conditional #1040 terminal / #1129 costed coverage |

Aristotle BIDI: G56 shows the full source is determined by small exact low-order interface, but G57 prevents naive closed linear updates; neither implies exponential algorithmic time. G59 is a concrete inherited-precision control on low-final-precision shortcuts; verify the actual deformation polynomial image and nodes before importing it. Prioritize a paid producer for the flag or actual useful contraction factors, and test both source-specific precision reduction and its obstruction; do not impose exact high modes, universal context support, full count or fixed observer as a necessary prerequisite to original SAT decision. Preserve independent indices and signed/zero modes as semantics, not mandatory materialization. Direct uniform endpoint remains P0. No P!=NP claim or extra certification phase.


## 26. P0-G60–G64 — actual multilinear producer, precision-aware degree pruning and joint support matching (2026-11-24)

Controlling endpoint: literal Clay P vs NP. Both user pasted files read at /mnt/data/Pasted text.txt and /mnt/data/Pasted text (2).txt: Langlands R92–R96 (reported #1549/#120 heads ef1661868132/e97832116b0a) and G56–G59. Both P0 branches read live at 970b7f363c41 / 4da19bd486b3, common blob 123338b300164bf7442da0e9cd5aa9d5325f4b93. Actual source inspected: https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex, Cauchy deformation, packet orientation, mode expansion and child descriptions (not an independent verification of the entire external theorem). Use G13/G45–G48 original selector/flag, G49–G52 count vs support, G53–G55 modular/weighted consumers, G56–G59 low modes and indexed signed residuals; R71–R74 Newton/Smith and R92–R96 taper and lift. Existing #1291/H05 GovernedIndexedResidualCubeExact (blob 42b70ebb7376813076934f2245ce6011b76f10c8), #1006 FactorsThrough/self-reduction, #123 JMD lowering, #1546 sharing, #1474/#1502 reductions, #1129 standard-machine coverage, #1040 terminal, #607/#678 Aristotle. No Langlands/TOE/Monster edits. Classical multilinear Boolean interpolation/Mobius transform used; no claim of novelty for that transform or matching algorithms. The new results are a source-specific degree/valuation/matching interface and exact restrictions on its use.

### G60 — actual multilinear producer degree rather than wire-count degree

In an active call with M real row ports and M real column ports (each side indexed by its named original edge), A(Y),B(X) are products of chosen lifted tensor entries. Source F(T)=sum_X,Y A(Y) B(X) prod_x l_(Y_x)((W(T)X)_x), l_0(z)=1-z, l_1(z)=z. Define Atilde(Z)=sum_Y A(Y) prod_x l_(Y_x)(Z_x)=sum_S a_S prod_(x in S) Z_x; unique multilinear extension with coefficients by subset Mobius inversion. Exactly

    F(T)=sum_X B(X) Atilde(W(T)X).

Since the row vertices' port sets are disjoint, Atilde is the product of their local multilinear extensions. Degree d_A is the sum of local degrees over Q for nonzero integer tensors (over rings use <= sum). Zero tensor implies zero contraction. Degree F<=d_A(2L-1), not necessarily M(2L-1). No change to the original contraction. Reversing the network sides and constructing the packets for that orientation permits degree <=min(d_A,d_B)(2L-1) at the chosen call; do not claim the two deformed polynomials are identical or ignore the packing requirements. With fixed active nodes and multiplicity parameter C from R93, sufficient linear taper becomes ceil((d_A(2L-1)+1)/C), including the smaller valid degree bound, subject to the rest of the source proof's constraints. This is a degree reduction, not an end-to-end asymptotic result.

At target origin precision 2^h, choose the local multilinear coefficients modulo 2^h, retaining explicit signed or canonical coefficient representatives, and evaluate those polynomials on Boolean inputs to give alternate integer lifts of local tensor entries. Every changed entry agrees modulo 2^h with its original. These lifts can delete all coefficients divisible by 2^h, and the resulting alternate deformation has degree bounded by the sum of the largest nonzero coefficient degrees in the local modular tables. It has the same F(0) mod 2^h. In addition the two entire local patch polynomials agree coefficientwise modulo 2^h by patch integrality and congruence of multilinear coefficients. They need NOT agree at the higher inherited precision required by Hermite recovery. Any use of the reduced degree requires running the recovery on the coherent alternate lifted deformation, NOT substituting its bound into an unchanged source algorithm or silently lifting residues again. Keep creation precision, chosen coefficient representatives, alternate-lift recipe, and actual difference (an integer multiple of 2^h at the tensor entry) separately indexed; retain R96 carry defects. If using canonical entry lifts as mandated by the existing source recursion, only their actual integral degree bound is immediate. Computing local coefficients explicitly costs O(r*2^r) ring operations for arity r by subset transform; for succinct high-arity tensors this is not a free polynomial operation. Polynomial for bounded arity; any full recursion integration must charge extraction and altered recipe evaluation. No claimed improvement to the published runtime.

### G61 — signed exact original contraction and degree/valuation profile

Let Btilde(X)=sum_U b_U X^U, with identical conventions for the columns. Boolean X_i^2=X_i gives the exact original origin contraction

    F(0)=sum_(S,U) a_S b_U 2^(M-|S union U|).

At precision 2^h terms with v2(a_S)+v2(b_U)+M-|S union U|>=h are exactly zero. In particular parity is sum over S union U=[M] of the products of coefficient parities. This is signed Mobius arithmetic on source supports, not a nonnegative term-count lower bound; equal supports combined before testing cancellation. At each patch W(t+alpha z) has coefficients in Z_2, so the same expansion of Atilde(WX) Btilde(X) has X support at most |S|+|U|. Let a_i=min_{|S|=i} v2(a_S), b_j=min_{|U|=j} v2(b_U), infinity for absent coefficients. Then coefficientwise content v2(F(t+alpha z)) is >=

    min_(i,j) (a_i+b_j+max(0,M-i-j)).

This holds for the whole integral local polynomial, not just its constant coefficient. In particular if d_A+d_B<M, parity vanishes everywhere (and at origin). A zero modular result does not certify UNSAT; the exact integer zero mode and original witness source remain distinct from this observation. G54 weighted fingerprints are admissible, changing the actual truth graph with paid overhead.

Profiles for products of local tensors on disjoint ports are min-plus convolutions of their local profiles: each global support has one local decomposition, so no artificial independent charge for overlapping coordinates. With explicit local tables, the convolution is polynomial in M and table input size. For sparse row-side multilinear expansion, evaluate at origin without interpolation: mu_B(S)=sum_X B(X) X^S = product_v sum_{X_v} B_v(X_v) X_v^(S intersect ports(v)). These local moments are superset zeta transforms of local tables (or computed directly with charged cost). Then F(0)=sum_S a_S mu_B(S). Given all local tables, with at most K row monomials, O(poly(M,table lengths)+K*poly(M)) ring operations suffice by enumerating local support choices (skip zero factors). Constant total row degree yields polynomial K; arbitrary product of sparse local tables may have exponential K. This is a direct modular/exact contraction shortcut, not a universal polynomial SAT solver. Bit precision and coefficient production must be charged.

### G62 — exact valuation of every actual scaled Cauchy entry

Use original grid G={-L,...,L-1}, L=2^a, alpha=2L, C(T)=prod_{s in G}(T-s), W_xy(T)=C(T)/(C'(0)(T-d)), d=y-x. For an actual node t in G and real row/column within same packet, define coefficientwise content lambda_t(x,y)=min over coefficients v2(W_xy(t+alpha z)). Then

    lambda_t(x,y)=0 if d=t,
                  a+1-v2(t-d) otherwise.

Proof: grid complete mod 2^(a+1); for s!=t, v2(t-s)<=a, so each linear factor t-s+alpha z has exact content v2(t-s), while t-s=0 gives exact content a+1. Content is additive under products over Q_2[z] (divide by minimal powers and multiply nonzero reduced polynomials over F2). The common derivative denominator has valuation sum_{s!=t} v2(t-s), independent of node. Remove factor d; formula follows. Cross-packet entries are zero (infinite content), padded ports absent, not additional independent choices. Thus modulo 2^h, any off-shift entry can only survive when v2(t-d)>=a+2-h; at h=1 only exact shift survives. No claim that computing the shifted node solves the original origin. Actual packet orientation uses this shift to align distinct group symbols; simply reindexing columns to restore original equality also restores the original cross-group dependencies. An invertible chart cannot make those original edges disappear. This is why replacing Hermite recovery with the origin shift alone is not an algorithmic improvement.

### G63 — exact joint-support valuation floor for each source monomial pair via matching

For given nonzero a_S,b_U in the actual source, expand Atilde(WX): choose map phi from row support S to real columns, using finite-cost packet entries. A row with no available entry makes its term zero, handle separately. The contribution of the choice has coefficientwise valuation exactly

    v2(a_S)+v2(b_U)+sum_(x in S) lambda_t(x,phi(x))
                         +M-|U union image(phi)|,

for the single product term before summing different choices. This follows from content additivity and Boolean cube summation; repeated columns contribute only once to the image. The floor across all maps has a polynomial matching solution. Define mu_x=min_y lambda_t(x,y), build bipartite graph on S and [M] minus U with edges at lambda_t(x,y)=mu_x, and let nu(S,U,t) be maximum matching size. Then

    min_phi [sum_x lambda_t(x,phi(x))+M-|U union image(phi)|]
       = sum_x mu_x + M-|U| - nu(S,U,t).

Proof: For any phi choose one distinct row representative for each distinct image outside U; they form a matching. Each such row with cost above mu_x pays at least one additional valuation digit (integer costs), cancelling its one-unit support benefit. Thus benefit minus extra cost <= maximum matching of cheapest edges. Conversely choose maximum matching on cheapest edges and assign all unmatched rows any cheapest column. No new outside-U column can be reached by an unmatched row at cheapest cost, since adding that edge would enlarge the matching; hence the attained value is exactly RHS. This is an exact minimum on the actual maps, not an assumption of independent row work. It is >=max(0,M-|S|-|U|), the earlier degree-only bound, and may be strictly stronger. Add coefficient valuations then minimize over supported pairs gives a sound lower bound on actual patch content. It is NOT equality for the sum: additional signed cancellation may occur between minimal terms. If the bound is >=h all terms vanish at requested patch precision. A pair can be pruned independently if its floor is >=h. Computing matching is polynomial PER chosen pair, but the pair family can be exponential. Do not claim polynomial total selection or infer time lower bound from the matching number. At origin W(0)=I, there is only phi(x)=x and we recover G61 exactly; no generic patch interpolation required on sparse cases. This retains source support overlap (zero mode and residual, no double charge) while admitting arbitrary shared computation.

### G64 — indexed precision and resource consequences

Retain (history,tau,k,j,version,coefficient ring,creation precision,requested precision,node,consumer) as independent coordinates; tau event time, k source chart/refinement, j iteration. Each row/column support refers to actual original edge identities and local vertex identities, even after an orientation reversal or invertible chart. The zero mode W and signed Fourier S(h) from G56 remain source semantics; an observed modular zero of a chosen weighted contraction is a separate fact. Retain gain/loss and overlap ledgers G58 and the exact creation-precision carry from R96. The matching graph is transported with the named row/column costs under invertible relabeling; actual degree depends on chosen basis/lift and is not declared invariant under arbitrary chart transformations. Coefficient truncation changes the representation at the requested precision; record the discarded signed coefficients, not an assertion that the original tensor is zero. No mandatory materialization of entire signed spectrum. Actual bounded-arity Boolean tensors can have degree M (e.g. pin every row bit to 1, product of unary pins), and B the same, giving F(0)=1 and no useful degree/support pruning at the origin. This is an easy source control: high degree/valuation budget does not imply intrinsic cost. R95's pinned deformation likewise confirms inherited precision can be an artificial debt. N4 needs actual total work under all legal shortcuts, not degree, channel count, matching count or chosen lift cost. G48 uniform flag and G38 central slice remain OR routes. No proof of P!=NP, no CI/kernel detour, no end-to-end algorithm improvement.

### Actually executed local regression (Python Fraction, exact integer, no CI/native kernel)

Local /tmp/p0_g60.py: 1,302 exact scaled Cauchy entry contents (L=1,2,4,8,16, all nodes and realizable differences); 2,120 exact matching vs exhaustive map minima (L=1,2,4, all nodes and all support pairs); 840 deformed polynomial degree/content/origin checks and 840 alternate-lift comparisons (all 256 pairs of Boolean two-port tables, 24 seeded signed four-port table pairs, nodes -1,0,1 and lift precisions 1,2,3); 240 additional sparse signed polynomial pair comparisons of matching bound vs actual patch content, of which 111 strictly improve the degree-only bound. Initial finite sentinel for infinity caused an all-zero tensor test failure; replaced by actual infinity and reran all successfully. Exact fraction arithmetic throughout, no extrapolation. Core reproduction (helpers for polynomial add/mul with ascending coefficients and vp2 of rational numerator minus denominator, infinity for zero):

```python
from fractions import Fraction as F
from itertools import product
from math import prod
from random import Random
rng=Random(369)
def vp(x):
    if not x:return float("inf")
    x=F(x);n=abs(x.numerator);d=x.denominator
    return (n&-n).bit_length()-(d&-d).bit_length()
def add(a,b):
    c=[F(0)]*max(len(a),len(b))
    for i,x in enumerate(a):c[i]+=x
    for i,x in enumerate(b):c[i]+=x
    return c
def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c
def ct(f):return min(map(vp,f))
def anf(A,m):
    a=list(A)
    for j in range(m):
        for s in range(1<<m):
            if s>>j&1:a[s]-=a[s^(1<<j)]
    return a
def ev(a,x):return sum(v for s,v in enumerate(a) if s&x==s)
def deg(a):return max((s.bit_count() for s,v in enumerate(a) if v),default=-1)
def prof(a,m):return [min((vp(v) for s,v in enumerate(a) if s.bit_count()==d),default=float("inf")) for d in range(m+1)]
def patch(L,t):
    R=range(-L,L);den=prod(-s for s in R if s);out={}
    for d in range(1-L,L):
        f=[F(1,den)]
        for s in R:
            if s!=d:f=mul(f,[t-s,2*L])
        out[d]=f
    return out
def contract(A,B,W,m):
    a=anf(A,m);res=[F(0)]
    for X,b in enumerate(B):
        if not b:continue
        rows=[]
        for i in range(m):
            z=[F(0)]
            for j in range(m):
                if X>>j&1:z=add(z,W[j-i])
            rows.append(z)
        for S,c in enumerate(a):
            if not c:continue
            z=[F(c*b)]
            for i in range(m):
                if S>>i&1:z=mul(z,rows[i])
            res=add(res,z)
    return res
def match(R,V,E):
    matched={}
    def aug(i,seen):
        for j in V:
            if (i,j) not in E or j in seen:continue
            seen.add(j)
            if j not in matched or aug(matched[j],seen):matched[j]=i;return True
        return False
    return sum(aug(i,set()) for i in R)
def bound(C,S,U,m):
    R=[i for i in range(m) if S>>i&1];V=[j for j in range(m) if not(U>>j&1)]
    mu={i:min(C[i]) for i in R}
    E={(i,j) for i in R for j in range(m) if C[i][j]==mu[i]}
    return sum(mu.values())+len(V)-match(R,V,E)
n=0
for L in (1,2,4,8,16):
    a=L.bit_length()-1
    for t in range(-L,L):
        for d,f in patch(L,t).items():
            assert ct(f)==(0 if t==d else a+1-vp(t-d))
            assert (f[0]==0)==(t!=d)
            n+=1
assert n==1302
n=0
for m in (1,2,4):
    a=m.bit_length()-1
    for t in range(-m,m):
        C=[[0 if t==j-i else a+1-vp(t-j+i) for j in range(m)] for i in range(m)]
        for S,U in product(range(1<<m),repeat=2):
            R=[i for i in range(m) if S>>i&1]
            exact=min(sum(C[i][j] for i,j in zip(R,phi))+m-(U|sum(1<<j for j in set(phi))).bit_count() for phi in product(range(m),repeat=len(R)))
            assert exact==bound(C,S,U,m);n+=1
assert n==2120
n=nl=0
for m in (2,4):
    pairs=product(product((0,1),repeat=1<<m),repeat=2) if m==2 else (([rng.randrange(-3,4) for _ in range(1<<m)],[rng.randrange(-3,4) for _ in range(1<<m)]) for _ in range(24))
    W={t:patch(m,t) for t in (-1,0,1)}
    for A,B in pairs:
        a,b=anf(A,m),anf(B,m);aa,bb=prof(a,m),prof(b,m)
        floor=min(aa[i]+bb[j]+max(0,m-i-j) for i,j in product(range(m+1),repeat=2))
        for t in W:
            z=contract(A,B,W[t],m)
            assert all(c==0 for i,c in enumerate(z) if i>max(0,deg(a))*(2*m-1))
            assert ct(z)>=floor
            if t==0:assert z[0]==sum(x*y for x,y in zip(A,B))
            n+=1
        for h in (1,2,3):
            ah=[v%(1<<h) for v in a];Al=[ev(ah,x) for x in range(1<<m)]
            assert all((x-y)%(1<<h)==0 for x,y in zip(A,Al))
            z=contract(Al,B,W[1],m);z0=contract(A,B,W[1],m)
            assert ct(add(z,[-c for c in z0]))>=h
            assert all(c==0 for i,c in enumerate(z) if i>max(0,deg(ah))*(2*m-1))
            nl+=1
assert (n,nl)==(840,840)
n=better=0
for m in (2,4):
    for t in (-1,0,1):
        W=patch(m,t);C=[[ct(W[j-i]) for j in range(m)] for i in range(m)]
        Bnd={(S,U):bound(C,S,U,m) for S,U in product(range(1<<m),repeat=2)}
        for _ in range(40):
            a=[0]*(1<<m);b=a.copy()
            for S in rng.sample(range(1<<m),rng.randrange(1,min(4,1<<m)+1)):a[S]=rng.choice((-2,-1,1,2))
            for U in rng.sample(range(1<<m),rng.randrange(1,min(4,1<<m)+1)):b[U]=rng.choice((-2,-1,1,2))
            A=[ev(a,x) for x in range(1<<m)];B=[ev(b,x) for x in range(1<<m)]
            lo=min(vp(v)+vp(w)+max(0,m-S.bit_count()-U.bit_count()) for S,v in enumerate(a) if v for U,w in enumerate(b) if w)
            hi=min(vp(v)+vp(w)+Bnd[S,U] for S,v in enumerate(a) if v for U,w in enumerate(b) if w)
            assert hi>=lo and ct(contract(A,B,W,m))>=hi
            assert sum(A[x]*B[x] for x in range(1<<m))==sum(v*w*2**(m-(S|U).bit_count()) for S,v in enumerate(a) for U,w in enumerate(b))
            n+=1;better+=hi>lo
assert (n,better)==(240,111)
```

### Endpoint-first ledger

| Gate | Deliverable | Status |
|---|---|---|
| G60 | actualMultilinearProducerDegree / coherentModularCoefficientLift | derived and tested; actual source degree, alternate-lift recursion integration open |
| G61 | exactSignedSupportUnionContraction / localMomentSparseShortcut | derived and tested; zero mode vs observed parity retained |
| G62 | exactScaledCauchyEntryContent | derived and tested on original grid |
| G63 | minimumSupportValuationMatching | derived and tested; exact single-pair minimum, cancellation and total pair generation not solved |
| G64 | indexedPrecisionResourceBoundary | derived; G58/R96, no H05 closure claim |
| N4/G12a | unrestrictedSerialCharge | OPEN: arbitrary algorithms, coherent alternate lifts, support sharing, cancellation and input-dependent contraction |
| N5/G12c | unrestrictedSuperpolynomialGrowth | OPEN; G48 uniform flag / G38 stronger nonuniform slice |
| N6 | originalClayTransport | conditional #1040 / #1129 |

Aristotle BIDI: use the G61 original moment contraction as a legitimate Hermite bypass on sparse sources, and G60/G63 for source-aware pruning on actual packets. Highest-alpha next step is to bound the generation of *surviving* signed support combinations or find a shared contraction of them, with a real cost inequality on full G48 locally-full hard inputs. Do not infer hardness from the artificial choice of deformation or require high degree/large support as a prerequisite. Neither the restricted matching minimum nor the finite checks pay unrestricted N4. No new mandatory certification phase.


## 27. P0-G65–G69 — GEOMETRY-FORWARD: signed separator contraction and exact source-minor transport (2026-11-24)

User direction: geometry-forward; retain original zero mode, signed residual, independent history/time/k/chart/version/precision/consumer indices and actual indexed hyperfabric. Literal Clay P vs NP is P0, not a requirement to materialize every representation. Start with actual source incidence and jointly reusable separator geometry, before polynomial expansion or arithmetic certification; steelman legitimate contractions, BIDI from original SAT endpoint, account for actual work and avoid independently charging overlaps. Both P0 branches read at 549739130a81 / e6a60428933b, common blob 8395076082289854f8f9609b67604285824470e9. Input user pasted G60–G64. Reuse G13 original selector, G16/G17 binary control, G28/G33 parity contraction, G45/G46 locally-full compiler, G48 forced flag, G56–G59 indexed modes, G60–G64 signed support/valuation; #1291 H05, #1006 FactorsThrough, #123 JMD lowering, #1546 shared computation, #1129 machine coverage, #1040 terminal, #1474/#1502 reductions, #607/#678 Aristotle. Reopened actual existing DASHI/Crypto/ConstraintCouplingSearchExact.agda (blob 6972ab099c268b3711dad9ab378d5e8620067c85, disconnected cut and bounded separator accounting; cites Arnborg–Corneil–Proskurowski 1987 DOI 10.1137/0608024); DASHI/Crypto/ObservationSeparatorGeometryExact.agda (blob ccbe9275669def08a2c37cc945c19e61990bece1, before/after separator work and observation cost); DASHI/Codec/IndexedCubeHyperfibreExact.agda (blob ce42b07fbaf430685ce172895cc482f933073577, actual typed cube, version alignment and history/time owner). These are donors, not a claim of native SAT attachment. No TOE, Monster, Langlands or crypto edits. Inclusion–exclusion, tree decomposition dynamic programming and elementary tensor-product evaluation are classical; the source-specific exact transport and pruning control below are derived, not claimed novel general algorithms.

### G65 — exact no-go for valuation-only rejection on actual clause/equality networks

Represent each normalized nonempty non-tautological clause by its Boolean allowed-pattern tensor, with independent occurrence ports; each used original variable has an equality tensor over its occurrences. Isolated variables are separated with factor 2 each for exact counts (or ignored for decision). For each clause its full-support integer multilinear coefficient is +1 or -1, since the forbidden-pattern indicator is a product of one literal factor per port and the clause indicator is one minus that product. The constant coefficient of every used-variable equality tensor is 1 (all-zero assignment accepted). Therefore the row tensor product has full support S=[M] with odd coefficient, and the column tensor product has empty support U with coefficient 1. At origin G61's individual contribution a_S b_U 2^(M-|S union U|) is odd, independently of satisfiability. The minimum individual valuation is exactly zero on every such network, including UNSAT. If no clauses, the empty network contraction is 1 after removing isolated variables. Thus an optimizer that merely computes the best individual support valuation cannot establish that all terms vanish modulo 2, even on UNSAT. Actual cancellation and joint contraction are necessary in this representation. This does not exclude other semantic decision algorithms or pruning after shared aggregation.

### G66 — source-variable signed cover algebra

For each selected clause C let E_C(x) be its forbidden pattern indicator on its original scope I_C. Then b(x)=prod_C(1-E_C(x)). Expanding on original clause choices J, the joint forbidden-pattern product vanishes if two assignments disagree on a common original variable; otherwise it fixes exactly the union D(J) of those scopes. Hence

    W = sum_(compatible J subset clauses) (-1)^|J| * 2^(q-|D(J)|).

This is classical inclusion–exclusion with exact source overlap and signed coefficients; no independent occurrence charge or cancellation-free relaxation. At mod 2^h, compatible J with q-|D(J)|>=h vanish, but the remaining sum can cancel. Retain each original variable's three partial-pinning basis states e_0 (neutral/unassigned, TWO extensions), e_- (pin Boolean zero), e_+ (pin Boolean one); conflict is algebraic zero, not e_0. Define e_0 as multiplicative unit, e_-^2=e_-, e_+^2=e_+, e_-e_+=0. This is a commutative associative rank-three algebra over integers (or any chosen coefficient ring); tensor over named variables. A clause is 1 minus the product of its actual forbidden pins. The sum-over-assignments functional on a variable sends e_0 to 2 and each signed pin to 1. Tensor evaluation of the product gives the exact count. Keep signed sums rather than support-only saturation.

### G67 — geometry-first elimination and exact frontier contraction

Given an ordering of the actual clauses, introduce original variables at first occurrence; after last occurrence eliminate them by the extension functional. At a step use the set of live variables including current scope, of size <=w (this is a bag size, not graph width minus one). Maintain a signed partial-pin coefficient table D on 3^w basis states. New clause: keep each old contribution and subtract its compatible pin refinement; incompatible refinement is zero. When eliminating a variable multiply each entry by 2 if neutral, 1 otherwise, aggregate identical residual states. This is exactly the signed cover formula grouped by boundary; no exponential expansion in the number of clauses is required if w is small. Cost O(poly(input length)*3^w) ring operations for this supplied order, O(3^w) table entries; bit costs charged (coefficients bounded by 2^(number of processed clauses+q)). Isolated variables multiply 2 in final count. For arbitrary tree decomposition of the primal graph (edges join variables co-occurring in a clause), assign each clause to a bag containing its scope (clique property of subtrees of a tree). Use standard tree DP with Boolean boundary assignments: multiply child messages on bag assignments and local clause indicators, sum over bag variables not on parent intersection. Running intersection ensures eliminated variables never reappear in another branch, and every clause used once. With bag size <=w+1 and polynomially many bags, cost poly(input, decomposition size)*2^(w+1) operations; count bit length O(q), modular version valid. Decomposition search is not free. This is an upper bound for a supplied geometric decomposition, not a lower bound for arbitrary algorithms. Decision can use OR rather than signed summation if only nonemptiness needed.

### G68 — exact consumer quotient and zero/signed modes

The evaluation map on the partial-pinning algebra is e_0 -> (1,1), e_- -> (1,0), e_+ -> (0,1); target has pointwise multiplication. It is a surjective algebra homomorphism. Kernel generated by e_0-e_--e_+; for w named live variables the tensor product map onto functions on {0,1}^w is surjective and has free integer kernel rank 3^w-2^w (tensor pin basis gives an explicit splitting). This remains a quotient over any coefficient ring. The kernel is a consumer-invisible dependent residual, not equality of the original source histories. Multiplying by clause filters, introducing a neutral variable and eliminating by extension functional commute with evaluation, since extension functional is sum of the two evaluation coordinates. Hence the entire signed cover DP can be jointly compressed to the actual binary boundary evaluation table without enumerating any global support pairs. For the fixed interface of arbitrary signed boundary functions and all future full pin contexts, the 2^w linear output coordinates are independent (each pin queries one function value). Not a standard-machine lower bound; source structure may allow cheaper implicit states. Fourier coordinates on this boundary have zero mode sum and signed modes sum_b f(b)(-1)^(h dot b). One-bit transform gives f_0+f_1, f_0-f_1; recovering f from integer modes modulo 2^p requires up to w additional binary precision digits for inverse Walsh, not an unconditional precision requirement for algorithms staying in evaluation coordinates. Keep explicit neutral provenance and source label even when the chosen consumer uses quotient, retain signed gain/loss and actual face defects per G58/G64. Coordinate permutations intertwine evaluation; arbitrary lossy chart changes need their own residual. No blanket H05/H07/H14 commutation assertion. The processed constraint history remains separately indexed from the geometric elimination order; reordering factors preserves terminal count but changes intermediate signed records.

### G69 — locally-full compiler preserves actual primal separator geometry up to a constant

Let original normalized selected width<=3 clauses have primal graph G, treewidth w, with isolated original vertices included. G46 creates private literal occurrence copies, the six globally-zero gadget variables Z, and equality clauses linking each copy to its original via one of Z. It may create copies for inactive selector clauses too. In the compiled primal graph G', delete Z, contract each copy-original edge, and discard loops/duplicate edges. The resulting graph is exactly G: equality clauses become loops, active clause copies become original clause scopes, inactive copies add no edges between distinct originals. Thus G is a minor and tw(G')>=tw(G) (minor monotonicity follows by deleting vertices from bags and merging the connected occurrence subtrees of endpoints of a contracted edge, which share a bag).

For upper bound take any tree decomposition of G. Add all six Z vertices to every original bag. Every active clause scope I is contained in some original bag (pairwise intersecting connected subtrees of a tree have common intersection); attach a leaf containing I, its <=3 private copies, and all six Z. Its size <=12. For inactive clause occurrences attach one leaf per copy containing its original, copy and all six Z to a bag containing that original. Every compiled equality edge and active clause edge is covered, and each vertex's bags stay connected. All gadget edges are covered by Z in original bags. Hence

    tw(G) <= tw(G') <= max(tw(G)+6, 11).

This applies to the ordinary G46 compiler with arbitrary selected clause pattern, including the universal occurrence allocation. Balanced inert alternatives only involve one copy and Z, already covered by its leaf. It is an actual graph transport, not an assumption that locally unrestricted tensors are intrinsically difficult. Given original decomposition the above construction has polynomial cost in compiled input length; no claim of efficient optimal treewidth computation. In particular G46 can hide all local unary, affine and parity reductions while preserving bounded-treewidth exact contraction. Conversely large primal treewidth alone is not a time lower bound: the formula imposing equality on every pair has complete primal graph, yet only two satisfying assignments and trivial signed-component contraction. Its G46 locally-full compilation has at least that treewidth by minor transport and is also easy by recognizing the constant gadget/occurrence equality construction. The key target is cost after all *semantic* graph contractions, not raw width, expanded monomials or local affine rank.

### Actual local regression, no CI/native kernel

Executed /tmp/p0_geometry_forward.py with exact Python integers: 660 original formulas (all 260 selectors q=1,2; 100 seeded formulas at each q=3..6), including 311 UNSAT, comparing signed frontier DP and binary boundary DP to full enumeration. 86,402 actual boundary evaluation equalities checked. Independently checked 300 signed union expansions on q=1..5 with up to ten clauses. Checked 180 actual G46 primal decompositions and contracted graph equality, q=1..6, 30 seeded active selector sets per q, allocating all private occurrences. All passed. Reproduction core for signed and evaluation contraction (forbidden patterns in tuples, no implicit witness pruning):

```python
from itertools import combinations,product
from collections import defaultdict
from random import Random
rng=Random(369)
def clauses(q):
 return [(I,p) for d in range(1,min(3,q)+1) for I in combinations(range(q),d) for p in product((0,1),repeat=d)]
def brute(q,C):
 return sum(all(any((x>>i&1)!=v for i,v in zip(I,p)) for I,p in C) for x in range(1<<q))
def dp(q,C):
 last={i:j for j,(I,p) in enumerate(C) for i in I}; first={}
 for j,(I,p) in enumerate(C):
  for i in I:first.setdefault(i,j)
 D={():1}; E={():1}; active=[]; checks=0
 for j,(I,p) in enumerate(C):
  new=sorted(i for i in I if first[i]==j);active+=new;ix=[active.index(i) for i in I]
  T=defaultdict(int)
  for a,v in D.items():
   b=a+(-1,)*len(new);T[b]+=v
   if all(b[k] in (-1,s) for k,s in zip(ix,p)):
    z=list(b)
    for k,s in zip(ix,p):z[k]=s
    T[tuple(z)]-=v
  V=defaultdict(int)
  for a,v in E.items():
   for x in product((0,1),repeat=len(new)):
    b=a+x
    if any(b[k]!=s for k,s in zip(ix,p)):V[b]+=v
  for x in product((0,1),repeat=len(active)):
   assert sum(v for b,v in T.items() if all(a==-1 or a==s for a,s in zip(b,x)))==V[x];checks+=1
  keep=[k for k,i in enumerate(active) if last[i]>j];gone=[k for k,i in enumerate(active) if last[i]==j]
  D=defaultdict(int);E=defaultdict(int)
  for a,v in T.items():D[tuple(a[k] for k in keep)]+=v*2**sum(a[k]==-1 for k in gone)
  for a,v in V.items():E[tuple(a[k] for k in keep)]+=v
  active=[active[k] for k in keep]
 assert D[()]==E[()]
 return D[()]*2**(q-len(last)),checks
n=checks=unsat=0
for q in range(1,7):
 C=clauses(q)
 Fs=([C[i] for i in range(len(C)) if t>>i&1] for t in range(1<<len(C))) if q<=2 else (rng.sample(C,rng.randrange(min(20,len(C))+1)) for _ in range(100))
 for F in Fs:
  ans,c=dp(q,F);assert ans==brute(q,F);n+=1;checks+=c;unsat+=ans==0
assert (n,checks,unsat)==(660,86402,311)
```

Additional executed tests: 60 seeded formulas each q=1..5, select up to 10 clauses; enumerate all clause subsets, maintain map variable->forbidden bit, add (-1)^|J| times 2^(q-len(map)) only when no conflict; compare brute. For graph tests after those seeded draws: q=1..6, 30 trials each, choose up to 12 selected clauses from all possible patterns, build original path decomposition by first/last occurrence plus singleton bags for isolated variables, extend bags by Z and append leaves exactly as G69. Check every compiled scope contained in a bag, every vertex's bag subgraph connected by DFS, max bag size minus one <=max(original width+6,11), and quotient edge set after deleting Z and mapping private copies to originals equals original selected-clause primal edges. No measured asymptotic performance or native certification claimed.

### Endpoint-first ledger

| Gate | Deliverable | Status |
|---|---|---|
| G65 | actualClauseEqualityZeroValuationControl | derived, all normalized nonempty clause networks after free-variable removal |
| G66 | signedOriginalCompatibleCover / inhabitedNeutralPinAlgebra | derived and tested |
| G67 | chronologicalSeparatorContraction / suppliedTreeDecompositionDecision | derived, exact frontier tests; classical bounded-width algorithm |
| G68 | ternaryBoundaryEvaluationQuotient / indexedSignedModeTransport | derived and tested; consumer-specific, retain source and precision |
| G69 | locallyFullCompilerPrimalMinor / boundedWidthTransport | derived and tested; source graph, not intrinsic cost |
| N4/G12a | unrestrictedSerialCharge | OPEN: must survive semantic geometry contraction, arbitrary sharing and other nonlocal algorithms |
| N5/G12c | unrestrictedSuperpolynomialGrowth | OPEN; G48 uniform flag or G38 stronger nonuniform slice |
| N6 | originalClayTransport | conditional #1040/#1129 |

Geometry-forward continuation: identify actual source separators after legitimate semantic contraction and study a global resource inequality or an exact shortcut on G48. Do not require all algorithms to use these separators, or charge width, signed cover size, channel dimension, individual valuation, or precision debt as unavoidable cost. G65 rules out valuation-only rejection; G69 lets us separate actual geometric hardness from merely hiding locally visible reductions. The neutral zero mode and signed residual are retained through the typed source/consumer hyperfabric, but materialization is optional. Keep direct uniform endpoint active. No additional mandatory certification phase and no P!=NP claim.


## 28. P0-G70–G74 — geometry-forward two-sided bijunctive fibres and guarded implication transport (2026-11-24)

Controlling endpoint literal Clay P vs NP. User continuation of G65–G69, attached source read in container; geometry-forward, retain original zero mode, inhabited neutral fibre, signed residual and indexed hyperfabric. Both roadmaps read live at 7dcee418032a / c315cce7c3d8, common blob 89d6606ba60c7e5626218d4b48f3f21455362374. Producers: G13 original selector, G16 median/pair-hull, G17 implication reachability, G22/G30 compressed CLIQUE, G45–G48 locally-full compiler/flag, G51 canonical consumer quotient, G56–G59 modes/history, G65–G69 signed separator and graph minor; existing ConstraintCouplingSearchExact, ObservationSeparatorGeometryExact, IndexedCubeHyperfibreExact (section 27), #1291 H05, #1006 FactorsThrough and decision-to-witness, #123 JMD lowering, #1546 sharing, #1474/#1502 reductions, #1129 costed machine coverage, #1040 terminal, #607/#678 Aristotle. Standard 2-SAT implication graph and median closure are classical; source-specific compiler and two-sided transport derived here. No claim of novelty for general restricted-SAT hardness, no native kernel execution or CI. No changes to other programmes.

### G70 — crossing ternary geometry, both conditional fibres bijunctive

Partition source variables into L,R. Suppose every selected clause meets both sides and has width <=3. Fix any assignment x on L. Delete each clause already satisfied by x, remove all its remaining left literals from the others. Every residual clause on R has width 1 or 2 (no empty clause since original clause crosses). Similarly fixing y on R yields 2-CNF on L. Each conditional existence query therefore has a polynomial implication-graph algorithm; no assertion that conditional exact counts are polynomial. General cut of any width-three formula has this property for the crossing clauses ONLY, not arbitrary internal right/left clauses.

### G71 — exact semantic separator and signed class contraction

For a 2-CNF H on r right variables, and any boundary subset B, its existential projection to B is majority-closed: the solution relation of each binary clause is majority-closed, intersections preserve this, and three projected witnesses can be lifted and combined by coordinatewise majority. G16 then recovers the projected relation exactly from unary/binary pattern supports. Compute these supports by polynomially many 2-SAT queries with one or two pinned variables; separately test satisfiability and represent empty relation by an explicit bottom marker (also valid for B empty). Output canonical formula K_B(H): forbid all missing unary/binary patterns on B. This is a polynomial-time source-specific semantic contraction for decision. At B=R the key kappa(x)=K_R(F_x) is equal iff the right witness relations are equal. For every future context on R alone, equality of keys implies equal count and existence for that fixed left assignment; different keys distinguished by a full right pin context. This is the minimal equivalence relation for all those contexts, not a minimal bit representation or lower bound on arbitrary computation. Existential projection onto a proper subset does NOT preserve conditional multiplicities: y OR z projects to both y values but has 1 and 2 extensions respectively. Keep count weights when the consumer needs them.

For each key K, let X_K be its actual source fibre of left assignments. With original left/right independent weights a(x),c(y) (including signed Fourier characters, or symbolic witness weights), the exact sum is

    Z = sum_K (sum_{x in X_K} a(x)) * (sum_{y models K} c(y)).

For a general cut, internal left constraints filter X_K and internal right constraints multiply the second sum; crossing residual key remains 2-CNF but internal right SAT may not. For unweighted count this retains W as zero mode; for signed modes retain h_L,h_R independently and their products. A zero signed class weight does not imply an empty X_K; retain its inhabited support, source provenance and gain/loss separately. All additions and multiplications in the coefficient ring, creation precision and lift residual as G64. Original chronological history tau and refinement/chart k independent of chosen cut/elimination order, and original labels transported in any chart. Grouping is exact for fixed crossing source and future right-only contexts. A new crossing event can split a class; retain original source descriptions rather than assert canonical keys alone suffice for arbitrary updates. G58 six-face source mask identity and dependent residual remain separate from any lossy quotient.

Computing one key costs polynomial in input and r, but generating all reachable keys and multiplicities may be exponential. Example r independent crossing equalities x_i=y_i: each x induces its own singleton right relation, 2^r keys, even though whole formula is easy and primal graph a matching. Thus number of semantic classes cannot be charged independently to unrestricted time. Another control: all crossing binary clauses not x_i OR y_j have complete bipartite primal graph, but only two residual keys (all y free if x=0, all y pinned 1 otherwise); large width need not imply many keys.

### G72 — explicit locally-full crossing-only parsimonious compiler

Construct eight zero-gadget variables Z indexed 0..7, with left Z0..Z3, right Z4..Z7. List in lexicographic order all 48 triples I with min(I)<4<=max(I); forbid the little-endian pattern given by the corresponding digit of

    737362511425175275471342317614566635167417725234

Every digit nonzero. Exact exhaustive enumeration of 256 assignments (reproducer below) gives unique all-zero solution. Each clause allows 7/8 patterns, all unary/pair projections and affine hull full as in G45. Every clause crosses the named partition. This is a fixed finite source witness, not an assumed new forcing theorem.

For arbitrary normalized width<=3 input formula/selector on q original variables, put originals on L. Allocate distinct private copies a per literal occurrence for each possible original clause (or just given list). First copy on L, later copies on R. For every occurrence of x add

    (not x OR a OR Z6), (x OR not a OR Z7).

Both cross, with distinct scopes and global equality because Z6=Z7=0. For each selected original clause use its occurrence copies with original signs, pad a unit with Z4,Z5 and a binary with Z0. All ternary clauses now cross, every scope unique: private copies separate main clauses, equality clauses contain original variables, gadget contains neither. Every local relation on a selected triple has exactly one forbidden pattern and all other scopes full. Original witness extends uniquely by copies and fixed gadget; converse by original clause semantics. Selector projection uses only constants and original unnegated absent-clause bit (one per main clause), so monotone. Output variable count O(q+total occurrences) and full selector length polynomial. Hence SAT on this promise is NP-complete, exact witness count preserved, despite all local affine/pair projections being full and every one-side pinned conditional decision in P. This also applies to G48's always-inhabited known-witness flag construction. The flag can remain on L, with exact original b=0 and b=1 fibre counts unchanged. No claim of P!=NP.

Fixed-weight option: if original main clause inactive, select the inert alternative (a_first OR not Z6 OR Z7). Crosses and distinct from main/padded equality scopes; always true globally. Exactly one main/alternative per original clause, so total selected count 48+2*occurrences+number of clauses, independent of input. This is a complemented projection, not monotone. No central-weight assertion. Empty source formula permitted; original empty clause handled separately by fixed UNSAT or pre-normalization.

Geometry transport: deleting Z and contracting occurrence-original edges gives original primal graph exactly. Add eight Z to each bag of original tree decomposition; attach leaf of active scope originals + up to three copies + Z, size <=14. Inactive copies attach individually to original bag with Z; inert alternative contained there. Thus tw(G)<=tw(G')<=max(tw(G)+8,13). Given original decomposition construction polynomial; no assumption of polynomial optimal treewidth. The locally-full crossing constraint need not inflate geometric width asymptotically.

### G73 — guarded implication paths: shared polynomial residual evaluator, not a polynomial joint selector

For each crossing clause C write its left literals and right literals separately. Let g_C(x) be conjunction of the negations of its left literals; length <=2. This is the exact activation guard of its right residual clause. Build a symbolic implication graph on the 2r right literals. A residual (u OR v) supplies edges not u -> v and not v -> u, both labelled g_C; unit treated as u=v. OR duplicate edge guards, include identity reachability. Compute symbolic transitive closure by Floyd–Warshall using shared AND/OR gates:

    A^(k+1)_ij = A^k_ij OR (A^k_ik AND A^k_kj).

For each fixed x, induction gives exactly the actual right implication reachability. Define bad(x)=OR_i (A_(i+,i-)(x) AND A_(i-,i+)(x)). Then good(x)=not bad(x) iff right fibre inhabited. Symbolic evaluator has O(number of clauses+r^3) bounded-fanin gates, uniform polynomial construction in original input and source labels; negated left literals shared, one final NOT for complement; no unrolling of path families or semantic class enumeration. All guard dependencies retained (not independent switches). This is a legitimate global joint *representation* shortcut beyond G71. It returns the exact Boolean function of left variables whose nonemptiness is the original problem. If both sides nonempty, |L|<=O(log N) yields polynomial enumeration of left assignments (similarly right); no such bound for all instances. Finding x with good(x)=1 remains NP-complete by G72. For UNSAT, every left assignment activates contradictory two-way paths, but may activate different paths. The circuit computes this universally indexed failure predicate on each input; it does not decide its tautology for free. This isolates the actual global existence operation while allowing shared paths, different orderings, signed cancellation and alternate representations. No lower bound on arbitrary algorithms from count of paths, classes or reachability matrix entries.

### G74 — retain G30's actual restricted lower bound on this geometry

Rechecked Błasiok–Meierhöfer CCC 2025 Corollary 5, https://drops.dagstuhl.de/storage/00lipics/lipics-vol339-ccc2025/html/LIPIcs.CCC.2025.4/LIPIcs.CCC.2025.4.html. Use G22's O(n)-variable fixed threshold circuit/clauses for choosing at least k vertices. Put original vertex and gate variables on L. Compile only fixed threshold clauses via G72; conditional missing-edge clause (not x_i OR not x_j OR Z4) crosses and occupies distinct scope (two original variables, one zero gadget). All emitted constraints locally-full and crossing, total m=Theta(n), N=Theta(n^3). Every conditional clause depends monotonically on one graph edge bit in absent-clause coordinates. Exact CLIQUE projection preserves gate size (and actual NOT count for G25's separate restricted theorem). Taking k=floor(n^(5/12)), delta=1/24 as G30 yields 2^Omega(N^(5/36) log N) monotone size lower bound on the promise. Thus even every conditional fibre's tractable decision does not remove the established monotone lower bound for selecting one. This is a restricted-model result, NOT a lower bound for general circuits or for computing the guarded evaluator on a specified x. Fixed-weight alternative uses complemented projection; no monotone transfer there.

### Actual local execution (Python integers, no CI/kernel)

Ran /tmp/p0_cross.py. Found fixed gadget at first seeded draw Random(369), exhaustive all 256 assignments gives unique zero. 580 full compiler model counts (all 260 original q=1,2 selectors, 30 seeded q=3, both ordinary and fixed-weight alternatives) checked by independent exact DPLL on complete emitted clauses, no pre-set gadget values; 50,865 emitted clauses checked for unique scopes and crossing width. 600 random 2-CNF existential projections (r=1..6, 100 each) verified 3,931 projected assignments by implication reachability vs exhaustive witness projection. 400 random crossing formulas r=1..4 each side, 3,000 left residual keys, checked grouped exact count and both zero/signed left character sums against original exhaustive joint enumeration. 400 additional crossing formulas r=1..5 each side, 4,960 left assignments: evaluated guarded closure bitsets against exhaustive right-existence queries, all passed. Bitsets are finite test harness, not claimed algorithmically cheap truth-table materialization. Exact symbolic recurrence above uses gates. Reproducer core for compiler and semantic/guarded closure (same code structure used in tests):

```python
from itertools import combinations,product
from collections import Counter,defaultdict
from functools import lru_cache
from random import Random
D='737362511425175275471342317614566635167417725234'
G=[tuple((i,1-(int(p)>>j&1)) for j,i in enumerate(I))
   for I,p in zip((I for I in combinations(range(8),3) if min(I)<4<=max(I)),D)]
def clauses(q):return [tuple(zip(I,p)) for w in range(1,min(3,q)+1) for I in combinations(range(q),w) for p in product((0,1),repeat=w)]
def brute(q,F):return sum(all(any((x>>i&1)==v for i,v in C) for C in F) for x in range(1<<q))
assert len(G)==48 and brute(8,G)==1 and all(any(v==0 for i,v in C) for C in G)
def compile_(q,C,t,bal):
 z=list(range(q,q+8));m=q+8;R=set(z[4:]);F=[tuple((q+i,v) for i,v in c) for c in G]
 for j,c in enumerate(C):
  a=[]
  for k,(i,v) in enumerate(c):
   p=m;m+=1;a.append((p,v))
   if k:R.add(p)
   F.extend([((i,0),(p,1),(z[6],1)),((i,1),(p,0),(z[7],1))])
  if not(t>>j&1):F.append(tuple(a+([(z[4],1),(z[5],1)] if len(a)==1 else [(z[0],1)] if len(a)==2 else [])))
  elif bal:F.append(((a[0][0],1),(z[6],0),(z[7],1)))
 assert len({tuple(sorted(i for i,v in c)) for c in F})==len(F)
 assert all(len(c)==len({i for i,v in c})==3 and 0<len({i for i,v in c}&R)<3 for c in F)
 return m,F,R
@lru_cache(None)
def cnt(F,free):
 while True:
  if not F:return 1<<free.bit_count()
  if any(not c for c in F):return 0
  units={c[0] for c in F if len(c)==1}
  if not units:break
  if len({i for i,v in units})!=len(units):return 0
  ix={i for i,v in units};free &= ~sum(1<<i for i in ix)
  F=tuple(sorted({tuple(l for l in c if l[0] not in ix) for c in F if not any(l in units for l in c)}))
 i=Counter(i for c in F for i,v in c).most_common(1)[0][0]
 return sum(cnt(tuple(sorted({tuple(l for l in c if l[0]!=i) for c in F if (i,v) not in c})),free^(1<<i)) for v in (0,1))
def sat2(r,F):
 if any(not c for c in F):return False
 R=[1<<i for i in range(2*r)]
 for c in F:
  a,b=c[0],c[-1];i=2*a[0]+a[1];j=2*b[0]+b[1]
  R[i^1]|=1<<j;R[j^1]|=1<<i
 for k in range(2*r):
  for i in range(2*r):
   if R[i]>>k&1:R[i]|=R[k]
 return not any(R[2*i]>>(2*i+1)&1 and R[2*i+1]>>(2*i)&1 for i in range(r))
def project(r,F,B):
 if not sat2(r,F):return [()]
 out=[]
 for d in (1,2):
  for I in combinations(B,d):
   for p in product((0,1),repeat=d):
    if not sat2(r,F+[((i,v),) for i,v in zip(I,p)]):out.append(tuple((i,1-v) for i,v in zip(I,p)))
 return out
def guard_eval(r,F):
 full=(1<<(1<<r))-1;A=[[0]*(2*r) for _ in range(2*r)]
 for i in range(2*r):A[i][i]=full
 for c in F:
  g=sum(1<<x for x in range(1<<r) if all(x>>i&1!=v for i,v in c if i<r))
  D=[(i-r,v) for i,v in c if i>=r];u=2*D[0][0]+D[0][1];v=2*D[-1][0]+D[-1][1]
  A[u^1][v]|=g;A[v^1][u]|=g
 for k in range(2*r):
  for i in range(2*r):
   for j in range(2*r):A[i][j]|=A[i][k]&A[k][j]
 bad=0
 for i in range(r):bad|=A[2*i][2*i+1]&A[2*i+1][2*i]
 return full^bad
```

Sampling details to replay counts: Random(369), consume 48 rng.randrange(1,8) for gadget discovery, matching D. For q=1,2 enumerate all selector integers t; q=3 draw 30 rng.getrandbits(len(C)); compare both compiler modes with brute(q,[c for j,c in enumerate(C) if not t>>j&1]), clear count cache each call. Then for r=1..6 choose 100 2-CNFs by sampling 0..min(len(C),12) clauses uniformly without replacement from all width1/2, choose random subset B of size rng.randrange(r+1); compare projected support against exhaustive assignments. Next r=1..4, 100 each sample crossing formulas up to 20 clauses; group all x by project(r,residual,list(range(r))), compare sums len(group)*brute(r,key) and signed sums for h=0 and h=(1<<r)-1 against full joint enumeration. Finally r=1..5, 80 each sample crossing formula up to 30 clauses, compare guard_eval bits against exhaustive y existence for each x. All exact finite tests, no asymptotic inference.

### Active P0 ledger

| Gate | Deliverable | Status |
|---|---|---|
| G70 | twoSidedConditionalBijunctiveGeometry | derived |
| G71 | canonicalSemanticSeparator / signedClassContraction | derived and tested; G16/G51/G68 |
| G72 | crossingLocallyFullZeroGadget / parsimoniousTwoSidedCompiler / minorTransport | derived and tested, fixed-weight variant separate |
| G73 | guardedImplicationPathEvaluator | derived and tested; joint nonemptiness OPEN |
| G74 | crossingPromiseMonotoneBound | external G30 theorem transported, restricted |
| N4/G12a | unrestrictedSerialCharge | OPEN: cost of selecting globally inhabited fibre or other direct uniform endpoint, allow all shared symbolic algorithms |
| N5/G12c | unrestrictedSuperpolynomialGrowth | OPEN; G48 forced flag or G38 central slice |
| N6 | originalClayTransport | conditional #1040 / #1129 |

Geometry-forward Aristotle BIDI: G73 gives a real polynomial shared representation of every conditional fibre's existence. Do not charge class enumeration, raw separator width, path count, conditional count or arithmetic precision as required for decision. The remaining joint support query over the guarded evaluator is NP-complete on G72. Next target the existence of a compatible assignment of the ORIGINAL guard variables, or a direct standard-machine lower-bound argument; distinguish the easy symbolic representation from its global nonemptiness. Preserve source zero mode, inhabited neutral fibre, signed residual and independently indexed histories, not obligatory materialization. No new certification prerequisite; no P!=NP claim.


## 29. P0-G75–G78 — geometry-forward: shared guard geometry, bounded internal components and exact parity control (2026-11-24)

Controlling endpoint literal Clay P vs NP. User supplied three pasted files, read directly in container: Langlands R99–R104 (reported #1549/#120 73bf0b2a23a3/f3141d518702), R107–R111 (0208b560be2a/69e842c43939), and G70–G74. Continue general P vs NP (no Langlands/Monster/TOE edits). Both P0 branches read live at f10fa7a0852e / d941e2e046eb, common blob 61c3a293db787f0d094eba2920b50480b2255d10. Geometry-forward, retain zero mode, inhabited neutral fibre, signed residual, original source labels and independently indexed hyperfabric. Use R102 invertible local correction and R108/R109 certified signed symmetry as allowed shortcuts; R110 exact symmetry recognition Clay-equivalence is a boundary, not a required operation. Existing G13, G16/G17, G45–G48, G51, G53–G59, G65–G74, ConstraintCouplingSearchExact, ObservationSeparatorGeometryExact, IndexedCubeHyperfibreExact (section 27), #1291 H05, #1006 FactorsThrough, #123 JMD lowering, #1546 sharing, #1474/#1502 reductions, #1129 costed standard machine coverage, #1040 terminal, #607/#678 Aristotle. Classical gate encodings, variable elimination, implication graphs, parity CNF size and two-state automata used; no literature novelty claim. No native kernel certification or CI.

### G75 — locally-full crossing compiler with bounded right components and independent left guards

Let F be any normalized CNF of nonempty clauses of width <=3 on original left variables x. For each clause C independently create one private right state r_i for each literal l_i, enforcing r_1=l_1 and r_i=r_(i-1) OR l_i for i>=2 and r_last=1. Encode r_1=l_1 by (not l_1 OR r_1),(l_1 OR not r_1); each OR step by (not r_prev OR r_i),(not l_i OR r_i),(r_prev OR l_i OR not r_i). This preliminary formula has at most one original left variable and one or two right variables per clause, including pure-right units/binaries. It has exactly one right extension for each satisfying x and none for nonsatisfying x; the whole right induced graph is disjoint paths.

Use actual G72 eight-variable zero gadget Z0..Z7 with Z0..Z3 left, Z4..Z7 right. For EVERY right literal occurrence in each preliminary clause allocate a private right copy a of right variable r, enforcing equality with (not r OR a OR Z0),(r OR not a OR Z1). Use copies in main clause; if no left variable pad with Z0, if only one right variable pad with Z4. All nongadget emitted clauses have exactly one left and two right variables, all scopes distinct (main scopes use private copies, equality scopes use original right r and copy, gadget neither). Every selected scope has exactly seven of eight allowed patterns, all other scopes full, so local affine and pair projections full. All eight Z are globally zero and each private copy uniquely determined. Thus original witness projection is a bijection. General formula encoding is polynomial in clause list; full selector length polynomial. Original source empty clause can be handled separately, empty formula works with gadget only. Exact witness preservation extends to G48 known-witness flag; no assumption of large conditional count complexity.

Delete the eight gadget vertices: left induced graph has no edges, and each right connected component belongs to one original clause block, with <=16 right vertices (width-three chain: 3 originals, 2 copies for first equivalence, 5 copies per later OR, 1 for final unit). The right graph has treewidth <=7 even before deleting the four right gadget vertices: original path bags of size <=2, attach leaf containing the one/two original right states and one/two copies for each preliminary clause; add all four right gadget vertices to every bag, connect distinct block decompositions via an auxiliary bag of gadget vertices. Every equality/main right edge is covered; every vertex's bags connected. Left induced graph has treewidth <=3 (only gadget can have left-left edges). Despite these restrictions, SAT on this crossing promise is NP-complete, and exact counting #P-hard via parsimonious reduction. The guard labels repeated across right components carry all original interaction. This is stronger than G72's individual conditional 2-SAT result, and prevents a claim that small internal treewidth on BOTH sides ensures polynomial joint decision. No unrestricted lower bound.

### G76 — exact component elimination and guard interaction hypergraph

After the fixed gadget is eliminated using its constant-size proof, let right components be R_j and N_j the original left guard variables adjacent to them. The existential right projection factors as H(x)=prod_j H_j(x|N_j), where H_j is one iff the component has an allowed extension. For exact count/weighted contraction replace H_j by the corresponding regional extension sum, which is not necessarily Boolean. Computing a table for one component by direct enumeration costs O(poly(local clauses)*2^(|N_j|+|R_j|)) with arithmetic bit costs; zero table entry in a signed ring need not mean no extensions. For G75 |N_j|<=3, |R_j|<=16, and the unweighted extension count is exactly the original clause indicator, by unique extension. Eliminating these components restores the original clause hypergraph on left labels, not a new independent selector per occurrence. Thus the cost of component projection is polynomial but the remaining global product can represent any original 3-CNF. Retain source original guard label, occurrence, event history, time tau, chart/refinement k, iteration j, version, coefficient ring, creation/requested precision, consumer as separate fields. For independent weights on original left coordinates the zero/signed/weighted contractions recover G53/G56; weights on private right variables can be included in the local extension sum before elimination. Local R102 inverse does not change the original incidence identity. Contract only on certified symmetry subspaces relative to the actual weighted consumer (R108/R111); do not require computing exact stabilizers. In a new crossing event, previously separate right components can join and guard scopes can enlarge; retain original constraint records and signed gain/loss, not a claim that old tables suffice.

### G77 — guard path pairs, exact forbidden cubes and overlap

In G73's symbolic right implication graph, every edge carries an activation guard (a conjunction of at most two original left literals), or a disjunction of guards if multiple clauses share an edge. Retain named clause witnesses for those alternatives. For each pair of directed simple paths from a right literal u to not u and back, choose one original guard per edge, and take the union of their signed left literals. A conflict (both pins for the same source variable) makes this path pair infeasible, distinct from a neutral unassigned coordinate. Otherwise the union is a partial assignment cube. Every extension of that cube activates the contradictory cycle and is bad. Conversely for every bad x, active implication reachability supplies both simple paths and an active guard per edge; their consistent union contains x. Hence the union of all such cubes is exactly B(x), the bad-left set. Each path has at most 2r-1 edges for r right variables, so a path-pair certificate has <=4r-2 edge occurrences; shared guard coordinates counted once. Empty guards/cubes mean unconditional edges/contradiction respectively, not empty fibre. This is an exact proof-search description; shared symbolic transitive closure G73 avoids explicit path listing. Minimal forbidden guard cubes are minimal partial assignments all of whose completions are bad; they may also arise by merging/consensus across multiple path certificates (do not assert every prime cube itself comes from one pair). Expanding every such cube is not required by arbitrary algorithms.

### G78 — exponential prime guard obstruction with a cheap signed two-state contraction

Construct another original crossing network on q>=1 left bits x_i, right path states r_0..r_q, r_0=r_q=0, r_i=r_(i-1) XOR x_i. For each step use four ternary truth-graph clauses, one for each input pair, excluding its incorrect output. Apply the same G75 private-right-copy compiler and gadget. Every nongadget clause crosses with one left and two right coordinates; unique right extension iff x has even parity. After deleting gadget, right graph is path of constant-size local bags (original adjacent state pair plus at most two private copies per main clause leaf); before deletion right treewidth <=7, left <=3 by the same decomposition. No claim of constant-size right COMPONENT for this parity example: it is a path of growing length.

Every proper partial assignment on left variables has both even and odd extensions by a free bit, so the minimal bad cubes are exactly the 2^(q-1) full odd assignments. Any CNF on original left variables alone defining the projected even-parity relation needs at least 2^(q-1) non-tautological clauses: each clause's falsifying subcube must lie in odd parity, hence has to be a single full odd assignment. Matching upper by forbidding each odd assignment. This is an exact guard-only CNF size obstruction even for an easy original projected relation. It does NOT rule out auxiliary variables, circuits, signed weights or shared automata. The actual path evaluator is linear size.

Retain the original zero mode and signed character residual: for b(x)=[even parity], unnormalized Walsh S(0)=S(all_ones)=2^(q-1), all other coefficients zero (q>=1), by b=(1+chi_all)/2 over Q. Its exact translation stabilizer is the even-weight subspace (q-1 dimensional), supplied by the known source XOR geometry, not a computed arbitrary global stabilizer. General product weights z_i can break translation symmetry; nevertheless there is an exact division-free shared contraction over ANY commutative ring. Initialize (E,O)=(1,0); for each original variable i, update

    (E,O) <- (E+z_i O, O+z_i E)

using both old states, keeping the odd signed/complementary fibre. E is the weighted even-parity witness polynomial, O its odd counterpart. Over integers E+O=prod_i(1+z_i), E-O=prod_i(1-z_i). These identities retain both baseline and signed residual; never divide by a possibly nonunit 2 or infer emptiness from E=0 modulo p^H. In any ring the recurrence takes O(q) operations; in odd characteristic the displayed two modes recover E by division by 2, but binary consumers should use the direct recurrence. Character sign choices can be incorporated into z_i. This is an explicit adaptive weighted contraction with two state sectors, valid even when weights break the original symmetries. The original assignments and time/ refinement/chart indices remain attached; state aggregation is consumer-specific. For original compiled auxiliaries set their weights to 1 to recover these exact left witness polynomials; arbitrary auxiliary weights require the appropriate local transition weights.

Thus even exponentially many minimal incompatible guard cubes and high projected CNF size coexist with a tiny exact weighted contraction and a polynomial decision circuit. Do not charge these expansions or independent path certificates as unavoidable time. G75/G76 isolate a genuinely hard guard-sharing geometry with trivial individual components; G78 prevents turning the number of bad cubes into a universal cost bound. Both upper and obstruction are model-specific; no P!=NP assertion.

### Actually executed local regression (exact Python/DPLL, no CI/kernel)

Local /tmp/p0_guardgeo.py: 256 original gadget assignments checked (unique zero). 320 complete compiled SAT model-count comparisons (260 exhaustive q=1,2 selectors and 20 seeded q=3,4,5 formulas each); 37,058 emitted clause checks, distinct crossing scopes, exact right component owner and size <=16, left independent outside gadget. For parity q=1..8 checked 8 complete counts and 510 fixed-left fibre counts, 1,152 emitted clause checks and right state adjacency; 200 exact signed product-weight recurrence comparisons vs exhaustive parity polynomial and product identity. Separately enumerated 9,840 partial guard assignments, exactly 255 minimal bad full assignments across q=1..8; 510 signed Fourier coefficients compared to explicit parity spectrum. All passed. DPLL prioritizes branching on fixed gadget variables, but does not preassign them; independent count on full emitted formula. No end-to-end external solver benchmark. Reproduction core (normalized literal tuple (index,satisfying bit), G72 gadget string and compiler, independent DPLL):
```python
from itertools import combinations,product
from collections import Counter
from functools import lru_cache
from random import Random
from math import prod
D='737362511425175275471342317614566635167417725234'
G=[tuple((i,1-(int(p)>>j&1)) for j,i in enumerate(I)) for I,p in zip((I for I in combinations(range(8),3) if min(I)<4<=max(I)),D)]
def ev(F,x):return all(any((x>>i&1)==v for i,v in c) for c in F)
assert [x for x in range(256) if ev(G,x)]==[0]
def allclauses(q):return [tuple(zip(I,p)) for k in range(1,min(3,q)+1) for I in combinations(range(q),k) for p in product((0,1),repeat=k)]
def truth(q,F,parity=False):
 m=q;A=[];blocks=[]
 if parity:
  prev=m;m+=1;A.append(((prev,0),))
  for i in range(q):
   v=m;m+=1;blocks.append((prev,v))
   for a,b in product((0,1),repeat=2):A.append(((i,1-a),(prev,1-b),(v,a^b)))
   prev=v
  A.append(((prev,0),));return m,A,blocks
 for C in F:
  B=[];prev=None
  for i,s in C:
   v=m;m+=1;B.append(v);A.append(((i,1-s),(v,1)))
   if prev is None:A.append(((i,s),(v,0)))
   else:A.extend([((prev,0),(v,1)),((prev,1),(i,s),(v,0))])
   prev=v
  A.append(((prev,1),));blocks.append(tuple(B))
 return m,A,blocks
def compile_(q,m,A):
 z=list(range(m,m+8));right=set(range(q,m))|set(z[4:]);F=[tuple((z[i],v) for i,v in c) for c in G];n=m+8;owner={i:i for i in range(q,m)}
 for c in A:
  left=[(i,v) for i,v in c if i<q];rr=[]
  for i,v in c:
   if i<q:continue
   a=n;n+=1;right.add(a);owner[a]=i;rr.append((a,v))
   F.extend([((i,0),(a,1),(z[0],1)),((i,1),(a,0),(z[1],1))])
  assert len(left)<=1 and 1<=len(rr)<=2
  F.append(tuple((left or [(z[0],1)])+rr+([(z[4],1)] if len(rr)==1 else [])))
 assert len(F)==len({tuple(sorted(i for i,v in c)) for c in F})
 assert all(len(c)==len({i for i,v in c})==3 and 0<len({i for i,v in c}&right)<3 for c in F)
 assert all(sum(i not in right for i,v in c)==1 for c in F[48:])
 return n,F,right,z,owner
def count(n,F,priority,pins=()):
 @lru_cache(None)
 def rec(F,free):
  while True:
   if not F:return 1<<free.bit_count()
   if any(not c for c in F):return 0
   u={c[0] for c in F if len(c)==1}
   if not u:break
   ix={i for i,v in u}
   if len(ix)!=len(u):return 0
   free &= ~sum(1<<i for i in ix)
   F=tuple(sorted({tuple(l for l in c if l[0] not in ix) for c in F if not any(l in u for l in c)}))
  freq=Counter(i for c in F for i,v in c);i=min(freq,key=lambda i:(priority(i),-freq[i],i))
  return sum(rec(tuple(sorted({tuple(l for l in c if l[0]!=i) for c in F if (i,v) not in c})),free^(1<<i)) for v in (0,1))
 return rec(tuple(sorted({tuple(sorted(c)) for c in F+[(p,) for p in pins]})),(1<<n)-1)
def graphcheck(q,m,F,right,z,owner,blocks,parity):
 E={tuple(sorted((i,j))) for c in F for i,j in combinations([i for i,v in c],2)}
 assert all(i in right or j in right for i,j in E if i not in z and j not in z)
 R=[i for i in right if i not in z];adj={i:set() for i in R}
 for i,j in E:
  if i in adj and j in adj:adj[i].add(j);adj[j].add(i)
 if not parity:
  lab={i:k for k,B in enumerate(blocks) for i in B}
  assert all(lab[owner[i]]==lab[owner[j]] for i in adj for j in adj[i])
  assert max(Counter(lab[owner[i]] for i in R).values(),default=0)<=16
 else:assert all(abs(owner[i]-owner[j])<=1 for i in adj for j in adj[i])
 return len(F)
rng=Random(369);checks=clchecks=0
for q in range(1,6):
 C=allclauses(q)
 Fs=([C[j] for j in range(len(C)) if t>>j&1] for t in range(1<<len(C))) if q<=2 else (rng.sample(C,rng.randrange(min(8,len(C))+1)) for _ in range(20))
 for F in Fs:
  m,A,blocks=truth(q,F);n,B,R,z,o=compile_(q,m,A)
  pri=lambda i:0 if i in z else 1 if i<q else 2
  assert count(n,B,pri)==sum(ev(F,x) for x in range(1<<q))
  clchecks+=graphcheck(q,m,B,R,z,o,blocks,False);checks+=1
assert (checks,clchecks)==(320,37058)
checks=cn=weighted=0
for q in range(1,9):
 m,A,blocks=truth(q,[],True);n,B,R,z,o=compile_(q,m,A)
 pri=lambda i:0 if i in z else 1 if i<q else 2
 assert count(n,B,pri)==2**(q-1);cn+=graphcheck(q,m,B,R,z,o,blocks,True)
 for x in range(1<<q):
  assert count(n,B,pri,tuple((i,x>>i&1) for i in range(q)))==int(x.bit_count()%2==0);checks+=1
 for _ in range(25):
  zt=[rng.randrange(-4,5) for i in range(q)];e,o=1,0
  for a in zt:e,o=e+a*o,o+a*e
  assert e==sum(prod(zt[i] for i in range(q) if x>>i&1) for x in range(1<<q) if x.bit_count()%2==0)
  assert 2*e==prod(1+a for a in zt)+prod(1-a for a in zt);weighted+=1
assert (checks,cn,weighted)==(510,1152,200)
n=bad=four=0
for q in range(1,9):
 for a in product((-1,0,1),repeat=q):
  xs=[x for x in range(1<<q) if all(v==-1 or x>>i&1==v for i,v in enumerate(a))]
  b=not any(x.bit_count()%2==0 for x in xs)
  assert b==(-1 not in a and sum(a)%2==1);n+=1;bad+=b
 for h in range(1<<q):
  s=sum((-1)**((h&x).bit_count()) for x in range(1<<q) if x.bit_count()%2==0)
  assert s==(2**(q-1) if h in (0,(1<<q)-1) else 0);four+=1
assert (n,bad,four)==(9840,255,510)
```

### Active P0 ledger

| Gate | Deliverable | Status |
|---|---|---|
| G75 | boundedInternalComponentCrossingCompiler | derived and tested; exact parsimonious reduction, left tw<=3 right tw<=7 |
| G76 | exactGuardHypergraphComponentElimination | derived; local table upper bound, joint global product remains hard |
| G77 | compatibleGuardPathPairCover | derived; original clause labels, conflict vs neutral preserved |
| G78 | exponentialPrimeGuardCubeControl / divisionFreeWeightedParityContraction | derived and tested; projected CNF restriction only, cheap two-state shortcut |
| N4/G12a | unrestrictedSerialCharge | OPEN: actual paid computation after all semantic/signed/shared contractions, no mandatory explicit guard cube expansion |
| N5/G12c | unrestrictedSuperpolynomialGrowth | OPEN; G48 uniform flag / G38 stronger nonuniform slice |
| N6 | originalClayTransport | conditional #1040/#1129 |

Geometry-forward Aristotle BIDI: the remaining source geometry is the interaction of repeated original guard labels across independently contractible regions. G76 allows eliminating them to the true original factors, not merely hiding them. G78 establishes that exponential projected clause complexity is not sufficient to charge general work; parity has a linear shared weighted transfer even when product weights break the unweighted symmetry. Next investigate actual reusable guard interactions (and shortcuts via nonlocal basis changes), or direct uniform-machine N4/N5, rather than postulate obligatory full stabilizer, prime CNF, separator table or path listing. Preserve zero mode, inhabited neutral fibre, signed residual, actual source and independent time/k-indexed hyperfabric as semantics, not mandatory materialization. No new certification prerequisite; no P!=NP claim.


## 30. P0-G79–G83 — GEOMETRY-FORWARD: minimal joint linear overlap, indexed refinement and rigid full-affine guard carriers (2026-11-24)

Literal Clay P vs NP P0. User big-paste files read directly from /mnt/data/Pasted text.txt and /mnt/data/Pasted text (2).txt: G75–G78 and Langlands R114–R118 (reported #1549/#120 dd68910684ca / cc5228088c20, blob d34da42a75e2ef3cb975c70c6b785ebf813eab49). Both actual P0 roadmaps read at a81e2f6d0eea / 048398039a65, common blob cafd38e41ff43f8fd4565ba234d49ee066b14c32. Use R114 syndrome trellis, R115/R116 exact conditional symmetry and weighted orientation, R117 symmetry-free gadget as donors, not independent Langlands work. Reuse G13 original selector, G16/G17 binary control, G33 signed components, G45–G48 flag/local-full, G56–G59 signed indexed modes, G65–G69 source separator, G70–G78 guard geometry and parity transfer, ConstraintCouplingSearchExact, ObservationSeparatorGeometryExact, IndexedCubeHyperfibreExact (actual blobs in section 27), #1291 H05, #1006 FactorsThrough and self-reduction, #123 JMD lowering, #1546 sharing, #1474/#1502 reductions, #1129 costed machine, #1040 terminal, #607/#678 Aristotle. Elementary finite linear algebra, affine coding and separator DP used; no claim of literature novelty. No changes to other programmes; no CI/native kernel.

### G79 — minimal joint overlap subspace (not pairwise overlap)

After any certified consistent affine restriction, parameterize original source by y in F2^q via x=a+By, retaining the affine anchor and inverse on its image. Inconsistent restriction rejects. Each remaining factor j is a function of linear forms spanning U_j in the dual E=(F2^q)^*. Use independent bases and absorb actual offsets in its local table f_j:U_j^* -> R (R a commutative coefficient ring). Put T=sum U_j, r=dim T, D_j=U_j intersect sum_{i!=j} U_i, D=sum D_j, d=dim D. All subspaces obtained by Gaussian elimination on actual original labelled forms. Pairwise intersections can miss dependencies: U1=<a>, U2=<b>, U3=<a+b> pairwise disjoint yet D=<a,b>.

Claim T/D is direct sum of U_j/D_j. First U_j intersect D=D_j: if u=sum d_i lies in U_j, subtract d_j, then u-d_j in U_j intersect sum(other U_i), hence in D_j. Next if sum u_i in D, choose d_i in D_i whose sum equals that vector; sum(u_i-d_i)=0, so every u_i-d_i belongs to D_i, and hence u_i belongs to D_i. This proves the direct sum, including empty or zero subspaces. Moreover D is the least subspace L of E for which the images of the U_j in E/L sum directly. Necessity: u in D_j is expressible as sum of other U_i, so its image must be zero in any direct sum quotient; D subset L. Sufficiency for L=D by previous proof. IMPORTANT: not every larger L works: U1=<a>, U2=<b>, D=0, quotient by <a+b> makes their two images equal and nonzero. Initial test harness used an erroneous iff for arbitrary L; corrected to necessity and directness at D. This is the least linear conditioning space for making ALL regional linear observation coordinates independent, not a minimum arbitrary nonlinear decision representation, nor a lower bound on unrestricted algorithms. A local table may not actually need every supplied form; exact semantic removal is allowed before computing spans.

### G80 — joint nonlinear block contraction with private degrees eliminated once

For each s in D^* define regional message

    M_j(s|D_j)=sum_{alpha in U_j^*: alpha|D_j=s|D_j} f_j(alpha).

By G79, any tuple of local functionals agreeing with the given s on all D_j has exactly one extension to T^*: choose a complement of D in T and compatible local private coordinates; equivalently sum the local functionals on U_j, well-defined because any relation sum u_j=0 has all u_j in D_j and sum s(u_j)=0. Every functional on T has exactly 2^(q-r) extensions to E, which correspond to actual original parameters y. Therefore

    Z=sum_y prod_j f_j(y|U_j)
     =2^(q-r) sum_{s in D^*} prod_j M_j(s|D_j).

This exact division-free contraction holds over any commutative ring, including signed integer coefficients and modular arithmetic. With explicit local tables, build messages by summing each table once over its restriction fibres (coordinates obtained by Gaussian elimination); outer loop over 2^d signatures, each message lookup via linear restriction. Arithmetic operation bound poly(input description)*(sum_j 2^dim U_j + 2^d), charge local table access, ring bit costs, and any chosen affine parametrization. For satisfiability of Boolean factors use OR for each sum and AND for product; the free extension factor is always inhabited and does not become zero mod p. Bounded local rank and d=O(log N) is a polynomial decision subclass. Larger rank can still be treated by splitting/recursive contraction or any other legitimate algorithm. For ordinary coordinate scopes, D is precisely span of original coordinates used in >=2 factors; after affine substitution D captures multiway dependencies invisible to pairwise label overlap. This is a true extension of G76 independent regions and R114 affine trellis, not a claim of a new optimal general algorithm.

Weights: include unary weights on original source coordinates as extra factor(s) on their actual linear forms after affine substitution, including anchor. A general weight may enlarge D, as in R111/R114; can fold into existing factors when forms permit, with actual cost. Original signed Fourier mode h gives a factor (-1)^(h dot x) depending on a single linear form plus anchor sign, so may be absorbed or included as a one-dimensional factor. Retain exact zero mode separately. An inhabited neutral fibre or local signed sum that vanishes in the ring is not empty; original Boolean support and source provenance separate. Free extension multiplier is not an independent repeated-guard charge. Overlap ranks and table sizes are representation-dependent, not standard-machine time lower bounds.

### G81 — exact indexed overlap update under a new regional factor

For fixed affine chart, append a new observation subspace V. Old T,D as above, K=V intersect T. Let pi_j:T/D -> U_j/D_j be the canonical projection of G79. The new shared subspace D' contains D, lies in T, and

    D'/D = direct sum_j pi_j((K+D)/D)  inside T/D.

Proof: the new factor has overlap K. Old region's new overlap is U_j intersect (sum_{i!=j} U_i+V); any element of it is an old sum plus v with v in V intersect T, so its image modulo D is the j-th component of some k in K. Conversely decompose any k in K into old u_j; each u_j is in the new overlap of U_j because it equals k minus the other components. The projections span exactly the displayed subspace, and the image of K already lies in their sum. Thus D' can be computed from old direct-sum geometry and actual new overlap, without assuming that merely adding K to D is sufficient. Example old U1=<a>, U2=<b>, add V=<a+b>: K has dimension 1, but D' has dimension 2. If K=0 the new factor is independent and D unchanged. This exact rank/refinement rule is for adding a factor without changing old chart/factor spans; deletion, semantic simplification or affine reparametrization can shrink or otherwise change the separator, so preserve separate indices. Keep (history,tau,k,j,version,ring,creation/requested precision,consumer,separator partition) independent, actual source masks and gain/loss G58, signed weights and dependent residual G68. Retain map D^* <- D'^* by restriction and actual new regional source tables; summing over refined source fibres recovers old baseline before applying new filter, not equality of old and new filtered counts. No new H05/H07/H14 closure or mandatory materialization. A larger quotient can couple previously independent components, so recompute actual quotient property rather than rely on rank monotonicity.

### G82 — constant-multiplicity nonlinear code removes even GLOBAL affine and translation reductions

This strengthens R117 on the projected ORIGINAL guard carrier (not on all deterministic right auxiliaries). On four binary coordinates (little-endian integer masks) choose disjoint five-point sets

    A_0={0,1,2,4,8}, A_1={3,5,6,9,11}, A=A_0 union A_1.

Both A_b have full affine dimension 4; verify by taking four independent differences to a chosen anchor (or exact finite Gaussian elimination). Both have trivial translation stabilizers since odd size, are not translates of each other, and A also has trivial stabilizer. The last two claims are fixed finite checks of all 16 translations (explicit test below); no asymptotic assumption. Encode every logical original bit x_i by a raw 4-bit block in A_(x_i). For any original relation X define

    E(X)=union_{x in X} product_i A_(x_i).

Exact decoding maps every raw block to its type; fibres disjoint and each original witness has exactly 5^q extensions. If X is nonempty, any one x supplies a product of full-affine-hull factors, so aff(E(X))=F2^(4q). For any translation h preserving E(X), fix a raw block i and choose a nonempty slice obtained by fixing all other raw blocks. Such a slice is A_0, A_1 or A, because the other decoded logical bits fixed and admissible original i values either singleton or both. Translation carries it bijectively to another nonempty slice, with shift h_i. Distinct slice types cannot be translates (different cardinalities or explicit A0/A1 check); each type has trivial stabilizer. Hence h_i=0 for every block. Thus every nonempty encoded relation has complete affine hull and trivial global translation stabilizer, not merely local full hulls or conditional trivial stabilizers.

Polynomial source compiler: impose raw domain A on each block by forbidding six invalid four-bit patterns. For every selected original clause forbidding logical pattern p on d<=3 distinct variables, forbid all 5^d tuples of corresponding raw block representatives (each is a clause of width 4d<=12). Exact raw relation is E(V(F)), and local raw factor tables on code domains have full affine hull whenever nonempty (any allowed logical tuple yields product of full-affine sets). All factor arities bounded by 12 and count polynomial in original clause list. Apply G75's deterministic OR evaluation chain and G72 zero gadget/private-right-copy crossing compiler to EACH bounded-width raw clause: the same construction works for constant width d, with at most 6d-2 right vertices per clause after removing gadget (d state variables, 2 first-step copies, 5 each later OR, 1 final unit copy). For d<=12 bound 70. Original raw guard variables on left; after fixed gadget elimination left induced graph independent, right components bounded, all nongadget clauses exactly one left and two right vertices, every selected ternary scope allows 7/8 patterns and distinct scopes. Deterministic auxiliaries uniquely determined for each valid satisfying raw assignment. The GLOBAL projected left relation on named raw guards (excluding gadget left constants) is exactly E(V(F)); do not claim full affine hull in whole compiled auxiliary space. SAT preserved; NP-completeness on these promised encodings by polynomial reduction. Original logical weights z_i recovered via local block weight 1 on A0, z_i on A1, auxiliary weights 1: raw zero-mode and weighted polynomial multiply by 5^q, exact integer recovery, modular inverse over binary/ternary rings (5 unit), explicit depth q over 5-adic field. Signed logical characters encoded by same block weights. Arbitrary unary raw weights need not have constant fibre factor; retain actual local orientation sums. Decoding is a legal nonlinear shortcut; do not charge this artificial rigidity or require finding the complete hull before deciding. G82 eliminates a proposed affine/symmetry-only sufficient strategy even if global symmetry/hull for inhabited instances were given, but computing whether hull is empty already contains SAT. No stronger unrestricted lower bound follows. Fixed code proof is finite, general transport is mathematical, no new native certification.

### G83 — explicit dense full-affine easy control, exponential balanced linear separator

For q>=3 use original ternary clauses forbidding 111 on EVERY triple. Actual relation X={x:|x|<=2} contains 0 and each coordinate vector, hence full affine hull. Stabilizer trivial: if h has weight>2, translates 0 outside X; if weight 2 add a disjoint unit vector; if weight 1 add two disjoint unit vectors (possible q>=3), producing weight 3. Every local factor allows 7/8 patterns. For any balanced partition of the triple factors into sides each containing at least one-third of all triples, let U,V be their variable unions. As in G39, if both have an exclusive variable, a triple containing the two exclusive variables could belong to neither, contradiction. Thus one side covers all q and the shared set is the other side's union of size s. It covers at least binom(q,3)/3 triples, and binom(s,3)/binom(q,3)<= (s/q)^3, so s>=q/3^(1/3). This gives a linear-dimensional shared span at every such balanced cut of the actual original local factors. Every binary factor contraction tree with >=3 leaves admits a cut with both sides >=one-third leaves (centroid node and largest incident component), so a procedure mandatorily materializing all linear boundary states at such cut incurs exponential table size. This is NOT a lower bound even for all tensor algorithms, let alone general SAT: actual functions can have sparse/symbolic states. Here the exact weighted witness polynomial is 1+sum_i z_i+sum_{i<j} z_i z_j. Division-free update of sectors (E0,E1,E2,O) initialized (1,0,0,0):

    (E0,E1,E2,O) <- (E0,E1+z E0,E2+z E1,(1+z) O+z E2).

O retains overflow (weight>=3), with total E0+E1+E2+O=prod(1+z_i). Count is 1+q+binom(q,2); signed modes via z_i=+/-1; actual Boolean support separate from modular zero. O(q) ring operations, no per-separator-state materialization, even with broken translation symmetry. Thus full affine hull, trivial exact stabilizer, dense genuinely nonlinear factors, and large balanced shared linear separators can coexist with a simple global shortcut. This is a decisive check against converting G79 minimality in its linear model into N4. G82 also decodable; neither code rigidity nor tree cuts prove a lower bound for unrestricted computation.

### Actual local exact regression (Python integers, no CI/kernel)

Executed /tmp/p0_affine_overlap.py. 700 random finite subspace arrangements (q=1..7, 100 each), 8,400 alternative quotient necessity checks, 6,104 conditioned joint Cartesian fibre comparisons, 700 signed contractions compared with exhaustive assignments AND separately constructed message tables, 700 appended-factor refinement identities. Initial overly strong test that every larger quotient is independent failed; corrected to exact least-subspace theorem and the projected overlap update, all corrected checks passed. Fixed code search found A0/A1 above; exhaustive 16 translations on each of the three slice types and each distinct type comparison. 20 arbitrary logical relations on q=1,2 with exact decoded witnesses/multiplicity, 18 nonempty full affine hull and 18 trivial global stabilizer comparisons. 300 actual normalized selector formulas (all 260 q=1,2, 40 seeded q=3) checked 105,600 raw assignments and exact counts and 300 signed weighted sums. For q<=2 enumerate all raw words, for q=3 enumerate valid raw-domain products. Tested raw forbidden-pattern factor predicate, not an integrated emitted crossing DPLL run this tranche; width-12 chain compiler transport follows from explicit G75 extension. 678 balanced triple-factor cuts (q=4,5), 200 weighted dense-control recurrence comparisons (q=3..12), including overflow identity; full affine and trivial stabilizer checked on those 10 carriers. Reproducer core (small explicit sets only for regression; polynomial basis operations are the mathematical production method):

```python
from itertools import combinations,product
from random import Random
from collections import Counter
from math import prod
def span(xs):
 s={0}
 for x in xs:s|={a^x for a in s}
 return s
def basis(xs):
 b={}
 for x in xs:
  while x:
   k=x.bit_length()-1
   if k in b:x^=b[k]
   else:b[k]=x;break
 return tuple(b.values())
def dim(s):return len(s).bit_length()-1
def sig(x,B):return sum(((x&b).bit_count()%2)<<i for i,b in enumerate(B))
def overlap(U):
 T=span(a for u in U for a in u)
 J=[u&span(a for k,v in enumerate(U) if j!=k for a in v) for j,u in enumerate(U)]
 return T,J,span(a for v in J for a in v)
def combvec(b,mask):
 v=0
 for i,a in enumerate(b):
  if mask>>i&1:v^=a
 return v
def coords(b,a):return next(k for k in range(1<<len(b)) if combvec(b,k)==a)
rng=Random(369);cases=keys=minimal=weighted=revisions=0
for q in range(1,8):
 for trial in range(100):
  n=rng.randrange(1,6)
  B=[basis([rng.randrange(1<<q) for _ in range(rng.randrange(0,min(4,q)+1))]) for j in range(n)]
  U=[span(b) for b in B];T,J,D=overlap(U)
  assert all(u&D==j for u,j in zip(U,J))
  assert dim(T)-dim(D)==sum(dim(u)-dim(j) for u,j in zip(U,J))
  for _ in range(12):
   L=span([rng.randrange(1<<q) for _ in range(rng.randrange(q+1))])
   direct=dim(span(T|L))-dim(L)==sum(dim(span(u|L))-dim(L) for u in U)
   assert not direct or D<=L;minimal+=1
  f=[[rng.randrange(-3,4) for _ in range(1<<len(b))] for b in B]
  h=rng.randrange(1<<q)
  if h:B.append((h,));f.append([1,-1])
  U=[span(b) for b in B];T,J,D=overlap(U);db=basis(D)
  groups={}
  for x in range(1<<q):groups.setdefault(sig(x,db),[]).append(x)
  z=0
  for s,xs in groups.items():
   P=[{sig(x,b) for x in xs} for b in B]
   joint={tuple(sig(x,b) for b in B) for x in xs}
   assert len(joint)==prod(map(len,P))==1<<(dim(T)-dim(D))
   z+=prod(sum(t[p] for p in ps) for t,ps in zip(f,P));keys+=1
  messages=[]
  for b,t,dj in zip(B,f,J):
   dd=basis(dj);loc=[coords(b,a) for a in dd];glob=[coords(db,a) for a in dd];M=Counter()
   for k,v in enumerate(t):M[sig(k,loc)]+=v
   messages.append((M,glob))
  assert z==sum(prod(M[sig(k,glob)] for M,glob in messages) for k in range(1<<len(db)))
  assert z*2**(q-dim(T))==sum(prod(t[sig(x,b)] for b,t in zip(B,f)) for x in range(1<<q))
  cases+=1;weighted+=1
  V=span([rng.randrange(1<<q) for _ in range(2)]);K=V&T
  _,_,new=overlap(U+[V])
  jj=[u&span(K|span(a for k,v in enumerate(U) if k!=j for a in v)) for j,u in enumerate(U)]
  assert D<=new and new==span(D|K|set().union(*jj));revisions+=1
assert (cases,keys,minimal,weighted,revisions)==(700,6104,8400,700,700)
A={0,1,2,4,8};B={3,5,6,9,11};C=[A,B];union=A|B
def stab(S,d):return {h for h in range(1<<d) if {x^h for x in S}==S}
def affdim(S):
 a=next(iter(S));return len(basis([a^x for x in S]))
assert all(affdim(S)==4 for S in C)
for S in (A,B,union):
 assert stab(S,4)=={0}
 for V in (A,B,union):
  if S!=V:assert all({a^h for a in S}!=V for h in range(16))
rc=aff=st=0
for q in (1,2):
 for mask in range(1<<(1<<q)):
  X={x for x in range(1<<q) if mask>>x&1}
  Y={sum(a<<(4*i) for i,a in enumerate(t)) for x in X for t in product(*(C[x>>i&1] for i in range(q)))}
  assert len(Y)==5**q*len(X)
  assert {sum(((y>>(4*i)&15) in B)<<i for i in range(q)) for y in Y}==X;rc+=1
  if Y:assert affdim(Y)==4*q and stab(Y,4*q)=={0};aff+=1;st+=1
assert (rc,aff,st)==(20,18,18)
def clauses(q):return [(I,p) for k in range(1,min(q,3)+1) for I in combinations(range(q),k) for p in product((0,1),repeat=k)]
def ok(F,x):return all(any((x>>i&1)!=v for i,v in zip(I,p)) for I,p in F)
def rawok(F,y,q):
 return all((y>>(4*i)&15) in union for i in range(q)) and all(any((y>>(4*i)&15) not in C[v] for i,v in zip(I,p)) for I,p in F)
fc=rawchecks=weightchecks=0
for q in (1,2,3):
 cs=clauses(q)
 fs=([cs[i] for i in range(len(cs)) if t>>i&1] for t in range(1<<len(cs))) if q<=2 else (rng.sample(cs,rng.randrange(0,min(12,len(cs))+1)) for _ in range(40))
 for F in fs:
  X=[x for x in range(1<<q) if ok(F,x)]
  ys=range(1<<(4*q)) if q<=2 else (sum(a<<(4*i) for i,a in enumerate(t)) for t in product(sorted(union),repeat=q))
  Z=W=0;z=[rng.randrange(-3,4) for _ in range(q)]
  for y in ys:
   v=rawok(F,y,q);valid=all((y>>(4*i)&15) in union for i in range(q));x=sum(((y>>(4*i)&15) in B)<<i for i in range(q))
   assert v==(valid and ok(F,x));rawchecks+=1
   if v:Z+=1;W+=prod(z[i] for i in range(q) if x>>i&1)
  assert Z==5**q*len(X)
  assert W==5**q*sum(prod(z[i] for i in range(q) if x>>i&1) for x in X);fc+=1;weightchecks+=1
assert (fc,rawchecks,weightchecks)==(300,105600,300)
cut=0
for q in (4,5):
 E=list(combinations(range(q),3));n=len(E)
 for t in range(1<<n):
  if 3*t.bit_count()<n or 3*t.bit_count()>2*n:continue
  U=set().union(*(set(I) for j,I in enumerate(E) if t>>j&1));V=set().union(*(set(I) for j,I in enumerate(E) if not(t>>j&1)))
  assert U==set(range(q)) or V==set(range(q))
  assert 3*len(U&V)**3>=q**3;cut+=1
assert cut==678
n=0
for q in range(3,13):
 Y={x for x in range(1<<q) if x.bit_count()<=2}
 assert affdim(Y)==q and stab(Y,q)=={0}
 for _ in range(20):
  z=[rng.randrange(-4,5) for _ in range(q)];a,b,c,o=1,0,0,0
  for w in z:a,b,c,o=a,b+w*a,c+w*b,o*(1+w)+w*c
  assert a+b+c==sum(prod(z[i] for i in range(q) if x>>i&1) for x in Y)
  assert a+b+c+o==prod(1+w for w in z);n+=1
assert n==200
```

### Endpoint-first ledger

| Gate | Deliverable | Status |
|---|---|---|
| G79 | leastJointLinearOverlap / directPrivateQuotient | derived and tested; pairwise overlap insufficient |
| G80 | exactNonlinearRegionalMessageContraction | derived and tested; actual paid upper bound |
| G81 | indexedNewFactorOverlapRefinement | derived and tested; source chart fixed |
| G82 | fullAffineAperiodicGuardEncoding / constantMultiplicityTransport | derived, raw relation tested; G75 bounded-width compiler extension derived, not separately integrated DPLL-tested |
| G83 | balancedLinearSeparatorDenseEasyControl | derived and tested; cheap weighted transfer defeats universal width charge |
| N4/G12a | unrestrictedSerialCharge | OPEN: allow nonlinear decoding, global sharing, arbitrary algorithmic alternatives |
| N5/G12c | unrestrictedSuperpolynomialGrowth | OPEN; G48 uniform flag / G38 stronger nonuniform central slice |
| N6 | originalClayTransport | conditional #1040/#1129 |

Geometry-forward Aristotle BIDI: G79–G81 give an actual least linear independence interface, not a required state representation. G82 shows that removing affine equations and exact translation symmetries alone need not eliminate the hard guard relation; G83 shows that even exponential linear separator materialization is not necessary for easy instances with these same invariants. Do not pursue more compulsory rank, hull, symmetry or width proxies as if they were N4. Highest-alpha next test is a target-specific bound on actual nonlinear transformation/composition cost that admits all these shortcuts, or direct uniform-machine obstruction; explicitly allow original logical decoding of G82, compact cardinality sectors of G83, and all G37 reported subexponential shortcuts. Preserve original zero mode, signed residual, inhabited neutral fibre and separate time/k-indexed hyperfabric as semantics. No new certification prerequisite and no P!=NP claim.


## 31. P0-G84–G88 — GEOMETRY-FORWARD: ordered shared guards, affine fibres, noncrossing contraction and commutation residuals (2026-11-24)

Literal Clay P vs NP remains the endpoint. Read both current pasted files directly: G79–G83 and Langlands R121–R125 (reported #1549/#120 48577ab92422/266ade6fd1f5, blob 364a28fec27af403adf73906d6e76ae4465d56ca). Both P0 roadmaps read live at 7821f6d2b7efd70919b68f21850af115b73123a1 / 448970922066a2204029ab4fa1ba82ba60638278, common blob 71e8d067fe40c5a4c3192bde6da0685ba1b8a33f. Use R122 matroid intersection as a restricted linear interface and R124 shared-orientation induced coupling as a donor, not a new Langlands endpoint. Continue G70–G83 from actual repeated original guard geometry; do not charge expanded channel ranks or compulsory materialization. Producers/consumers: G13 original selector, G16/G17, G33 signed components, G45–G48 flag, G51 consumer quotient, G53–G59 indexed modes, G65–G69 signed separators, G70–G78 crossing/guard/parity, G79–G81 minimal linear overlap, G82/G83 controls, existing ConstraintCouplingSearchExact, ObservationSeparatorGeometryExact, IndexedCubeHyperfibreExact (section 27), #1291 H05, #1006 FactorsThrough/self-reduction, #123 JMD lowering, #1546 sharing, #1474/#1502 reductions, #1129 standard machine, #1040 terminal, #607/#678 Aristotle. Use classical deterministic branching programs/finite automata, bounded-occurrence splitting, matrix products, noncrossing partitions and vertex-cover branching; no claim of literature novelty. Preserve original zero mode, inhabited neutral fibre, signed residual and separate time/k-indexed hyperfabric; no other programme edits, no CI/native kernel.

### G84 — constant-state transfer and two-sided affine-fibre hardness

Take normalized nonempty clauses of width <=3 on original left bits x. Use a row-vector deterministic three-state automaton U,S,D: U means all previous clauses satisfied, current clause not satisfied; S means current clause satisfied; D means a previous clause failed. For a literal that is false the transition is identity; for a true literal U->S, S->S, D->D. At every clause boundary reset U->D, S->U, D->D. Starting row e_U, ending accept column e_U^T, the resulting product F(x)=e_U product_j M_j(x_i) e_U^T is exactly the original CNF truth function. Boundary reset matrices are constant and do not introduce independent guards. State D is explicit excluded residual, not neutral. Empty formula accepts; empty clause handled by immediate reset/rejection. Each original guard label occurs once per actual literal occurrence, not replaced by independent per-occurrence choices.

Introduce a right state row p_j for each step, impose p_0=e_U, p_j=p_(j-1)(M_j(0)+x_i(M_j(1)-M_j(0))) over F2, and p_m[U]=1. Constant transitions use no x. These are equations of total degree <=2, and no within-side nonlinear terms. Fix x: the initial and transition equations form a square block lower-triangular system with identity diagonal on all 3(m+1) right unknowns, hence full column rank and a unique right run before terminal equation. The complete right fibre is that one run if accepted, empty otherwise. The coefficient rank is constant on ALL x; adding the single terminal equation increases augmented rank by precisely 1 on rejected x and by 0 on accepted x. Fix all p_j: every equation is affine in original left guards, so the left fibre is affine or empty, computable by Gaussian elimination. The joint relation is parsimoniously equivalent to original SAT. Thus NP-completeness survives even with both conditional fibres affine and the right-side conditional coefficient matrix always full column rank. This is a bilinear-equation model, NOT a new claim of crossing-only 3-CNF with affine fibres in all original auxiliary coordinates; converting equations to a Boolean gate graph may lose that fibre property. G48 always-inhabited flag may be evaluated by a deterministic transfer of its bounded-width truth-graph clauses with the original flag retained as a guard. No claim that a rank check at specified x is hard.

Bounded occurrence strengthening: split each variable with t>=2 occurrences into t private logical bits, each used in one original clause, and add cyclic implications (not a_i OR a_(i+1)), indices mod t. The directed cycle forces all copies equal, so every original assignment has exactly one extension to its copies, and conversely all satisfying copy assignments reconstruct original used bits. Each copy appears at most three times (one original clause and two cycle implications). Keep unused original variables as free bits for parsimonious counting. t=1 needs no extra clauses. Width <=3, polynomial-size reduction. Hence width-three deterministic transfer SAT remains NP-complete with each guard read at most three times and both conditional fibres affine in the bilinear formulation. This does not show that all orderings or all representations must use costly repeated reads.

### G85 — actual division-free contraction for noncrossing guard words

General source word of m positions, each labelled by original guard i or a constant, with d-by-d matrices M_j(0),M_j(1) over any commutative coefficient ring R. For a constant position both matrices equal, no guard weight. Use independent unary weights w_i(0),w_i(1), including signed Fourier factors w_i(1)=(-1)^h_i z_i. Define the entire weighted transfer

    T = sum_x (prod_i w_i(x_i)) M_1(x_label1)...M_m(x_labelm).

Unused guard factors contribute w_i(0)+w_i(1). At each original guard the weight occurs once regardless of read count. This computes the exact matrix of all source endpoint consumers, not just the scalar. For deterministic Boolean transitions the acceptance and rejection sectors sum to the full baseline; keep their actual supports distinct from signed or modular cancellations. Boolean semiring evaluation with all allowed input weights true computes existence; signed/ring transfer does not by itself provide nonemptiness from a modular zero.

Call two distinct labels interleaved if there are positions i<j<k<l with word[i]=word[k]=a, word[j]=word[l]=b. Constants ignored. When no pair interleaves, the partition of occurrence positions into guard labels is noncrossing. Exact recursive contraction: start at the first nonconstant guard a, with all occurrence positions i1<...<it. Every other label occurring strictly between i1 and it lies entirely within exactly one gap (i_j,i_(j+1)); otherwise a,b,a,b occurs. Labels after it are also disjoint from all these gaps. Constant prefixes can simply multiply on the left. Thus recursively compute gap matrices G_j and suffix S, then

    T_block = (sum_(b=0,1) w_a(b) M_i1(b) G_1 M_i2(b)...G_(t-1) M_it(b)) S.

This follows by factoring the finite assignment sums of disjoint labels, preserving the original order of noncommuting matrices. Each gap computed ONCE and reused for both orientations. No division, no independence assumption for repeated positions, no commutation of overlapping matrices. There are O(m) matrix products/additions (each occurrence and gap belongs to one recursion), hence O(m d^3) ordinary ring operations after polynomial parsing; memory polynomial, exact bit costs charged (for signed integer input with bounded bit length, products/sums here have polynomial bit length in explicit word and matrices). All unused guards separately handled. In particular the nested word 1,2,...,q,q,...,2,1 has q simultaneously live labels at its middle cut, but contracts in O(q d^3) operations. This is an actual shared contraction bypassing a potentially exponential chronological separator table, including arbitrary signed noncommuting transfers. No requirement to list the intermediate assignment fibres. Not all original SAT words are noncrossing.

### G86 — vertex-cover parameterization of actual interleaving obstruction

Build a simple graph on original guard labels with edge for each interleaved pair. This is computable in polynomial word length even by exhaustive quadruples. If K is a vertex cover of size k, enumerate the 2^k assignments to these actual original labels (not occurrences), replace each of their occurrences by the corresponding constant matrix, multiply their unary weights once, and contract the remaining noncrossing word by G85. Sum all conditional matrices. Exact cost O(2^k poly(m,d,q)) operations including parsing and weights; no assumption of free cover discovery. Given budget k, choose an uncovered edge and branch on either endpoint, removing incident edges; at most 2^k poly(m,q) work finds a cover of size <=k or proves none. Iterative budget search gives the same fixed-parameter exponential dependence on minimum k up to polynomial factors. Decision version uses Boolean semiring and original existential support. Thus bounded width and k=O(log N) give a polynomial algorithm for this actual supplied representation, even when raw live boundary width is linear. Word order may be changed if source semantics proves it; no assumption an optimal word can be obtained efficiently. This is an upper bound, not a claim that all computation is required to use this order/cover or that k bounds time below.

### G87 — exact commutation shortcut and signed swap defect

For adjacent distinct source labels a,b, if M_i(u)M_j(v)=M_j(v)M_i(u) for all u,v in {0,1}, they can be swapped together with their position and original label without changing ANY assignment's transfer. Constants covered by same criterion. The exact signed residual when the criterion fails is prefix times [M_i(u),M_j(v)] times suffix, where [A,B]=AB-BA. Its weighted sum is the actual consumer difference, not a declaration that two chronological histories are identical. If two labels commute at every mutual occurrence pair, grouping all their occurrences is permitted by repeated swaps through those positions. If all different labels commute pairwise, group by label, preserve within-label order and contract

    T=prod_i (sum_(b=0,1) w_i(b) prod_(j:label j=i) M_j(b))

with constant factors handled by compatible commutation (or kept in their original order if no swap needed). This costs O(m d^3) ring operations after certificate/ordering costs. More generally use any supplied verified swaps to a noncrossing word before G85/G86; computing optimal normalization is not assumed polynomial. An invertible simultaneous chart change preserves commutators, with start/end maps transported; arbitrary lossy changes do not.

Control: word (1,2,...,q) repeated THREE times; each guard read three times, interleaving graph complete, minimum cover q-1. At every occurrence choose identity for 0 and the same involution X for 1 swapping two states (third fixed), so all commute and X^3=X. Weighted contraction is product_i(w_i(0) I + w_i(1) X), O(q) fixed-size matrix operations. The accept sector is even parity and rejected sector odd parity on the two active states. This provides a cheap exact contraction even with maximal interleaving and bounded read count. It also allows general weights breaking an unweighted translation symmetry. Do not turn the interleaving cover size into an unrestricted lower bound.

### G88 — indexed composition and remaining obligation

Keep (source history,tau,k,j,version,coefficient ring,creation/requested precision,word/position,original label,consumer) independent. The actual original guard word is a chart/algorithmic ordering, not a replacement for chronological source events. Nested contraction groups disjoint source labels, while interleaving conditioning retains the original pin and aggregates its two actual orientations. A neutral unassigned bit has both possibilities; modular cancellation is not empty source. Retain acceptance zero mode, signed character moments, rejected residual and original witness extension map. When reordering by commutation, retain source-position bijection and exact swap certificates; if not commuting retain signed defect, rather than silently identify histories. G58 gain/loss and governed six-face residual semantics unchanged, no blanket H05/H07/H14 closure. R122 linear rank and G79 shared linear overlap remain usable but not obligatory. G84 makes the individual affine computations even cheaper than G70; G85–G87 give actual nonlinear composition algorithms, rather than another compulsory width invariant. Remaining N4 is actual global work under all legitimate orderings, semantic substitutions, commutation, branching, signed contractions and arbitrary standard-machine shortcuts. No unrestricted lower bound follows from constant-width program SAT hardness, full rank, or the size of a particular interleaving graph.

### Actually executed local regression (exact Python integers/GF2, no CI/kernel)

Local /tmp/p0_guardword.py: 350 formulas (260 exhaustive q=1,2, 30 seeded each q=3..5); 2,712 original assignments with explicit full right coefficient rank and augmented rank comparison to source CNF; 2,712 original assignment to bounded-occurrence copy extensions checked (reverse follows from equality-cycle proof; did NOT exhaust all independent copy assignments). 360 arbitrary signed noncommuting 3x3 matrix word contractions via minimum vertex cover versus exhaustive source guard assignments; 360 minimum cover checks versus exhaustive subsets. 112 direct noncrossing comparisons including ten deeply nested words q=1..10 (some also included in 360); 240 actual signed formula accept/reject contractions (q=1..6, 40 each) compared with exhaustive assignments, including unused guard factors. 50 complete-interleaving commuting controls (q=1..10, five each) checked against exhaustive source assignments. All passed. No runtime benchmark or native kernel claim. Core reproducer (matrix operations exact Python ints; deterministic seed 369, sampling as described below):

```python
from itertools import product,combinations
from random import Random
from collections import Counter
rng=Random(369)
I=((1,0,0),(0,1,0),(0,0,1))
def mul(A,B):return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(3)) for j in range(3)) for i in range(3))
def add(A,B):return tuple(tuple(A[i][j]+B[i][j] for j in range(3)) for i in range(3))
def scale(a,A):return tuple(tuple(a*x for x in row) for row in A)
def edges(word):
 e=set()
 for i,j,k,l in combinations(range(len(word)),4):
  a,b=word[i],word[j]
  if a is not None and b is not None and a!=b and a==word[k] and b==word[l]:e.add(tuple(sorted((a,b))))
 return e
def cover(E,k):
 if not E:return set()
 if k==0:return None
 a,b=min(E)
 for x in (a,b):
  c=cover({e for e in E if x not in e},k-1)
  if c is not None:return c|{x}
 return None
def nested(word,ms,w):
 if not word:return I
 a=word[0]
 if a is None:return mul(ms[0][0],nested(word[1:],ms[1:],w))
 ix=[i for i,b in enumerate(word) if b==a];last=ix[-1]
 gaps=[nested(word[i+1:j],ms[i+1:j],w) for i,j in zip(ix,ix[1:])]
 C=scale(0,I)
 for b in (0,1):
  P=ms[0][b]
  for G,j in zip(gaps,ix[1:]):P=mul(mul(P,G),ms[j][b])
  C=add(C,scale(w[a][b],P))
 return mul(C,nested(word[last+1:],ms[last+1:],w))
def brute(word,ms,w):
 labels=sorted(set(word)-{None});C=scale(0,I)
 for vals in product((0,1),repeat=len(labels)):
  x=dict(zip(labels,vals));P=I;z=1
  for a in labels:z*=w[a][x[a]]
  for a,M in zip(word,ms):P=mul(P,M[0 if a is None else x[a]])
  C=add(C,scale(z,P))
 return C
def conditioned(word,ms,w,K):
 C=scale(0,I);K=sorted(K)
 for vals in product((0,1),repeat=len(K)):
  x=dict(zip(K,vals));z=1
  for a in K:z*=w[a][x[a]]
  ws=[None if a in x else a for a in word]
  M=[(m[x[a]],m[x[a]]) if a in x else m for a,m in zip(word,ms)]
  C=add(C,scale(z,nested(ws,M,w)))
 return C
def matrix(f):return tuple(tuple(int(j==f[i]) for j in range(3)) for i in range(3))
R=matrix((2,0,2));N=I;Y=matrix((1,1,2))
def compile_formula(F):
 word=[];ms=[]
 for c in F:
  for i,v in c:word.append(i);ms.append(tuple(Y if b==v else N for b in (0,1)))
  word.append(None);ms.append((R,R))
 return word,ms
def val(F,x):return int(all(any(x[i]==v for i,v in C) for C in F))
def rank(rows):
 piv={}
 for v in rows:
  while v:
   k=v.bit_length()-1
   if k in piv:v^=piv[k]
   else:piv[k]=v;break
 return len(piv)
def right_rank(word,ms,x):
 n=3*(len(word)+1);A=[1<<j for j in range(3)];rhs=[1,0,0];p=[1,0,0]
 for t,(i,M) in enumerate(zip(word,ms)):
  T=M[0 if i is None else x[i]]
  for j in range(3):
   A.append((1<<(3*(t+1)+j))|sum((T[k][j]&1)<<(3*t+k) for k in range(3)));rhs.append(0)
  p=[sum(p[k]*T[k][j] for k in range(3))%2 for j in range(3)]
 assert rank(A)==n
 A.append(1<<(3*len(word)));rhs.append(1)
 return rank([a|(b<<n) for a,b in zip(A,rhs)])-n,p[0]
fc=ac=cc=0
for q in range(1,6):
 C=[tuple(zip(J,p)) for k in range(1,min(3,q)+1) for J in combinations(range(q),k) for p in product((0,1),repeat=k)]
 Fs=([C[j] for j in range(len(C)) if t>>j&1] for t in range(1<<len(C))) if q<=2 else (rng.sample(C,rng.randrange(min(8,len(C))+1)) for _ in range(30))
 for F in Fs:
  word,ms=compile_formula(F)
  for x in product((0,1),repeat=q):
   r,v=right_rank(word,ms,x);assert v==val(F,x) and r==1-v;ac+=1
  C2=[];uses=[[] for _ in range(q)];n=0
  for c in F:
   C2.append(tuple((n+j,v) for j,(i,v) in enumerate(c)))
   for j,(i,v) in enumerate(c):uses[i].append(n+j)
   n+=len(c)
  for L in uses:
   if len(L)>1:C2.extend([((a,0),(b,1)) for a,b in zip(L,L[1:]+L[:1])])
  assert max(Counter(i for c in C2 for i,v in c).values(),default=0)<=3
  for x in product((0,1),repeat=q):
   y=[0]*n
   for i,L in enumerate(uses):
    for a in L:y[a]=x[i]
   assert val(C2,y)==val(F,x);cc+=1
  fc+=1
assert (fc,ac,cc)==(350,2712,2712)
rchecks=nc=vc=0
for q in range(1,7):
 for _ in range(60):
  word=list(range(q))*2+[rng.randrange(q) for i in range(rng.randrange(3))];rng.shuffle(word)
  E=edges(word);K=next(c for k in range(q+1) if (c:=cover(E,k)) is not None)
  assert all(set(e)&K for e in E)
  assert len(K)==min(len(J) for j in range(q+1) for J in combinations(range(q),j) if all(set(e)&set(J) for e in E));vc+=1
  ms=[tuple(tuple(tuple(rng.randrange(-2,3) for j in range(3)) for i in range(3)) for b in (0,1)) for _ in word];w={i:(rng.randrange(-3,4),rng.randrange(-3,4)) for i in range(q)}
  assert conditioned(word,ms,w,K)==brute(word,ms,w);rchecks+=1
  if not E:assert nested(word,ms,w)==brute(word,ms,w);nc+=1
for q in range(1,11):
 word=list(range(q))+list(reversed(range(q)));assert not edges(word)
 ms=[tuple(tuple(tuple(rng.randrange(-1,2) for j in range(3)) for i in range(3)) for b in (0,1)) for _ in word];w={i:(1,rng.randrange(-2,3)) for i in range(q)}
 assert nested(word,ms,w)==brute(word,ms,w);nc+=1
assert (rchecks,nc,vc)==(360,112,360)
zchecks=0
for q in range(1,7):
 C=[tuple(zip(J,p)) for k in range(1,min(3,q)+1) for J in combinations(range(q),k) for p in product((0,1),repeat=k)]
 for _ in range(40):
  F=rng.sample(C,rng.randrange(min(6,len(C))+1));word,ms=compile_formula(F);L=set(word)-{None};E=edges(word);K=next(c for k in range(q+1) if (c:=cover(E,k)) is not None)
  w={i:(rng.randrange(-3,4),rng.randrange(-3,4)) for i in range(q)};T=conditioned(word,ms,w,K);free=1
  for i in set(range(q))-L:free*=sum(w[i])
  a=d=0
  for x in product((0,1),repeat=q):
   v=1
   for i,b in enumerate(x):v*=w[i][b]
   if val(F,x):a+=v
   else:d+=v
  assert (free*T[0][0],free*T[0][1],free*T[0][2])==(a,0,d);zchecks+=1
X=matrix((1,0,2));control=0
for q in range(1,11):
 word=list(range(q))*3;assert len(edges(word))==q*(q-1)//2
 ms=[(I,X)]*len(word)
 for _ in range(5):
  w={i:(rng.randrange(-3,4),rng.randrange(-3,4)) for i in range(q)};P=I
  for i in range(q):P=mul(P,add(scale(w[i][0],I),scale(w[i][1],X)))
  assert P==brute(word,ms,w);control+=1
assert (zchecks,control)==(240,50)
```

### Endpoint-first ledger

| Gate | Deliverable | Status |
|---|---|---|
| G84 | constantWidthBilinearGuardTransfer / fullColumnRankAffineFibres / boundedReadHardness | derived and tested source evaluation and rank, copy extension tested |
| G85 | noncrossingGuardWordDivisionFreeContraction | derived and tested; actual upper bound, arbitrary noncommuting matrices |
| G86 | interleavingVertexCoverContraction | derived and tested; FPT upper bound including cover search |
| G87 | certifiedGuardSwap / signedCommutatorResidual / denseCommutingControl | derived and tested commuting control |
| G88 | indexedGuardCompositionResourceBoundary | derived; actual source and separate zero/signed/rejected sectors |
| N4/G12a | unrestrictedSerialCharge | OPEN: cost under all legitimate nonlinear/ordering/commutation/shared computation shortcuts |
| N5/G12c | unrestrictedSuperpolynomialGrowth | OPEN; original uniform G48 flag / stronger nonuniform G38 |
| N6 | originalClayTransport | conditional #1040/#1129 |

Geometry-forward Aristotle BIDI: the real improvement is G85/G86, an actual exact upper-bound algorithm bypassing both compulsory linear channel enumeration and chronological boundary enumeration on nested guard geometry. G84 says even affine conditional fibres and constant full right coefficient rank can retain the hard joint selector. G87 admits source-dependent commutation and explicitly defeats a compulsory interleaving charge. Next investigate actual noncommuting interaction and reusable subword transfer or the direct standard-machine N4 endpoint, without assuming a particular branching program, word, or its optimized form is universally necessary. Do not replace SAT by counting, full global symmetry, optimal normalization or rank computation. Preserve zero mode, inhabited neutral fibre, signed residual and indexed hyperfabric as semantics, not mandatory materialization. No P!=NP claim, no additional certification prerequisite.


## 32. P0-G89–G93 — GEOMETRY-FORWARD: exact rank-one decision boundary and rank-two guard transfer (2026-11-24)

Literal Clay P vs NP P0. Inputs: both current pasted files, G84–G88 and Langlands R128–R133 (reported #1549/#120 b9443ceb0f28/dd6c33352dca, blob 30b6833e0b111b8eaa70d96269a459a0520766cb). Use shared-orientation accounting as donor, not a new Langlands endpoint. Initial live P0 reads 41bf8d6ed02d / 43898587b2e0, common blob d13acfbfda00542f3cd762659c2c9fce1f251cb7. Reconciled concurrent appended guard-obstruction section at Agda e193c4f777f9 / Lean e9acb018e2fe: both contents equal except repository-relative reproducer link. Preserve that work and its original IDs; in this section denote its duplicate G89–G93 labels as G89–G93 (parallel obstruction-cube ledger), distinct from main sections 29–30 G89–G83. G92's consumer-complete quotient is not a SAT/UNSAT collision, and G93's signature is a proof-search instrument, not mandatory state. Reuse G16/G17 median/implication graph, G45–G48 flag, G51 quotient, G53–G59 signed precision, G65–G83 separator/guard geometry, G84–G88 ordered transfer, G89–G93 guarded-path residual, section 27 ConstraintCouplingSearchExact / ObservationSeparatorGeometryExact / IndexedCubeHyperfibreExact, #1291 H05, #1006 FactorsThrough, #123 JMD lowering, #1546 sharing, #1474/#1502 Karp/Cook-Levin, #1129 costed machine, #1040 SATDecisionFailure, #607/#678 Aristotle. Classical 2SAT algorithm Aspvall–Plass–Tarjan 1979 DOI 10.1016/0020-0190(79)90002-4; counting control Valiant 1979 DOI 10.1137/0208032 (#monotone-2CNF completeness). No literature novelty claim for elementary matrix factoring or classical reductions. No other programme edits, CI or native kernel.

### G89 — exact rank-one guard support is bijunctive

Given original guard word F(x)=a^T product_j M_j(x_label_j) b over an effective field (explicit rational or fixed finite field matrices, or integers using fraction field), assume both orientations at every nonconstant position have rank <=1. Arbitrary constant matrices permitted. Factor each nonzero matrix M=u v^T by a nonzero pivot p=M_rc, u=column c, v=row r/p. Zero matrix uses u=0, v arbitrary. For integer decision only, take unscaled row r, giving u v^T=p M; multiplication by nonzero pivot does not change nonvanishing but DOES change weighted scalar, so do not reuse scaled count as original. All factoring and constant bridge products cost polynomial in explicit input length with exact rational/integer bit costs.

Absorb constant runs into bridges B_j. The exact unscaled scalar is
    (a^T B_0 u_1) prod_j (v_j^T B_j u_(j+1)) (v_m^T B_m b).
If no guarded positions evaluate constant directly. Field has no zero divisors; support is conjunction of unary endpoint and at-most-binary consecutive overlap nonzero tests. For each zero table entry forbid its assignment by a clause of width <=2. If labels coincide, use only the two consistent orientations, not independent copies. Thus arbitrary interleaving/read count, arbitrary noncommuting rank-one matrices, zero transitions and constant bridges reduce exactly to 2SAT on original guards. Rank-one support is majority-closed by G16; projected support through existential Boolean auxiliaries remains majority-closed. In particular cannot represent OR3 by existential rank-one guard encoding preserving original witness projection. No claim all tractable relations are bijunctive or that arbitrary decision reductions must preserve that projection.

Converse: every 2CNF has an exact width-two rank-one word with 0/1 matrices. For clause (l(x) OR r(y)), set e=(1,0)^T, L=l(x), R=r(y). Use A(x)=e(L,1-L), B(y)=(1,R)^T e^T. Both ranks exactly one; AB=[L+(1-L)R]ee^T. Concatenate clause pairs, endpoints e^T,e. Unit duplicates label, empty clause constant zero, empty formula one. Exact scalar equals Boolean clause product over any nonzero field. This is an exact characterization of rank-one support expressiveness on original guards, not a claim of universal efficient representation. Ring with zero divisors does NOT obey product-nonzero equivalence (2*2=0 mod4); modular nonzero differs from original integer support.

### G90 — width-two rank-two transfer already captures original SAT

Compress G84 to two LIVE states U,S with dead represented by zero row. Literal false selects I=[[1,0],[0,1]], true selects Y=[[0,1],[0,1]]. Clause boundary constant R=[[0,0],[1,0]]. Start e^T=(1,0), end e. True sets S, false retains state, R resets S to U and sends U to zero. Zero stays zero. Thus F(x) in {0,1} equals original CNF truth over integers and any nonzero field. All displayed matrices nonzero 0/1 rank<=2; only I rank two. Empty formula accepts, empty clause rejects by reset. Reduction linear in source occurrences and clauses. G84 cyclic-implication private copies restrict each guard to at most three reads with unique extension on used variables, unused original bits retained free. Hence exact global nonzero decision NP-complete on this width-two bounded-read transfer subclass, membership by evaluation at supplied x. The fixed-guard trajectory system still full column rank, unique run before terminal equation, and fixed trajectory equations affine in guards as in G84. Retain rejected source indicator 1-F, not interpret zero row as absence of original assignment. This is sharp rank-one vs rank-two threshold for this model, not P!=NP or a lower bound on required rank of all general algorithms.

### G91 — explicit higher-rank guard strong backdoor

Let K be original labels with any occurrence having any orientation rank>=2, excluding constants. Compute by exact rank tests. Enumerate 2^|K| assignments to original labels K, substitute every occurrence consistently, leave resulting constant bridges of arbitrary rank, and invoke G89 2SAT. OR branch decisions, reconstruct witness on success. Bound 2^|K| poly(input bit length), including rank tests/bridge products, no interleaving or separator-state enumeration. |K|=O(log N) gives polynomial decision for supplied representation. This is a strong backdoor, not minimum over all charts or a lower bound: G87 commuting rank-two words can be cheap, and 2SAT itself may have rank-two transfer via G90 and rank-one transfer via G89. Invertible per-boundary state gauges preserve rank with endpoints transported; blocking factors depending on multiple guards need not yield binary support. All lawful preprocessing costed.

### G92 — counting hardness already below decision boundary

G89's 0/1 rank-one encoding of monotone 2CNF preserves original assignments exactly; W=sum_x F(x) #P-hard by Valiant (and #P-complete for Boolean acceptance family under standard counting reductions). Decision remains in P. With actual unary weights w_i(0),w_i(1), retain accepted A=sum_x F(x) prod_i w_i(x_i), rejected R=sum_x (1-F(x)) prod_i w_i(x_i), A+R=prod_i(w_i(0)+w_i(1)). Over any commutative ring, exact signed or modular weighted sums with no division. Fourier signs are weights; zero mode is original integer count; modular cancellation not empty source. Counting hardness is not required computation for decision, as G53–G55 show. No inference from R128 generic rank or #P-hard count to unrestricted lower bound.

### G93 — indexed transport and remaining endpoint

Keep (history,tau,k,j,version,ring,creation/requested precision,word position,original guard label,consumer) independent. Attach actual matrices, rank certificate, factor pivot/scaling, bridge intervals and original pin correspondence. Distinguish inhabited neutral guard, rejected run, signed residual, exact zero mode and modular zero. Reordering requires G87 swap certificate/actual commutator residual; conditioning K is not deletion of source; K may change with source revision. Keep G58 gain/loss and G90 signed coefficient/support ledger, no blanket H05/H07/H14 closure. A uniform polynomial-cost transformation of arbitrary SAT into rank-one (or logarithmic-backdoor) decision class would imply P=NP; converse if P=NP by deciding input then outputting fixed yes/no instance, not a witness-preserving transformation. Proving impossibility of arbitrary polynomial-time decision reductions to that class would settle P!=NP, not a free enabling lemma. Witness-preserving rank-one reduction with existential auxiliaries is already ruled out for nonbijunctive relations on original guards, but that restricted result is NOT general decision-reduction impossibility. N4/N5 remain actual unpaid obligations. Keep direct candidate-failure / observer-collision / resource-closed self-diagonal OR routes, #1040/#1129 terminal. G92 collision boundary retained. No certification prerequisite.

### Actual local execution (Python exact integers)

Executed local /tmp/p0_rank_boundary.py, Random(369): 560 signed 2x2 word cases q=1..7 (80 each), with arbitrary constant matrix bridges, zero matrices, repeated labels, 127 nonempty higher-rank backdoors. 771 conditioned branch decisions compared with implication-graph closure, 20,320 support comparisons (each assignment checked in its own branch), all 560 global decisions compared with exhaustive enumeration. 280 width<=2 formulas (40 per q), 10,160 assignment truth checks, 280 weighted acceptance/rejection identities. 280 width<=3 formulas, 10,160 truth checks, 280 weighted identities, 10,160 intended bounded-read copy extensions. All passed. Reverse extension uniqueness by equality-cycle proof, not enumeration of all independent copy assignments. No finite-field extension tests or asymptotic runtime benchmark. Core exact integer decision reproducer (pivot scaling used only for support):

```python
from itertools import product
I=(1,0,0,1); Z=(0,0,0,0); e=(1,0)
def mm(A,B):
 a,b,c,d=A; f,g,h,i=B
 return (a*f+b*h,a*g+b*i,c*f+d*h,c*g+d*i)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def row(a,M):return (a[0]*M[0]+a[1]*M[2],a[0]*M[1]+a[1]*M[3])
def outer(a,b):return tuple(x*y for x in a for y in b)
def rank(M):return 2 if M[0]*M[3]!=M[1]*M[2] else int(any(M))
def fac(M):
 if M==Z:return (0,0),(1,0)
 i=next(i for i,x in enumerate(M) if x);r,c=divmod(i,2)
 return (M[c],M[2+c]),(M[2*r],M[2*r+1])
def eval_(W,x,a=e,b=e):
 for i,M in W:a=row(a,M[0 if i is None else x[i]])
 return dot(a,b)
def residual(W,pins,a=e,b=e):
 A=I;last=None;C=[]
 def forbid(labels,fn):
  J=sorted(set(labels))
  for bits in product((0,1),repeat=len(J)):
   if not fn(dict(zip(J,bits))):C.append(tuple((i,1-v) for i,v in zip(J,bits)))
 for i,M in W:
  if i is None or i in pins:A=mm(A,M[0 if i is None else pins[i]]);continue
  assert all(rank(m)<=1 for m in M)
  U,V=zip(*(fac(m) for m in M))
  if last is None:forbid([i],lambda x:dot(row(a,A),U[x[i]]))
  else:
   j,V0=last;forbid([j,i],lambda x:dot(row(V0[x[j]],A),U[x[i]]))
  last=(i,V);A=I
 if last is None:
  if not dot(row(a,A),b):C.append(())
 else:
  i,V=last;forbid([i],lambda x:dot(row(V[x[i]],A),b))
 return C
def cnf(C,x):return all(any(x[i]==v for i,v in c) for c in C)
def sat2(q,C):
 if () in C:return False
 R=[1<<i for i in range(2*q)]
 for c in C:
  a,b=c[0],c[-1];i=2*a[0]+a[1];j=2*b[0]+b[1];R[i^1]|=1<<j;R[j^1]|=1<<i
 for k in range(2*q):
  for i in range(2*q):
   if R[i]>>k&1:R[i]|=R[k]
 return not any(R[2*i]>>(2*i+1)&1 and R[2*i+1]>>(2*i)&1 for i in range(q))
U=(0,1,0,1); R=(0,0,1,0)
def rank1_formula(F):
 W=[]
 for c in F:
  (i,s),(j,t)=c[0],c[-1]
  W.append((i,tuple(outer(e,(int(x==s),int(x!=s))) for x in (0,1))))
  W.append((j,tuple(outer((1,int(y==t)),e) for y in (0,1))))
 return W
def rank2_formula(F):
 W=[]
 for c in F:
  for i,s in c:W.append((i,tuple(U if b==s else I for b in (0,1))))
  W.append((None,(R,R)))
 return W
```

Sampling reproducibility: rng=Random(369), vec() two rng.randrange(-2,3), rank1() outer(vec(),vec()), randomM() four rng.randrange(-2,3). For q=1..7, trial=0..79, draw a,b=vec(),vec(); word length rng.randrange(1,3*q+1); each position label rng.randrange(q), matrices rank1(),rank1(). Insert 3 constant randomM bridges (draw insertion index first). Odd trial choose K by rng.sample(range(q),rng.randrange(min(q,3)+1)); each position with label in K replace pair by randomM(),randomM() if rng.randrange(2). Recompute actual K by rank; iterate all pins and compare residual 2CNF on every consistent assignment to original nonzero, compare sat2 to branch truth. Continue RNG q=1..7, width2 then3, 40 clausesets each, sample 0..min(12,len(all clauses)) from all clauses ordered by width, lexicographic scope/sign bits, draw q vec() weights. Compare weighted sectors and truth; for width3 use G84 copy split with unused original bits retained free. Exact regression counts above.

| Gate | Deliverable | Status |
|---|---|---|
| G89 | rankOneGuardSupportBijunctive / exactBinaryOverlapReduction | derived and tested, converse exact |
| G90 | rankTwoWidthTwoBoundedReadSATHardness | derived and tested, copy reverse by proof |
| G91 | higherRankGuardStrongBackdoor | derived and tested, paid upper bound |
| G92 | rankOneCountingDecisionSeparation / weightedRejectedResidual | derived and tested, classical #2CNF hardness |
| G93 | indexedRankBoundaryResourceTransport | derived |
| GO75–GO79 | parallel guard-obstruction / consumer-signature route | expanded in section 33; separate from G75–G93 |
| N4 | unrestrictedSerialCharge | OPEN: arbitrary legal preprocessing, sharing and bypass |
| N5 | unrestrictedSuperpolynomialGrowth | OPEN; direct uniform or stronger central slice |
| N6 | originalClayTransport | conditional #1040/#1129 |

Geometry-forward Aristotle BIDI: G89/G90 establish actual support-composition transition and G91 a paid shortcut, not obligatory rank. G92 is decisive count-vs-decision control below that transition. Next examine legitimate reductions of higher-rank dependencies to binary factors and residual costs, or direct uniform endpoint, allowing arbitrary representations. Preserve independent indices, zero mode, inhabited neutral fibre and signed residual as semantics, not compulsory materialization. No P!=NP claim.

## 33. P0-GO75–GO79 — GEOMETRY-FORWARD: path-pair obstruction antichain, signed ternary contraction and parity anti-control (2026-11-24)

**Controlling endpoint remains literal Clay P vs NP.** This section continues G70–G93 and expands the reserved parallel GO75–GO79 route and the Aristotle BIDI route. It does not create a new prerequisite programme. Geometry is the proof-search coordinate system; no count of paths, cubes, antichain members, separator states, or semantic classes is promoted to a lower bound on arbitrary computation.

### GO75 — exact path-pair obstruction antichain and obstruction CNF (formalizes G77)

Let the left variables be \(L\), with \(q=|L|\), and let every clause cross \(L\mid R\), have width at most three, and contain at least one variable on each side. A literal \((v,b)\) is satisfied when \(x_v=b\).

For a clause \(C\), define its left activation guard as the partial assignment

\[
\gamma_C=\{(v,1-b):(v,b)\in C,\ v\in L\}.
\]

The residual right clause \(D_C=C\cap R\) has width one or two. Its ordinary 2-SAT implication edge or edges all carry the same guard \(\gamma_C\). A path is active at \(x\) exactly when \(x\) extends the compatible union of all its edge guards.

For each right variable \(i\), pair a path \(P:i^+\leadsto i^-\) with a path \(Q:i^-\leadsto i^+\). If the union of their guard pins is consistent, call that union an obstruction cube \(\sigma(P,Q)\). Let \(\mathcal O_F\) be the inclusion-minimal antichain of all such path-pair labels, discarding inconsistent unions and any label subsumed by a smaller pin set.

The exact theorem is

\[
\boxed{
\{x:F_x\text{ is unsatisfiable}\}
=\bigcup_{\sigma\in\mathcal O_F}[\sigma],
}
\]

where \([\sigma]\) is the set of full left assignments extending \(\sigma\).

Proof: an active contradictory path pair gives a 2-SAT contradiction; conversely, if \(F_x\) is unsatisfiable, the 2-SAT implication criterion supplies a variable with mutually reachable complementary literals and hence an active path pair. Antichain pruning does not change the union. This is the antichain of single path-pair certificates, not necessarily the complete set of prime bad cubes or prime implicates. Consensus across several path-pair certificates can yield a larger bad cube that is not itself one path-pair label; retain the existing G77 consensus caveat. The cover identity is exact even when this path-generated CNF is not globally minimal.

Therefore the existential projection onto the left variables has the exact obstruction-CNF representation

\[
\boxed{
\exists y\,F(x,y)
\iff
\bigwedge_{\sigma\in\mathcal O_F}
\ \bigvee_{(v,b)\in\sigma}(x_v\ne b).
}
\]

An empty obstruction pin set gives an empty clause and no good left assignment; an empty obstruction family gives the true relation. This is exact quantifier elimination for this guarded 2-SAT fibre presentation. It is not claimed to be a polynomial-size CNF.

The path-label operations form an antichain semiring: alternatives are antichain union; path composition is pairwise compatible pin-union followed by antichain reduction. The G73 Boolean guarded-closure DAG remains the compact producer. The antichain is an optional expansion, not the required execution representation.

### GO76 — signed ternary join contraction and inhabited-support ledger (extends G76)

The partial-assignment space is

\[
\mathcal P_L=\{*,0,1\}^{q}.
\]

Here \(*\) is an inhabited neutral coordinate with two extensions; \(0\) and \(1\) are pinned coordinates with one extension each. Compatible partial assignments join by union. Opposite pins on the same coordinate join to bottom, representing an empty intersection.

For \(\mathcal O_F=(\sigma_1,\ldots,\sigma_m)\), define the signed coefficient map by

\[
\alpha_0(\varnothing)=1,\qquad
\alpha_0(\tau)=0\quad(\tau\ne\varnothing),
\]

\[
\boxed{
\alpha_{j+1}(\tau)
=
\alpha_j(\tau)
-
\sum_{\rho:\ \rho\sqcup\sigma_{j+1}=\tau}\alpha_j(\rho),
}
\]

where incompatible joins contribute nothing. Independently define the inhabited-support bit

\[
s_0(\varnothing)=1,\qquad s_0(\tau)=0\quad(\tau\ne\varnothing),
\]

\[
\boxed{
s_{j+1}(\tau)
=
s_j(\tau)\ \lor\
\bigvee_{\rho:\ \rho\sqcup\sigma_{j+1}=\tau}s_j(\rho).
}
\]

The coefficient recurrence is the expansion of the product of obstruction complements. The support recurrence records whether any compatible subfamily actually inhabits that intersection, even when its signed coefficient cancels to zero. Both recurrences are order-independent because they represent the same finite product and the same family of compatible subfamily joins.

Writing \(G_F(x)=1\) exactly when the right fibre is nonempty,

\[
G_F(x)=\prod_{\sigma\in\mathcal O_F}(1-\mathbf1_{[\sigma]}(x))
      =\sum_{\tau\in\mathcal P_L}\alpha_m(\tau)\mathbf1_{[\tau]}(x).
\]

For a Walsh character \(\chi_\eta(x)=(-1)^{\eta\cdot x}\), its signed residual is

\[
\boxed{
Z_\eta
=
\sum_{\tau\in\mathcal P_L}\alpha_m(\tau)
\begin{cases}
(-1)^{\eta\cdot\tau}\,2^{q-|\operatorname{dom}\tau|},
 & \operatorname{supp}(\eta)\subseteq\operatorname{dom}\tau,\\
0,&\text{otherwise}.
\end{cases}
}
\]

In particular, \(Z_0\) counts left assignments with an inhabited right fibre. It is **not** the total number of satisfying pairs. The latter remains the separate multiplicity consumer

\[
W_F=\sum_x |\{y:F(x,y)\}|.
\]

The ledger must distinguish: (i) bottom from incompatible pins (empty intersection); (ii) an inhabited \(\tau\) whose signed coefficient is zero; and (iii) cancellation in a nontrivial Walsh mode because a character is free on a neutral coordinate. None of these signed zeros is evidence that the original fibre is uninhabited. Keep source identity, multiplicity, support, coefficient, history/time, closure-stage \(k\), and chart/refinement indices distinct.

### GO77 — parity is an exponential-antichain negative control (strengthens G78)

For \(q\ge1\), take left variables \(g,x_1,\ldots,x_q\) and right variables \(z_0,\ldots,z_q\). For each \(i\), add the four clauses encoding

\[
z_i=x_i\oplus z_{i-1}.
\]

Also add the two crossing clauses

\[
(g\lor\neg z_0),\qquad(g\lor\neg z_q).
\]

Every clause crosses the partition and has width at most three. If \(g=1\), the endpoints are unconstrained and every \(x\) has two right witnesses. If \(g=0\), the endpoints force \(z_0=z_q=0\), so a right witness exists exactly when \(x\) has even parity, and is then unique. Thus

\[
G_F(g,x)=g\lor[\operatorname{parity}(x)=0],
\]

\[
\{(g,x):F_{(g,x)}\text{ is unsatisfiable}\}
=\{(0,x):\operatorname{parity}(x)=1\}.
\]

Every subcube contained in this bad set must pin \(g=0\) and every \(x_i\): freeing \(g\) admits \(g=1\), and freeing any \(x_i\) admits an even-parity assignment. Hence the path-pair obstruction cover has exactly \(2^{q-1}\) singleton cubes. The symbolic G73 closure still has size \(O(q^3)\), while the source has only \(4q+2\) clauses. The fibre-support function itself has a linear-size parity circuit.

The zero mode and full witness multiplicity are different:

\[
Z_0=2^q+2^{q-1}=3\cdot2^{q-1},
\qquad
W_F=2\cdot2^q+2^{q-1}=5\cdot2^{q-1}.
\]

For characters indexed by \((\eta_g,\eta_x)\), the support Walsh modes are

\[
Z_{(\eta_g,\eta_x)}
=
\begin{cases}
(-1)^{\eta_g}2^q+2^{q-1},&\eta_x=0,\\
2^{q-1},&\eta_x=(1,\ldots,1),\\
0,&\text{otherwise}.
\end{cases}
\]

This is a decisive negative control: an exponential path-obstruction antichain can describe an easy function. **Antichain cardinality, path count, or the cost of expanding the obstruction CNF cannot be charged as unavoidable SAT computation.**

A side-preserving G72 occurrence-copy lift makes the same control locally unrestricted: put each private occurrence copy on its source variable's side, enforce equality using fixed-zero gadget variables on the opposite side, and pad the binary endpoint clauses with a positive zero-gadget literal. Every emitted relation is a three-variable clause with one forbidden pattern; scopes are distinct and crossing, and all unary/binary projections are full. The valid left slice (zero gadget coordinates and consistent left copies) retains the odd-parity bad points. Any subcube containing two distinct valid odd points also contains a consistent-copy even point, so any path-pair cube cover still needs at least \(2^{q-1}\) members. This is a cover-size theorem, **not** a circuit lower bound.

### GO78 — exact factor-through boundary: the semantic quotient is not a SAT/UNSAT collision

G71's canonical key \(\kappa(x)=\operatorname{Canonical}_{2\mathrm{CNF}}(F_x)\) preserves the entire right witness relation. It therefore distinguishes an empty fibre from a nonempty fibre. It is a consumer-complete semantic quotient, not the lossy observer required by the existing P-vs-NP collision route.

This is consistent with the existing Clay owners:
- PNotEqualsNPDirectSATLowerBoundExact requires failure for every polynomial-time SAT decider, yielding SATNotInP and then the literal Clay endpoint.
- PNotEqualsNPObserverCoverageExact requires, for every anchored polynomial candidate, a polynomial observer and a satisfiable/unsatisfiable pair with the same observer representation.
- PNotEqualsNPPolynomialObserverNoGoExact rules out promoting identity, injective, or merely polynomial-time representations to a collision.
- PNotEqualsNPResourceBoundedSelfDiagonalExact retains the separate semantic self-diagonal versus resource-closure split.

GO75–GO77 do not yet supply a candidate-specific SAT/UNSAT collision or universal polynomial-decider failure. Do not promote them to SATLowerBoundProducer.

### GO79 — Aristotle BIDI next cut: consumer-complete residual transport (extends G79/G88)

Forward producer: guarded implication DAG, antichain path-pair labels, signed ternary join coefficients, inhabited-support ledger.

Backward consumer: the exact decision \(\exists x\,G_F(x)\), or equivalently the literal SAT decision on the compiled formula.

The next alpha search is to construct a **consumer-complete residual signature across a cut of the original guard variables**. It must compose under future guard events and preserve, separately:
1. nonempty versus empty residual support;
2. right-witness multiplicity when that is the consumer;
3. zero mode and signed Walsh residuals;
4. the actual source pins and their provenance;
5. the independent chronological, closure-stage, and chart/refinement indices.

A proposed signature is admissible only if its forward reconstruction and backward consumer equivalence both hold. It must not assume that equal scalar residuals imply equal inhabited fibres, or that a locally identical 2-SAT residual remains identical after a new crossing guard event. The signature is a proof-search instrument, not a mandatory materialization or an extra Clay prerequisite.

**Unpaid Clay obligations remain unchanged:**

| Gate | Exact obligation | Status |
|---|---|---|
| GO75 | Path-pair obstruction-cube coverage and obstruction CNF | Derived and tested |
| GO76 | Signed ternary coefficient/support recurrence and Walsh formula | Derived and tested |
| GO77 | Exponential-antichain parity anti-control; side-preserving local-full lift | Derived; local q=1 lift tested |
| GO78 | Semantic quotient versus actual SAT/UNSAT observer collision boundary | Derived from existing owners |
| GO79 | Consumer-complete residual signature across arbitrary future guard cuts | Open search |
| N4 | Unavoidable global selection cost across all sharing, bypasses, recomputation, and representations | **Open** |
| N5 | Unrestricted superpolynomial lower bound / universal polynomial SAT failure | **Open** |
| N6 | Literal Clay P vs NP endpoint transport through SATLowerBoundProducer | Conditional consumer |

### Exact local regression and source ownership

Committed dependency-free reproducer: [scripts/check_p0_guard_obstruction_geometry_20261124.py](../../scripts/check_p0_guard_obstruction_geometry_20261124.py) in both P0 branches.

Exact Python-integer results:
- 300 random crossing formulas; 2,220 left assignments; all guarded-path obstruction covers agreed with independent 2-SAT implication closure; 470 total antichain terms, maximum 9.
- 250 random formulas; 1,846 Walsh modes agreed between inclusion-exclusion and direct assignment sums; maximum 10 obstruction terms.
- 100 random formulas; 764 Walsh modes verified the ternary coefficient recurrence, reverse-order invariance, and support ledger; maximum 17 inhabited partial-assignment states.
- Parity widths \(q=1,\ldots,6\): exact obstruction antichain sizes \(1,2,4,8,16,32\).
- Parity widths \(q=1,\ldots,4\): all 60 support Walsh modes checked; zero modes \(3,6,12,24\).
- G72 side-preserving local-full parity smoke: 48-clause zero gadget has exactly one solution; compiled instance has \(12\) left and \(16\) right variables, \(86\) crossing clauses with unique scopes, three nonempty left fibres, right witness counts \(1,2,2\), and total witness count \(5\).

These are finite exact local regressions only. No CI, Agda kernel, Lean kernel, or asymptotic lower-bound verification was run. The parity antichain theorem for all \(q\) is the direct subcube argument above, not an extrapolation from the finite table.

Existing donors reopened and retained: ConstraintCouplingSearchExact; ResidualConstraintDecompositionExact; ObservationSeparatorGeometryExact; TransformLocalFibreGeometryExact; IndexedCubeHyperfibreExact; VerifiedFractranCrankPipeline; PNotEqualsNPClayCoreExact; PNotEqualsNPDirectSATLowerBoundExact; PNotEqualsNPObserverCoverageExact; PNotEqualsNPPolynomialObserverNoGoExact; PNotEqualsNPResourceBoundedSelfDiagonalExact. Aristotle BIDI search remains linked to #607/#678. FRACTRAN/MDL #123, FactorsThrough #1006, sharing #1546, machine/terminal coverage #1040/#1129, and the existing G22/G30/G45–G93 producers remain donors, not proof prerequisites.

**P0 priority:** find a representation-independent obstruction to global selection, or discharge one of the existing direct candidate-failure / observer-collision / resource-closed self-diagonal OR routes. Do not count the antichain. Retain the zero mode, inhabited neutral fibre, signed residual, and indexed hyperfabric.



## 34. P0-G94–G98 — geometry-forward: exact majority-defect backdoors and exponential flat binary-cover cost (2026-11-24)

Stay on literal Clay P vs NP. Inputs: current pasted G89–G93 rank boundary (section 32 locally labelled GO75–GO79), section 33 independent guard-obstruction route, G16/G17 majority closure, G84–G88 ordered shared guard transfer. Retain #1006 FactorsThrough, #1546 sharing, #123 JMD lowering with attribution, #1040/#1129 SATDecisionFailure and costed machine, #607/#678 Aristotle BIDI. Section order differs on the two branches due to parallel work; append without reordering or overwriting existing sections. Gate names G94–G98 are new in the inspected roadmaps. No claim of literature novelty for elementary majority/cover arguments.

### G94 — exponential flat witness-preserving rank-one cover

Let S_m be the satisfying assignments of F_m=AND_i(x_i1 OR x_i2 OR x_i3) on 3m distinct original bits. One-hot witness set W_m={100,010,001}^m has size 3^m. Every rank-one word's nonzero support over an effective field is bijunctive by section 32, also after existential projection of arbitrary Boolean auxiliaries. For any sound majority-closed chart A subset S_m, its projection to each block is majority-closed and excludes 000, so misses at least one one-hot state e_j (majority of all three is 000). Consequently A is contained in the product chart requiring OR of the other two bits per block: the only forbidden local states are 000 and e_j. In particular |A intersect W_m|<=2^m. Every exact flat union of projected rank-one charts requires at least ceil((3/2)^m) charts even with cross-block constraints, overlaps, and arbitrary auxiliary counts. This is a semantic flat-cover lower bound, not an unrestricted decision time bound.

### G95 — exact reduction to ternary box covering, matching exponential rate

For p in {0,1,2}^m define B_p on W_m by w_i != p_i at every block and lift to the binary CNF AND_i OR of the two coordinates other than p_i. Every chart in G94 can be enlarged to one such B_p lift without leaving S_m. Conversely covering all W_m by B_p covers S_m, because every satisfying assignment dominates a one-hot assignment and the lifted charts are upward closed. Hence optimal flat chart count equals the minimum number of these ternary boxes covering the ternary cube. Independently sample k exclusions uniformly; a fixed witness is covered with probability (2/3)^m per sample. Union bound gives failure probability <= 3^m exp(-k(2/3)^m)<1 for k=ceil((3/2)^m(m ln 3+1)). Therefore the lower and upper exponential rates agree. This is an existence upper bound, not an efficient generator claim. Exact small minima m=1,2,3 are 2,3,5 by enumerating box subsets (see local regression).

### G96 — exact semantic strong backdoor via majority defects

For S subset {0,1}^n, collect D(a,b,c)={i:a_i,b_i,c_i not all equal} for triples a,b,c in S with coordinatewise majority outside S. For original-coordinate pin set K, all residual fibres S|p (including empty) are majority-closed iff K intersects every defect D. Forward: a missed D leaves all three witnesses together in the same K fibre and the invalid majority has the same pins. Backward: any fibre violation gives a missed D. Projection/extension of fixed pins preserves majority. By the usual Boolean majority/2CNF characterization (G16), minimum strong semantic backdoor size is exactly the transversal number of this defect hypergraph; for no defects it is zero. This invariant depends on original labelled support, not transfer representation, but constructing the full hypergraph or extracting a minimum transversal is not claimed polynomial. Keep defect triples and their excluded majority as signed source residual; do not conflate empty fibre with inhabited neutral guard.

### G97 — reverse-pin exact characterization for monotone CNF

Let P be inclusion-minimal positive clauses (remove duplicate and subsumed clauses). K is a strong semantic backdoor iff every C in P has |C minus K|<=2. Sufficiency: all surviving clauses under any pins have width<=2. Necessity: for C with |C minus K|>=3 set K intersect C to zero and K minus C to one. C minus K remains minimal: any surviving D with D minus K subset C minus K must have D subset C, so D=C. A monotone relation with a minimal clause E of width>=3 is nonbijunctive: set all outside E to one and choose three assignments with distinct single ones in E; all satisfy every clause by minimality, while their majority has zeros on E. Thus exact for all pins, not merely the all-zero branch. For S_m, K must hit each disjoint block, and one pin per block suffices; optimum m. The 2^m exhaustive branch count is not a lower bound on adaptive or compositional decision. Empty/universal monotone relations handled by empty clause/no clauses.

### G98 — compositional bypass, indexed weighted transport, and exact unpaid endpoint

The same S_m has a linear-size AND of local unions: (x_i1) OR (NOT x_i1 AND (x_i2 OR x_i3)); both local alternatives are bijunctive and disjoint. Thus a factored AND/OR representation is linear and a single witness is obtained by setting x_i1=1 for every i. Flat chart blowup and optimal semantic backdoor size cannot be mandatory time charges for arbitrary algorithms, even preserving full support through shared composition. Exact unary-weight acceptance for independent blocks is product_i [product_j(w_ij(0)+w_ij(1))-product_j w_ij(0)]; rejected weight is total minus acceptance. Each block's disjoint chart sum gives the same result without flat expansion. Overlapping covers require Boolean union or overlap correction, not naive signed sum. This example has 7^m accepting states, 8^m-7^m rejected states and nonzero signed modes as determined by weights; keep these semantics, not obligatory materialization. Retain independent (history,tau,k,j,version,original guard,source chart,pin,consumer,ring,precision) and defect witnesses, signed residual and neutral fibre. No implication from exponential flat cover to time lower bound; allowing arbitrary nonlinear coordinate decoders also escapes the original-coordinate projection hypothesis.

| Gate | Deliverable | Status |
|---|---|---|
| G94 | flatBijunctiveCoverLowerBound | proved; scoped to explicit flat union |
| G95 | ternaryBoxCoverEquivalenceAndRate | proved; small minima tested |
| G96 | semanticBackdoorIffDefectTransversal | proved and tested |
| G97 | monotonePrimeClauseBackdoorIff | proved and tested |
| G98 | factoredCoverBypass / weightedResidual | derived, no unrestricted charge |
| N4 | unavoidable cost across all legal sharing, recomputation, nonlinear charts and bypasses | OPEN |
| N5 | universal polynomial SAT failure / unrestricted separation | OPEN |
| N6 | original Clay transport through SATLowerBoundProducer | conditional |

Next endpoint search: do not strengthen flat expansion counts. Seek a decision-specific invariant preserved by costed composition and arbitrary machine simulation, or the direct candidate-failure / observer-collision / resource-closed diagonal OR routes from the existing producers. Any proposed mandatory charge must pass G98 as an anti-control; an observer collision must separate actual SAT from UNSAT, not merely distinguish witness relations. G96 is a source-geometry diagnostic, not an extra Clay prerequisite. No native Agda/Lean kernel or CI execution, no P!=NP claim.

### Local exact regression (dependency-free Python)

Executed locally: all 128 subsets of OR3, 93 majority-closed, all contained in one pair-OR; exact ternary box minima 2,3,5 for m=1,2,3; all 168 monotone 4-bit relations (including constants), 2688 pin-set tests with both prime-clause and defect criteria; all 256 arbitrary 3-bit relations, 2048 pin-set tests with the defect criterion. All passed. Reproducer:

```python
from itertools import product, combinations
from math import ceil
def maj(a,b,c): return (a&b)|(a&c)|(b&c)
def closed(S): return all(maj(*t) in S for t in combinations(S,3))
S=set(range(1,8)); count=0
for mask in range(128):
    A={x for x in S if mask>>(x-1)&1}
    if closed(A):
        count+=1
        assert any(x not in A for x in (1,2,4))
        assert any(all(x & (7^e) for x in A) for e in (1,2,4))
print('OR3 subsets',128,'majority-closed',count)
for m in range(1,4):
    words=list(product(range(3),repeat=m)); full=(1<<len(words))-1
    boxes=[sum(1<<i for i,w in enumerate(words) if all(a!=b for a,b in zip(w,p))) for p in words]
    for k in range(ceil((3/2)**m),len(words)+1):
        found=None
        for inds in combinations(range(len(words)),k):
            union=0
            for j in inds: union |= boxes[j]
            if union==full: found=inds; break
        if found is not None: break
    print('cover',m,k,[words[i] for i in found])
n=4; allx=range(1<<n); total=0; checks=0; defect_checks=0
for mask in range(1<<(1<<n)):
    A={x for x in allx if mask>>x&1}
    if any((x|(1<<i)) not in A for x in A for i in range(n)): continue
    total+=1
    C=[15^x for x in allx if x not in A and all((x|(1<<i)) in A for i in range(n) if not x>>i&1)]
    D={((a^b)|(b^c)) for a,b,c in combinations(A,3) if maj(a,b,c) not in A}
    for K in allx:
        fibres={p:{x for x in A if (x&K)==p} for p in allx if p&K==p}
        actual=all(closed(f) for f in fibres.values())
        assert actual==all((c&~K).bit_count()<=2 for c in C)
        assert actual==all(K&d for d in D)
        checks+=1
print('monotone relations',total,'backdoor tests',checks,'two characterizations each')
for mask in range(256):
    A={x for x in range(8) if mask>>x&1}
    D={((a^b)|(b^c)) for a,b,c in combinations(A,3) if maj(a,b,c) not in A}
    for K in range(8):
        actual=all(closed({x for x in A if x&K==p}) for p in range(8) if p&K==p)
        assert actual==all(K&d for d in D)
        defect_checks+=1
print('general relation backdoor checks',defect_checks)
```


## 35. P0-G99–G104 — geometry-forward: semantic-backdoor hardness and signed candidate-failure compiler (2026-11-24)

Stay on literal Clay P vs NP. Inputs: G94–G98 and user-attached Langlands R144–R149 (reported #1549/#120 437ddf26cef6/4937d741c994), donor only: clause reset, signed ternary intersection, weighted frontier and orbit contraction. Live P0 starting heads 5bfc4a078984/12ec96edf1b6. Reopened master Agda actual owners PNotEqualsNPSATShannonSemanticAuthorityExact (blob d83aaa5b9e3949678a857da7d4e7754165a0917c), PNotEqualsNPDirectSATLowerBoundExact (0838b3252b3ffb91993e4cb47a5d5c06a00e4fe1), PNotEqualsNPResourceBoundedSelfDiagonalExact (37f9e7d26334383cacaf86db15f6f3be07e5ebd9). Reuse #1006 FactorsThrough/self-reduction, #1040 SATDecisionFailure, #1129 standard machine, #1474/#1502 Cook-Levin, #123 JMD lowering with attribution, #1546 sharing and #607/#678 Aristotle BIDI. Shannon semantic authority and explicit self-tableau no-go are existing owners, not new results. Backdoor complexity context: Dilkina, Gomes, Sabharwal, Tradeoffs in the Complexity of Backdoor Detection (CP 2007), https://www.cs.cornell.edu/gomes/pdf/2007_dilkina_cp_tradeoffs.pdf; not attribution of the exact gadget below. No literature novelty claim.

### G99 — known-inhabited switch gadget, exact 3CNF extension

Given original width<=3 CNF F(x), add switch s, r>=1 disjoint triples z_j, and one private y per original clause or triple clause. For every source coordinate v in x,z require (s OR NOT v). For each nonempty clause (a OR b OR c), pad shorter clauses by repeated final literal. Require y iff s AND NOT a via (NOT y OR s), (NOT y OR NOT a), (NOT s OR a OR y), and impose (NOT y OR b OR c). For an empty clause use NOT s and NOT y. Apply the same construction to each OR3 z_j. Every source assignment has exactly one candidate extension y, which satisfies the encoding iff (s=0 and x=z=0) or (s=1 and F(x) and every z_j nonzero). Thus the all-zero full assignment is a known witness and the switched sector is inhabited iff original SAT. Encoding O(n+clauses+r) literal occurrences, polynomial bit length. No existential auxiliary multiplicity ambiguity. All variables remain labelled. With auxiliary weights one, weighted acceptance equals base weight + w_s(1) times original weighted F acceptance times product of weighted OR3 block sums. At unit weights count = 1+7^r #SAT(F), rejected count is full ambient count minus this; nonzero source flag is not inferred from modular/signed cancellation.

### G100 — representation-independent semantic-backdoor gap with known witness

Let beta be the minimum pin set whose every residual fibre of the FULL encoded relation is bijunctive (G96). If F UNSAT the entire relation is the singleton base, beta=0. If F SAT, choose a fixed satisfying x, s=1, and fix all other blocks to one-hot witnesses. Vary one block across its three one-hot assignments with uniquely determined auxiliaries. Their majority has original block 000 and is rejected regardless of auxiliary values. The defect support lies entirely in that block's three bits and private y; supports from distinct blocks are disjoint. Therefore beta>=r. For r=1, recognizing semantic bijunctivity is coNP-hard on 3CNF even with known satisfying assignment, and is in coNP by explicit triple of accepted assignments with rejected majority. Checking a proposed semantic strong backdoor K is likewise coNP-complete (K=empty hardness, certificate triple agrees on K). For any fixed threshold b use r=b+1; deciding beta<=b is coNP-hard even at b=0. This is not ordinary syntactic 2CNF backdoor recognition. For variable b do not claim coNP membership for existential minimum search. Polynomial construction for polynomially bounded r. A uniform exact optimizer or zero-detecting multiplicative approximation would solve SAT; no unconditional superpolynomial lower bound. The switched input itself is trivially SAT, so its ordinary decision does not require discovery of the nontrivial sector. This is a stronger anti-control for mandatory semantic normalization than G98.

### G101 — signed candidate Shannon discrepancy, bidirectional finite authority

Fix original F on n labelled bits. For arbitrary deterministic total Boolean candidate A evaluate A(F,p) on the ordinary formula F conjoined with unit pins for prefix p (or an explicitly costed equivalent encoding); no correctness assumption. Internal residual delta=A(F,p)-OR(A(F,p0),A(F,p1)); leaf delta=A(F,x)-F(x). Correctness at all nodes iff all delta vanish: backward induction from leaves, forward Shannon law. A wrong node with zero local delta has at least one wrong child. Therefore every extensional error descends to a nonzero delta; conversely internal nonzero delta contradicts joint correctness of parent and two children, leaf nonzero gives a specific error. A local certificate does not necessarily identify WHICH formula is wrong. Descent by arbitrary wrong-child selection is an existence proof, not an algorithm using unknown SAT truth. However from a known false-negative witness follow that witness path; either a negative-to-positive transition gives local mismatch or leaf delta=-1. From a known false-positive root follow a candidate-accepting child when possible; both children rejecting gives delta=+1, or a fully assigned rejected leaf has delta=+1. These targeted procedures need O(n) candidate evaluations and original leaf evaluation; the prior knowledge of an error is not free. Distinguish locally consistent neutral state from globally correct state.

### G102 — polynomial bounded-domain failure formula, no semantic oracle

Canonical fixed-size clause selector t over all non-tautological clauses of width<=3 (including empty if desired), O(n^3) bits, and prefix pins encoded by depth k and n bits with unused suffix zero. Use legal state guard 0<=k<=n and canonical suffix. Every ordinary 3CNF can be normalized into this domain with polynomial cost; reconstruct standard explicit clauses and add unit pins when invoking the candidate. At each internal state simulate the same clocked A on the parent and two child inputs; at leaves evaluate F directly and simulate A once. For each fixed deterministic polynomial-time A with explicit polynomial clock, a uniform polynomial-size Boolean circuit computes the predicate B=valid AND [delta!=0]. Its size and generation time polynomial in n (exponent may depend on A and machine simulation); no SAT oracle. Introduce gate equivalences of width<=3 (NOT, AND, OR, XOR) and assert B. For each legal source triple (t,p,k) the deterministic gate extension is unique. Result Q_A,n satisfies SAT(Q_A,n) iff A fails on at least one canonical formula/prefix in the finite domain. This is a symbolic compiler theorem; the local regression tests gate encoding and bounded table instances, not a universal machine-to-circuit implementation. For arbitrary syntax-dependent candidates this only characterizes errors on the covered canonical inputs, not all possible encodings. Coverage is enough for the endpoint: an A correct on all canonical roots would decide all ordinary 3SAT after polynomial normalization. Conversely if P=NP there is a polynomial A correct on every root and restriction. Thus under standard fixed-machine coverage, P!=NP iff for every clocked polynomial A there exists n with SAT(Q_A,n). Do not confuse easy construction of Q with proving its satisfiability.

### G103 — signed failure sector, mixed interface and exact endpoint boundary

Write u=A(parent),v=A(left),w=A(right). delta=u-(v+w-v*w). Positive bit dplus=u AND NOT v AND NOT w; negative bit dminus=NOT u AND (v OR w). Disjoint; delta=dplus-dminus and delta^2=dplus+dminus. At leaves use direct F(x) in place of child OR. For any weights on legal states retain signed residual sum and positive/negative counts separately. At integer unit weights Z_bad=sum delta^2, SAT(Q) iff Z_bad>0. Signed sum can cancel; computing either full count is not required for decision. For mixed region composition, on a shared boundary b with disjoint internal variable sets use existential support messages E_i(b)=exists internal witness and combine by OR_b AND_i E_i(b). Weighted counterpart uses sum_b product_i W_i(b) times shared boundary weight exactly once. This is exact with original boundary labels and costs of messages/decoders charged; signed W_i=0 does not imply E_i=0. Each local chart may use rank-one, affine, orbit or signed intersection geometry only if exact on its boundary. This is an upper-bound/semantic gluing law, no global mandatory interface materialization. Keep independent (history,tau,k_chart,restriction depth,version,original clause/guard,ring,precision,consumer), original candidate identifier and clock, and positive/negative/neutral sectors. The known zero-mode anchor s=0 in G99 cannot be substituted for the switched existence consumer.

### G104 — reverse endpoint, no diagonal cost escape

The genuine remaining target is universal nonemptiness of Q_A,n, or an alternative direct lower bound. The compiled local defect verifier proves a finite obstruction can be checked cheaply even when a particular false-positive formula lacks a known short UNSAT certificate. It does NOT guarantee any nonzero defect. Evaluating A on Q_A,n is not a contradiction: Q's length is polynomial in the original bounded-domain size, potentially larger than that bound, and A is not forced to misclassify Q even if a defect exists. Reuse resource-closure no-go for self-tableau and never infer same-object diagonal closure from ordinary Cook-Levin. To attach the existing SATDecisionFailure producer, a local triple gives a contradiction to simultaneous correctness; identifying a specific failing member constructively may need a semantic witness/UNSAT proof. In classical logic it gives existence of a failing member. No Agda/Lean kernel verification and no endpoint closure claimed.

### Exact local regression

Executed local Python integer enumeration with Random(369) plus SymPy exact symbolic residual. 120 random F (n=1..4, 30 per n, r=1 or 2, random width<=3 including empty clauses); 64,800 deterministic extension truth comparisons, 4,800 exhaustive auxiliary uniqueness comparisons on first three trials per n, 86 block majority defect witnesses with disjoint support checks, 120 weighted source contractions. 101 candidate tables on all 256 two-variable width<=2 clause masks (8 possible nonempty clauses) and all seven prefix nodes: 180,992 local-node checks and 3,520 wrong-node descent paths; first table correct, other tables independently flip each correct bit with probability .02. All passed. SymPy signed discrepancy truth table 8/8; explicit OR/XOR Tseitin gate with output pinned to one 8/8 unique-extension checks. Rechecked G94 majority-closed count 93. These are finite regressions, not asymptotic evidence or machine coverage. Standalone reproducer recorded separately if available; no CI.

| Gate | Deliverable | Status |
|---|---|---|
| G99 | knownInhabitedSwitch3CNF / exact unique extension | derived and tested |
| G100 | semanticBackdoorGap / coNP-complete recognition | derived and tested gadget |
| G101 | candidateShannonDefectIffBoundedFailure | derived and tested |
| G102 | boundedCandidateFailure3CNFCompiler | mathematical construction; local gate tests; native machine compiler not implemented |
| G103 | signed defect sectors and mixed-interface support gluing | derived; signed gate tested |
| G104 | universal nonemptiness endpoint and self-size boundary | equivalence derived; universal nonemptiness OPEN |
| N4/N5 | actual unrestricted lower bound / universal polynomial SAT failure | OPEN |
| N6 | original Clay transport | conditional |

Next: work on actual candidate nonemptiness or costed universal lower bound, not another mandatory semantic expansion. Attach G101/G102 to existing Shannon authority and #1040 only with exact coverage and failure witness semantics; preserve #1129 machine bit-cost accounting and existing resource-closure boundaries. No other programme edits.


## 36. P0-G105–G109 — geometry-forward: sound policy normalization, constructive wrong-turn defects and refinement transport (2026-11-24)

Stay on P vs NP. Inputs: user G99–G104, Langlands R150–R156 (joint interface and independent support donor only), COMP5u #1546 at reported 52013742c16e (contract decision instead of arithmetic state), H05-F8 refinement #1547 at reported 9b601db (signed transport difference, separate time/refinement). These donor reports are not claims of fresh native verification. Live P0 starting heads d5605aacb063 / b16546eaefb81. Reuse actual owners reopened in section 35: PNotEqualsNPSATShannonSemanticAuthorityExact, PNotEqualsNPDirectSATLowerBoundExact, PNotEqualsNPResourceBoundedSelfDiagonalExact; existing SATDecisionToWitnessSelfReductionExact, BooleanFormulaSATSelfReductionExact, #1006 FactorsThrough, #1129 costed machine, #1474/#1502 Cook-Levin, #123 JMD lowering with attribution and #1546 sharing. Standard search-to-decision is not new; the following one-sided local discrepancy/repair ledger is the current endpoint-facing construction. No literature novelty claim.

### G105 — polynomial sound routing normalization

Use the original indexed input (F,p), with F an explicit width<=3 CNF, original labelled variable count n, p a legal prefix. On any internal prefix q choose c_A(F,q)=0 iff A(F conjoined with unit pins q0)=1, else 1. For fixed deterministic clocked polynomial A, follow choices until a full assignment g_A(F,p) extending p, and let S_A(F,p)=F(g_A(F,p)). Do not query A for parent acceptance. At most n candidate calls on polynomially sized ordinary formulas plus polynomial source reconstruction and evaluation; each call uses same explicit clock. At leaves evaluate F directly. S is sound unconditionally, with genuine witness g whenever S=1. If A is globally correct, any inhabited prefix retains an inhabited child: if zero child is inhabited A says yes, else the one child must be inhabited. Hence S is complete on all legal pairs. Conversely any polynomial sound complete policy on original F at empty prefix gives polynomial 3SAT decision. More generally arbitrary polynomial bit-routing policy c suffices for this equivalence. Input to S is the labelled pair (F,p), not an unlabelled simplified CNF; the original n and prefix history must be retained. Ordinary SAT and pair SAT are polynomially equivalent via unit pins and empty prefix. This avoids assuming syntax-independent A or equality with an independently rerun solver on a re-encoded pinned formula.

### G106 — one-sided constructive wrong-turn defect

For chosen child pc and sibling p(1-c), g(F,p)=g(F,pc), hence S(p)=S(pc). Let a=S(pc), b=S(sibling). Shannon residual delta=S(p)-OR(a,b)=-(1-a)b. Positive sector identically absent; at fully assigned leaves delta=0 by direct evaluation. A defect is precisely a=0,b=1. The sibling's actual greedy completion is an explicit satisfying assignment extending p, while S(F,p)=0. This is a specific false negative of the normalized pair solver, not an ambiguous triple of failures of original A. The parent witness and actual rejected completion are both polynomially verifiable by rerunning at most two routes. They do not establish that the chosen subtree is UNSAT. Neutral delta=0 with a=b=0 may hide an inhabited fibre. For any fixed F, all internal defects vanish iff S agrees with true SAT on EVERY prefix, by Shannon induction from leaves. If an inhabited p has S(p)=0, some descendant defect exists: follow a satisfying full assignment until a zero-to-one transition, which forces the unchosen child to have value one. With a known missed witness this localization needs only polynomially many route evaluations. A correct root may still have defects at other prefixes; distinguish root correctness from all-pair correctness.

### G107 — exact single-node policy refinement and signed transport

Fix a defective node p of a fixed original F and current policy c. Let c' differ only at p, choosing the sibling. The exact route change for any starting prefix q is: if the old route visits p, it now follows the old successful sibling completion; otherwise the old completion is unchanged. Define I_c(q,p)=1 iff p lies along the old route from q (including q itself). Then S_c'(q)-S_c(q)=I_c(q,p). In original source terms, positive accepted mask is enlarged by the old routed basin, with no loss; rejected mask decreases by the identical indicator. For any signed prefix weights w(q), gain is sum_q I_c(q,p) w(q); at unit weights gain is number of affected prefixes. Weighted gain may cancel but support gain remains. This is an exact finite refinement face with independent candidate version, time of update, original prefix depth and chart index. For general changes the decision difference need not be nonnegative; for multiple edits telescope using the CURRENT policy and its own basin at each step, not an old fixed basin. Coordinate transport must carry original choices, source and weights. Signed rectangular finite difference identity (z-v)-(w-u)=(z-w)-(v-u) is a ledger identity, not proof that arbitrary policy refinement commutes.

### G108 — repair anti-control and precise scope

Bottom-up repairing defective nodes on a finite complete prefix tree yields correct S at all prefixes: once both child outputs equal true satisfiability, choose a successful one if available; if neither is successful there is nothing to repair. No more than one edit per internal node in this specific bottom-up schedule. This does not give polynomial time: traversing the full tree costs exponentially many nodes and storing distinct policy patches can do likewise. Explicit family F(x)=x_n, initial policy always chooses zero. Every depth n-1 prefix is defective (2^(n-1) distinct nodes). Any sequence of single-node policy-bit edits making every prefix correct must change all these choices, since the final bit must be one at every such node. But a single shared rule 'at the last coordinate choose one' repairs all of them with constant-description logic; SAT itself is trivial. Thus even a one-sided constructive defect count or local repair count is not a mandatory cost for unrestricted shared algorithms. No lower-bound claim from patch count.

### G109 — direct one-sided obstruction compiler and unpaid nonemptiness

On the G102 canonical width<=3 clause-selector domain, compile two route computations from p's chosen and unchosen children and their original formula evaluations. Assert a=0,b=1 plus legal prefix/domain. For each fixed clocked polynomial policy, size and generation time polynomial in n by standard deterministic machine-to-circuit and Tseitin equivalences, with unique gate extension for each legal state. Each witness decodes to a specific false negative of S on a labelled pair and an original satisfying assignment. No need for an UNSAT proof or signed cancellation inversion. Conversely an incorrect S on any legal pair forces a defect in that same bounded source tree. Thus P!=NP iff every fixed polynomial bit-routing policy has a nonempty wrong-turn formula at some n, assuming standard machine coverage; if P=NP a correct A produces a policy with no defects, and if a complete policy exists it decides 3SAT at empty prefix. To attach #1040 constructively, transport the pair-language solver via an explicitly costed canonical encoding; do not identify a false negative of S with a known false negative of original A. Uniform nonemptiness remains OPEN, and compiling a policy's own wrong-turn formula does not settle same-object resource closure. A generic machine-to-circuit implementation is not provided by this tranche.

### Exact local acceptance

Committed scripts/check_p0_routing_policy_defect_20261124.py, identical blob fa3d5164afa1ca16aec740bbd7bbc4913689429e in both branches. Actually executed local Python and SymPy: all 128 deterministic full three-bit prefix routing tables crossed with all 256 leaf truth tables (32,768 instances); 229,376 local one-sided identities, 57,344 constructive defect witnesses, 860,160 single-repair face checks including 90,112 positive changes, exact global no-defect iff all-prefix correctness checked on all instances; two exact symbolic identities. All passed. These are exhaustive finite tests on an unrestricted three-bit truth table carrier, not benchmark of real SAT machine compilation or evidence of an asymptotic separation. No CI or Agda/Lean kernel execution.

| Gate | Deliverable | Status |
|---|---|---|
| G105 | soundRoutingNormalization / polynomial overhead | derived |
| G106 | oneSidedShannonDefect / explicit false-negative witness | derived and tested |
| G107 | exactSinglePolicyRepairFace / signed basin gain | derived and tested |
| G108 | exponential local edit vs shared repair anti-control | derived |
| G109 | oneSidedWrongTurnCompiler / universal nonemptiness equivalence | mathematical construction; implementation and nonemptiness open |
| N4/N5 | unavoidable unrestricted cost / every polynomial policy fails | OPEN |
| N6 | original Clay transport | conditional |

Next endpoint attack: force a wrong turn in every polynomial policy on some original formula, permitting arbitrary preprocessing, nonlinear representations, global rule patches, recomputation and sharing. A proof may use a different lower-bound route; do not make local patch enumeration compulsory. Preserve original source, zero mode, inhabited neutral fibre, signed residual, independent history/time/refinement and restriction depth. No other programme edits or Clay solvedness claim.


## 37. P0-G110–G114 — original Shannon owners, logarithmic failure localization and endpoint audit cost (2026-11-24)

Stay on literal Clay P vs NP. User requests reuse of repository Shannon and no chat attachments. Inputs G105–G109, attached Langlands R157–R163 (consumer-directed quotient, signed refinement donor only), prior COMP5u and H05 F8. Starting heads 29f1690dc541 / 287e2eaac855. Reopened the actual BooleanFormulaSATSelfReductionExact, SATDecisionToWitnessSelfReductionExact, PNotEqualsNPCookShannonSemanticAuthorityExact (d01d395a1aee), PNotEqualsNPSelfDiagonalRestrictionFamilyExact, PNotEqualsNPSelfDiagonalFutureCongruenceExact, PNotEqualsNPQ1GradedShannonRepairGeneratorExact (cd7fb563f803), PNotEqualsNPQ1KeyOnlyTransitionExact (e875f8e789cb), PNotEqualsNPShannonExactSharingNoGoExact (7d16358ad0d9), PNotEqualsNPNonOracularShannonTerminalProgressExact (e9c66bff972e). Exact-syntax sharing no-go does not prohibit semantic sharing; key-only transition does not pay generating/storing the keys; structural progress must not become mandatory all-branch materialization. Existing #1006 FactorsThrough, #1040 failure, #1129 standard cost, #1474/#1502 Cook-Levin, #1546 sharing, #123 JMD lowering with attribution remain authoritative.

### G110 — opposite-endpoint localization without monotonicity

Given original F, rejected prefix p and a genuine satisfying assignment x extending p, let m=n-|p|>0 and a_j=S_c(F,x restricted to |p|+j), 0<=j<=m. a_0=0, a_m=1. Maintain l<r with a_l=0,a_r=1; at midpoint set l=mid if a_mid=0, otherwise r=mid. After at most ceil(log2 m) intermediate route-score queries r=l+1. This argument does not assume monotonicity. The successful child is necessarily unchosen because parent score equals the chosen child's score. Re-run its route to decode the genuine satisfying assignment (or retain its cached completion). Known endpoints and supplied witness are premises, not free discovery. At most O(m log m) policy calls for midpoint route evaluations, plus O(m) to recover a completion and validate endpoints, source evaluation and costed pin construction; compare to O(m^2) for naive full witness-prefix scan. No claim of faster actual bit runtime without accounting for policy and encoding costs. Query count sharp for general bit sequences with opposite endpoints: threshold sequences have m possible unique transitions and a binary decision tree must distinguish them. Not a SAT time lower bound.

### G111 — exact decision-only descendant audit and hidden neutral sector

At any prefix p define B(q)=(1-S(q)) OR(S(q0),S(q1)) for internal q; product means Boolean AND. Let D(p)=OR over all internal descendants q extending p including p of B(q). Then SAT(F|p)=S(p) OR D(p). Forward: if S(p)=0 and p is inhabited, G110 localizes a defect along a witness; if S(p)=1 there is a routed witness. Backward: S(p)=1 gives a witness; any descendant defect supplies a child completion which lifts through original prefix provenance to p. This is a consumer-level equality, not a computational entitlement to enumerate D. The signed decision error S(p)-SAT(F|p)=-(1-S(p))D(p). D(p)=1 can coexist with S(p)=1; an accepted root does not certify all-prefix correctness. Neutral local B(p)=0 with S(p)=0 can hide a nonempty fibre. Concrete two-variable collision under all-zero routing: F=x1 AND x2 and G=false (same score zero, both immediate child scores zero, hence B(root)=0); only F has deeper defect and inhabited support. A quotient of current score and even immediate branch scores therefore need not preserve future decisions. Do not confuse hidden-neutral with empty or a numerical zero.

### G112 — audit cost already contains original SAT

For the fixed constant-zero routing policy c0, reduce arbitrary width<=3 CNF F(x) to G(s,x)=s AND F(x), adjoining one unit clause with switch ordered first. G's root score is always zero, including satisfiable inputs. By G111, G has a wrong-turn somewhere iff F is SAT. Any wrong-turn witness decodes a satisfying original x by completing the successful child and removing s. Testing existence of a defect belongs to NP for a fixed polynomial policy (guess prefix, evaluate both child routes); thus the fixed-policy defect-existence problem is NP-complete, even with known rejected root, and certifying defect-free on a supplied formula is coNP-complete. A generic polynomial auditor that returns either a wrong-turn witness or a correct declaration of no defect would decide SAT already for c0. This is not a lower bound for arbitrary SAT policies: the all-zero policy itself is trivial, and the theorem does not force a defect in an arbitrary polynomial policy. Witness-guided localization is distinct from unguided discovery.

### G113 — actual native Shannon carrier weld (source candidate)

Agda branch adds DASHI/Mathematics/Complexity/PNotEqualsNPShannonRoutingDefectExact.agda, blob 65a0a8b02871fc49ad3f3474af10e5e55fbd42a2 at initial commit 1beedeb1e6df. It imports original indexed SAT, restriction derivation and future terminal observer. Policy consumes the original root-labelled restriction derivation, not a truth table or collapsed syntax. score follows one child, scoreSound reconstructs a satisfying assignment using existing liftFalse/liftTrue, Boundary retains actual current formula, remaining arity, derivation and successful action, boundaryWitness / boundaryRootWitness lift through original provenance, locate structurally descends using existing satisfiableSplits, defectFreeComplete targets completeness from absence of Boundary. This is a native proof-source candidate, NOT kernel-checked. Structural locate is distinct from G110 logarithmic-query algorithm. No Agda/Lean executables available locally; no new native Lean module in this cut. Lean roadmap records the shared math/acceptance and Agda owner for later port. Standard fixed-machine cost certification and direct SATDecisionFailure bridge remain separate; do not attach an unproved universal defect assumption as solved. No postulated endpoint.

### G114 — exact local regression and endpoint boundary

Actual local Python/SymPy execution of scripts/check_p0_shannon_endpoint_localization_20261124.py: all 65,535 opposite-endpoint bit sequences for lengths m=1..16, max 4 midpoint queries; 139,264 missed-witness localization cases across all 128 three-bit policies and all 256 truth tables; 491,520 descendant audit identities; 20,352 hidden-neutral occurrences; 256 fixed-policy switch-gadget controls; 1 symbolic OR residual identity. All assertions passed. These are finite tests, not universal asymptotic evidence. No CI, native formal kernel, generic machine compiler or runtime benchmark. Independently retain history, chronological update, policy version, chart/refinement index, original prefix/restriction depth, source identity, consumer, ring and precision. Preserve support vs signed zero; no files attached in chat.

| Gate | Deliverable | Status |
|---|---|---|
| G110 | oppositeEndpointLocalization / logarithmic score queries | derived and tested |
| G111 | descendantDefectAudit / exact hidden-neutral control | derived and tested |
| G112 | fixed-policy audit NP/coNP completeness | derived; finite switch controls passed |
| G113 | original Shannon derivation native weld | Agda source written, kernel unverified; Lean port open |
| G114 | exact regression / independent cost ledger | local tests passed |
| N4/N5 | unconditional lower bound / universal polynomial policy failure | OPEN |
| N6 | original Clay transport | conditional |

Next maximum cut: force nonemptiness of a polynomial policy's wrong-turn formula without a supplied witness, or establish an unrestricted cost obstruction permitting arbitrary preprocessing, source re-access, nonlinear quotient, shared patch and recomputation. G112 prevents treating a general audit as free, but cannot be used circularly as a universal failure proof. A formal kernel check is useful for G113, not a new Clay prerequisite. No other programme edits.

## 2026-11-24 — G115–G120: P0 Langlands-assisted witness extraction and shared signed residual

Priority correction (explicit user direction): literal Clay P vs NP is P0; Langlands is a supporting mathematical route, not a competing endpoint. Active P0 Agda #1548 at 270b846169f1 and Lean #119 at 56224dd976d7; live donor Langlands Agda #1549 at 650a1c218eb2 and Lean #120 at 41ee9b63851e (R164–169). Keep the original G113 Shannon carrier and G110–114 audit authorities; no duplication or donor branch edits. R78 unique-extension compiler, R85 rank-two weighted probe, R158–159 regional frontier and R165 pin-conditioned residual are direct donors. COMP5u consumer-only contraction and F8 signed refinement remain conceptual donors.

### G115 — nonzero rank-two probe to original witness
For original F on n labelled Boolean guards, P_F(z)=sum_x F(x) prod_i z_i^x_i in characteristic two; distinct original assignments give distinct monomials, so P_F is identically zero iff F is UNSAT. For a prefix p, P_p restricts the sum to original assignments extending p, retaining ALL original weights including pinned coordinates. A_p is the corresponding unrestricted cylinder baseline, D_p=3A_p-4P_p in the R85 unramified coefficient ring at mod8 precision, with coefficientwise division of (3A_p-D_p) mod8 by 4 giving P_p mod2. This is the R85 scalar on the subcarrier (or multiply the reduced source's response by its known prefix monomial); do not confuse with a full fixed-carrier selector whose baseline stays A_empty. A_p=A_p0+A_p1, P_p=P_p0+P_p1, D_p=D_p0+D_p1 in this subcarrier convention. Equivalently a full fixed-carrier probe for F AND prefix pins uses A_empty and its known baseline.
If P_p mod2 is nonzero, query only P_p0 at the same z; choose p0 if nonzero, otherwise p1 with inferred nonzero value P_p-P_p0. At a leaf this value equals F(x) z^x, so nonzero gives an original satisfying x. At most n-|p| conditional scalar queries after a successful sample, plus polynomial original source evaluation and arithmetic. No fresh randomness at each branch; no exact count, entire polynomial, or independent sibling query. Unique-extension compiler auxiliaries are unit-weight and recoverable by the original gate graph (R164); not additional witness bits. The same reasoning applies at arbitrary original pinned source fibres. This is a conditional search-to-evaluation reduction, not a polynomial general scalar evaluation algorithm.

### G116 — one-sided randomized endpoint and exact cost boundary
For uniformly independently sampled z_i in F_Q^* (Q=2^d), nonzero P_F has total degree <=n, so Schwartz–Zippel gives Pr[P_F(z)=0]<=n/(Q-1). Select d with Q-1>=4n, so a SAT source yields a nonzero sample with probability >=3/4. UNSAT always gives zero. Independent initial samples amplify false-negative probability; no resampling needed inside extraction. Each field sample/lift and ring arithmetic has polynomial bit cost for d=O(log n) when field representation is supplied or constructed in polynomial time (brute-force monic degree-d irreducible enumeration is polynomial in n at this degree). A uniform polynomial-time exact evaluation of arbitrary R85 scalar queries would imply SAT in RP, hence RP=NP; this does not imply deterministic P=NP. A polynomial-size uniformly constructible deterministic hitting set PLUS paid polynomial evaluation would imply P=NP. Neither is established. Even assuming P=NP does not by itself give a known polynomial algorithm for these parity/weighted counting queries. A zero sample is inconclusive: e.g. F=true on one guard at z=1 has P=1+1=0 in characteristic two although support is inhabited; the empty relation also gives zero. Do not use ring zero as emptiness. Keep exact support separately where available.

### G117 — missed-witness extraction and constructive defect localization
For any fixed clocked polynomial policy c, score S_c(F,p) evaluates its actual routed terminal. If root score is 0 and a sample is nonzero, G115 yields an original satisfying witness x. G110 opposite-endpoint localization on a_j=S_c(F,x|j) then finds adjacent 0->1 with <=ceil(log2 n) intermediate route-score queries, no monotonicity assumption; this child is necessarily unchosen and its completion is a genuine witness. Thus a successful initial scalar sample plus <=n child scalar calls and <=ceil(log2 n) intermediate route-score calls (plus endpoint/certificate checks) produces a constructive G106 defect. Each route-score call costs up to n policy calls plus source evaluation. A correct candidate's accepted input needs no audit for the decision endpoint; accepted root does not prove all-prefix defect freedom. For rejected inputs the route is a conditional failure finder, not a theorem that any supplied polynomial policy fails on some input.

### G118 — exact source-labelled signed path telescope (F8 donor)
At every leaf x set a_j=S_c(F,x|j). Then F(x)-S_c(F,empty)=sum_j (a_(j+1)-a_j). With arbitrary commutative ring unary weights, sum over original x to obtain
 P_F-S_c(F,empty) A = sum_{edges p->pb} (S_c(F,pb)-S_c(F,p)) W(pb),
 W(pb)=sum_{x extends pb} w(x)=prod_{i pinned} w_i(x_i) prod_{i free}(w_i(0)+w_i(1)).
Chosen edges contribute zero. An unchosen 0->1 score edge is a constructive G106 defect; unchosen 1->0 edges are negative transport changes, not unsound positive decision errors. Keep both signed transition sectors; they can cancel. Multiply by -4 for the corresponding rank-two signed response difference relative to the constant root-score model. This is a mathematical identity, not a claim that summing all edges is efficient. Source history, prefix labels and chronological/policy/chart indices remain independent.

### G119 — first successful prefix partition, no compulsory per-defect charge
For a rejected root and any accepting original x, define j(x)=min{j:S_c(F,x|j)=1}; exists since terminal is accepted. The first-successful prefix q=x|j has a rejected parent and successful unchosen child, hence a constructive defect. All such first-successful prefixes form an antichain: no one can extend another since all strict ancestors have zero score. Their cylinders partition the accepted source (intersect each cylinder with F); they also may contain rejected leaves, so do not replace F by the prefix cylinder. Therefore P_F=sum_{q first-successful} P_q, with original weights and disjoint source support. G110 bisection finds SOME rise, not necessarily first; do not identify the two. First-rise witness label is computable with <=n score queries given x, and can be deterministic auxiliary provenance in a unique-extension graph. The source-to-labelled-leaf bijection preserves coefficients without duplicate counting, but discovery/aggregation of all first-rise prefixes can be exponential. G108 shared rule bypass remains authoritative; no charging each prefix as compulsory work. The exact remaining endpoint is still forall polynomial c exists rejected inhabited original F (equiv G109 wrong-turn somewhere on formula/prefix carrier). This tranche contracts conditional failure recovery; it does not force nonemptiness.

### G120 — actual local execution and reproducibility
Standalone identical repository script scripts/check_p0_weil_witness_residual_20261124.js, executed in JS tool with exact small integer ring coefficients and BigInt clause masks, seed 115 xorshift32. Coefficient ring (Z/8)[X]/(X^5+X^2+1); 31 nonzero Teich lifts via 32nd powers, residue and 31st root checked. 180 random width<=3 CNF sources (including empty clause/conjunction), n<=7, four pseudorandom sampled weight vectors per source; 1264 prefix ring/Weil additive comparisons against exhaustive source or two-child split; 720 initial probes; 288 extracted original witnesses using 1086 child scalar queries; 168 rejected test-policy roots localized using 341 midpoint route-score queries; 24 inhabited zero initial samples, plus explicit true/empty zero collision. Routing test uses a pseudorandom 7-bit policy mask with JavaScript's shift index taken modulo 32 (bits 7..31 zero; repeated mask above index 31), not all policies for n>3. Exhaustive separate n=3 suite: all 32768 policy/truth-table pairs, 262144 signed path telescope comparisons, 57344 accepting-leaf first-rise labels, 16384 rejected-root antichain/mass controls with signed integer leaf weights; weighted aggregate identity checked each pair. Mod8 ring frontier evaluation uses actual original CNF clause masks, no full coefficient polynomial; exhaustive reference only tests. No generic polynomial-time evaluation bound, actual local-factor oracle, native proof kernel, CI, Node subprocess or performance benchmark. No files provided in chat.
 
| Gate | Deliverable | Status |
|---|---|---|
| G115 | one successful Weil sample -> original witness via one child query per bit | derived and tested |
| G116 | one-sided randomized detection and cost boundary | derived; scalar evaluation open in general |
| G117 | constructive policy defect from successful scalar sample | derived and tested |
| G118 | source-labelled signed path telescope | derived and tested |
| G119 | disjoint first-rise fibres with shared repair allowed | derived and tested |
| G120 | repository-only exact regression | executed and committed |
| N4 | unconditional resource obstruction permitting arbitrary sharing | OPEN |
| N5 | universal polynomial policy failure | OPEN |
| N6 | original Clay endpoint transport | conditional |
Next P0 maximum cut: use R170 backward consumer and R165 pin-conditioned scalar update as donors to derive costed scalar evaluation certificates directly on the original defect/witness source, not mandatory full packets or defect enumeration. Pursue universal policy failure separately, with resource-closed diagonal and no circular assumption of a general auditor. Deterministic hitting-set and evaluation obligations must be separated from RP route; don't mistake an oracle reduction for either P=NP or P!=NP. Keep signed residual, zero mode, inhabited neutral, original labels, policy/source history, restriction depth, chart refinement, time/Frobenius and precision independent. No other branch changes.


Cross-tranche P0 reconciliation: concurrent source-revision work is now G121–G125; preserve both sections. A G115 recovered original witness on a rejected root supplies the premise of either G110 fixed-policy prefix localization or G122 ordinary-formula anchored unit-gain bisection, with actual unit-pin re-encoding and candidate calls charged. Neither route obtains the initial nonzero sample for free or forces universal failure. Literal P vs NP remains controlling P0, Langlands supports it; this explicit priority supersedes earlier portfolio preferences.

## 39. P0-G121–G125 — source revision gain, unique-extension transport and bounded repair closure (2026-11-24)

Stay on literal Clay P vs NP. User supplied G110–G114 and Langlands R164–R169 (reported heads 650a1c218eb2 / 41ee9b63851e; donor report only, not independently reproduced). Source revision, deterministic extension and direct signed residual are the donors; no Langlands branch edits. Starting live P0 heads 270b846169f1 / 56224dd976d7. Concurrent G115–G120 Langlands-assisted witness-extraction section retained intact; this source-revision tranche is renumbered G121–G125 to avoid duplicate gate IDs. Reuse section 37's actual Shannon owners and G113 source candidate, #1006 FactorsThrough, #1040 direct failure, #1129 costed machine, #1474/#1502 Cook-Levin, #1546 sharing and #123 JMD lowering with attribution. Do not conflate source revision with fixed-policy child transport. No novelty claim for monotonicity of satisfiability or SAT self-reduction.

### G121 — signed direct source/refinement residual

For any deterministic total polynomial assignment producer W on ordinary explicitly labelled CNFs, set S(F)=F(W(F)); the producer may be arbitrarily wrong, but S is sound by evaluation. For F'=F AND Q on the same original coordinates, x=W(F), y=W(F'), the exact identity is S(F')-S(F)=-L+R with L=F(x)(1-Q(x)), R=F(y)Q(y)-F(x)Q(x). L measures loss of the actual old completion, not loss of all witnesses; R measures rerouting relative to evaluating that completion on the revised source. A 0->1 gain gives an explicit missed witness y for F. If F(x)Q(x)=1 and S(F')=0, x is an explicit missed witness for F'. The remaining 1->0 case with L=1 does not establish UNSAT. Both accepting may have different witnesses without any decision error. No policy invariance, count, or complete intermediate packet required. The endpoint scalar can be evaluated by two W calls and original evaluations. Keep original source revision, original labels, both actual witnesses, chronological update, chart/refinement, policy version, precision, consumer, signed residual and support distinct.

### G122 — ordinary formula unit-gain criterion

Use a fixed declared finite variable universe with polynomial bit-cost encoding (or canonical densely numbered labels; no exponentially large unused declared universe). W is total, polynomial, always returns a full assignment; if explicit unit clauses pin all original variables consistently, override W with that assignment and directly evaluate. Inconsistent full pins cannot be satisfiable; zero-variable inputs evaluated directly. A sound and complete ordinary solver yields such W by the existing Shannon search-to-decision producer; arbitrary W requires no correct oracle. If S rejects an inhabited F with witness x, append the unit literals of x for all unpinned original variables. The fully pinned final formula has score 1 by anchor. A 0->1 adjacent source revision exists, even for a syntax-sensitive W; no assumption about consistency of internal route histories. Conversely any gain G_W(F,l)=(1-S(F))S(F AND l)=1 is a specific false negative on F, with W(F AND l) as witness. Thus for anchored W, correctness on every formula iff no unit gain anywhere. P!=NP iff every clocked polynomial anchored W has some unit gain on ordinary 3CNF (including unit clauses). A polynomial W with no gain decides SAT; if P=NP existing self-reduction constructs a complete W. The candidate normalized from a possibly incorrect A uses at most polynomially many calls, but the gain is a failure of the normalized decision candidate, not automatically of the original A at that formula. Given x and a rejected F, G110 opposite-endpoint bisection locates an adjacent gain with ceil(log2 m) intermediate score calls, m remaining units; actual query lengths and W calls are charged. This is conditional localization, not free discovery of x. G102's deterministic circuit-to-3CNF compiler can encode the two W calls and verification on bounded source inputs, with unique deterministic gate extensions; generic machine implementation remains open. No need for the full restriction-tree carrier to state this equivalent endpoint.

### G123 — unique-extension source transport, not arbitrary auxiliary elimination

Suppose a supplied polynomial deterministic compiler maps F(x) to E_F(x,a) with exactly one extension a_F(x) for every satisfying x and no extension otherwise; it includes the acceptance flag constraint, unlike a total truth graph with flag unasserted. Assume a_F computable in polynomial time on accepting x and original labels/projector retained. For an original unit l, the fibre E_F AND l has precisely the same satisfying projection as F AND l, and extends a satisfying x using the original gate graph. If instead recompiling F AND l changes auxiliary coordinates, transport through the original x, then rerun the new gate graph; never identify auxiliary labels across revisions. A solver on compiled formulas projects genuine witnesses to the original source; fully pinned source anchor can be supplied by direct F evaluation and deterministic lift, not by the compiled candidate alone. A solver on original F can solve this compiler-image family by lift when source provenance is available. Thus the unit-gain certificate is polynomially transported with original source coordinates under either compiled revision convention; solver outputs and gain locations can differ across encodings. This is a conditional mathematical transport, not an implementation of the Langlands compiler or a claim for arbitrary added auxiliary constraints. For signed weights, source marginal weights count once; arbitrary auxiliary weights must be explicitly composed, and modular cancellation is not empty support. Existing G99/G102 unique-extension producers remain the relevant SAT-side owners.

### G124 — finite-radius repair closure and shared-bypass control

For fixed original F and a legal partial pin assignment p in {-1,0,1}^n (-1 unpinned), evaluate S(p) on the actual ordinary pinned formula. Define C_0(p)=S(p), C_(k+1)(p)=C_k(p) OR OR_{one new pin q extends p} C_k(q). Exactly C_k(p)=OR_{q extends p, at most k new pins} S(q), by induction. Preserve witnesses by lifting accepted revised assignments; C_k is sound and monotone in radius. For fixed k, explicit enumeration needs at most sum_{j<=k} binom(n-|p|,j) 2^j candidate calls, polynomial for fixed k, but not for k growing with n. Anchors imply C_(n-|p|)(p)=SAT(F|p). A gain-free score is already a fixed point. An abstract all-partial-reject score with full-pin acceptance is an extended failure-return solver control; F=true cannot exhibit this behavior with a total full-assignment producer. A strict total-producer anti-control on n>=1 uses F=(x_1 AND ... AND x_n) and, whenever any variable unpinned, choose zero on one such variable and fill others consistently; fully pinned assignments evaluated directly. At root all accepting revisions must pin every variable to one, so exact closure requires n iterations, despite trivial original SAT. This rules out treating closure depth or number of refinements as compulsory unrestricted computation. The finite test includes the abstract all-partial-reject score control; the strict total-producer variant is proved by inspection, not separately executed. A globally shared repair can bypass the entire closure. Do not infer universal lower bound from enumeration.

### G125 — exact local regression, cost ledger and unpaid endpoint

Actual local execution Python/SymPy, script scripts/check_p0_source_revision_gain_20261124.py, matching local git hash-object and both remote blobs fffc03951d1ced0622079c20bb8fae08fac19add. 5,120 instances: all 1,024 combinations of 2-bit Boolean truth tables and independently selected valid completions at every partial-pin state; plus 4,096 seeded 3-bit table/completion instances (16 per truth table). 119,808 sound/anchor states, 233,472 single-pin signed edges, 37,836 constructive source gains, 8,662 surviving-witness losses, 26,564 known-witness bisections, 1,461 hidden neutral states (inhabited rejection with no immediate gain), 119,808 full closure comparisons, 269 gain-free complete instances, 1/1 exact symbolic identity and 8/8 abstract closure-depth controls. All assertions passed. The finite carrier allows independently chosen completions at each pin state, hence not just one fixed prefix policy; it is not an actual arbitrary-machine compiler or a performance benchmark. No native Agda/Lean kernel or CI execution; G113 remains source-only and Lean port open. No chat files.

| Gate | Deliverable | Status |
|---|---|---|
| G121 | direct signed source-loss/reroute decomposition | derived and tested on unit revisions |
| G122 | anchored unit-gain iff ordinary SAT incompleteness; logarithmic localization given witness | derived and tested |
| G123 | unique-extension source/compiled gain certificate transport | conditional mathematical derivation |
| G124 | exact radius closure with shared-bypass anti-control | derived and tested (abstract score control) |
| G125 | repository-only exact regression and endpoint accounting | passed |
| N4/N5 | unrestricted lower bound / universal polynomial candidate failure | OPEN |
| N6 | literal Clay endpoint transport | conditional |

Next maximum cut: force a unit-gain (or G109 wrong-turn) against arbitrary anchored polynomial candidates without first supplying a missed witness. Investigate source-sensitive candidate revision, not compulsory expansion of the pin lattice. Candidate calls, deterministic extension, re-encoding, source provenance, shared preprocessing, nonlinear representations and arbitrary recomputation must remain costed. Neither a signed residual nor a large repair radius forces a universal nonempty obstruction. No Clay solvedness claim or other programme changes.


## 40. P0-G126–G130 — delayed constructive gains and the clocked counterexample-search boundary (2026-11-24)

Stay on literal Clay P vs NP. User attachment is previous G121–G125 source revision tranche (provisional headings G115 onward superseded by reconciled IDs). Starting live heads d73d306c123f / 0ac8ed9e8a0b. Preserve concurrent G115–G120 Langlands-assisted section. Reopened actual Agda owners PNotEqualsNPKleeneSpecializationFixedPointExact (blob 8ac31231804cfea9358d87b1dafa610de77d2b31), PNotEqualsNPResourceBoundedSelfDiagonalExact (37f9e7d26334383cacaf86db15f6f3be07e5ebd9), PNotEqualsNPSelfDiagonalClockTagNoGoExact (fd0fffcf674b4ce2346ceec825483fec268b39ae). Use G122 unit gain, G110 localization, G113 original Shannon source candidate, #1040 direct failure, #1129 concrete costed machine, #1474/#1502 Cook-Levin, #1006 FactorsThrough, #1546 sharing, #123 JMD lowering with attribution. Classical halting undecidability is the standard external theorem used below; no new claim about the theorem itself. No reliance on an unproved same-object diagonal or a new SAT oracle.

### G126 — delayed-gain program compiler without a SAT self-reference assumption

Use a fixed effective ordinary 3CNF encoding with a declared densely labelled variable universe of polynomially bounded size in the input length N; all bit costs include variable labels and pins. Fix a sound verification wrapper S_W(F)=F(W(F)) with W total assignment-producing and the G122 fully pinned evaluation anchor. Conflicting pins are unsatisfiable and cannot generate a false acceptance. Define fallback W_0 as all-zero except explicit unit pins (resolve contradictory pins deterministically); it is polynomial, anchored, but incomplete. For arbitrary no-input deterministic machine M, effectively generate unclocked program W_M: on F, honor the anchor, simulate M for N-1 steps; if it has not halted run exact exhaustive SAT search with a default assignment on UNSAT, otherwise return W_0(F). This is a total program for every M, as every bounded simulation and finite search terminates. If M halts at time T, then every input with N<=T is decided correctly and only finitely many input lengths use exhaustive search; the cost of that finite portion is a constant depending on M. All other inputs cost bounded simulation plus polynomial fallback and verification. Thus W_M is polynomial-time in the semantic sense when M halts, without a uniformly supplied polynomial bound. No gain can have parent length <=T, since that parent is correct and a gain supplies a real witness for it. A gain does exist: take F_m=(x1 OR x2) AND all (x1 OR xi), 3<=i<=m, with no unit clauses; choose m large enough that both F_m and F_m AND x1 have encoded length >T. Fallback rejects F_m and accepts F_m AND x1. Thus minimum parent-length gain mu(W_M)>T. The witness family is linear in clause count; no need for repeated syntactic padding or exponential assignment output. If M never halts, this construction is complete but may not be polynomial. In the reduction only the halting case must be in the polynomial promise class.

### G127 — unconditional noncomputable obstruction deadlines on unclocked descriptions

Suppose total computable B(e) gives a finite upper bound on mu(W_e) for every incomplete anchored polynomial-time W_e, when e is only an arbitrary unclocked program description. On other descriptions B may have any value but must halt. Compile M to e_M as above, compute B(e_M), then simulate M up to B(e_M) steps. If M ever halts at T, G126 gives T<mu(W_M)<=B(e_M); hence the bounded simulation decides halting, contradiction. This also rules out a total computable bound in description length alone. Any total computable counterexample selector on all raw descriptions that returns a valid gain on every incomplete polynomial-time candidate would induce such a bound (length of returned parent, or zero on malformed output). This is an unconditional metacomputability obstruction, NOT a SAT decision time lower bound. A partial finder that terminates on incomplete polynomial candidates can still exist. Explicitly clocked descriptions are different: the G126 program generator does not produce a uniform clock certificate, because its finite exceptional exhaustive-search constant depends on the uncomputed T. Do not infer N5 from this theorem or demand totality on arbitrary unclocked inputs.

### G128 — reverse endpoint on explicitly clocked candidates

Use standard fixed deterministic bit-machine code plus syntactically explicit clock c(N+1)^d (or an equivalent effectively enumerated polynomial bound). The normalized evaluator stops at the clock, substitutes a fallback on timeout/malformed result, and independently honors the fully pinned anchor and verifies the output. All valid code/clock pairs denote polynomial-time anchored candidates; every actual polynomial search algorithm has some valid such pair (clock and wrapper can absorb polynomial overhead). Valid syntax is decidable. Define Bad(e) iff there exists a unit gain on ordinary 3CNF; gain verification is effective by bounded simulation and polynomially sized original evaluation. By G122, correctness iff not Bad, and P!=NP iff Bad(e) for every valid e. Invalid codes may be assigned an arbitrary fixed sentinel.

The following are equivalent, classically and with standard machine coverage:
(i) P!=NP;
(ii) there is a total computable B(e) bounding minimum parent gain length on every incomplete valid clocked candidate;
(iii) there is a total computable finder on valid clocked candidates returning a genuine gain whenever that candidate is incomplete (arbitrary result otherwise);
(iv) Bad(e) is a decidable set of valid clocked descriptions.
Proof (i)->(iii): enumerate finite encoded source formulas and legal unit refinements, verify gains; all candidates incomplete, so search always terminates. (iii)->(ii) by length of output parent, (ii)->(iv) by exhaustive finite enumeration of parent length at most B(e), all legal units (each original variable bounded by input length), and bounded evaluation. Alternatively (iv)->(iii) by searching if Bad, returning sentinel if not.
For (iv)->(i), suppose P=NP. Fix a complete polynomial anchored assignment producer W_* by original decision-to-witness self-reduction and fix a polynomial clock for it. For arbitrary no-input machine M construct a clocked W^*_M: honor the anchor, simulate M for N-1 steps, use W_* if it has not halted, else W_0. Unlike G126, both branches are polynomial with a uniform effective clock generator in M using the fixed W_* clock, standard bounded-simulation overhead (include actual bit representation), source evaluation and wrapper overhead. If M never halts, W^*_M is complete. If M halts, the late family from G126 yields a gain. Deciding Bad would decide halting. The contradiction shows (iv) implies P!=NP. The existential choice of W_* under P=NP is legitimate for undecidability; this is not a construction of W_* unconditionally. If a total B(e) exists, one can also obtain a total computable bound in valid clocked description length alone by maximizing B over finitely many encodings of bounded length; conversely a length bound gives B(e). No polynomial bound on B, or on enumeration/search time, follows.

### G129 — exact index-set / diagonal boundary

On explicit clocks, Bad is recursively enumerable unconditionally by gain enumeration; its complement is co-r.e. If P!=NP, Bad is the entire valid clocked carrier and correctness empty. If P=NP, the G128 reduction M -> W^*_M gives r.e.-completeness of Bad and co-r.e.-completeness of correctness under computable many-one reductions. Consequently a uniform terminating verifier of candidate completeness would itself imply P!=NP, even though candidate execution is fully clocked. This is an alternative reverse endpoint, not a proof of the required decidability. An unbounded enumeration of constructive gains is a partial procedure with exactly the desired domain. Proving totality on clocked descriptions is precisely the unpaid universal nonemptiness, not a way to assume it. Each found gain is a finite original witness and verifier receipt, independently of whether a global proof of termination is available. Do not equate finite counterexample verifiability, existence of a total finder on an explicitly promised class, and polynomial candidate time. The existing Kleene specialization and resource-closing same-object certificate goals remain distinct: the delayed construction establishes the boundary of universal external counterexample selection, not SAT self-evaluation inside the same source formula. No universal clock extraction from a raw polynomial-time description is assumed. Retain original F, unit literal, both verified assignments, signed gain, neutral support status, source history, chronological simulation time, policy clock, formula length, restriction depth, chart refinement, ring/precision and consumer independently.

### G130 — actual local acceptance and repository-only regression

Executed Python script scripts/check_p0_delayed_gain_20261124.py locally, git hash-object fd9e8d3941e6afb39530dfa380a4a83e35f89290, same readback blob in both branches. The script uses a real bounded two-register instruction interpreter with inc/dec/zero-branch/halt; tests 17 finite delay programs T=0..256 (selected values), all 256 two-variable width<=2 clause masks and all four possible original unit additions. Results: 4352 sound formula checks, 2222 short-input correctness checks, 17408 unit edges, 8888 short zero-gain edges, 176 observed constructive gains, 2448 anchor checks, 17 explicit late-gain families, 4608 conditional clocked finite controls (including a nonhalting loop with bounded simulation). All assertions passed. The conditional clocked toy substitutes exhaustive search on the finite carrier for the hypothesized W_*; it is NOT a general polynomial SAT implementation and does not test undecidability or prove either side of Clay. The unbounded theorem is the mathematical halting reduction above. No native Agda/Lean kernel or CI run, no general SAT machine compiler implemented, no new formal module in this tranche. No chat attachments or unrelated branch edits.

| Gate | Deliverable | Status |
|---|---|---|
| G126 | delayedGainCompiler / semantic polynomial promise | derived; finite controls passed |
| G127 | unclocked noncomputable counterexample deadlines | proved by halting reduction |
| G128 | explicit-clock deadline/finder/Bad decidability iff P!=NP | proved as conditional equivalence |
| G129 | clocked index-set dichotomy and diagonal/resource boundary | derived |
| G130 | repository-only finite regression | executed and committed |
| N4/N5 | unrestricted lower bound / universal clocked candidate failure | OPEN |
| N6 | original Clay endpoint transport | conditional |

Next maximum cut: try to establish clocked Bad decidability via an actual costed source-gain invariant, or force a gain by the resource-closing diagonal route. Any proposed finite deadline must depend on actual clocked descriptions, not raw polynomial promise, and must withstand arbitrary sharing, delayed finite exceptional behavior and bounded simulations. No generic computable bound has been constructed. Do not treat the new equivalence as a compulsory additional Clay prerequisite or a separation. Preserve zero mode, signed residual, inhabited neutral fibres and independently indexed hyperfabric.


## 41. P0-G131–G136 — shared reverse scalar boundary and bounded clocked obstruction contraction (2026-11-24)

P vs NP is P0 in this thread. Inputs: user attachments G126–G130 (delayed gain/explicit clock) and G115–G120 (Langlands-assisted witness, first-successful prefix, signed telescope), earlier R165/R170 Langlands donor (pin-conditioned loss and backward consumer). Starting verified heads 4da161df2ff3 / 56e36158dddd. Preserve all previous work. Reuse actual original Shannon and restriction owners from G113, G115 weighted probe, G122 ordinary source gain, G102 unique-extension failure predicate, #1006 FactorsThrough, #1040 direct failure, #1129 standard machine, #1474/#1502 Cook-Levin, #1546 sharing and #123 JMD lowering with attribution. Reverse differentiation is standard arithmetic-circuit calculus, not a new general complexity theorem; this tranche applies it to the original signed source and clocked obstruction consumers. No donor branch changes.

### G131 — original independent unary weights and exact pin marginals

Let Z_F(a,b)=sum_{x:F(x)=1} product_i a_i^(1-x_i) b_i^x_i in the polynomial ring on 2n independent formal variables over any commutative coefficient ring. Every monomial chooses exactly one of the two variables at each original coordinate, even if a source variable is unused. Z_{i,0}=a_i partial_(a_i) Z_F, Z_{i,1}=b_i partial_(b_i) Z_F, Z_{i,0}+Z_{i,1}=Z_F. These are polynomial identities; evaluate at arbitrary weights including zero only AFTER differentiation (or propagate formal derivative values by AD). No division or invertibility assumed. Original Langlands witness specialization a_i=1,b_i=z_i. Distinct original assignments have distinct monomials before evaluation; support must not be confused with a zero scalar. For a unit append x_i=b, retained scalar is Z_{i,b}, loss Z_{i,1-b}; with a common ambient A, original D=3A-4Z gives D'-D=4Z_{i,1-b}. If the ambient A changes, retain extra 3(A'-A) instead of dropping it. For removing/adding a general constraint distinguish gain/loss support and signed scalar as G121/R165.

### G132 — all unit consumers via one reverse pass

Given a costed arithmetic DAG of binary addition and multiplication gates computing Z_F as a polynomial in the independent weights, evaluate once, retain forward values and gate edges, set output adjoint to one and accumulate backwards. Addition sends its adjoint to both operands; product v=u*w sends bar(v)*w to u and bar(v)*u to w. Repeated operands and shared nodes accumulate all incoming adjoints; proof by the formal product/chain rules over any commutative ring. All 2n pinned scalars recovered by multiplying each input adjoint by its original weight. At most constant ring operations per edge and O(n) final multiplies: O(C+n) additional arithmetic work and O(C+n) retained values for C binary gates plus 2n inputs; include DAG construction, indexing, coefficient bit costs and actual memory in total. No claim of free scalar oracle or universal small DAG. With any supplied variable elimination order, let w be maximum scope size of factors multiplied before summation (induced width + 1 in the ordinary graph convention). Explicit truth-table factors for source clauses and unary weights, bucket multiplication then summation construct the DAG with O((m+n)2^w) ring gates (each initial or generated factor consumed once, plus final scalar products, and initial width<=3 truth tables). Scope management polynomial in input/order sizes. General w can be n. Restricted forward arithmetic gate count not an unrestricted lower bound.

### G133 — endpoint-specific shared refinement and countercontrols

A nonzero sampled parent Z guarantees at least one nonzero branch for every original coordinate. The whole boundary can be obtained with one forward/backward pass, so selecting a preferred next coordinate can use all marginals without n separately built contractions. After choosing a nonzero branch, condition on that joint prefix and repeat as needed; G115's one child query per step remains a cheaper alternative when no all-variable selection is needed. No claim that the initial adjoint alone reconstructs a full witness or that an adaptive run needs only one pass. If parent sample is zero but some marginal nonzero, a child is already an inhabited starting point. All-zero parent and first marginals do NOT certify emptiness: for the full two-bit cube at all weights one over characteristic two, parent 4=0 and each pinned mass 2=0. More generally the full n-bit cube at weights one has all partial-assignment masses of order <n zero in characteristic two; increasing fixed derivative order does not generally remove hidden support. Distinctness from empty is original-support, not just numeric zero. For XOR(x1,x2), weights (a1,b1)=(1,2),(a2,b2)=(1,3) over GF(32), both branches of both coordinates have nonzero scalar and parent 2+3=1, but choosing both zeros violates the formula. Joint conditional information remains essential. Keep zero mode, inhabited neutral, signed gain/loss, source label, time, policy version/clock, restriction depth, chart refinement, field/precision, Frobenius and consumer independent.

### G134 — bounded source-gain scalar on the explicit-clock carrier

For a fixed valid explicitly clocked candidate e and finite encoded source length bound N, choose a canonical polynomial-length binary encoding u of (F,l) with |F|<=N, legal original variable and literal, and no duplicate encodings (include length and canonical zero padding). Original verifier V_e,N(u)=valid(u)*(1-S_e(F))*S_e(F AND l) is uniformly constructible as a deterministic polynomial-size Boolean circuit for each fixed e (time bounded by the declared polynomial clock on both encoded formulas, and validation/source evaluation). Standard unique-extension Tseitin encoding of all gate equations plus asserted flag yields CNF K_e,N(u,a) with a unique accepting auxiliary extension iff V=1. This reuses G102/G122, not a new generic machine compiler. Weight only u with independent unary weights; auxiliary coordinates have both weights one. Original gain polynomial Z_e,N = sum_u V_e,N(u) product weights has distinct monomials and is nonzero formally iff at least one bounded gain exists. On the actual factor DAG of K, G131/G132 extract all original coordinate marginals with a shared reverse pass, independent of auxiliary count beyond its actual factor/clock costs. Decode any recovered u by the original verifier, reconstruct a genuine missed assignment from W_e(F AND l), not an accepting flag alone. Preserve canonical source IDs through compiler. At a random field point, using a_i=1,b_i=z_i and sufficiently large GF(2^k), Schwartz-Zippel as G116 gives one-sided bounded detection, and G115/G133 conditional pin descent recovers a gain from a nonzero scalar. Every finite N contraction is computable by exhaustive fallback. If all samples vanish, unresolved unless an independent exact zero test/complete hitting set or exhaustive support proof is paid. No general polynomial contraction follows, and a sequence of zero bounded polynomials does not certify all larger bounds. The G128 computable deadline/finder equivalence stays independent of this finite scalar evaluator.

### G135 — reverse endpoint cost and strict scope

General exact evaluation of integer Z_F at a_i=b_i=1 is #SAT (standard #P-complete counting problem), and parity at the same weights in characteristic two is parity of #SAT; do not equate either with decision support. General polynomial-time sampled evaluation over growing binary fields would imply RP=NP as G116; deterministic hitting set plus that evaluator would imply P=NP. A lower bound for exact weighted counting, sampled evaluation, or this elimination order cannot itself force P!=NP because a general SAT solver need not compute these consumers. Conversely, a shared adjoint does not require an independently expanded backward row per pin. The useful direct obligation is either a paid forward contraction for the actual bounded gain graph with nonzero sample, or unconditional proof of existence of a finite nonzero gain for every clocked candidate. The latter can equivalently be a total computable deadline (G128), with arbitrary sharing and source revisits permitted. No theorem of universal nonemptiness or deadline obtained.

### G136 — executed local regression and repository-only acceptance

Actual Python/SymPy script scripts/check_p0_reverse_scalar_20261124.py, local git hash-object 94c61cae8c9c501f01343ccb50a8012343ff2b77, matching both GitHub blobs. Actual factor elimination constructs a shared arithmetic DAG from original clause factors, not merely a precomputed truth table. 240 seeded original width<=3 CNF cases (n=1..6, 20 per n per ring) over Z/8 and GF(32) with polynomial X^5+X^2+1; 1680 marginals compared to independent brute enumerations, 1680 independent added-unit contraction comparisons, 840 Shannon checks. Three independent-set cyclic CNF tests n=12,48,192 with max multiplied scope 3 and respectively 300,1308,5340 forward arithmetic gates; all scalar values mod8=2 matched independent 2x2 transfer trace; all 252 cycle marginal sum checks passed. Cyclic comparisons use mod8, not growing extension-field guarantee. Neutral and joint controls 2/2, exact SymPy XOR derivative identities 2/2. These are real finite arithmetic executions, not performance measurements or general gain-graph circuit compiler tests. No Teichmuller extension-ring execution in this tranche; GF(32) is the residue field, mod8 is scalar ring. No CI/native Agda/Lean kernel, no generic machine-to-CNF implementation, no new formal module. G113 source candidate and native port remain unverified. No chat files.

| Gate | Deliverable | Status |
|---|---|---|
| G131 | original weight marginal identities / signed Weil loss | derived, tested |
| G132 | costed shared reverse boundary on actual elimination DAG | implemented and tested |
| G133 | adaptive nonzero pin selection / neutral and joint anti-controls | derived and tested |
| G134 | bounded explicitly clocked source-gain polynomial and original witness transport | conditional construction; machine compiler unimplemented |
| G135 | unrestricted endpoint cost distinction | derived; no general evaluator or deadline |
| G136 | repository-only exact regression | passed |
| N4/N5 | unrestricted lower bound / universal clocked candidate failure | OPEN |
| N6 | original Clay endpoint transport | conditional |

Next maximum cut: instantiate the bounded gain graph using the existing concrete machine compiler and original source labels, then seek nonzero scalar / certified support with a paid shared contraction. In parallel attack the uniform finite obstruction deadline independently; avoid making scalar evaluation a mandatory path for unrestricted algorithms. No other programme changes.

## 42. P0-G137–G142 — finite signed consumer obstruction and global quotient anti-control (2026-11-24)

Literal Clay P vs NP remains P0; Langlands is a supporting donor. Read all three supplied pastes (G121–125, G126–130, G115–120); live initial P0 heads 4da161df2ff3 / 56e36158dddd. Concurrent G131–136 weighted backward-consumer work preserved; this tranche provisionally reported as G131–136 in chat is renumbered G137–142. Reopened actual master owners PNotEqualsNPQ1KeyOnlyTransitionExact (e875f8e789cbe713c34b5e5ba22f89a26eb5f455: key-only transition with finite search), PNotEqualsNPSelfDiagonalFutureCongruenceExact (a95e710b90df5b5f8cff276c6706fac4c2b2ed52: fixed root and same remaining arity), PNotEqualsNPResourceBoundedSelfDiagonalExact (37f9e7d26334383cacaf86db15f6f3be07e5ebd9: semantic diagonal vs resource closure). G122 original unit gain, G128 clocked deadline equivalence, G115–120 reverse witness, R135–143 contextual algebra and R150–169 signed precision are donors; #1006 FactorsThrough, #1040 direct failure, #1129 costed machine, #1474/#1502 Cook-Levin, #1546 sharing and #123 JMD lowering with attribution remain authoritative. Standard weighted automata reachability and module finite-length arguments used; no literature novelty or other programme changes.

### G137 — finite consumer obstruction over a field
Let e be an explicitly clocked anchored assignment producer. A word w over a finite alphabet encodes original F and legal unit l, with effective decoding. Suppose a supplied finite linear representation g_e(w)=u T_w v (row u, matrices T_a, column v, dimension d) is support-faithful: nonzero iff a genuine G122 gain, zero on malformed inputs. Set V_j=span{u T_w: |w|<=j}. Then V_(j+1)=V_j+sum_a V_j T_a. Equality implies invariant stabilization forever. If u=0 the series is zero; otherwise dim V_0>=1, hence stabilized by d-1. A nonzero terminal functional on this span implies some actual word of length <=d-1 with nonzero terminal coefficient. The witness is an actual original word, not a linear combination. To bound parent formula length for G128 take maximum decoded parent size over the finite word ball (or a length-respecting encoding). For a supplied representation over a computable field this is effective; no uniform compiler from arbitrary clocks follows.

### G138 — finite chain ring extension
For finite chain ring R of length H with uniformizer 2 (Z/(2^H) or unramified binary extension ring), replace spans by submodules. R^d has composition length Hd; every strict inclusion consumes at least one length, so the same argument bounds a nonzero word by Hd-1. The ring statement is exact, not an extrapolation of finite tests. Preserve R85 D=3A-4P at precision H+2 before extracting P mod2^H. A modular weighted count can vanish on inhabited support; arbitrary Weil samples are not support-faithful gain indicators. Source support fidelity must be established separately. No free local-factor oracle or compulsory exact global transfer claim.

### G139 — constructive closure and reverse provenance
Queue actual (row,word) generators, initially (u,empty) if u!=0. Append a successor iff it is outside the current generated submodule; preserve its originating word. If a retained row has nonzero terminal value, decode and directly verify G122 by two bounded producer calls and source evaluation. If queue exhausted with zero terminal on generators, the generated submodule is invariant and annihilated by v; all coefficients zero. FIFO retains words of length <=Hd-1 (or d-1 over field); at most Hd independent additions and |alphabet|Hd successor checks. Field membership Gaussian elimination; finite chain-ring membership effective by enumeration or elimination with annihilator multiples. Actual regression uses column-wise minimal 2-valuation pivot, unit inverse after factoring out 2-power, clearing other rows, retaining the pivot annihilator multiple as a tail generator. Nonunit pivots are not field pivots. No measured runtime or optimal bit complexity claimed. Preserve original words and separate support, signed residual, clock, source history, word depth, original formula size, chart refinement k, Frobenius/field and precision. Fixed-root finite quotient is not global quotient over all input formulas.

### G140 — global exact linear coverage anti-control
On raw ordinary clause-list syntax permitting repeated clauses, take two-guard F_(m,n)=(x1 OR x2)^m AND (x1 OR NOT x2)^n, m,n>=1 (powers mean repeated clauses). Define total polynomial anchored W: honor consistent full pins first; on this ordered family output (0,0) iff m=n, else (1,0); on F AND x1 output (1,0) unless full anchor applies; elsewhere arbitrary total polynomial assignment fallback. Extend to other arities with anchor. All these formulas and their unit restrictions are satisfiable. Actual G122 gain on fixed unit x1 iff m=n. Encode this regular source subfamily by a^m b^n tokens. The equality language is nonregular. A finite-dimensional representation over a finite ring has finitely many reachable rows, so its nonzero language is regular and cannot recognize the whole equality family. Over any field (even infinite), K-by-K matrix g(a^i b^j), 1<=i,j<=K, is diagonal with nonzero diagonal, rank K, yet factors through d coordinates; d>=K for every K. Exact 0/1 indicator over finite ring likewise gives identity after residue reduction. Thus even simple explicitly clocked bad candidates need not admit a fixed finite-dimensional exact *linear* representation on this source chart. This is not a SAT time lower bound: W counts in polynomial time and has a tiny gain. If parser canonicalizes duplicates, this specific raw-syntax control does not apply. Arbitrary preprocessing or nonlinear chart changes may recognize equality first. G126 delayed exceptional behavior is independent anti-control.

### G141 — weakest sufficient sound obstruction certificate
Full exact global gain-series representation is unnecessary. Sound underapproximation with a nonzero word suffices for constructive failure; zero underapproximation does not show no gain. Overapproximation with zero certifies absence if coverage is proved; nonzero may be spurious. A total effective compiler on all clocked e returning finite sound underapproximation nonzero whenever Bad(e) would decide Bad via G139; G128 then implies P!=NP. Conversely under P!=NP G128 enumeration terminates for every e and can produce a singleton-word recognizer for a found gain (a word of length m uses m+2 states with dead state). Hence the weakest uniform certificate construction is equivalent to P!=NP, not free via finite linear algebra. Need noncircular discovery or total effective bound. The concurrent G131–136 bounded gain-polynomial / reverse weighted consumer supplies a separate route: a nonzero evaluated bounded-source gain polynomial can recover an actual word by G115 and unit gain by G122; zero sample is not emptiness, and finite contraction at each input horizon gives no uniform horizon bound. Do not require all algorithms to use either weighted evaluation or linear transfer.

### G142 — actual exact execution
Identical repo-only script scripts/check_p0_finite_consumer_obstruction_20261124.js executed in JS tool, seed 131 xorshift32. Moduli 2,4,8, dimensions 1..3, 120 trials per combination: 1080 membership comparisons against explicit finite spans, 1080 invariant searches vs full reachable-vector BFS, 782 nonzero / 298 zero series, returned words and length/generator bounds checked; max generators observed 4. 32 unary delay chains (dimension 1..32) attain field bound d-1. 2304 actual two-guard repeated-clause refinement comparisons for 1<=m,n<=48, 48 positive gains, all match equality predicate. Fully pinned anchor added to test producer and corrected script re-executed. Tests use integer arithmetic mod 2^H, not unramified extension ring execution; small dimensions only. No native kernel, CI, Node subprocess, actual local factor oracle, general candidate-to-transfer compiler or performance benchmark. No chat attachments.

| Gate | Deliverable | Status |
|---|---|---|
| G137 | finite field obstruction d-1 | derived |
| G138 | chain-ring obstruction Hd-1 | derived |
| G139 | original-word invariant search | implemented and tested |
| G140 | global exact linear coverage anti-control | scoped proof and tests |
| G141 | weakest sufficient finite certificate | conditional equivalence derived |
| G142 | repo-only regression | executed |
| N4 | unrestricted resource obstruction | OPEN |
| N5 | universal clocked failure / uniform finite bound | OPEN |
| N6 | original Clay endpoint transport | conditional |

Next: instantiate the bounded gain compiler from concurrent G134 with actual machine/source authority, seek a paid nonzero scalar or certified support, and independently seek a finite obstruction construction without global exact linear coverage. Charge discovery, source encoding, arbitrary sharing and nonlinear preprocessing. Retain zero mode, inhabited neutral and signed residual with independent indices. No Clay solvedness claim.


## 43. P0-G143–G148 — paired bounded gain verifier, original-word scalar contraction and fixed-clock anti-control (2026-11-24)

Stay on literal Clay P vs NP. Inputs: user reports G131–G136 (shared reverse scalar boundary) and G137–G142 (finite signed consumer and uniform certificate boundary). Starting live heads 291fcff59cf0 / e69e2a760669. Reopened actual Agda owners PNotEqualsNPPolynomiallyClockedStandardCandidateExact (blob 0af35005027588b651982a5dd538e33d99981b0d), ConcreteTapeCookLevinCookFormulaExact (32ee558f944d6566bb69b902364f42324e537b1b), PNotEqualsNPConcreteCircuitSharedSemanticsExact (763a8a53a3edb89bd8b954f96dad077a8c9f7a04). The first supplies a standard-machine clock receipt conditional on an exact step bound, the second fixed-input exact-budget accepting-run equivalence, the third shared gate semantic equivalence. None alone is the symbolic-source parsimonious gain compiler. Reuse these owners, G113 original Shannon, G122 source gain, G128 deadline, G134/G137–G142, #1006 FactorsThrough, #1040 direct failure, #1129 standard machine, #1474/#1502 Cook-Levin, #1546 sharing and #123 JMD lowering with attribution. This tranche instantiates the contract in an executable bounded streaming-machine submodel, not a native port of those Agda compilers or a universal TM construction. No donor branch modifications.

### G143 — actual bounded gain graph and deterministic auxiliary contract

For a fixed clocked candidate e and canonical source input u=(F,l), the required weighted CNF compiler contract is cardinality of {a:K_e(u,a)} = G_e(u) (zero or one), not just satisfiability equivalence. A fixed deterministic transition graph with symbolic inputs, exact gate equations and asserted gain flag has this property: topological evaluation gives the unique extension to ALL gate equations, and the final assertion accepts precisely when the gain bit is one. Each AND/OR gate is encoded with three width<=3 clauses; NOT with two binary clauses; constants by units. Unit weights on auxiliaries then preserve original weighted mass without multiplicity. A verifier that only proves accepting-run existence must separately establish deterministic extension, including any nondeterministic rule-selector encoding, padding, initial row and output conventions, before this weighted conclusion follows. The generic symbolic-input standard TM integration is still open.

Actual bounded carrier: canonical n=2 ordinary clause-selector representation (four unit and four non-tautological binary clauses, no repetitions; eight selectors), original unit l encoded in two bits, ten source bits total. Candidate is a four-state deterministic streaming machine with arbitrary fixed transition table tab[q,b], starting state 0, consuming the eight clause bits in canonical order, final state interpreted as an assignment. Explicit budgets 0,4,8 transitions; if fewer than eight, use all-zero fallback. Independently override fully pinned inputs by their direct unique assignment when pins consistent (on inconsistent pins score zero); this is the G122 anchor. Verify actual original formula, never trust output state as acceptance. Append the selected unit by OR-ing its original selector bit. The gate compiler builds both bounded runs on the same source inputs with shared gate cache, verifies scores and asserts gain=(1-S_parent)*S_revised. All accepting CNF lifts decode genuine missed satisfying assignments on the parent. Duplicate-unit additions harmlessly yield no gain. This small carrier includes timeout and arbitrary syntax-sensitive transition choices; no claim of arbitrary polynomial-machine coverage.

### G144 — original-source paired transfer without compiled incidence expansion

Let l be the chosen literal index; q,r the parent/revised machine state; A the bitmask of original assignments satisfying all encountered selected clauses; U the explicit unit-selector mask. Retain independent source position k, clock, machine and source identities, refinement version. First consume the two literal bits, then eight source clause selectors. For selector b_i, revised b'_i=b_i OR [i=l]. Both state updates follow tab within the clock; A intersects the actual clause truth mask only when b_i=1; U accumulates the four original explicit units. At terminal, revised support A'=A intersect mask(l), revised units U'=U OR {l}. Evaluate anchored/verified scores from (q,A,U) and (r,A',U'), including timeout fallback. The gain flag is (1-S_parent)*S_revised. Induction on source positions proves equivalence with the actual circuit compiler. This is a single joint state, not product of unrelated marginals. State enumeration is costed; retaining A uses one bit per original assignment (four here), potentially exponential in a growing original-variable universe, and must not be promoted as general tractable geometry.

### G145 — finite invariant + shared backward consumer on the actual bounded graph

For each source position k and reachable state s, retain forward weighted mass f_k(s), independent original-word reachability and one actual source predecessor/witness. For transitions s --b--> t, let g_k(s)=sum_b w_k(b)g_(k+1)(t), with g_N(s)=gain(s). Then Z=g_0(s0)=sum_s f_N(s)gain(s), and Z_(k,b)=sum_{s --b--> t} f_k(s)w_k(b)g_(k+1)(t). This is G131–G132 reverse source boundary on an actual paired gain verifier, using O(E+N) ring operations beyond constructing the reachable graph with E edges (constant work per edge, all marginal coordinates accumulated once), no divisions. Forward/backward equality and Z_(k,0)+Z_(k,1)=Z hold over every commutative coefficient ring. Include state bit length, actual graph discovery, hashing, provenance, ring bit costs and original witness replay. Independent support propagation gives an actual accepting word even if every sampled numeric mass cancels; it is paid for by traversing the reachable graph, not a free general SAT oracle. A layered graph can be embedded in a single finite transfer carrier using direct sum of layers and transitions advancing only one layer, with accepting functional at terminal layer. Its dimension is the sum of reachable layer cardinalities; G137/G138 then apply but the original 10-bit length is already known. No global cross-source-length coverage or new unbounded deadline follows from this bounded graph. Zero numerical mass, absent support and invalid source remain separate.

### G146 — unconditional fixed-clock-only failure deadline anti-control

In the conventional finite-control deterministic multitape TM cost model (one transition charged per step, machine code fixed for a run), fix an effective canonical explicit source encoding with output assignment length polynomially bounded in input length. For each integer T, hardwire a finite trie for all valid encodings of length <=T, storing a precomputed exact satisfying assignment when one exists and an arbitrary assignment otherwise. Read the source in a single pass, keeping a copy; if it terminates at a stored leaf, emit its hardwired assignment via finite control; if it extends beyond or leaves the trie, rewind or reuse the saved source and run the SAME anchored polynomial fallback W0 from G126. The finite control may grow exponentially in T, but on stored inputs runtime is at most a fixed polynomial in source length independent of T (read plus output), and on other inputs at most the common fallback polynomial plus linear scan/rewind. Thus all these candidates admit a single common explicit clock c(N+1)^d in this machine-step model, independent of T. The compiler is effective by exhaustive finite preprocessing; its construction and code size are not free and may be huge. For all |F|<=T the verified score is correct, so no genuine unit gain has parent length <=T even if the child is longer. For sufficiently long canonical distinct-clause family F_m=(x1 OR x2) AND all (x1 OR xi), 3<=i<=m, with |F_m|,|F_m AND x1|>T, fallback rejects parent and accepts refined formula. Consequently min gain length exceeds T for incomplete candidates with the SAME clock. No finite bound depending on clock degree and coefficient alone can cover all incomplete candidates, unconditionally. More generally no fixed finite test suite independent of program descriptions is sufficient: include its parent formulas in the correct finite patch (or choose T at least their lengths). This is not a noncomputability statement about bounds depending on the entire explicit code+clock (G128 remains exact). If code lookup cost is charged by a universal interpreter, include program-size-dependent overhead; fixed coefficient claim is for conventional per-machine transitions, not arbitrary uniform bit-cost interpreters. This closes a potential mistaken resource argument, not N4/N5. Finite-trie lemma is mathematical, not an executed large-machine benchmark.

### G147 — finite underapproximation weld and remaining noncircular target

The bounded paired verifier gives a concrete sound finite recognizer H_(e,N) in the executed carrier. It is exact there, and any nonzero word decodes an original source gain; if weighted cancellation occurs the separate reachable-support graph can still find a witness. For arbitrary clocked e, a fully costed bounded graph is in principle computable by finite simulation/enumeration even without a compact compiler. Thus the central missing implication is selecting N(e) computably such that Bad(e) implies at least one bounded original gain, or equivalently the G141 support-faithful finite underapproximation with conditional nonemptiness. G146 shows that such a bound must exploit more than runtime clock parameters, even when the machine itself is known to run polynomially. A universal finite graph generated independently of machine descriptions or mandatory linear exact coverage is invalid. General arbitrary-code finite state rank, nonlinear compression, source re-access and arbitrary sharing are still allowed; no uniform finite obstruction has been established. The bounded graph's support computation may be as expensive as enumerating every source word; weighted adjoints are conditional efficiencies, not an unconditional lower bound.

### G148 — actual local acceptance

Executed local Python/SymPy script scripts/check_p0_paired_gain_stream_20261124.py, git hash-object f95e12e6548a88ecef475460d1de5906ee63e207, matching GitHub readback in both branches. Twelve seeded four-state transition tables crossed with budgets 0,4,8 (four each); all 1024 source words per table: 12,288 direct-execution vs compiled-gate/CNF-lift checks, 471 accepted gain lifts each verified against the original refined formula, 144 weighted scalar comparisons (mod 2,4,8,17; three weight choices per table/ring), 2,880 independently enumerated marginal comparisons and 1,440 Shannon marginal-sum identities, 98 inhabited zero samples with actual original source word recovered, max 328 auxiliary gates, max 414 reachable frontier states, max 1450 transition edges, 1/1 SymPy signed residual identity. All passed. Gate uniqueness is a consequence of deterministic topological equations; tests evaluate the unique lift, not exhaustive enumeration of all auxiliary bit strings. These are actual bounded streaming and circuit executions, not the full repository concrete tape compiler, not generic growing-variable SAT, not a benchmark of unbounded finite certificate search. No Teichmuller extension-ring run, CI, native Agda/Lean kernel, or new native proof module. No chat files.

| Gate | Deliverable | Status |
|---|---|---|
| G143 | bounded paired machine gain verifier / deterministic auxiliary lift | implemented and tested in streaming submodel |
| G144 | original-source paired transfer | implemented and tested |
| G145 | shared backward boundary and support witness on finite gain graph | implemented and tested |
| G146 | fixed-clock-only deadline anti-control | mathematical proof in finite-control TM model |
| G147 | bounded graph / uniform nonempty finite certificate distinction | derived; universal construction open |
| G148 | repository-only exact regression | passed |
| G134a | full standard-machine symbolic-source compiler weld | OPEN |
| N4/N5 | unrestricted obstruction / universal clocked failure | OPEN |
| N6 | original Clay endpoint transport | conditional |

Next maximum cut: extend the actual symbolic-source bounded compiler through the concrete tape initial-row and deterministic transition owners, paying unique extension of rule selectors and halt/padding states; integrate the source-preserving frontier without assuming a full truth-mask carrier is tractable. Independently attack uniform nonempty underapproximation using the entire candidate code, not only its clock or fixed test length. Do not make that representation compulsory for every algorithm. Retain signed residual, zero mode, inhabited neutral, original coordinates and independently indexed history/time/refinement/precision/consumer. No other programme edits or Clay solvedness claim.


## 44. P0-G149–G154 — symbolic padded tape gain compiler without assignment-mask expansion (2026-11-24)

Stay on literal Clay P vs NP. Inputs: user G143–G148 and Langlands R170–R176 (outside environment, signed local revision and consumer-directed precision; donor report only, not reproduced). Live starting heads 62ae7f47484e / fdae7b5feb00. Reopened actual Agda owners ConcreteTapeMachineLocalityExact (fcce0a493b71996ec8296e1cb3230caa8a76ac6d), ConcreteTapeInputInitialRowExact (aa4d853bbd80c9c026966bcedd38702961023554), ConcreteTapeTimeBudgetPaddingExact (cf914346f9f0c8419aac2294609356faa290472c), ConcreteTapeRuleSelectorExact (c7664390fcab7e1e67c549a053c4918591da7529). Reuse G143 clock/semantic compiler owners, G113 Shannon, G122 unit gain, G128 deadline, G131 reverse scalar and G137 finite invariant, #1006 FactorsThrough, #1040 direct failure, #1129 standard machine, #1474/#1502 Cook-Levin, #1546 sharing, #123 JMD lowering with attribution. This is an executable symbolic tape implementation matching the local-rule/initial-margin conventions, not a native import or execution of the Agda compiler. No other programme changes.

### G149 — deterministic rule-selector and padding seam

The original locality owner represents a tape step by a three-cell radius-one rewrite with head movement left/stay/right. The original initial row puts a head at the first input symbol (blank for empty input) and one blank either side, and the time-budget owner adds T blanks on each end. Its original rule decoder maps the first selected bit to a listed rule (fallback if no bit selected). That decoder is intentionally not injective: several bit patterns can select the same rule. Acceptance equivalence does not imply parsimonious symbolic-source weighted compilation. Do not infer that the actual existing global CNF has multiple models without inspecting all its other constraints. A sufficient separate deterministic circuit contract is to set each firing bit at each site equal to H_(t,j,q) AND X_(t,j,a), with a total single-valued rule table on (q,a). Well-formed one-hot initial head and symbols imply exactly one firing bit per step, hence unique next row. A halted state is absorbing (same state, same symbol, stay); timeout explicitly uses a fixed full-assignment fallback. Initial input bits remain symbolic, not replaced by one constant input. Every deterministic gate is encoded by equivalences with unique topological extension; assert the final gain flag separately. Guarded tape size m+2T+2 for nonempty input word length m ensures the head never reaches the outer boundary during the T steps. Original clock, time, position, source, policy version and refinement index distinct.

### G150 — direct verified output contraction, eliminating the full assignment mask

For canonical clause selectors u_i with original clauses C_i, define S(u,x)=product_i [1-u_i(1-C_i(x))] for Boolean assignment x; product is Boolean conjunction, equivalently integer product on Boolean values. Let x=W_e(F), y=W_e(F AND l) be the actual normalized outputs, including fully pinned anchor and timeout fallback. Then G_e=(1-S(u,x)) S(u,y) l(y). The revised formula uses the same original clauses with an added unit; if the unit already occurs this is a duplicate-free selector OR and yields no gain for deterministic identical encoding. If ordinary clause lists retain duplication, re-run on that actual encoding and preserve provenance; do not silently identify syntax-sensitive candidates. The verifier never constructs all 2^n original assignment bits: evaluate the original selected clauses only on x and y. For fixed-width clauses cost O(m) Boolean gates besides actual two bounded computations and full-pin anchor, on a canonical universe of m possible clauses. For width<=3, m=O(n^3); a sparse explicit input version can instead charge actual incidence and parser. Direct symbolic compiler requires deterministic outputs, not a free solver. The old mask A_k from G144 is not necessary for correctness; nevertheless contraction of the new factor graph may still be exponentially costly.

### G151 — local symbolic tape execution and unique extension

Implemented a three-symbol (0,1,blank), three-state (two live plus absorbing halt) deterministic single-tape submodel with arbitrary complete rule table, left/right/stay, symbolic initial clause selectors, blank margins and fixed literal l per compiled graph. For each time and site, retain one-hot symbol and joint head/state. New symbol at a site is either its old symbol if no head, or the write-symbol of the active local rule. New head/state is the OR of incoming firing bits from adjacent or same site according to rule direction and target state. This is exactly the local transition model; induction on time gives one-hot rows and agreement with concrete execution. Output convention in this test: at halt first n cells read as 1 iff symbol 1, otherwise 0; if not halted output all zero. A fully explicitly pinned original source overrides output bits from positive unit pins and directly verifies clauses (contradictory pins necessarily fail). Compile paired original and refined runs in one cached acyclic Boolean gate graph (share identical gates), then direct verifier G150. All gates have deterministic truth equations and Tseitin clauses of width at most 3. On fixed symbolic input u, the gate CNF has exactly one extension before flag assertion, and zero or one after; reconstruct by gate execution. This mathematical uniqueness is not an exhaustive search over auxiliary assignments. The test compiles each literal separately, not a single graph with symbolic literal bits; a joint graph can use selection gates but is not implemented here. Input universe is width<=2 (unit and non-tautological binary clauses), n=2,3,5; no general source parser or concrete standard TM Agda integration. For fixed machine state and alphabet size, straightforward unrolling has O(T(m+T)+m+n) Boolean gates, counting all site updates, direct verification and initialization, before hash-sharing savings. With variable machine size charge local rule scans, symbol/head encodings, gate generation and actual bit sizes. This cost is compiler size/time (up to indexing overhead), not the SAT/weighted elimination cost. The one-hot simulator avoids the full original assignment mask.

### G152 — signed outside consumer with source-sensitive rerouting

From R170-R176, a fixed factor outside environment provides clause deletion/addition effects only when other factors are held fixed. For a fixed verified completion x, C_i(x) is a direct local clause factor; if clause i is appended, its old-witness loss is S(u,x)(1-C_i(x)). For the actual revised output y, the full score difference is -S(u,x)(1-C_i(x)) + [S(u',y)-S(u',x)] with u'=u OR e_i. The bracket is the signed algorithmic reroute contribution, not captured by differentiating a frozen-output factor. This is G121 on the direct symbolic verifier. For a clause deletion, the outside product with that clause removed restores precisely the old-completion violation sector if all other clauses hold; but revised W may change every output coordinate and its trajectory. No claim a single outside derivative supplies arbitrary rerun gains. Joint edits require the actual revised computation or a proved transport of its output. Independent numerical support, zero-mode and signed residual remain attached; auxiliary elimination and precision reduction must not erase original source identity or an inhabited zero. Backward contractions on the actual gate factors are the next costed implementation, not claimed by the current tape tests.

### G153 — finite obstruction scope and unpaid endpoint

For each fixed bounded source universe and clock, deterministic gate lift provides a finite exact gain recognizer and a weighted source polynomial with coefficient 0/1 per original encoding. This is a concrete bounded symbolic tape witness for G134, and one can use G131/G137 conditional contraction on its factor graph. It removes the requirement for a full original SAT truth-mask state, but neither guarantees polynomial width of the resulting graph nor bounds the first gain uniformly across candidate descriptions. All arbitrary shared algorithms, source revisits, nonlinear transforms and recomputation remain admissible. G146 prevents clock-only deadlines, G128 equivalence still requires a total computable B(e) or other genuine unconditional universal failure proof. The full standard machine symbolic-source compiler (original parser, bit-cost, exact native rule-selector/padding/clock seam and proof of unique lift) remains open. No generic native tape machine integration or finite deadline obtained.

### G154 — actual regression and repository-only acceptance

Executed exact JavaScript in the current tool runtime; scripts/check_p0_symbolic_tape_gain_20261124.js, identical GitHub readback blob 5e42f76332430e31b27394e79f38ef6808675d9a in both branches. All 256 selector masks for n=2 and seeded 32 masks per graph for n=3,5; three transition-table kinds (moving/halting, nonhalting, pseudorandom), clocks 0,2,5, four fixed literal choices at n=2 and two at n=3,5. Actual results: 10,368 direct vs compiled score/output/CNF-lift comparisons; 357 accepting gain witnesses verified on original parent; 48,384 concrete vs symbolic row comparisons and 6,147,072 individual head/state/symbol coordinates; 5,760 guaranteed timeout-control instances (clock zero or nonhalting kind), 5,442 parent full-pin anchor instances; 216 weighted scalar comparisons mod 2,8,17 across the enumerated test inputs; largest cached auxiliary graph 11,310 gates and 33,599 CNF clauses. Weighted tests compare sums of lifted gain flags vs direct gain flags over tested source samples; NOT independent general variable elimination, adjoint, full growing-source contraction, performance measurement, or proof of asymptotic separation. Exact uniqueness derived from gate equations, not exhaustive auxiliary enumeration. No native Agda/Lean checks, CI, or external file attachment. No local SymPy in this round; exact JavaScript used for executable tape/CNF comparison.

| Gate | Deliverable | Status |
|---|---|---|
| G149 | deterministic rule-selector and padding contract | derived |
| G150 | direct two-output gain verifier without assignment mask | implemented and tested |
| G151 | bounded symbolic tape / shared unique-extension compiler | implemented and tested in stated submodel |
| G152 | signed frozen-outside vs actual reroute ledger | derived |
| G153 | bounded compiler vs uniform obstruction distinction | derived; deadline open |
| G154 | repository-only exact regression | passed |
| G134a | full standard machine / parser / native weighted compiler weld | OPEN |
| N4/N5 | unrestricted cost obstruction / universal clocked failure | OPEN |
| N6 | literal Clay endpoint transport | conditional |

Next maximum cut: connect actual standard-machine input/parser/clock owners to the symbolic tape graph; construct the backward consumer on its real transition factors without rebuilding original truth-mask state. Pursue an unconditional uniform finite obstruction independently; neither gate unrolling nor derivative width is a mandatory path for arbitrary algorithms. Retain original source, zero mode, inhabited neutral, signed residual and independently indexed hyperfabric. No other programme edits or Clay solvedness claim.


## 45. P0-G155–G160 — geometry-forward exact finite secant transport and source revision squares (2026-11-24)

Standing user direction: GEOMETRY-FORWARD, endpoint-first, bidirectional and reverse-solved. Stay on literal Clay P vs NP; Langlands R177–R183 is donor only (ordered separator transport, mixed revision residual, precision), not a changed programme. Starting heads 92d62779be87 / 79604d8b7b21. Reuse actual G151 symbolic tape graph scripts/check_p0_symbolic_tape_gain_20261124.js (blob 5e42f76332430e31b27394e79f38ef6808675d9a), original concrete tape locality/initial row/padding owners in G149, G121 signed rerouting, G131 reverse scalar, G137 finite invariant, G146 fixed-clock anti-control, G128 deadline, #1006 FactorsThrough, #1040 direct SAT failure, #1129 concrete machine, #1474/#1502 Cook-Levin, #1546 sharing and #123 JMD lowering with attribution. No novelty claim for telescoping product rules or circuit differentiation. The new application is exact finite paired source transport on the actual bounded tape gain graph.

### G155 — exact signed finite secant on original gates

For two actual legal source words u,u' in the same fixed compiled graph, let v,v' denote actual Boolean gate values and delta v=v'-v in the signed integers. At an ordered AND v=ab, delta v=b delta a+a' delta b; at OR v=a+b-ab, delta v=(1-b) delta a+(1-a') delta b; at NOT delta v=-delta a; constants have zero residual. All are exact algebraic identities, not infinitesimal linearization or differentiating an already evaluated scalar. Ordered operands retain source orientation: alternate decomposition a delta b+b' delta a is equally exact but changes individual path attribution; do not confuse a path ledger with a canonical decomposition. Repeated operands and shared nodes keep both incoming contributions. This defines a linear transport for the specified pair of actual histories, not a globally fixed linearization of arbitrary revisions. Keep both endpoint values, signed delta and actual source coordinates. At a fixed precision reduce the integer identity if desired; do not use cancellation as absence of original support.

### G156 — actual causal cone and source-indexed repair geometry

Local tape updates at time t+1 use only tape/head-state coordinates at j and neighbors j+-1 (G149/G151); induction bounds the potentially affected tape sites after t steps from a source edit at position i by |j-i|<=t on the original padded carrier. This is a structural bound for the actual tape rows with fixed rule table and clock, not an exact changed-support claim. The final score includes global halted-state observation, original clause selectors, full-pin anchor and direct clause verifier; their dependency edges must be retained separately, not assumed radius-one. For the fixed literal revised run the forced unit selector can erase a source bit change in that run while the parent still changes. On a topologically ordered deterministic DAG, propagate dirty flags from edited source nodes, recompute a marked gate and propagate to successors only when its value actually changes. Induction gives exact new values even with reconvergence, since all changed predecessors are processed before the gate. Multiple edits can mark their union; update histories and actual changed support are distinct from the static cone. The executed reference implementation uses a full topological scan to check dirty flags, so touched-gate count is NOT total runtime or a sublinear execution claim. Fanout construction, copies, scanning, propagation, indexing and arbitrary source re-access are charged. A priority-based sparse scheduler is possible but not implemented. This is geometry of one supplied graph, not an unavoidable path for all SAT algorithms.

### G157 — endpoint-first exact backward secant

For a fixed source pair let alpha_v,beta_v be the exact coefficients of G155 for the gate v and its two ordered parents. Seed terminal covector lambda_out=1, others 0. In reverse topological order accumulate lambda_a += lambda_v alpha_v, lambda_b += lambda_v beta_v. Then delta G = sum_i lambda_i delta u_i, with input source indices i and constants omitted because their deltas vanish. Proof: substitute the exact local secant equations backwards in the output linear form, preserving common gate sharing. Every addition is exact in Z (or a chosen commutative residue ring after reduction). This computes a signed finite endpoint residual for a pair, not all counterfactual edits from a single frozen adjoint. One pass costs O(C+m) integer operations on C bounded fan-in gates and m inputs once both actual histories are available; coefficient bit sizes are separately charged (bounded by O(C) bits in this Boolean circuit setting with coefficients 0,+/-1, since the number of directed paths is at most exponential in C). For a single changed source bit the endpoint is its signed edit times the corresponding pair-specific covector coordinate. For multiple source edits, all terms must remain in the joint paired geometry. This is reverse-solving which actual source directions contribute to a terminal change, not a procedure that finds a nonempty gain fibre without knowing either endpoint. Delta G=+1 means a new actual source-gain witness on u'; -1 means a previous gain on u; zero can be 0->0 or 1->1 and can retain many nonzero interior residuals. G itself is a gain predicate between original formula and its added unit; a source edit of G is a second revision index, not the original unit-gain sign. Keep original support independent of scalar zero.

### G158 — six-face direction and mixed source-revision square

For two distinct original source bit edits i,j let v00,v10,v01,v11 denote actual four executions on the same graph and define M_v=v11-v10-v01+v00. Let the i-oriented secants on the j=0 and j=1 edges have coefficients (alpha0,beta0) and (alpha1,beta1). Then M_v=alpha1 M_a+beta1 M_b+(alpha1-alpha0)(a10-a00)+(beta1-beta0)(b10-b00). This follows by subtracting the two exact edge equations. The last terms are the signed change in transport, a genuine mixed revision residual; one cannot use only a frozen baseline derivative. At the terminal, (G11-G10)-(G01-G00) = (G11-G01)-(G10-G00)=M_G. The two source edit paths agree at their actual terminal execution because the edits commute on distinct input coordinates and the deterministic graph is fixed; their increments need not agree. A complete indexed cube can use execution time, original source edit and consumer projection as axes; time-specific geometry and pair-specific covectors must be transported before comparing faces. This tranche tests source-edit squares and pairwise gate transport, not every face of such a full cube. Separate indices: original source/label and literal, source revision i,j, physical computation time, tape site, machine state/symbol, policy and clock, chart/refinement, actual history, coefficient ring/precision and consumer. Retain original zero mode, signed residual and inhabited neutral support. No silent identification of terminal equality with internal transport equality.

### G159 — reverse Clay endpoint and limitation

The geometry provides an exact endpoint residual and a shared repair route on the actual supplied bounded verifier. It does not establish that any such residual is nonzero on arbitrary code, or that the verifier must be implemented by this graph. G128 remains the exact alternate endpoint: total computable B(e) with Bad(e) -> mu(e)<=B(e), full code and clock needed (G146). Alternatively force a genuine G122 unit gain for every clocked e. A finite secant on a candidate that rejects all relevant unpinned sources may still have neutral terminal values while interior state changes. No sign, influence cone, expanded separator width, number of gate changes, or independently counted paths proves unrestricted complexity. Permit arbitrary preprocessing, source re-access, recomputation, nonlinear geometry and sharing. The next maximum cut is an actual uniform source-derived obstruction, while pursuing paid joint conditional contraction on the actual tape factors as a supporting route; do not turn the latter into compulsory endpoint infrastructure.

### G160 — executed exact regression and repository-only acceptance

Executed exact JavaScript/BigInt in current tool runtime, using the actual G151 compiler code copied from the verified blob through its compile function (no changes to that producer); new script scripts/check_p0_tape_secant_geometry_20261124.js, identical readback blob e316d137c2ed2aef86481c32b35c735b56e8f3bb in both repositories. Fixed original n=2,3,5 width<=2 source universes, same three machine-table kinds and clocks 0,2,5, two fixed original literal choices per graph; 1,008 seeded source pairs of distinct bit edits, four source corners each. Exact checks: 5,040 paired backward endpoint contractions, 10,787,260 local signed gate identities; endpoint changes +1:73, -1:121, zero:4846; 1,008 mixed source-edit squares, 41 nonzero mixed residuals; 3,024 incremental update vs full lift comparisons, 172,548 dirty gate evaluations vs 6,472,356 full-lift gate evaluations for those same updates; the incremental reference still scans the full topological graph, so no runtime claim. 100,147 nonzero-adjoint gate visits and 228,793 changed gate occurrences across the five tested edges per square; 109 accepting source-corner gain witnesses verified against direct original clauses. Direct original candidate scores also checked at all 4,032 source corners. All assertions passed. No independent full weighted elimination or general native standard machine parser, no Agda/Lean kernel or CI, no elapsed-time benchmark. The full three-axis indexed cube and uniform deadline remain open. No other programme edits or chat files.

| Gate | Deliverable | Status |
|---|---|---|
| G155 | ordered exact finite signed gate secants | derived and tested |
| G156 | causal cone and exact changed-value repair | derived; repair implemented and tested |
| G157 | endpoint-first paired backward finite covector | derived and tested |
| G158 | mixed source revision square / transport-change residual | derived; terminal squares tested |
| G159 | uniform source-derived nonempty obstruction | OPEN |
| G160 | repository-only exact regression | passed |
| G134a | full native standard-machine symbolic compiler | OPEN |
| N4/N5 | unrestricted resource obstruction / universal clocked failure | OPEN |
| N6 | original Clay endpoint transport | conditional |

Next: geometry-forward through actual source/time/refinement faces, pay joint conditional contraction and support discovery on real factors, seek a uniform nonempty obstruction independently of the chosen representation. Maintain prior attribution and all independent indices. No Clay solvedness claim.


## 46. P0-G161–G166 — geometry-forward competing gain charts and causal output-cut obstruction (2026-11-24)

Standing direction GEOMETRY-FORWARD, steelman, BIDI, endpoint-first and reverse-solved; literal Clay P vs NP only. Input user G155–G160 and attached Langlands R184–R190 (source-derived separator discovery, BIDI witness, demand precision, competing primal/signed/affine charts; donor report only). Starting verified heads 7bf3c0dd41d3 / adc1fbb9395e. Reuse actual G151 symbolic tape compiler blob 5e42f76332430e31b27394e79f38ef6808675d9a; G149 locality/initial row/padding/selector owners, G113 original Shannon derivation, G110 opposite endpoint localization, G122 source gain, G128 explicit-clock deadline, G131 weighted backward boundary, G137 future invariant, G146 clock-only anti-control, G155 exact secant. Existing #1006 FactorsThrough, #1040 direct failure, #1129 standard machine, #1474/#1502 Cook-Levin, #1546 sharing and #123 JMD lowering with attribution remain authoritative. No other programme edits.

### G161 — actual primal, functional and consumer charts

A fixed bounded G151 graph computes the original Boolean gain G(u) with deterministic unique extension. Simplify constants, double negations, identical operands, commutative operand order and direct complementary pairs; retain only the actual terminal gate cone, while retaining ALL original source variables and their independent weights even if unused. Removing deterministic unused auxiliaries preserves weighted source mass because each source has one original lift before flag assertion. For the primal chart build actual local gate truth factors, terminal flag and original unary weights, then discover a min-fill elimination order with deterministic tie breaking. Multiply and sum over joint bag assignments in the numeric ring and independently OR/AND over Boolean support (weights do not filter original support). Store actual compatible eliminated-bit choices for each inhabited message; reverse elimination reconstructs original source and deterministic gate values, re-evaluate original candidate and refined assignment. Charge graph discovery, max multiplied scope, factor accesses, state storage, indexing and all weight/bit costs. This is independent variable elimination on the simplified actual gate graph, not merely summing lifted flags. No guarantee of optimal geometry.

### G162 — exact future-consumer quotient, not sampled equality

For fixed original source order and depth k, residual R_p(z)=G(pz) on remaining source bits; p~q iff R_p=R_q as Boolean functions. This is a right congruence for the next bit and is the coarsest exact deterministic layered quotient for that order (any common state with identical future transitions and terminal output requires equal suffix functions). Compile symbolic cofactors of the actual simplified Boolean DAG, hash structural identities, then merge backward by the ordered pair of exact successor keys, with terminal keys 0 and 1. Distinct source prefixes may merge; retain weighted incoming sums and independent inhabited predecessor words, never interpret a sum as a genuine word. For each layer shared weights indexed by its actual source bit give backward mass w0*Z0+w1*Z1 and support OR; a support path reconstructs the original source even with zero numerical mass. Exactness by induction over remaining bits. Constructed and compared forward/reversed source orders, not a compulsory ordering or universal finite rank. The structural cofactor graph may be much larger than the minimized semantic quotient; charge discovery/memoization. Fixed width and source order cannot imply arbitrary machine lower bound. First implementation caps maximum multiplied bag size at 14 and each cofactor layer at 4096 distinct roots; reports joint comparison stop if ANY chart exceeds its cap, does not identify individual failing chart. It still attempts the three charts separately before reporting a joint stop. Pin partition tests in that implementation are numeric only (weight zeroing excludes mass, not source support).

### G163 — source-derived causal output cut and signed independent products

For the actual single-tape G151 submodel on canonical unit-then-binary clause selectors, fixed literal l is one of the first 2n unit bits. On fixed nonempty input length m, a T-step head starting at 0 can read original nonnegative positions only in 0..T-1; output reads cells 0..n-1 at halt (timeout zero), and anchor depends only on first 2n unit selectors. Consequently fixing K={0,...,k-1} with k=min(m,max(T,n,2n)) determines both original outputs x,y under the same fixed literal refinement, including fully pinned override; this is a safe superset of actual read support, not an optimal cut. Fix cut assignment c, w(c) its unary product. Let A_c(x), A_c(y) denote satisfaction of all selected clauses in K, using original selectors; separately require l(y)=1. For each free source selector i outside K, define L_i(y)=w_i(0)+w_i(1)C_i(y), L_i(x,y)=w_i(0)+w_i(1)C_i(x)C_i(y). Exact gain scalar:
Z=sum_c w(c) A_c(y) l(y) [ product_i L_i(y) - A_c(x) product_i L_i(x,y) ].
Proof: on each output fibre revised acceptance is a product of independent selector filters; intersecting with original acceptance gives the second product. The difference removes exactly the simultaneous-acceptance sector; no division, no full SAT assignment mask or enumeration of free selector suffix. Works over any commutative ring, including zero divisors. Independent support: require A_c(y)l(y) and a legal free selector value for each coordinate, then either a fixed original clause fails on x or at least one free clause false on x can be selected while true on y. Choose such an actual selector and complete others legally to reconstruct a gain; no inference of emptiness from weighted zero. Arbitrary explicit source pins can be imposed by filtering each original selector's legal values. Prefix/suffix products yield all free-coordinate weighted marginals in O(m) ring operations per cut row, fixed-coordinate marginals accumulated once; zero weights do not erase support. Thus total O(2^k (m+cost of two actual bounded runs)) plus parsing and graph/weight/provenance costs, not polynomial in general. Source m=2n^2 for the tested width<=2 canonical universe; width<=3 analogue uses O(n^3) selectors with units first, but not executed. The source cut can be full for a sufficiently large clock or a different machine/encoding. This contracts source coordinates rather than merely optimizing the large tape gate graph. No universal SAT evaluator or bound.

### G164 — reverse endpoint on output fibres and unread-clause obstruction

Let a selector subcube have fixed base formula F_p (all free selectors off), and suppose normalized output x is constant throughout that subcube (not merely its verified score). Completeness on that subcube iff (i) F_p UNSAT, or (ii) x satisfies F_p and for each free clause C false on x, F_p AND C is UNSAT. Proof: if F_p inhabited but x fails it, base is a missed witness. Otherwise any missed satisfiable extension contains a free clause false on x, hence that single-clause extension is satisfiable; conversely such a single-clause extension is itself a missed witness. This is an exact restricted criterion, not a free test of satisfiability of F_p AND C. In particular on the empty-source fibre, every individual nonempty non-tautological clause is satisfiable. If a free selector C is false on the constant output x, selecting C alone forces an actual false negative, construct a witness by making any literal of C true, then append that witness's original units and use G110/G122 anchor bisection to recover a specific genuine unit gain. This is a direct source-derived obstruction for a restricted observation geometry, not a universal one. For the tested prefix cut, a whole unobserved four-clause sign block for a pair of variables suffices since one clause of that block is false on every x. More generally any deterministic sound assignment producer on dense width-r selector input, on the all-zero input, must inspect every selector of the binom(n,r) clauses falsified by its returned x if it is to be complete (unqueried source bit flip leaves computation/output unchanged under ordinary bit-probe semantics; normalized unit anchor either counted or irrelevant for r>=2). This gives only Omega(n^r) probes, linear in the dense input size for fixed r, not a superpolynomial separation. Arbitrary source access, nonlinear representations, shared computations and longer clocks can bypass the short observation cone. The source-sensitivity obstruction does not force a gain for a general polynomial candidate. The finite deadline from G128 still unpaid.

### G165 — paid geometry comparison and acceptance

Two exact JavaScript regressions executed in tool runtime on the verified G151 compiler copied through compile(), no edits to original producer. scripts/check_p0_competing_gain_geometry_20261124.js blob 5aa231356c1982af7dd1a86383ee04d5db9dae5c: 10 graph fixtures, 30 ring/weight comparison attempts (mod 2,8,17), 15 complete three-chart comparisons on five n=2 graphs; 15 joint cap stops on n=3,5, not a failure of math or lower bound. 3840 direct source cases, 45 original witnesses decoded across the three charts, 9 inhabited zero samples, 5 numeric pin partition checks. For successful n=2 graphs original gates 99..2923, live simplified factor gates 57..67, max multiplied scope 14, 132798..150622 factor accesses in bucket products, discovery pair checks 46707..64725, exact forward semantic peak 2..3 and reversed peak 2..4. Raw cofactor states and discovery are paid separately; no elapsed-time performance claim.

scripts/check_p0_causal_output_cut_20261124.js final blob 5a49eeb8536009b327e584aac89aab2cb3f7dcab: 11 fixtures n=2,3,5,7, fixed original literals and small clocks 0,2,5, same original machine kinds; 31 ring/weight runs, 265984 direct enumeration comparisons (all 256 sources on five n=2 fixtures times three regimes, plus one complete 18-bit n=3 clock-zero mod8 fixture), 1360 marginals computed and sum-checked, 276 of those independently brute-compared, 40 independent conditioned-marginal checks with explicit pins, 1408 sampled paired output invariance checks, 31 support witnesses verified in original direct run and compiled lift, 23 inhabited zero endpoint samples. Largest n=7,m=98,T=2 fixture: 14 cut bits, 16384 cut rows, 254 rows retained after revised cut check, 248106 modular multiplications including all marginal products, 126 inhabited zero cut rows. All 2^98 original source words represented by the product formula; NOT independently enumerated, nor general factor elimination on that largest graph. n=5,m=50,T=2: 1024 cut rows, 62 retained, 29290 modular products. Metrics exclude machine execution, geometry discovery, allocation and runtime. Unread-clause forcing: 36 short-clock fixtures, 35 forced original failures and genuine unit-gain witnesses, one unforced because no suitable unread falsified clause; 77 midpoint score evaluations in bisections. The test also precomputes full path scores as an independent control, so 77 counts only midpoint calls not total test calls. No universal nonemptiness result. All assertions passed and final identical blobs verified in both branches.

### G166 — endpoint and independent index ledger

| Gate | Deliverable | Status |
|---|---|---|
| G161 | actual simplified gate factor min-fill and witness backsubstitution | implemented; bounded controls passed |
| G162 | original-order and reverse-order future-consumer quotient | implemented; bounded controls passed |
| G163 | causal output-cut signed contraction and shared marginals | derived, implemented and tested |
| G164 | restricted original output-fibre completeness criterion / constructive unread-clause failure | proved within stated scope; 35 witnessed |
| G165 | repository-only exact regression | passed with explicit comparison caps |
| G166 | full-code uniform source-derived obstruction | OPEN |
| G134a | native standard-machine symbolic source/parser/clock correspondence | OPEN |
| N4/N5 | unrestricted resource obstruction / universal clocked failure | OPEN |
| N6 | original Clay endpoint transport | conditional |

The genuine next geometric question is whether every polynomial source computation can be forced into a nonempty missed-witness fibre despite adaptive full source access, arbitrary nonlinear quotient, source revisits and sharing. Fixed short-clock output cut and fixed source order are restricted models, not mandatory. Need an unconditional code-sensitive finite obstruction or equivalent universal gain theorem, not larger regressions. Keep original source/literal, output fibre, actual time, tape position/state/symbol, source revision, chart/refinement, source order, weighted precision/ring, zero mode, signed residual, inhabited neutral support, provenance, consumer separate. No complete six-face cube execution, native Agda/Lean kernel, CI, general machine compiler, adaptive low-precision producer or elapsed-time benchmark in this cut. No chat files, no Langlands or unrelated branch changes, no Clay solvedness claim.


## 47. Endpoint maximum cut — one universal resource frontier, adaptive affine incompatibility, and full-code deadline growth (2026-11-24)

USER DIRECTION: stop taking small bites. Replace incremental bounded-regression milestones as P0 with broad theorem cuts aimed at literal Clay P vs NP. Geometry-forward, steelman/BIDI/reverse-solve, original labelled source, zero mode, signed residual, inhabited neutral and independently indexed hyperfabric remain mandatory. The bounded compiler, G161–G166 competing chart tests, and Langlands R191–R197 mixed affine/incidence extraction are supporting mathematics, not mandatory serial prerequisites. Starting verified heads bf355d0c26f7 / 9c4eda439fe3. Actual reopened owners: DASHI/MDL/CodeLengths.agda (38a879891c1e1f8b2a7e5788a43c29dd4daec715), DASHI/Combinatorics/FractranComputationEquivalence.agda (e9f8156806f04efe9bde510acbf9b7b46d310348), PNotEqualsNPDirectSATLowerBoundExact (0838b3252b3ffb91993e4cb47a5d5c06a00e4fe1), PNotEqualsNPStandardFiniteCandidateCodeExact (edbaa4d1fd2849f5d48635c27daf983e387f835d). The MDL owner is a code-length carrier, not already a universal time-bound theorem; FRACTRAN owner explicitly requires a representation witness and does not assert arbitrary program coverage. Reuse G105–G114 Shannon localization, G122 source gain, G126–G130 clocked deadline, G137–G142 finite invariant, G146 clock-only anti-control, G164 output-fibre obstruction, older G6/G48 unrestricted uniform route and G38 stronger nonuniform route, #1006 FactorsThrough, #1040 direct failure, #1129 standard machine, #1474/#1502 Cook-Levin and #123 JMD FRACTRAN/MDL lowering with correct attribution. Levin-style universal search and Gaussian elimination are standard mathematics, not claimed new inventions. No Langlands branch modification.

### A. Unrestricted resource geometry: remove the candidate-by-candidate quantifier

Fix an ordinary efficiently universal binary program machine U with polynomial simulation overhead for each standard finite program, and a canonical ordinary 3CNF source encoding F of bit length N with polynomially bounded assignment length. U(p,F) is partial; a candidate witness is accepted only on actual termination with a valid full assignment satisfying F. Include simulation/verification/encoding costs in overall bounds; choose an ordinary machine whose tape operations have polynomial bounded universal overhead (no free huge-integer step). The program receives F as original input. Define kappa(F)=min over verified halting p of |p|+ceil(log2(t_U(p,F)+1)); infinity if no witness. The feasible region R_F={(L,T):exists p of length<=L halting within T steps with a verified witness} is upward closed, with independent program length and time axes. Its empty case is genuine UNSAT; a bounded budget can have empty intersection with an inhabited R_F. The logarithmic scalar is a particular endpoint consumer of that region, not a replacement of its two axes.

For integer b>=0, universal budget evaluator E_b(F) enumerates every binary word p of length l<=b, simulates for at most 2^(b-l)-1 U steps, and verifies any output. Invalid code, nonhalting, malformed output and failed verification never accept. E_b(F)=1 iff kappa(F)<=b. It is monotone in b and returns an original witness on acceptance. Across all code lengths the sum of simulation steps is at most (b+1)2^b (plus code enumeration, bounded interpreter overhead, verification, output lengths and original input costs). Prefix-free code may sharpen the ledger but is not assumed. For fixed integer c take b_c(N)=floor(log2((N+2)^c)), exactly computable; b=O(log N), so this is a polynomial algorithm for each c. It need not be polynomial when c is part of the input. If P=NP, standard SAT search-to-decision gives one fixed polynomial witness-producing program p, hence for some c every satisfiable F has kappa(F)<=b_c(N), absorbing constants. Conversely if such c exists, E_b_c decides SAT. Thus literal Clay equivalence:
P!=NP iff for every integer c there exists a satisfiable F with kappa(F)>b_c(|F|).
This is standard conditional Levin-search reasoning applied to the original source and resource hyperfabric. It admits arbitrary ordinary finite-program computations, sharing, nonlinearity, repeated source access, and recomputation. No universal interpreter imported into native Agda/Lean here. It is not a claim that time-bounded description complexity has a known superlogarithmic lower bound on SAT witnesses.

For a fixed c, define E_c=E_b_c and H_c={F:SAT(F) and E_c(F)=0}. E_c is polynomial, H_c in NP (original satisfying assignment plus deterministic negative budget check), disjoint decomposition SAT=E_c^{-1}(1) union H_c. If H_c is nonempty it is NP-complete: fix any F_c in H_c; polynomial reduction r(F)=F_c if E_c(F)=1, else F. Then F SAT iff r(F) in H_c. Fixing F_c is an existential constant for each c, not an unconditional uniform generator across c. If P!=NP, every H_c is infinite: any finite exception list could be hardwired into E_c to decide SAT in P. Thus for every c and every cutoff there exists a longer missed inhabited formula. This is a stronger useful endpoint constraint: filtering all budget-easy witnesses leaves an NP-complete residual whenever nonempty, not a gradual proof that the residual disappears or a proof that it stays inhabited.

Normalize a bounded universal producer W_c to use its found witness, otherwise a fixed polynomial default with G122 fully-pinned anchor. For sufficiently large fixed c the budget includes the fixed program for that default/anchor (absorb its polynomial runtime and code length), so on H_c the normalized producer still rejects. For any finite set of actual polynomial producers, increase c enough to include their fixed program lengths and polynomial runtimes for all N. A formula in H_c then defeats all those producers simultaneously by direct verified rejection. More generally an individual program with |p|+ceil(log2(t+1))<=b_c cannot produce a witness there. Given the actual missed witness, G110/G122 recover a specific original unit gain for every anchored missed producer along its source pin path; the gain edge can differ by candidate. Under P!=NP this supplies arbitrarily long simultaneous counterexamples to any fixed polynomial budget, but does not unconditionally produce them. Under P=NP some H_c is empty and every larger budget covers SAT. For nonuniform advice/circuit algorithms, the description may be polynomial length rather than O(log N); do not conflate polynomial circuit size with short uniform program descriptions. The earlier nonuniform stronger NP not subset P/poly route remains sufficient, not required.

### B. Adaptive affine source-observation geometry and exact rank obstruction

Canonical dense width-r universe (exact r distinct variable scopes with all signs) has M=2^r binom(n,r) selectors. For any assignment x let B_x be the falsified-clause set and S_x={u:u_i=0 for i in B_x}; SAT selector support S=union_x S_x. For any deterministic candidate whose output is constant x on an arbitrary transcript fibre A, completeness on A iff A intersect S subset S_x. This is exact without any chart assumption. For an affine transcript A={u:Lu=b} over F2, an incompatible source exists iff there are y and i in B_x minus B_y such that linear system Lu=b, u_(B_y)=0, u_i=1 is consistent. Forward: a satisfying source missed by x has a true selected clause false on x; backward: solve the system and return original source u and assignment y, verify both. For fixed y the linear systems are polynomial in explicit M and L size, can exploit a single elimination/affine solution basis to test all relevant coordinate projections. Searching y remains a nontrivial existential problem. Do not treat numerical zero or low rank as absence of support.

On the empty-source transcript u=0 of a deterministic adaptive parity-query algorithm, let L contain the actual queried rows on that transcript and x be its returned assignment. An adaptive next query may be an arbitrary deterministic function of prior answers. If rank(L restricted to B_x)<|B_x|=binom(n,r), take nonzero delta supported in B_x with L delta=0. On source delta the entire adaptive transcript and output remain identical, by induction (each queried row is the same and its answer unchanged). Every selected clause is false at x and true at complement y=not x; at least one selected clause exists. Thus original F_delta is satisfiable and x rejects, with a constructive original witness y. Fully pinned normalization is irrelevant on these exact-width r>=2 sources (there are no unit pins); or count anchor observations if other encodings are used. In the surrounding ordinary 3CNF carrier (r=2 or 3), append y's original pins and use G110/G122 to find genuine unit gain from missed source. This proves rank and number of binary parity queries >=binom(n,r) on the zero transcript for complete search in this query model. It is linear in dense input length for fixed r. A nonlinear observer can combine many coordinates into one Boolean OR test at explicit computation cost, and an unrestricted machine can read all coordinates. No superpolynomial bound or mandatory global affine geometry.

Sharp anti-control: even an explicitly supplied homogeneous one-dimensional source fibre can make incompatibility NP-complete. Given arbitrary 3CNF F, add fresh unit z (and an unused declared dummy if needed to avoid fully pinned override), form its nonzero selector vector v. Let A={0,v}=span(v) and x=all zero. At 0 x satisfies the empty formula. At v x violates the added unit; there exists y satisfying that source iff original F is satisfiable. Thus deciding existence of an incompatible inhabited source on a supplied one-dimensional affine fibre with fixed x is NP-hard, in NP by source+assignment witness, and deciding absence is coNP-complete. Encoding v or linear basis polynomial in canonical selector universe; no implication that the fibre is an actual trace of every candidate. This illustrates why affine compression alone does not discharge the nonlinear acceptance consumer. Width<=2 finite line controls below test identity only; unbounded hardness uses width<=3. A low-dimensional interface can be cheap to enumerate but the original SAT truth remains hard to establish. No assumption of P!=NP in these equivalences.

### C. Full-code deadline growth and hard-witness generation boundary

Retain exact G128: existence of total computable B(e) bounding mu(e) (first parent length with genuine unit gain) for each incomplete explicitly clocked valid code iff P!=NP. Define M(s)=max({mu(e):e valid, |e|<=s, Bad(e)} union {0}). For P!=NP, every valid clocked code is incomplete; finitely enumerate all codes length<=s and find first gain by exhaustive finite size search, so M is total computable. For P=NP, fix a complete polynomial witness producer W_* and clock. For ANY total computable f(s), encode the no-input machine M_s that writes binary s, computes f(s), waits at least f(s)+1 steps and halts. In a conventional efficient finite-machine encoding its description length is poly(log(s+2)) (fixed f-program plus O(log s) states/bit-literal setup with ordinary state labels). Use G128 delayed fallback construction: W_s on input length N simulates M_s for N-1 steps; before detection use W_*, after detection use W0; anchor independently. All branches are polynomial with an effective clock. A standard bounded interpreter overhead polynomial in code length and N, or direct finite-control embedding, yields a clock and compiled description of length poly(log(s+2)); encode its coefficient/degree in binary in the ordinary code format. Explicitly require this ordinary efficiently compositional encoding; pathological unary blowups not asserted. Thus |e_s|<=s for sufficiently large s. Since M_s halts at T>f(s), W_s incomplete and mu(e_s)>T by G126/G128. Therefore M(s)>f(s) for all sufficiently large s. Under P=NP the finite maximum first-gain function eventually dominates every total computable function; under P!=NP it is computable. This is a conditional growth dichotomy, not a proof of either case, not a bound on actual SAT runtime, and not a claim that clock parameters alone suffice. G146 unconditional clock-only anti-control remains.

If P!=NP, choose by effective exhaustive search a sequence (F_k,x_k) of strictly growing lengths N_k>=k with F_k satisfiable, kappa(F_k)>b_k(N_k), and original witness x_k. Search uses decidable finite bounded budget check plus exhaustive original witness search; conditional termination follows from infinite H_k, not free construction. Suppose a single generator on input k outputs these same pairs in time polynomial in N_k (or N_k+k). Then a program containing binary k and fixed generator can ignore its F input, run generator and return x_k. Efficient standard encoding/simulation gives description O(log(k+2)) and runtime poly(N_k), hence kappa(F_k)<=C log2(N_k+2) for a constant C, contradicting the chosen resource frontier for sufficiently large k. Thus no output-polynomial generator of verified witness pairs for such a diagonal hard sequence exists. This does not forbid efficient generation of hard formulas alone, nor require a proof of P!=NP to include an output-polynomial witness generator. It is an exact anti-control on demanding constructive witnesses at the same budget whose impossibility we seek to prove. Do not confuse computable existential counterexample search with polynomial generation, or impose the latter as a Clay prerequisite.

Plain counting of assignments or of absolute descriptions cannot prove the required conditional resource lower bound: e.g. every n-bit vector occurs as the unique satisfying assignment of the n original unit pins specifying it, yet one fixed linear/polynomial program reads those pins, yielding kappa=O(log N) for all such formulas. Affine systems with an explicit full-rank solution have the same shared bypass via Gaussian elimination. Any claimed endpoint invariant must exclude this anti-control and must account for formula-conditioned computation, not only number of possible witnesses, rank, source width, chart cardinality or expanded circuit size.

### D. Acceptance and controlling next mathematical cut

Actual exact JavaScript/BigInt tool-runtime regression scripts/check_p0_universal_resource_affine_maxcut_20261124.js, matching verified blob c8a4f4eedd3ad680996a69c4549e16a680d6f0ed in both repos. 512 affine-fibre comparisons (128 seeded systems on all 8 width<=2 original selectors, all four fixed outputs), 26,692 feasible source/output cases enumerated, 379 incompatible fibres, 56 empty affine fibres, 33 inhabited fibres with correct output throughout (remaining nonempty no-failure fibres have no satisfiable source). 144 adaptive parity kernel witnesses on n=3..8, exact widths 2,3, up to 448 selectors, 524 original zero-transcript queries and matching replay; all decoded witnesses checked against original clause semantics. 256 exact dimension-one fibre finite reduction controls. Universal budget control is a deliberately finite 4-bit opcode interpreter (272 programs of length one/two opcodes, explicit jumps and bounded nontermination, 256 original source formulas, budgets 0..11), NOT a universal TM or a general polynomial SAT solver. 3072 exact budget/minimum description-time comparisons, 294912 budgeted executions, 2816 monotonicity checks; 350 budget-accepted inhabited cases, 790 budget-missed inhabited cases and 1932 unsat cases. Finite results do not test NP-completeness, undecidability, eventual dominance, or universal nonemptiness; those are the mathematical derivations above. No native Agda/Lean checks or CI, no general universal interpreter or machine coverage port, no runtime benchmark. No chat artifacts.

P0 controlling deliverables (supersede micro-gate cadence, retain prior gate identifiers for provenance):
- Direct unrestricted route: prove the universal conditional description-time frontier has superlogarithmic worst-case growth on satisfiable original formulas, or equivalently prove every H_c nonempty. A code/time budget is an admissible universal geometry, not a new necessary technique if another proof works. Need actual noncircular lower-bound theorem; not more endpoint equivalences or bigger finite samples.
- Full-code finite-obstruction route in parallel: prove total computable upper bound on first genuine gain for explicit clocked descriptions, or otherwise produce universal direct SATDecisionFailure. Clock-only, finite hardcoded exception, affine rank, restricted linear representation, frozen chart, and arbitrary shared computation anti-controls are mandatory. The conditional M(s) dichotomy explains why an actual bound would settle Clay.
- Opposite-direction steelman: seek a uniform short-fast witness programme / paid scalar contraction and uniform hitting set giving P=NP, not presume separation. Distinguish RP=NP, P/poly and P=NP. General weighted/affine contraction and chart discovery remain donors, not compulsory representation.
- Supporting implementation only when it tests a new mathematical implication or pays a genuine missing cost/coverage obligation. Native standard-machine/compiler and proof-assistant transport remain open but not a substitute for endpoint theorem. Complete original six-face cube / bounded weighted contraction not a blocking prerequisite for an independent successful proof.

N4/N5 remain OPEN. N6 conditional transport through the original direct owner. No Clay solvedness claim. Preserve all previous roadmap work, zero mode, inhabited neutral support, signed residual, original source and independently indexed program length/time/refinement/precision/consumer. Do not modify other programmes.


## 48. Endpoint maximum cut — quantitative clocked obstruction lower bounds and resource-closed external self-repair (2026-11-25)

User direction: stop small bites. Literal Clay P vs NP remains the objective of this thread. The attached Langlands integrated restricted pipeline through R208 (reported #1549/#120 heads 9fbb619f5f01 / 8a3e837d809e) is a donor: direct residual/crossing-space geometry, paired old/loss/common/new support, complete specified source/pin/precision cube and paid precision planning. No independent verification of those Langlands commits in this tranche and no modifications to those branches. Live starting P vs NP heads bdb74f190ddb1792bc5451cbb621ec19a80571ca / 24430459e46b1be6a49571fa3b9f6b65d08b5a0e. Reuse Section47 universal conditional description/time frontier, G122 source gains, G126–G130 delayed/clocked deadline equivalence, G137–G142 finite underapproximation, G146 fixed-clock-only no-go, G164 output fibres, G149 native source/tape boundary, #1006 FactorsThrough, #1040 direct failure, #1129 standard machine, #1474/#1502 Cook-Levin and #123 JMD FRACTRAN/MDL lowering with attribution. Standard background only: deterministic time hierarchy and EXP/2-EXP classes; Kleene syntactic self-reference and specialization (https://plato.stanford.edu/entries/recursive-functions/). Do not claim the ordinary Kleene theorem alone provides quantitative resource closure. These are new mathematical cuts on the explicitly specified code carrier, not claims of novelty in complexity literature or a Clay solution.

### A. Exact model and encoding boundary

Work with syntactically valid explicit clocked descriptions e=(p,c,d) in the Section47/G128 carrier: a normalized assignment producer on ordinary canonical 3CNF source F of encoded length N, run with clock c(N+1)^d, deterministic fixed incomplete fallback W0 on timeout/malformed output, and direct evaluation/fully pinned anchor. Inputs have polynomially bounded declared variable count, legal unit refinements have polynomially bounded encoded length, and ordinary deterministic bit-machine simulation has polynomial overhead in code, input and bounded time. This is the clock-wrapper carrier, not a language whose input must contain a proof of candidate correctness or an Agda proof object. The candidate may actually obey its clock; all lower-bound reductions below construct such candidates after choosing sufficient constants. If the original native clock carrier encodes Nat values in unary or includes different costs, do not silently transfer quantitative bounds without an encoding receipt.

For the strongest quantitative statements use a conventional compact binary description: fixed code with binary literal data of length k can be specialized in O(k) description bits (plus at most linear self-delimiting overhead); c,d binary, with efficiently computable pairing, quotation and specialization. A raw finite-state transition table might use O(k log k) or other polynomial overhead. State explicitly when weaker stretched-exponential bounds follow. Clock degrees/coefficient are fixed per candidate, not fixed across candidate descriptions unless stated. A candidate with a huge constant or degree is still polynomial-time in its own original input length; this does not make uniform simulation polynomial in code length. All original inputs and actual output assignments verified; no numeric cancellation or coarse terminal observation substitutes for support.

Use W0 that sets unpinned coordinates to zero and respects original units (conflicting units resolved deterministically; direct score rejects). On canonical distinct-clause family F_m=(x1 OR x2) AND ... AND (x1 OR xm), W0(F_m) rejects, W0(F_m AND x1) accepts. Both formula lengths grow. Duplicate-free unit append is deterministic; if same encoded source, gain necessarily zero. This gives an infinite supply of explicit fallback gains, unaffected by finitely many patched parent/revised source encodings.

### B. Unconditional quantitative lower bound on first obstruction length

Let mu(e)=min parent bit length of a genuine gain G_e(F,l)=1 on an incomplete clocked candidate, and M(s)=max({mu(e): |e|<=s, valid and incomplete} union {0}). For each integer k>=1 set K=2^k. Compile W_k: solve every valid input F with N<=K by exact exhaustive assignment search (return an arbitrary assignment if unsatisfiable), and use W0 beyond K. Retain pinned anchor. No gain with parent N<=K: correct verified parent either accepts or is truly UNSAT, so an accepted refined formula is impossible in the latter case. For sufficiently long F_m and F_m AND x1 both outside cutoff, fallback gives actual gain. Thus mu(e_k)>2^k.

If the declared assignment length is O(N^a) for a fixed a>=1, the exhaustive prefix including standard simulation/verification overhead is bounded by 2^{C K^a} times polynomial factors, for suitable fixed constants. Choose binary degree d_k >= C' K^a plus sufficient fixed fallback degree so that for all N>=1, (N+1)^{d_k} >= 2^{d_k} covers the entire finite exceptional cost and input/literal setup; beyond cutoff ordinary fallback has its fixed polynomial runtime. Adjust c to absorb fixed implementation constants. K and d_k have O(k) binary bits; the compiler stores K as binary literal in otherwise fixed program, so |e_k|=O(k) in compact binary carrier. For all sufficiently large s choose k proportional to s small enough that |e_k|<=s; hence M(s)>=2^{Omega(s)} unconditionally. With polynomial-size literal embedding O(k^q) get M(s)>=2^{Omega(s^{1/q})}, still superpolynomial; for O(k log k) get 2^{Omega(s/log s)}. This is an actual lower bound on any uniform first-gain deadline as function of compact code size, including candidate clock tag, independent of P=NP. Not a lower bound on SAT runtime or proof that computable deadlines fail (G128 remains exact). With unary d or fixed degree this specific exponent construction does not establish the same code-length lower bound. A finder emitting literal original source necessarily has output-length lower bound on these candidates; compressed counterexample descriptions are not literal source witnesses until decoded and verification cost paid.

### C. Exact complexity of bounded failure on a FIXED original source domain

Fix a constant N0 large enough to contain the parent of a known W0 gain and choose a fixed cutoff R0 >= N0 large enough to contain both parent and refined instance of that gain. Define B_N0(e) iff there is a genuine original unit gain with parent bit length <=N0. Even if every supplied e is incomplete, exact decision of B_N0 has the following complexity under polynomial-time many-one reductions in code size s:
(i) for c binary and a common fixed sufficiently large degree d0 (covering W0, normalizer and finite-source operations), EXPTIME-complete;
(ii) for c,d binary with variable d, 2-EXPTIME-complete.
In particular these are not P-hardness assumptions from SAT, but unconditional uniform computation lower bounds by deterministic time hierarchy. Use EXP=union_a DTIME(2^{s^a}) and 2-EXP=union_a DTIME(2^{2^{s^a}}).

Upper bounds: finite constant number of legal parent/refined source pairs; even refined bit lengths are bounded by a fixed constant R' since N0 fixed and original encoding effective. Simulate actual normalized candidate on both and evaluate. Binary c,d <=2^{O(s)}. Fixed d0 gives time <=2^{poly(s)} including bounded interpreter overhead; variable d gives c(R'+1)^d <=2^{2^{O(s)}} before polynomial overhead. Invalid code rejected by syntactic parser. No correctness certificate required.

Hardness: let L be any language decidable in the target time class and z its input. Compile p_z with z as literal data and a fixed simulation of the L-decider. For valid source length N<=R0 simulate decider on z; if it accepts use W0, otherwise use a fixed finite correct assignment table for all such sources. For N>R0 always use W0. Anchor and direct verification unchanged. On rejection, every parent with N<=N0 is correct, so B_N0 false even if its refined length exceeds R0. On acceptance the selected known fallback gain has both source lengths <=R0, so B_N0 true. In both cases arbitrarily long fallback gain remains, so all reduction outputs satisfy incomplete promise. Program and z literal have polynomial code size. If decider time <=2^{poly(|z|)} including simulation/encoding overhead, encode sufficiently large binary c=2^{poly(|z|)} (binary representation polynomial length) and fixed d0. If time <=2^{2^{poly(|z|)}}, choose degree d >=2^{poly(|z|)} with binary representation polynomial length and suitable c; for all nonempty valid encoded sources (N+1)^d>=2^d covers simulation. Use polynomially large enough exponents/coefficients to cover all overhead; cutoff finite table and fallback fixed. Thus reductions are polynomial-time and B_N0(e_z) iff z in L. No call to unknown SAT solver, since finite table domain is fixed independent of z. For fixed degree statement choose d0 covering the fixed normalization/fallback (not every smaller degree). The fixed-source-domain decision hardness applies to uniform candidate-code analysis, not to SAT itself. In particular no uniformly polynomial-time construction of a support-faithful bounded-gain chart followed by uniformly polynomial exact support test can work for all such codes, even when source bound fixed, unless it contradicts time hierarchy. A tiny chart can exist after expensive discovery; this is a paid construction obstruction not an intrinsic width lower bound. This does not rule out a total COMPUTABLE full-code failure deadline, and does not prove the Clay endpoint.

### D. Fixed-degree external finder no-go via resource-closed syntactic self-repair

Claim in compact efficient quotation carrier: no deterministic algorithm A, guaranteed to return an actual original gain pair (F,l) on every incomplete valid clocked description of a common sufficiently large fixed degree, can have worst-case time 2^{o(s)} on that promise. It need not return the satisfying assignment. Polynomial-time finders excluded in particular. The result is independent of P vs NP and independent of the variable-degree long-counterexample construction in B.

Proof with actual code and budget separate. Fix the hypothetical finder A as code. Choose an efficient ordinary syntactic specialization function spec(Q,data) embedding data in fixed program Q. A fixed template Q on parameters (q,k) and input H constructs the exact complete description e_k=(spec(q,(q,k)),c_k,d0) with q equal to the literal template Q; compile e_k=(spec(Q,(Q,k)),c_k,d0). This is explicit self-description via quoted template data; no need to evaluate A or solve its fixed point when creating code. Choose c_k=2^k (allow fixed constant slack by increasing binary exponent) and fixed d0 sufficiently large for the computations below. Compact tag length k+1 and fixed template/binary k specialization give |e_k|=O(k); computing its own complete description costs poly(k) and includes the clock tag. Ordinary polynomial-overhead deterministic simulation and parser must be paid. Fix large constant D so that simulating A for at most 2^{floor(k/D)} steps, processing its output of bounded length, code generation, comparing source encodings, unit append, evaluating W0 and original clauses, and normalization cost <=2^k(N+1)^{d0} for sufficiently large k, including all implementation overhead. This follows from polynomial overhead in bounded step budget, k and input length; choose D and d0 once after fixing template/A and interpreter. Use explicit timeout and W0 fallback for other k; no unbounded recursion. No assumption A total on arbitrary invalid or complete descriptions. The quoted program calls A on e_k within that internal cap, uses deterministic fallback if no valid pair output.

If A produces a syntactically legal pair (F,l), set y=W0(F AND l) and patch only the exact parent source F: on H=F and F(y)=1 return y, otherwise W0(H). The direct pinned anchor never spoils the repair: on a fully pinned satisfiable parent it already accepts and on unsatisfiable parent no gain exists. On any different encoded child H=F AND l, W_e(H)=W0(H), with same anchor. If child encoding equals parent, gain identically zero. Otherwise if W0(child) accepts child, y satisfies F so parent patched to accept; if W0(child) rejects child, child score is zero. Either way G_e(F,l)=0. This works even if A returns no witness. Patch is deterministic and independent of actual input H except the exact comparison; no recursively evaluating its own revised run, no circular SAT oracle. On invalid finder output or timeout, fallback. Every e_k is incomplete (even without successful finder output), because only one source encoding may be patched; sufficiently long explicit F_m and F_m AND x1 both outside it give fallback gain. Under the claimed correctness/time promise, A(e_k) must eventually halt and return genuine gain within 2^{floor(k/D)} steps, since |e_k|=O(k) and log runtime=o(|e_k|). For those k all code construction and repair costs fit clock, and the very pair returned has gain zero, contradiction. This is a resource-closed external counterexample-finder diagonal, not a Cook-Levin formula containing an opposite computation of itself. The exact syntax/efficient quotation assumption is essential for subexponential claim; polynomial description overhead alone suffices for no polynomial-time finder since cap exponential in k. Fixed degree may depend on A/interpreter; to formulate a single common fixed degree independent of all A, choose a standard fixed universal interpreter with fixed simulation overhead exponent and fixed parsing/normalization/patch algorithms, hardwire finder code as constant data, and choose d0 from these fixed operations; all A-dependent constants absorbed into sufficiently large k. Not claiming a no-go for every tiny degree. If a finder with polynomial-time runtime existed on the full syntactic clocked carrier, restriction to this family contradicts it. A total unbounded computable finder is not contradicted: its execution may exceed every chosen internal cap. Do not use this result to claim P=NP or P!=NP.

### E. Geometry-forward transport on the universal witness-resource frontier

Let R be any fixed deterministic polynomial-time source-to-chart construction (possibly mixed affine/incidence/residual Langlands chart), and D any fixed polynomial-time witness decoder with original verification, such that each returned valid chart witness decodes to an actual satisfying assignment of original F. For an inhabited chart input R(F) and verified chart program p returning a witness in time t, construct original witness program by storing p (self-delimiting O(|p|+log(|p|+2)) bits), computing R(F), simulating p on R(F) with ordinary polynomial overhead, decoding D and verifying on F. If |R(F)|<=poly(N) and output/decoder costs are polynomial in original/chart description and witness lengths, then kappa_original(F) <= C(kappa_chart(R(F))+log2(N+2)) for a fixed constant C (take minimizing p, include all overhead). If reverse uniform polynomial witness transport also exists, obtain the reverse inequality with log chart length, and a two-sided coarse resource comparison. If the chart is exponentially expanded or requires nonuniform expensive discovery, this conclusion cannot be applied. A uniformly constructible portfolio of polynomially many such chart choices and common decoder can be addressed by an O(log N)-bit index, still with the same form of resource bound; arbitrary long advice or a selected chart without a paid discovery mechanism does not qualify. A scalar-only consumer without constructive decoder needs separately paid original pin queries or another witness extraction method. Randomized detection with one-sided error yields RP-type conclusions only when paid, not deterministic P unless derandomized.

Under P!=NP, Section47 yields arbitrarily long inhabited F outside any fixed logarithmic resource budget. Therefore for every fixed uniformly polynomial chart portfolio and fixed c, arbitrarily long such F have NO chart in that portfolio admitting a verified witness with kappa_chart<=c log(N+2): otherwise transport gives cheap original witness. This is conditional hard-instance robustness under actual source-preserving polynomial chart transports, not a lower bound derived merely from crossing dimension or number of residual keys. Under P=NP, if chart witness search is polynomially verifiable and chart existence faithful, standard decision-to-search supplies a uniform polynomial producer. Preserve chart identities, original provenance and independent resource axes, not numerical equality as a proof of witness transport. B–D provide unconditional uniform code/clock/counterexample machinery lower bounds; E explains why restricted contractions do not discharge the unrestricted original conditional witness-resource lower bound.

### F. Actual acceptance, exact scope, and endpoint priority

Executed exact JavaScript regression scripts/check_p0_clocked_obstruction_maxcut_20261125.js, identical GitHub blob 5b7900134db4b851ec2922368c20185cc09e4f2a. Actual finite canonical two-variable source domain: all 1024 (parent,unit) pairs patched using W0(child), all proposed pairs eliminated (24 genuine initial fallback gains among them), every one of 1024 patched candidates still incomplete within the finite test carrier; 147456 fully-pinned anchor checks, 24560 genuine remaining gain witness verifications; six exact syntactic template/complete-clock-description reconstruction controls (binary coefficient length varying), two finite classifier branch controls. The quotation fixture uses a mock finder selecting an original fallback gain; it checks actual reconstruction and repair, not the existence of a correct uniform finder. Tests do not execute exponential clocks, prove time-class completeness, or validate full universal simulation; those conclusions are the mathematical reductions above. No native Agda/Lean kernel, CI, proof certificate compiler, timing benchmark, or chat attachments. No changes to Langlands or other programmes.

Major deliverables:
- Unconditional code-size first-gain lower bound (compact binary clocks): established within explicit encoding model.
- Exact fixed-bound uniform detection complexity (EXP / 2-EXP, binary clocks): established within syntactic clock-wrapper carrier.
- Resource-closed external finder no-go at fixed degree: established under efficient syntactic quotation and standard bounded simulation; finite patch controls passed.
- Original/alternate-chart conditional witness-resource transfer: derived; no general uniform polynomial chart producer constructed.
- Literal Clay N4/N5: OPEN. Section47 P0-A superlogarithmic conditional witness-resource lower bound on original satisfiable formulas, P0-B a total COMPUTABLE code-sensitive first-gain deadline or universal failure proof, and P0-C opposite-direction uniform polynomial witness producer remain controlling. Neither exponential code-size deadline lower bound nor high complexity of a finite bounded-failure question implies original SAT time lower bound. Under P!=NP, a total computable finder exists by exhaustive search, entirely consistent with new lower bounds; under P=NP, G128/Section47 deadline computability impossible. Do not confuse code-length resource geometry with original formula input-length geometry. N6 conditional original endpoint transport.

Next research should attack P0-A or P0-C directly, not try to optimize the impossible uniformly cheap external finder. A candidate-code lower bound can narrow the allowable proof route but is not a separation. Retain zero mode, inhabited neutral fibre, signed residual, source revision, original formula length, code length, clock coefficient/degree, actual simulation time, chart/refinement, ring/precision and consumer separately. Geometry-forward, steelman, BIDI, reverse-solve, no artificial mandatory representation and no micro-gate cadence.


## 49. Endpoint maximum cut — signed Singer precision, deterministic sparse enumeration, and ternary isolation/resource BIDI (2026-11-25)

User: see three attached sources for inspiration; continue literal Clay P vs NP, no micro-gate cadence. Geometry-forward, steelman, BIDI and reverse-solve. Donors: (1) SSP–FRACTRAN × Y443 × primal–dual hyperfabric report, PR #1291, actual checker scripts/check_ssp_singer_incidence_wheel_20261125.py reopened on agent/toe-relate369-hyperfabric-pants-20261027, blob a68708f3fa817f927fa80f0d2f10ebb60fc7a119 (Griess matrix, r=(1,1,1), dual action, incidence offsets, distinct sign/role, zero returning histories); (2) Langlands R209–R215 all-rank signed spectrum and parity/support distinction, reported #1549/#120 heads c4b1435a60f3 / 4fc2e8c7b03d, donor report not independently rerun; (3) P vs NP Section48 unrestricted resource obstruction. Starting live heads 1ed33eb0edd7 / 38a5546cc114. Reuse Section47 conditional witness-resource frontier, Section48 polynomial chart transport, G54 prior field fingerprint/parity/randomized reduction, G55 source-independent observer limits, G110/G122 pin witness and original gain, G131 weighted support, G149/G151 deterministic gate lift, #1006 FactorsThrough, #1040 direct failure, #1129 standard machine, #1474/#1502 original Cook-Levin/Karp and #123 JMD lowering. Attribution: Griess/Sah original matrix geometry, classical Singer incidence, JMD SSP primes/path/computation motivation and Conway FRACTRAN remain distinct from DASHI signed source-indexed finite attachments. New application of signed incidence precision and isolation to the P vs NP resource carrier; prime residue separation and pairwise-independent hashing are standard elementary/complexity methods, not claimed inventions. Valiant–Vazirani original unique-solution isolation theorem (see https://theory.stanford.edu/~trevisan/cs254-14/lecture07.pdf and https://people.csail.mit.edu/madhu/ST02/slides/lect10slx4.pdf); here ternary Toeplitz implementation and explicit original witness-resource weld. No changes to Langlands, TOE or other programmes.

### A. Actual Singer signed precision — exact arithmetic obstruction, not compulsory representation

Use original M=[[1,1,0],[0,1,1],[1,1,1]] mod3, N=M^(-T), r=(1,1,1), P_i=M^i r, L_j=N^j r and B_ij=[P_i dot L_j=0 mod3]. Source offsets {0,6,10,11}. Exact B B^T=B^T B=3I+J, B^(-1)=(4 B^T-J)/12. Local exact Smith normal form diag(1^7,3^5,12), giving rank 13 over Q, rank 12 over F2 and rank 7 over F3. This is an actual finite source-derived transform; do not identify the 26 signed spatial states with the two typed incidence roles or their composition laws.

For histogram on the original 27-element ternary carrier retain the zero bucket separately, plus c^+,c^- in Z^13 in the source-selected representative gauge. s=c^++c^-, d=c^+-c^-; store both channels and original support independently. Define A=B^T s, D=B^T d, Q=[[B^T,B^T],[B^T,-B^T]], R=4B-J, I=[[R,R],[R,-R]]. Then I Q=24 I_26. Thus c^±=R(A±D)/24 over the rationals on legitimate integral packets; parity/integrality constraints retained. Given A,D mod 2^(h+3), h>=1, compute I times any integral residue representatives; result divisible by 8, then divide by 8 and multiply by inverse of 3 mod2^h to recover c mod2^h. Three extra bits sufficient. Necessary without extra baseline information: c^+=c^-=2^(h-1) times all-ones gives A=2^(h+2) times all-ones and D=0, same observations mod2^(h+2) as zero histogram but nonzero original hist mod2^h. Zero vector bucket independently retained at h precision. This lower bound is for that signed sum/difference incidence packet, not separate positive/negative observations, known additional baseline, arbitrary observer or SAT computation. Reduction mod3 also loses modes (cannot divide by 3). Exact rational invertibility does not establish finite-ring invertibility; modular zero is not empty original support. A fixed 27-point transform cannot yield an asymptotic SAT lower bound by its own cardinality.

For uniform independent h(x),h(y) in F3^k with q=3^k, signed equality probability 1/q; projectivize by identifying nonzero z with -z while retaining zero separately: probability of same projected value is (2q-1)/q^2 (one singleton zero and (q-1)/2 doubletons). At k=3 this is 53/729 instead of 27/729. Thus the source wheel motivates retaining sign and zero, not using 13 projective directions as though they were 27 signed values. For general k this is a projective quotient, not a claim that the 13-wheel itself extends to all dimensions or that the hash acts as a FRACTRAN compiler. A hash bucket is not the complete assignment provenance; original x remains available for verification.

### B. Deterministic sparse witness enumeration and exact modular counting

Let S_F be original n-bit satisfying assignments, t>=|S_F| a supplied positive bound. Encode x injectively by a(x)=sum 2^i x_i (n-bit integer, no huge-integer free operations). For each fixed witness x, any other y excludes primes dividing the nonzero difference a(x)-a(y), whose absolute value is less than 2^n and hence has at most n distinct prime divisors. At most n(t-1) primes excluded; among first n(t-1)+1 primes there is one p with x unique in its residue r. Enumerate this fixed family and all residues; no witness/prime discovery oracle. For t=poly(N), primes and total number of buckets are polynomial in N (standard nth-prime O(k log(k+2)) bound, sieve or trial division). For every p,r construct original chart F AND [a(x) mod p=r]. Deterministic Boolean residue recurrence with p one-hot states, add 2^i mod p when bit i is 1, has O(np) gates; use gate equivalences width<=3 and assert target. Unique auxiliary extension for each original assignment, by topological evaluation; original clause ids and original x coordinates retained. No assumption of injectivity on all S for the shorter prime list: each x has its own isolating p.

Suppose a deterministic algorithm is guaranteed to find a satisfying assignment in polynomial time on every uniquely satisfiable 3CNF (with ordinary explicit assignment universe). On arbitrary charts impose its known polynomial clock, and verify any returned original assignment against both F and bucket; ignore malformed or invalid outputs, timeout, duplicates. Every original x is recovered somewhere in its singleton chart, and no extraneous x can pass original verification. Thus for every fixed polynomial sparsity bound t, all satisfying assignments of a formula promised |S_F|<=t can be enumerated deterministically in polynomial time, including exact count and emptiness, given this singleton witness solver. No guarantee on performance or completeness outside supplied sparsity promise. An algorithm deciding correctly only the 0/1-witness promise can be converted to a clocked singleton witness solver by standard original-variable pin descent, correct on unique formulas (each child 0 or 1); verify on original. Multi-witness cases need not be correct. No claim singleton search already polynomial.

A second exact identity: among first n*binom(t,2)+1 primes there is one injective on ALL S_F, by union bound over all pair differences. For C_(p,r)=# original witnesses in residue bucket, sum_r (C_(p,r) mod2) <= |S_F| for every p, equality for the injective p. Hence |S_F|=max_p sum_r(C_(p,r) mod2) over that list, including empty set. For supplied t polynomial, exact sparse count reduces deterministically to polynomially many full parity evaluations on ordinary polynomial-size charts; this identity requires actual parity on multi-witness buckets as well. Sparse enumeration above needs only promised singleton search, NOT full parity on all charts. These two different consumers must remain distinct. The parity result fits Langlands rank-two scalar mod8 with actual baseline D-3A=-4P, unit tags, independent original support; do not assume any unrestricted polynomial-time parity evaluator.

### C. General ternary affine isolation with a linear-size seed

Let h(x)=A x+b over F3^k, x original binary n-vector embedded coordinatewise, A random k-by-n Toeplitz matrix (n+k-1 independent trits a_(i-j)), b uniform independent k-vector. For x!=y, d=x-y nonzero over F3. Let j0 be least nonzero coordinate of d. In row i, (Ad)_i contains diagonal a_(i-j0) with nonzero coefficient and only smaller-index diagonals from j>j0. As i increases, each row introduces a fresh pivot diagonal; fixing other diagonals, map to Ad is surjective with equal fibres. Thus Ad uniform; independent uniform translation b makes (h(x),h(y)) independent uniform on F3^k x F3^k. Seed uses n+2k-1 trits. No independence of all witnesses claimed. If fair bits are the source, exact uniform trits can be sampled by rejection; bounded repetitions with a charged small failure probability give worst-case polynomial randomized time and no false positives.

For m=|S_F|>0,q=3^k, the event x uniquely hashes to 0 has probability >=1/q-(m-1)/q^2 by pairwise independence and union bound. Such events disjoint over x. Thus Pr(singleton zero fibre)>= (m/q)(1-(m-1)/q). Choose k least positive with 3^k>=2m, so 2m<=q<6m and probability >1/12. k<=n+1. Try all k=1..n+1 independently, repeat constant number (or O(log1/epsilon)) of bundles. Hash constraints are k independent mod3 residue recurrences, O(nk) deterministic Boolean gates with width<=3 equivalence CNF, unique original auxiliary lift. Retain n original coordinates, original clauses, hash seed, rank, actual signed syndrome, precision, original pin history and decoder. A true singleton on original binary assignments gives exactly one total compiled satisfying assignment; no parity/unique confusion from auxiliary multiplicity. For identity Toeplitz A with k=n and b=-x, compile instead as explicit original unit pins, equivalent and no auxiliaries. All charts have polynomial size, original support-preserving reverse decode, but a hash can eliminate all witnesses. This is a one-sided refinement, not a support-preserving equivalence for each individual seed. If F UNSAT all charts UNSAT. A complete original witness verifies positive output; no need certify that a chart really is singleton at runtime.

Consequences on literal source resource: If there exists fixed c such that every uniquely satisfiable original 3CNF H has kappa(H)<=c log2(|H|+2), Section47 bounded universal search with fixed budget solves singleton witness instances in uniform polynomial time; verify all returned outputs. The preceding random isolation then gives RP=NP (standard Valiant–Vazirani direction). Same consequence if a clocked decision consumer correctly detects only the empty vs singleton chart promise, including a promised rank-two pole/odd scalar observer: pin and verify to reconstruct original witness. It need not evaluate arbitrary counts, spectra or parity on multi-witness charts. Thus if NP!=RP, for every c and length cutoff there is a uniquely satisfiable ordinary 3CNF H of larger length with kappa(H)>c log2(|H|+2). Otherwise finite exceptional singleton formulas can be hardwired, yielding promised polynomial search and RP=NP. This narrows the lower-bound family conditional on NP!=RP; P!=NP alone does not entail this stronger hypothesis, and RP=NP does not by itself imply a deterministic singleton solver. Conversely P=NP yields uniform cheap singleton witnesses. Under cheap singleton solver, the sparse enumeration theorem covers every fixed polynomial witness-count bound, so any remaining deterministic SAT obstruction must evade those sparse instances (or their uniformly cheap isolating transforms).

### D. Exact BIDI resource split — isolate or solve

For satisfiable F of original bit length N, let s range over the admissible polynomial-size ternary Toeplitz seeds (1<=k<=n+1) whose zero fibre contains exactly one original witness. Write H_s for the above deterministic unique-extension chart. Define kappa_seed(s|F)=min_p {|p|+ceil(log2(t+1)): U(p,F) halts outputting s in time t}; seed generation need not certify uniqueness. Let iota(F)=min over isolating s of kappa_seed(s|F). Define J(F)=min over isolating s of [kappa_seed(s|F)+kappa(H_s)]. All quantities finite on satisfiable F; treat empty UNSAT separately. F is given as input; fixed efficient universal machine, ordinary bit-cost simulation, original formula and chart encoding lengths polynomially related in the needed direction. Preserve program length and actual time axes before logarithmic combination.

Original solve from seed plus chart witness: store both programs with efficient self-delimiting overhead, run seed program on F, compile H_s, run chart program on H_s, decode/verify original assignment. Polynomial overhead and lengths O(poly(N)) give kappa(F)<=C[J(F)+log2(N+2)]. Conversely from an original witness program producing x, generate identity Toeplitz A=I_n and b=-x. This is an isolating seed of polynomial length, with kappa_seed<=C'[kappa(F)+log2(N+2)]. Its special-case chart is original F plus all pins for x, with fixed polynomial witness decoder reading those pins (no auxiliaries). Thus kappa(H_s)=O(log(N+2)), and J(F)<=C''[kappa(F)+log2(N+2)]. Therefore a two-way comparison up to constants and additive logarithm, not an equality of exact running times or code lengths. In particular iota(F)<=O(kappa(F)+log N) unconditionally; if all singleton H have cheap kappa then kappa(F)<=O(iota(F)+log N) as well. Under that hypothesis P=NP iff every satisfiable F has an isolating seed with logarithmic conditional description/time cost. A uniformly polynomial-size computable list of candidate seeds containing at least one isolator would suffice, by enumeration; source-dependent generation and chart costs paid. The split separates deterministic isolation search from deterministic solving of an already isolated witness. It does not show either side superlogarithmic unconditionally. Random seed with constant success probability is not necessarily a short deterministic conditional seed program, and encoding an entire random tape may take O(n) bits. Do not conflate RP with P.

### E. Steelman — nonuniform derandomization versus universal observer no-go

For canonical width<=3 CNF on n explicitly named variables, number of possible clause selectors <=2^M, M=O(n^3). Each random bundle (one Toeplitz seed for each k=1..n+1) isolates any fixed inhabited support with probability >=1/12. By union bound, O(M+1) independent bundles have positive probability of isolating every satisfiable formula at this n simultaneously; thus a polynomial-size source-independent seed portfolio EXISTS for this canonical source domain. Includes arbitrary ordinary explicit formulas after polynomial duplicate removal and normalization (provenance retained). The seeds can be treated as nonuniform advice, not an efficiently computable uniform portfolio; no claim of a short conditional program for the particular advice. Searching exhaustive portfolios is computable but can be enormous. Cheap singleton solver would therefore also give polynomial circuits for SAT using this advice, consistent with NP=RP implying NP subset P/poly.

For comparison, any fixed family of subsets T_j of an arbitrary finite universe U that isolates EVERY nonempty S subset U (exists j with |T_j intersect S|=1) must have at least |U| members. Start S=U, select an isolating T_j and delete its unique element in S. That T_j has zero intersection with all later remaining sets, so cannot isolate again. Repeat until empty; each of |U| deletions requires a distinct test. Singleton tests can attain the bound. Applies also to deterministic adaptive BLACK-BOX observers whose only response is singleton yes/no: follow the all-negative path for empty support; fewer than |U| tests cannot distinguish some nonempty S from empty. Not a claim for adaptive source-aware algorithms, full histogram/count responses or arbitrary formulas of polynomial size. For U={0,1}^n lower bound 2^n on universal test count; arbitrary supports may themselves require exponentially long source descriptions. This is compatible with polynomial nonuniform families for the much smaller 3CNF family. Thus no automatic superpolynomial original input lower bound by compulsory isolation. Preserve empty vs inhabited neutral when testing parity or projective zero, and keep original source, coefficient ring, rank, seed, time, signed history, refinement and consumer as independent indices.

### F. Actual local acceptance and endpoint decision

Local Python/SymPy execution scripts/check_p0_signed_isolation_20261125.py, git hash-object a31ef72d0266ada877827bfb0ceb9f414e7e8e51 matching both remote blobs. Exact original matrix, offset, Gram, Smith and signed integer inverse 24I checks; 256 signed precision reconstructions across h=1..8, eight sharp loss examples; 315 sparse-support fixtures (all 255 nonempty 3-bit subsets plus 60 sampled 16-bit supports), 1396 individual witnesses isolated by short prime list, 315 parity count identities; 7371 ternary affine Toeplitz seeds exhaustively enumerated at n=3,k=1,2,3; 84 complete pairwise-distribution comparisons, all 255 nonempty support isolation probability bounds; 512 explicit residue/affine chart source projection comparisons and 30192 deterministic gate-lift values checked. Gate unique extension follows from topological equivalences, not exhaustive auxiliary enumeration. Sparse fixtures enumerate supplied supports to test mathematics; not a general SAT or singleton solver. No autonomous FRACTRAN compiler, general local-factor computation, native Agda/Lean kernel, CI, production timing or universal derandomization. No chat attachments, all artifacts in repositories. No other programme changes.

Major endpoint obligations:
- Deterministic sparse all-witness isolation and signed Singer precision: established within specified model.
- Ternary affine original unique-extension isolation: derived, locally tested; standard randomized reduction, not a deterministic derandomization.
- BIDI split of original witness resource into isolation seed plus isolated-chart solve: established within efficient universal program/encoding assumptions.
- Uniform polynomial singleton witness producer: OPEN (would imply NP=RP; not sufficient alone for P=NP).
- Uniform deterministic isolating seed/portfolio construction across arbitrary SAT: OPEN; polynomial nonuniform existence and restricted sparse construction do not pay uniform cost.
- Original P0-A superlogarithmic witness resource, P0-B total computable full-code deadline/universal failure, P0-C uniform polynomial witness producer: OPEN. N4/N5 unresolved, N6 conditional original endpoint transport.

Next broad cut: seek an unconditional lower bound on the joint isolation-plus-singleton resource or a uniformly paid construction of BOTH components. Treat NP!=RP as an unproved hypothesis, not replacement for Clay. Avoid using mandatory full parity/counting/signed-spectrum recovery, compulsory affine quotient, or black-box test size as unrestricted lower bound. Retain zero, sign, inhabited neutral, independently indexed source/refinement/time/precision and actual provenance. Geometry first, endpoint backwards, no further micro-gates for their own sake.

## 50. P0 maximum cut — sparse witness polynomial reconstruction, succinct neutral supports, and tame-clock reverse endpoint (2026-11-25)

Scope: literal P vs NP only, controlling P0-S/P0-C/P0-R directive. User supplies Langlands R224–R228 as donor, not a request to advance that programme. Reopened actual Agda Langlands #1549 head e8bd35e56c6f0291f5f0d9a4bf1788b79cc14962 roadmap blob 9a84b29524ed9de50af4662551ae104361129b46, R224/R225 original rank-two coefficient and full cyclotomic algebra packet. User reports matching Lean #120 head 31ce4fe5099e; not independently reopened here. Starting P vs NP heads 87c46ab1c0a4 / a2d22ac35698; reuse Sections47–49, G122/G126/G128, existing original source/unique-extension compilation. Credit Griess/Sah, Singer, JMD/Conway, Valiant–Vazirani, classical CRT and polynomial factorisation separately; DASHI new combination/application to this resource carrier, not claim of literature priority.

### A. Deterministic batch recovery of sparse original witnesses from weighted pole packets

Let n be original binary assignment dimension, a(x)=sum_i 2^i x_i, S the set of satisfying original assignments, m=|S|<=t for supplied positive integer sparsity bound t=poly(N). Use actual R225 D_p=3 A_p-4 M_p over full integral cyclotomic coefficient algebra reduced mod8, M_p=sum_r W_(p,r) zeta_p^r, A_p=prod_i(1+zeta_p^(2^i)); shared D_1=3*2^n-4m. Divide 3A_p-D_p by 4 and read at mod2 precision. For p odd, a_r=W_(p,r)-W_(p,p-1) mod2 in full basis, W_(p,p-1)=(m-sum a_r)/p mod2, recover all W_(p,r) mod2. No selected single component or mandatory full spectral evaluation. For R_p={r:W_(p,r) odd}, |R_p|<=m, with equality iff each occupied bucket has exactly one original witness (since any bucket size>=2 contributes strictly less than its size). At most L=n*binom(t,2) primes divide some nonzero pair difference; all other odd primes are injective. Take first K=L+(n+1)t+2 odd primes; primes, total packet dimensions and construction costs polynomial when t polynomial. Compute m=max_p |R_p|. If m=0 return empty on promise. Otherwise retain ALL good primes attaining m, not merely a presumed isolator. For P_S(X)=prod_(x in S)(X-a(x)), each good p gives exactly P_S mod p=prod_(r in R_p)(X-r). Integer coefficients have absolute value <=B=2^((n+1)t) (sum of absolute coefficients <= product_(x in S)(1+a(x)) <= 2^(nm), and the stated B is conservative). At least (n+1)t+2 good primes remain, so product exceeds 2B. Compute each integer coefficient by centered CRT, then factor monic P_S over Q in deterministic polynomial bit complexity, by A.K. Lenstra, H.W. Lenstra Jr., L. Lovasz, "Factoring Polynomials with Rational Coefficients", Math. Ann. 261 (1982), 515–534, https://ir.cwi.nl/pub/9304. All factors are distinct linear factors on the promise. Decode roots into n-bit assignments, verify against original F and preserve source coordinates. For m=0 polynomial is 1, not a phantom zero witness. This is a deterministic nonadaptive polynomial-query reduction of sparse original witness enumeration to weighted parity packets, with no serial pin queries, no independent bucket evaluations and no exact total-count oracle. It is conditional on paid packet generation and supplied sparsity, NOT an unrestricted SAT algorithm. Off-promise output verification protects positives but does not certify completeness; even m=0 cannot establish UNSAT without a valid promise. For singleton charts t=1, the promise is sufficient for this method; the ordinary scalar promise solver plus pin descent remains a weaker adequate alternative, so do not force weighted packets as a prerequisite. A weighted singleton solver plus a uniformly polynomial isolating portfolio closes P0-C, while random isolation plus either promise solver gives only RP=NP.

### B. Succinct source-indexed neutral parity packet: explicit anti-control to fixed prime portfolios

For any finite nonempty fixed portfolio P of odd primes set G(X)=prod_(p in P)(1+X^p) over F2. Constant and leading coefficients are 1, degree D=sum p. Define inhabited support S={a: coefficient of X^a in G is 1}; in particular a=0 is present and cannot be discarded as an absent mode. G is divisible by X^p-1 for each selected p in characteristic 2, so every residue parity vanishes (reduction folds coefficients by exponents mod p). Total parity G(1)=0 too. Thus all R225 mod8 packets, after subtracting the same known baseline, coincide with empty support, even though S is inhabited. If D<2^n and D=poly(n), compute coefficient support in polynomial time by successive XOR shifts. Use ell=ceil(log2(D+1)) low bits; force other original bits zero and forbid each low-bit assignment outside support by a single full-width exclusion clause. This yields a polynomial-size ordinary CNF on the original n coordinates (O((D+1)log(D+1)+n) literal occurrences), and deterministic gate equivalences give a polynomial-size 3CNF unique auxiliary extension when needed. For the latter use neutral weight 1 on auxiliaries, or operate on projected original coordinates as in R224; tagging all auxiliaries as extra original exponent bits would be a different packet and the claim does not follow. For an adaptive blind residue observer that sees only n and earlier packets, follow its all-zero path and use the finite prime list on that path: the constructed inhabited source follows the same transcript when queries ignore actual source clauses. This applies to variable-count-indexed source-oblivious prime portfolios of polynomial total degree, not a source-length-dependent budget that may outgrow the constructed source, arbitrary source-aware/adaptive computations, different precision, or arbitrary local-factor probes. It is an explicit succinct source anti-control, not an unrestricted lower bound. In particular it does not defeat A with a valid sparsity bound and sufficiently large portfolio.

### C. Reverse endpoint: fixed-degree, tame-coefficient conditional noncomputable frontier

Assume P=NP ONLY for this implication, choose complete polynomial anchored producer W_* with fixed clock, and use the existing W_0 fallback with genuine gains on arbitrarily long sources (G126/G128). For each ordinary no-input deterministic machine M build W_M that simulates M for N=|F| steps, uses W_* if M has not halted, else W_0; retain original verification and fully pinned anchor. Universal bounded simulation costs poly(code length,N), and fixed W_*,W_0 have fixed polynomial bounds. For all M one common integer degree d and constants c,a suffice for a clock c(m+1)^a(N+1)^d, where m is the underlying program description length before its clock; encode that coefficient explicitly, so it is at most polynomial in full clocked description length s>=m. A uniform computable compiler e(M) exists under the hypothetical fixed W_*; no effective W_* construction without the hypothesis. If M never halts candidate is complete. If M halts after T steps, all parents of length <T receive complete sound outputs (so cannot have gain); sufficiently large known fallback gain parent and its unit refinement both lie beyond the switch, making candidate incomplete. Therefore mu(e(M))>=T. If total computable b(s) bounds the minimum parent gain for every incomplete code in the common fixed-degree, polynomial-coefficient carrier, simulate M for b(|e(M)|) steps; every halting M must halt by then. This decides halting, contradiction. Thus under P=NP some fixed d,a,c tame-clock carrier has no computable description-size majorant for its incomplete-code frontier; its lower bound is inherited from halting-time maxima via the effective code map. No claim that every fixed degree has this property or that a particular numerical d is already identified. Under P!=NP, G128 exhaustive gain enumeration terminates for every valid code by standard-machine coverage; maximizing over finitely many codes up to size s computes a bound, also for every tame carrier. Consequently P!=NP is equivalent to the assertion that EACH fixed d,a,c tame carrier admits a computable size majorant (no uniform dependence on those constants required); if P=NP at least one fails. This refines G128 to polynomial code-size clock coefficients and fixed degree, not an unconditional proof of totality. Do not reuse hypothetical W_* as a free oracle in the actual programme. The unrestricted separation and total deadline exits remain OPEN.

### D. Acceptance and controlling frontier

Local Python/SymPy script scripts/check_p0_sparse_crt_neutral_20261125.py, exact git hash-object 278ba996f85f41c87d6d3cf71d20e6525b13a47a, committed identically and read back on both P vs NP branches. 296 support fixtures (all 256 subsets on 3 bits, 40 sampled 16-bit sparse supports), 19848 prime parity packets, 896 collision packets excluded, 1499 integer coefficients reconstructed, 1204 original roots recovered. 255 nonempty subsets of first 8 odd primes as neutral controls, 12544 zero-parity bucket checks, 18436 ordinary CNF/source support comparisons. Actual finite computation uses supplied support, not source-aware production local-factor contraction, no claim of efficient SAT. Factorisation theorem cited separately; SymPy finite regression does not certify asymptotic bit complexity. C is mathematical reduction, not empirical halting experiment. No CI or native Agda/Lean kernel run, no Langlands/SSP or other programme edits.

P0-S: still need unconditional superlogarithmic joint unrestricted witness resource; the explicit neutral sources only obstruct a specified observer model. P0-C: still need uniform deterministic isolating portfolio and polynomial singleton solver (or direct SAT); batch decoding removes serial pinning only conditional on a paid weighted consumer. P0-R: still need unconditional total computable deadline; tame-clock theorem sharpens the exact reverse target and demonstrates why a finite deadline for each individual candidate is insufficient. All three remain controlling and OPEN. Next substantial attack: seek source-aware polynomial promise singleton evaluation on actual original truth graphs without expansion (or other solver) together with uniform isolation; parallel seek unrestricted obstruction or proof of deadline totality. Do not add another finite representation as mandatory prerequisite. Keep zero, sign, inhabited neutral, source/refinement/time/precision and independent resource axes. Prize endpoint mathematics first.

## 51. P0 maximum cut — signed conditional isolation, source-discovery equivalence and reverse deadline quantifiers (2026-11-25)

Scope: literal Clay P vs NP only. Controlling P0-S/P0-C/P0-R directive; starting verified heads 2fc14e294f1c / 0a468abedd6a5. Reuse Sections47–50, G122/G128/G162, original ternary Toeplitz affine seed, deterministic gate extension, actual R224 pole consumer as optional singleton observation. Classical method of conditional expectations (https://classes.csail.mit.edu/6.856/current/Notes/n23-derandomizedrounding.html), Valiant–Vazirani isolation, standard finite-field Gaussian elimination, majority satisfiability/PP and ordered decision diagrams retain original mathematical attribution. DASHI application is the combined signed objective, explicit seed-prefix cost target and endpoint scope audit, not a claim of new literature priority. No other programme edits.

### A. Signed isolation objective with a robust deterministic descent theorem

For original S_F, m=|S_F|>0, hash seed s of length L=n+2k-1 trits, h_s(x)=A_s x+b_s over F3^k, q=3^k, let H_s count surviving original witnesses. Set Psi(s)=H_s(2-H_s)=H_s-H_s(H_s-1). This is positive iff H_s=1, zero for H_s=0 OR H_s=2 (retain distinct support), and negative for H_s>=3. Pairwise independence of Section49 yields E Psi=m/q-m(m-1)/q^2. Least positive k with q>=2m has 2m<=q<6m, so E Psi>1/12. No knowledge of m required: try every k from 1 to n+1. For a seed prefix u, V(u)=E[Psi|u], V(u)=(V(u0)+V(u1)+V(u2))/3. Exact maximum-child selection preserves V and ends at a singleton for the guaranteed k. More generally, a deterministic estimator for V(u) with absolute error <=1/(48L) allows maximum-estimate selection: the true V decreases by at most 2/(48L) each step, total <=1/24, and final true V>0. Thus a uniform polynomial-cost additive estimator gives a uniform deterministic polynomial-size isolation portfolio (one seed per k), no need to certify each seed as isolating, no need exact full count or spectrum output. All n,k,L and arithmetic representation costs polynomial. Joint with clocked singleton solver and original verification, this suffices for P=NP; wrong k and off-promise chart outputs never give false verified positives. This is conditional, not a paid general estimator.

### B. Exact source-indexed affine rank formula and the actual computational gap

For a fixed original assignment x and prefix u, h_s(x)=0 is a k-row affine linear system in remaining w=L-|u| seed trits. Let C_u(x) count its completions, and C_u(x,y) count simultaneous completions for two distinct original witnesses. Gaussian elimination gives C=0 for inconsistency, otherwise C=3^(w-rank), exact O(poly(n)) bit operations per specified one/pair (counts have O(L) bits). The conditional numerator is sum_(x in S_F) C_u(x) - 2 sum_({x,y} subset S_F) C_u(x,y); divide by 3^w. Keep original one/pair coordinates, sign, independent support and rank; coincident or zero syndrome does not identify witnesses. Rank evaluation for specified x,y is polynomial but the SUM over unknown original satisfying support is the unpaid computation. Finite supplied-support tests do not give a source-aware estimator. No requirement to compute all ranks or moments separately in a future unrestricted algorithm.

### C. Unrestricted comparison PP-complete even at final translation coordinate

For two equal-length seed prefixes u,v the comparison V(u)>V(v) is in PP: multiply by the common 3^w; sums count polynomially checkable tuples of completion and one original witness or ordered pair of distinct witnesses. Use the standard strict positive GapP characterization of PP (alternatively pad and compare accepting path counts). Hardness already at k=1, all A coefficients fixed selecting one binary coordinate z, final translation b either 0 or 2. Reduce majority circuit satisfiability: C on r bits, c accepting assignments; construct source with selector z, original x in {0,1}^r, two mode bits. At z=0 allow modes 00 and 01 iff C(x)=1; at z=1 allow mode 00 for every x; for both z allow modes 10 and 11 only when x=0. Disjoint modes give H0=2c+2 and H1=2^r+2. Encode this polynomial Boolean circuit into width<=3 CNF with deterministic gate equivalences and asserted output, hence unique auxiliary extension and exact branch counts. A selects z in the full compiled variable list (arbitrary 1-row Toeplitz coefficient vector allowed), all other coefficients zero. Translation 0 selects z=0; translation 2 selects z=1. Psi(H)=H(2-H) strictly decreases for integer H>=2, so Psi(H1)>Psi(H0) iff c>2^(r-1). This is a polynomial many-one reduction. The difference for unequal counts is integral and magnitude >=1, so sufficiently accurate general additive estimation at both leaves also decides strict majority (a gap threshold with tolerance below 1/4 handles equality). Thus demanding arbitrary prefix comparisons/estimates would demand at least PP-hard computation. This does NOT establish hardness for the restricted positive-prefix continuation consumer, which could use weaker certificates or a different potential; the majority reduction generally has nonpositive values. Do not force full parity, moment, or arbitrary conditional-expectation evaluation as compulsory infrastructure. P0-C target is uniform positive continuation or another uniformly paid isolation construction, plus singleton solving. P0-S remains unrestricted, not PP-hardness of a chosen intermediate.

### D. Singleton residual geometry has width two regardless of original variable order

For any empty-or-singleton original formula and any fixed variable order, at each depth the semantic residual R_p(z)=F(pz) is either identically zero or the unique suffix indicator; only the prefix matching the unique witness can have a nonzero residual. Thus the exact layered residual quotient (G162) has width <=2 and O(n) states, including empty case and terminal constants. Given a uniform polynomial-time promised singleton witness solver, clock it, verify outputs; on empty source no output can verify. Build the exact diagram from that witnessed assignment or constant-zero function in polynomial time on promise. Conversely a polynomial-time source-to-exact-quotient constructor on the promise allows traversal to a verified original witness, or detects no accepting path. Thus uniform polynomial construction of the quotient on this promise is equivalent to polynomial singleton solving, despite its always-small output. This is a source-discovery obstruction to using existential width as an algorithm, not a lower bound on actual construction. Distinguish semantic quotient from a syntactic intermediate frontier, whose width can be larger. A promise solver only implies RP=NP via random isolation; deterministic portfolio still unpaid.

### E. Reverse endpoint quantifier correction: nested universal-budget deadlines alone are insufficient

Take the Section47 universal evaluators with budget b_c(N)=floor(log2((N+2)^c)); include anchor/fallback and verification, so success sets monotone in c. Let W_c be normalized candidate, mu(c) its first gain length when incomplete. Classically there EXISTS a total computable b(c) majorizing mu(c) on all incomplete members of this one nested family, unconditionally by cases. If P!=NP, all W_c incomplete and unbounded gain enumeration terminates for each c, giving b. If P=NP, a finite c0 makes E_c complete for every c>=c0; only finitely many c can be incomplete, so finite hardcoded first gains give a total b (arbitrary zero otherwise). Existence of this bound does not select the case or provide a constructive uniform algorithm without the case information. For binary c encodings also obtain a computable size majorant by finite maximum. This does not contradict G128/Section50C full-code result: the arbitrary-code delayed-failure family is not the same as this nested sequence. Cofinal budget dominance of individual polynomial producers does not imply transport of their first-obstruction deadlines from a larger budget. A deadline for incomplete nested evaluators is NOT a sufficient Clay endpoint. To use this family one needs unconditional nonemptiness of every H_c, equivalently totality of gain search itself (not an incomplete-only deadline). Keep P0-R on full-code carrier or prove actual nonemptiness. No new unconditional unrestricted lower bound asserted.

### F. Actual execution and next endpoint cut

Local Python exact integer/rational + SymPy identity check scripts/check_p0_conditional_isolation_20261125.py, git hash-object 8cac0ef82f7d864a8fb10c401d77096c9b8b1513, identical remote readback both repositories. All 255 nonempty original 3-bit supports; 7371 ternary Toeplitz seed masks, 10200 independent F3-rank conditional score vs explicit prefix enumeration comparisons, 1700 exact and 1700 deliberately perturbed approximate greedy trit steps (both isolate every fixture), 518 numerical majority comparison controls, 216 empty/singleton residual width checks across all variable orders/depths. Majority source compilation argument and general bounds are proofs, not empirical consequences; test checks counts, not all compiled majority circuits. Scores computed from supplied support, not a general source-aware estimator or polynomial singleton solver. No CI, no native kernel, no other programme edits.

P0-S: unconditional superlogarithmic joint resource still OPEN. P0-C: source-aware positive seed continuation/other deterministic portfolio AND polynomial singleton witness discovery (or direct SAT algorithm) still OPEN. P0-R: unconditional full-code deadline or equivalent universal residual nonemptiness still OPEN. New results narrow the sufficient isolation consumer, identify a PP-hard stronger consumer to avoid, and remove two false shortcuts (small semantic quotient and restricted nested deadline). Next work should aim at a genuinely paid positive continuation and original singleton discovery, or an unrestricted lower bound or totality proof, not more decoder or geometry inventory. Maintain zero, signed residual, inhabited neutral and independent resource/source/time/precision indices. Literal prize endpoint first.

## 52. P0 maximum cut — shared continuation/solver theorem, paired signed pole and remaining endpoint welds (2026-11-25)

Scope: literal Clay P vs NP only; user supplies Langlands R229–234 and attached Section51, asks steelman/BIDI/reverse-solve/geometry and remaining deliverables. Actual P vs NP starting heads eaaa71fb7f77 / c30671013950. Actual Agda Langlands #1549 independently reopened at a2e49da98d4279b825a12ade0797fdca1f09c1e3, roadmap blob c8c2e55fcf4512d76dd95a26c26c3d39276051db through R242 (not only R234). Reuse R229–231 and R235–239 actual WD paired signed Gram and source diagonal; no donor execution claimed or donor edits. Original Rankin–Selberg, Weil–Deligne, Schur, Valiant–Vazirani, conditional expectation, prime separation and original DASHI owners retain attribution. New application is the shared continuation/solver reduction and indexed paired potential. User's controlling prize directive supersedes incidental formalisation. 

### A. One uniform positive-continuation algorithm suffices for both constructive obligations

Let C(F,k,u) be a deterministic polynomial-time algorithm on an ordinary explicitly encoded source F, its ternary Toeplitz hash dimension k, and a proper seed prefix u. On promise V(u)>0 it must return d in F3 with V(ud)>0. No value estimation, comparison or uniqueness certificate required. Clock it on ALL inputs (including unpromised), ignore malformed outputs and verify final original witnesses. Section51 guarantees a positive root for some k<=n+1 on every satisfiable F; try all such k, follow C until complete seed, compile ordinary unique-extension chart G=F AND [h_s(x)=0]. At least one chart is singleton; others arbitrary. Polynomial number of trits/branches and polynomial chart construction charged.

NEW reverse weld: for any promised uniquely satisfiable ordinary formula G on m variables, use k=1, fixed row e_i selecting original coordinate i, final translation b still free. Under the singleton promise exactly one b=-x_i mod3 gives H_b=1; other two give H_b=0. Thus parent V=1/3 and C returns the unique translation and therefore the original bit. Repeat m times, verify recovered full assignment; empty input cannot return a verified witness, multi-witness input may fail but verified positives sound. Arbitrary e_i is a valid 1-row Toeplitz coefficient list (in reversed diagonal order). For compiled chart use actual full variable list, whose deterministic auxiliary extension preserves singleton; decode original variables. Therefore C alone yields both isolation and singleton discovery and a deterministic polynomial SAT algorithm. No independence of those two missing algorithms is required on this route. Same reduction works for one constant-margin selector guaranteed to take V(u)>1/12 to V(ud)>1/12; guaranteed good k root >1/12 by Section51, and bit-probe parent 1/3. This stronger promise avoids requiring continuation for exponentially small positive values but requires margin preservation, not merely positivity after one call. No proof of existence of either algorithm. General positive/threshold selector may demand more than P=NP; do not assert converse for arbitrary affine-prefix potentials (PP comparison hardness in Section51).

### B. Exact bidirectional identity-translation endpoint; viability versus expectation

Fix k=n and A=I_n, a legal Toeplitz seed with coefficient prefix fully fixed. Each translation b retains at most one original binary x=-b; b containing 1 cannot retain a binary coordinate there. For any partial translation u, V(u)=#{x in S_F : x_i=-u_i on fixed prefix coordinates}/3^(n-|u|). Thus V(u)>0 iff the original assignment prefix has a satisfying extension, and every positive terminal translation gives the original witness directly. Polynomial positive continuation RESTRICTED to this identity chart is equivalent to P=NP: forward n calls on inhabited input, verify final candidate on all inputs; backward use polynomial SAT decision on pinned original source to choose a child, on promise. The promise root can be exponentially small (singleton gives 3^-n), so this does not establish equivalence for the constant-margin general selector.

Define existential viability E(F,k,u) iff some complete seed extending u has exactly one surviving original witness. A viable prefix need not have positive expected signed potential: terminal counts (1,3,0) give potentials (1,-3,0). Positive implies viable, converse false. Uniform deterministic polynomial viability continuation on arbitrary affine prefixes (promised viable) is equivalent to P=NP: forward identity translation as above; reverse under P=NP verify given seed has exactly one witness in polynomial time by SAT, recover candidate assignment, and test absence of a second via a blocking clause; the existential search over seed completions is then NP and hence P, with polynomial prefix search. More generally viability in Sigma_2^P by existential seed/witness and universal different witness check. A general P=NP hypothesis does not automatically pay PP comparison or a positive-expectation-preserving selector; distinguish these sufficient routes. Unconditional separation would follow from a lower bound against all polynomial identity-chart viability/positive selectors (equivalent standard SAT extension, not a new restricted-model shortcut). A lower bound solely against general stronger expectation consumers does not necessarily prove P!=NP.

### C. Final-trit continuation is exactly the promised singleton-solving obligation

At a proper prefix with ONE remaining trit and V(u)>0, the three child counts H_d satisfy sum_d H_d(2-H_d)>0. Any H_d>=3 contributes <=-3, whereas each of the other two contributes <=1, contradiction. Hence each child has at most two witnesses, at least one has exactly one, and sum_d H_d<=5. This is a count of child incidences, not necessarily distinct original witnesses; if translation selects disjoint buckets then it is their union cardinality as well. Given a polynomial promised singleton solver, apply Section49 sparse prime enumeration with t=2 to each child chart (including polynomial unique-extension compilation), verify/deduplicate all returned original witnesses and choose a child with count1. Every call stays within the sparsity promise on these positive parents. Conversely rank-one final-translation probes in A recover a singleton witness from a final-trit selector. Thus polynomial final-trit positive continuation iff polynomial promised singleton solving. This is not equivalence to P=NP by itself: random isolation would give RP=NP; arbitrary-prefix uniform isolation remains needed unless using direct SAT. It identifies the exact distinct work: early-prefix selection versus last-trit source discovery. Same terminal conclusion for V>1/12; terminal positive value1 preserves the margin. 

### D. Actual Langlands paired potential and original same-seed diagonal

Use actual R229–231 (and R235–238 length-one specialization) with common unit odd-order tag and chain length1. For fixed seed s and truth flag F(x)C_s(x), denote its accepted count H_s, use its own all-rejected baseline. The four-corner ordinary tensor-dual pole difference K_pair=8 H_s^2, since ordered accepted pairs include diagonal and off-diagonal; the original indexed matched diagonal K_diag=8 H_s. Thus 8 Psi(s)=2 K_diag-K_pair. For a partial prefix u, w=L-|u|, multiply the conditional objective by 8*3^w to get sum_(s extending u) [2 K_diag(s)-K_pair(s)]. If using one aggregate carrier, insist on SAME seed in paired source coordinates: records (s,x,y), identical s on both factors, original x=y only on diagonal. Pairing unconstrained aggregate sums creates cross-seed terms and does not equal conditional potential. Signed second moment and diagonal first moment must be computed on actual source predicates (each trit uniquely encoded as Boolean pair excluding fourth state, deterministic gate auxiliary lift); keep seed, original witness, ordered pair, source revision, chain k distinct from hash dimension, time, tag/precision and actual consumer. In particular positive potential does not follow from ordinary PSD Gram alone; empty H=0 and inhabited H=2 both yield neutral residual. Exact local-factor identities on explicit representations do not pay succinct production, and monodromy or arbitrary ramification is not required to use this length-one donor. A source-aware polynomial margin-selector from these indexed signed contractions would discharge A, but no free evaluation of exponential pair carriers, full factor, or exact signed moment is assumed. PP-hard unrestricted comparison in Section51 is a warning, not compulsory SAT lower bound.

### E. Remaining theorem-level phases and deliverables (parallel P0 routes)

| Phase / lemma or weld | Concrete mathematical deliverable | Status / dependency |
|---|---|---|
| C1-a early-prefix constructive selection | One uniform deterministic polynomial algorithm returning a positive child on every promised positive prefix, OR constant-margin child preserving >1/12, with known total polynomial clock | OPEN; alone with A/C suffices; does not require generic PP estimator |
| C1-b weaker viability or identity chart | Uniform polynomial viable-child selection, alternatively identity-translation positive selector with arbitrarily small positive margins | OPEN; exact P=NP equivalence, direct verified witness via B |
| C2 terminal source discovery | Uniform polynomial promised singleton solver, equivalently final-trit selector on positive parents via C | OPEN independently; implied by C1-a; not a serial prerequisite if C1-a paid |
| C3 alternate direct route | Any ordinary uniform polynomial SAT decision/search algorithm | OPEN; no hash/representation requirement |
| C4 source/resource weld | Deterministic hash/seed chart compilation with unique extension, clock/invalid-output handling, original decoder/verifier, polynomial whole-run cost | mathematical reductions in Sections49/51/52 supplied; attach to actual C1 or C3 proof, not new infrastructure gates |
| S1 unrestricted lower-bound target | For each fixed c produce existence of a satisfiable original F with kappa(F)>c log2(|F|+2), or equivalent joint J obstruction | OPEN; no conditional hypothesis P!=NP or NP!=RP allowed |
| S2 unrestricted coverage/anti-bypass | Proof ranges over all fixed ordinary programs with actual bit costs, sharing, source-aware nonlinear charts, recomputation; or establish lower bound against every identity-chart selector (equivalent to P) | OPEN as substantive lower-bound argument; standard machine fallback already available |
| S3 endpoint transport | Apply Section47 universal budget equivalence and Section49 joint resource comparison to actual S1 proof | derived conditional; no need for full FRACTRAN/GCT compiler, arbitrary observer recovery or nonuniform circuit lower bound |
| R1 arbitrary-code deadline | Total computable B(e) bounding first genuine gain of every incomplete valid clocked e, proof of totality over full code/clock domain | OPEN; G128 equivalence; not nested incomplete-only deadlines |
| R2 coverage/genuine obstruction | Standard machine coverage, original pinned anchor, sound verified outputs and finite gain verification; no false source reduction | mathematical G122/G128 assumptions retained; pay any required concrete source weld, not an extra goal |
| R3 endpoint transport | From B, decide Bad(e) by finite enumeration; use hypothetical complete W_* delayed-failure contradiction to derive P!=NP, or prove total gain search directly | conditional proof G128/50 supplied; R1 or equivalent nonemptiness unpaid |
| X final prize deliverable | Self-contained standard complexity model proof of P=NP or P!=NP, independent expert error audit and provenance; formalise decisive argument where useful | OPEN until any P0 route genuinely closes |

Keep C1/S1/R1 in parallel, not a serial gate chain. The paired arithmetic consumer is an optional constructive lever, not an endpoint prerequisite. Phase identifiers are research obligations not claims of existing Agda/Lean theorem declarations. Explicitly distinguish full-code carrier totality from fixed finite tests, nonuniform advice and randomized promise solving. If a proof cannot bridge restricted geometry to arbitrary computation, record that failure rather than claiming a separation. Do not assign invented completion percentages or deadlines.

### F. Actual execution and scope

Executed local Python/SymPy with 90s timeout (completed in about 4.7s here), scripts/check_p0_continuation_bidi_20261125.py, git hash-object a8980391109e4ca21ab3aaf11f7bda108d6b4fe6 matching both GitHub readback blobs. All 256 original 3-bit support fixtures including empty, 255 nonempty; 7371 seed masks; 1700 positive and 1700 constant-margin descent steps using first qualifying child not maximum; 1530 bit recovery probes; 10240 identity-prefix vs explicit completion comparisons; 723087 paired potential multiplicity checks; 729 final-trit count triple controls (19 positive). SymPy symbolic paired-potential identity. These are supplied-support reference checks and compressed isotypic dot products, NOT source-aware polynomial selectors or actual WD matrix/production factor runs. General reductions are mathematical arguments, not extrapolations. No CI, native kernel, or other programme changes. Three literal P0 endpoints remain OPEN; no Clay solvedness. Next substantive work: paid C1-a/b or C3 construction, unrestricted S1/S2 obstruction, or total R1 proof, not another decoder or formal inventory. Preserve zero mode, signed residual, inhabited neutral, original source and independently indexed hyperfabric.

## 53. P0 maximum cut — exact selector PP barrier and loss-tolerant Clay equivalence (2026-11-25)

Scope exclusively P vs NP. Actual starting heads #1548 251039780d7b7098b3352aefa6283632c8623365 and #119 11c61fa7e48333bbb83fbffbd10e83f93cc91fc2. Reopened actual Langlands #1549 f9d88726f64512bdfad2995564e657c5db4d465b, roadmap blob 33e281a31673e941a95afe0f79bb0d2863165255 through R251. R245 distinguishes step sign from loop sign, R249 supplies paired signed first/second moments; these are optional donors, not new prerequisites. Retain original source identity, signed and inhabited neutral sectors, and independent seed/precision/loop indices. No Langlands edits or rerun of its receipts. This cut strengthens and corrects Section52 C1-a: exact positivity or exact fixed-threshold preservation on ALL promised prefixes is equivalent to P=PP; neither is necessary for the Clay constructive route as currently specified. Replace it with the loss-tolerant theorem below, exactly equivalent to P=NP. Classical PP/GapP, majority circuit satisfiability, Stockmeyer approximate counting, Valiant–Vazirani and conditional expectations retain attribution; DASHI application is the specific promised selector reductions and signed moment bound. No claim of literature priority.

### A. PP-hardness of exact positive-child continuation on a promised positive parent

Take a Boolean circuit C on r>=1 bits x, c accepting inputs, M=2^r. Construct polynomial-size source on binary labels (z,u,x) with z one bit and u two bits, plus two multiplicity bits a. Require: u=0, a=0 and C(x) if z=0 or not C(x) if z=1; OR u=1,a=0 for every x; OR u=2, first x bit=0,a in {0,1,2}; OR u=3,z=1,x=0,a=0. Thus for each label the witness count is 0,1,or3. Use k=r+3 and fixed rectangular Toeplitz matrix [I_k | 0] selecting exactly label bits in that order, ignoring multiplicity bits and appended deterministic unique-extension circuit-to-3CNF auxiliaries. All translation trits free; u here is the label mode, not the seed prefix. Each completed seed selects its unique binary label if present, otherwise H=0. The first translation child b=0 selects z=0, b=2 selects z=1, b=1 empty. Since Psi(1)=1, Psi(3)=-3, child numerators in source-z order are N0=c+M-3M/2=c-M/2, N1=(M-c)+M-3M/2+1=M/2-c+1, and N2=0 for the remaining empty child. Common denominator 3^(k-1). Sum 1, so parent always strictly positive, and exactly one child positive: b=0 iff c>M/2, b=2 otherwise. This is a one-call polynomial reduction from strict majority circuit satisfiability to any deterministic exact positive selector with the Section52 all-positive-prefix promise, not merely hardness of comparing arbitrary unpromised scores. Source representation polynomial, C and NOT C are evaluated by deterministic gates; not enumeration of c or x. Conversely a PP oracle tests each child's sign by GapP characterization: numerator counts original witness-completion pairs minus ordered distinct witness-pair-completion triples, both #P via unique binary encoding of trits. Select any positive child, arbitrary output off promise. Thus a uniform polynomial exact positive selector exists iff P=PP. P=PP implies P=NP but converse not established. A lower bound only for this selector is not a sufficient P!=NP theorem. Reference: Fenner, Fortnow, Kurtz, Gap-Definable Counting Classes, JCSS 48 (1994), https://www.cse.sc.edu/~fenner/papers/gaps.pdf; standard PP-completeness of strict majority circuit acceptance follows directly from polynomial-time computation with a polynomial random bit string.

### B. Fixed margin 1/12 still encodes PP, even with H<=1 on every completed seed

Let w odd and >=r+3, D=3^w, B=floor(D/12); D mod12=3, so D/12=B+1/4, B>=M/2 and B+M/2+1<=D. Choose k=w+1 and fixed rectangular Toeplitz [I_k | I_k | 0] over F3 (diagonals 0 and -k equal1); first 2k binary variables grouped in two blocks; canonical digit lifts 0=(0,0),1=(1,0),2=(1,1). Auxiliaries appended and ignored, deterministic extension. Hash labels z in F3, a in [0,D) represented by w trits. Each label has one canonical binary lift and at most one satisfying assignment. Source accepts at z=0 all a<B-M/2 and, on disjoint interval [B-M/2,B-M/2+M), iff C(binary(a-(B-M/2))); at z=1 accept a<B-M/2+1 and on following interval of size M iff NOT C(binary(offset)); at z=2 accept a<B. Polynomial-size comparisons, ternary-to-binary arithmetic, C and deterministic gate extension, no count computation. First translation selects z=-b mod3. Child numerators in z order are B-M/2+c, B+M/2-c+1, B, all nonnegative because H<=1. Parent V=(3B+1)/(3D)=1/12+1/(12D)>1/12. Exactly one child strictly exceeds 1/12, at z=0 iff c>M/2, else z=1. Thus the exact fixed-margin selector on ALL promised prefixes is PP-hard; PP suffices by testing 12*GapP numerator minus the power-of-three denominator >0. Its polynomial solvability is also equivalent to P=PP. Constant threshold does NOT guarantee a constant gap from threshold: this parent can approach it exponentially closely. Section52 A's statement that the fixed-margin promise avoids exponentially small positive values remains true, but must not be read as avoiding exponentially fine threshold comparisons. These reductions do not establish hardness of a selector restricted to its own reachable descent trajectories or one permitted additive loss.

### C. Replacement constructive theorem: loss-tolerant signed continuation iff P=NP

For a proper seed prefix u of full length L=n+2k-1, require one uniform total polynomial-time algorithm S(F,k,u) with guarantee on V(u)>1/24: returns trit d with V(ud)>=V(u)-1/(24L). No requirement for exact sign or fixed-threshold preservation at arbitrary boundary inputs. Section51 root for a good k has V(empty)>1/12. Total loss at most 1/24 over L choices; all intermediate values strictly >1/24, hence every call on this path in promise and terminal Psi=1. Try all k<=n+1 using total clock, ignore malformed outputs. Section52 rank-one singleton bit probes have V(parent)=1/3 and only terminal values 1 or0, so the loss guarantee forces the unique correct translation. Apply S to compiled singleton chart and all its bit probes with their own L, verify full original assignment. At least one chart yields a witness when F satisfiable; none can verify when F unsatisfiable. Polynomial chart, seed, verification and decode costs as Section52. This proves S implies P=NP.

Reverse: under P=NP, the polynomial hierarchy collapses to P. For any positive parent, denote its three child distributions H, normalized mu=E H, nu=E[H(H-1)], V=mu-nu. Each V<=1 by pointwise Psi<=1. Since parent V=(sum child V)/3>0, every child V>-2. Jensen E H^2>=mu^2 yields V<=2mu-mu^2, so mu<1+sqrt(3)<3 and nu=mu-V<5. Therefore both nonnegative normalized moments have bounded magnitudes despite potentially exponentially large individual H. Their unnormalized numerators are #P counts of (completion,x) and (completion,x,y distinct ordered) with original source and hash predicates, using unique encodings of trits. Divide by the known denominator 3^(remaining trits); no unknown normalization. By Stockmeyer's deterministic relative approximate counting for #P with polynomial-hierarchy oracle (inverse-polynomial accuracy, polynomial runtime), approximate each numerator within relative error eta=1/(384L), zero exactly (can check zero with NP). Under P=NP that oracle computation becomes ordinary deterministic polynomial time; multiplicative factor 1+eta implies absolute relative error <=eta. Hence normalized signed V estimate has absolute error <=eta(mu+nu)<1/(48L) for each of the three children of a positive parent. Select maximum estimate: true child V>=maximum true child V-1/(24L)>=parent V-1/(24L). This establishes converse under P=NP and in fact gives a polynomial-hierarchy-oracle implementation unconditionally. Estimates off promise may be arbitrary as regards additive signed accuracy; underlying count approximation algorithms still have total polynomial oracle clocks. Classical sources: Larry Stockmeyer, The Complexity of Approximate Counting (STOC 1983), https://doi.org/10.1145/800061.808740; On Approximation Algorithms for #P (SIAM J. Comput. 1985), https://doi.org/10.1137/0214060; Auditable Algorithms for Approximate Model Counting, https://arxiv.org/abs/2312.12362. Do not conflate deterministic approximate counting with exact #P evaluation or claim unconditional polynomial counting. This is a two-way Clay endpoint equivalence for S; no S without oracle yet. In particular an unconditional lower bound ruling out every uniform polynomial S in the ordinary model would imply P!=NP, unlike A/B exact-selector lower bounds.

### D. Controlling roadmap and donor boundary

C1-a is now the loss-tolerant selector in C (or another direct SAT-equivalent algorithm), replacing exact positivity/threshold preservation as controlling sufficient target. A/B are optional stronger P=PP routes, not serial requirements. C1-b identity translation/viability and direct C3 remain exact P=NP routes from Section52. C2 final-trit singleton solving remains open independently and is implied by C. The Langlands R245 loop-sign repair retains orientation, R249 pair/diagonal gives signed V as in Section52D; computing arbitrary exact loop coefficients or exact sign cannot be presumed efficient. The bounded positive-parent moments furnish a precise target: source-aware relative approximations only to sufficient accuracy on this domain, or directly select a loss-tolerant child. No full count, monodromy spectrum, orbit classification, general epsilon factors or arbitrary PP decisions required. Keep actual source/seed equality and original witness pair indices. S1 unrestricted superlogarithmic original resource lower bound and R1 full-code deadline totality remain OPEN, existing endpoint transports unchanged. Pursue S1/R1 in parallel; no reduction from PP separation to P vs NP asserted. No new unconditional SAT algorithm, unrestricted lower bound or deadline totality proved. All three prize exits remain open.

### E. Actual local acceptance

Executed scripts/check_p0_slack_continuation_20261125.py locally using Python exact rational arithmetic and SymPy, timeout90; git hash-object bc6ebca32d9172e2db544b89b5ced59dddc6f264, identical GitHub blobs on both branches. Results: 132 positive-selector majority-count cases with 44688 labelled-fibre computations; 67 fixed-threshold cases with 2125035 ternary-labelled-fibre computations; 1092 actual rectangular Toeplitz canonical-lift comparisons; 2193 child moment bound checks and 46784 extreme independent relative-error controls for loss-tolerant selection, symbolic signed moment identity. Source fixtures use explicit interval acceptance x<c as finite count representatives, not arbitrary circuit execution or proof-kernel validation; general majority reductions and approximate-counting converse are mathematical arguments above. No actual source-aware unconditionally polynomial selector or approximate-counting oracle implementation, no CI, no native Agda/Lean kernel and no other programme edits.

## 54. P0 endpoint audit — existing constructors, rare-event obstruction and bounded occupancy geometry (2026-11-25)

Scope exclusively P vs NP; user requests geometry-forward, steelman, BIDI, reverse-solve, exact remaining gaps/constructors/welds, prize mathematics first. Starting verified P vs NP heads 172e2a301fff / e7e9c3b2c111. Actual Langlands Agda #1549 reopened at e00e26844db5dc972b62e7b7c1e87fb5ed40d470, roadmap blob a86ea7e1f477d7c7277bd2254ba03df5f508f17b through R259. R257 same-seed diagonal and wild orbit identities are donors; no new Langlands task, no epsilon computation required. Section53 exact selector PP barrier and loss-tolerant Clay equivalence remain valid. Preserve original zero, signed residual, inhabited neutral and independent source/time/refinement/seed/precision/resource indices; selecting one consumer never identifies entire underlying fibres.

### A. Actual constructor reuse audit (source readback, not new kernel acceptance)

Agda paths below relative to DASHI/Mathematics/Complexity/ at starting head:
- BooleanFormulaSATSelfReductionExact.agda blob 5991b2b90cf03be35769ca5ef6d8b47622aab24f: evaluate, restrictionEvaluation, satisfiableSplits, liftFalse, liftTrue, booleanSATSelfReduction, SATDecisionOracle, recoverSatisfyingAssignment, satSearchUsesExactlyVariableCountQueries. Decision oracle or viable branch information is an input, not constructed universally.
- PNotEqualsNPSelfDiagonalRestrictionFamilyExact.agda blob d8028d3637405af27dd1c237552e6e6bb8bb0651: RestrictionDerivation, RestrictionNode, rootNode, falseChild, trueChild, reachableShannonLaw, cookRestrictionRootRoundTrip. Reuse original-coordinate restriction transport.
- PNotEqualsNPShannonRoutingDefectExact.agda blob 65a0a8b02871fc49ad3f3474af10e5e55fbd42a2: actual Policy, score, scoreSound, Boundary, liftToRoot, boundaryWitness, boundaryRootWitness, locate, defectFreeComplete. Source explicitly says native kernel checking remains outstanding. locate requires rejected score AND an existing SAT.Satisfying current; follows satisfiableSplits. Not an oracle-free polynomial counterexample finder. defectFreeComplete consumes absence of every Boundary, not proof of that absence.
- PNotEqualsNPPolynomiallyClockedStandardCandidateExact.agda blob 0af35005027588b651982a5dd538e33d99981b0d: PolynomiallyClockedStandardCandidate, candidateConcreteClockReceipt. PNotEqualsNPPolynomiallyClockedCandidateTapeExact.agda blob 7e5e81dee6fbfe2f765a826282abddc9ca934932: polynomialStepBudget, PolynomiallyClockedCandidateTape, canonicalPolynomialClockBoundary. Reuse clock/candidate boundary; not deadline totality.
- PNotEqualsNPAnchoredCollisionEquivalenceExact.agda blob 5bc4f3ab8274c1f23eba2d3f3c2a20472cdd89e0: universalSATFailureCollisionEquivalence and both directions. PNotEqualsNPDirectSATLowerBoundExact.agda blob 0838b3252b3ffb91993e4cb47a5d5c06a00e4fe1: PolynomialSATDeciderCandidate, AnchoredPolynomialSATDeciderCandidate, SATDecisionFailure, UniversalPolynomialSATDecisionFailure, universalDecisionFailureGivesSATLowerBoundProducer, universalDecisionFailureClosesPNotEqualsNP; actual anchored collision equivalence. Correct full filename includes PNotEqualsNP prefix.
- PNotEqualsNPClayCoreExact.agda blob fc5aed11a1bc0a095ba3c64c7a3468bd059d1aae: SATLowerBoundProducer field satNotPolynomialTime, satLowerBoundProducerClosesClayCore, pNotEqualsNPClayCoreIsExactlySATNotInP. Requires actual PNotEqualsNPEstablishedBackground cost and producer, not arbitrary cost semantics.
- Lean Integration/ScopedVerifierConsumerSufficiency.lean blob 1afa1425acb4130fe545f626f2513d9e842f87a5: ConsumerFactorization, factorizedConsumersEqual, collisionBlocksFactorization, adequateRefinementMustSeparate; restricted consumer sufficiency, no unrestricted cost bound. MillenniumExternal/TerminalCensus.lean blob 9bd45df6546ddcefe919341012c72b139aefea28: pVersusNPLane and terminal census, not native endpoint proof. Changed-file audit of #119 contains roadmap and Python/JS scripts, no new Lean theorem file. Prior owners #1040, #1129, #1474, #1502, #1006 cited in earlier roadmap; not all re-read here.

### B. Rare-event obstruction to blind signed-moment sampling even on positive parent

Let w>=2 even, D=3^w, M=3^(w/2), fix k=w+1, and use actual rectangular Toeplitz [I_k I_k 0], canonical binary lift of trit labels as in Section53B, ignoring multiplicity and deterministic auxiliary coordinates. Labels are (z,a) with z one trit, a in [0,D); first free translation selects z=-b mod3 and remaining translations each select one a. Choose good child g and a hidden exceptional label a_z for each other child. Accept multiplicity index j=0 for EVERY label, additionally 1<=j<=M iff z!=g and a=a_z. Use ceil(log2(M+1)) binary bits for j, polynomial-bit comparisons and unique-extension Boolean gate compilation. Every completed seed has H=1 except one exceptional completion in each bad child, where H=1+M. Source description polynomial in w. Psi(1+M)=1-M^2, so V_g=1, V_bad=1-M^2/D=0, V_parent=1/3. Normalized mu_bad=1+M/D<3 and nu_bad=(M+M^2)/D=1+M/D<5; all Section53 conditions hold. The Section53 loss-tolerant selector must choose g.

Blind leaf-count oracle obstruction: with q<D deterministic adaptive leaf queries, run on all-ones answers, then choose g different from its returned child and choose a hidden exceptional label not queried in each bad child. Transcript unchanged, wrong answer. For randomized observers choose g uniformly and hidden labels independently uniformly. Couple to all-ones transcript with same random coins; probability any hidden exceptional query occurs <=q/D by union bound on this baseline transcript, and probability baseline returned child equals g is 1/3 (or <=1/3 for malformed outputs). Thus success <=1/3+q/D; success>=2/3 requires q>=D/3. This lower bound is in a black-box completed-seed count model, even with exact counts and positive margin, not source-aware computation, partial aggregate oracle, or unrestricted SAT lower bound. The explicit source visibly encodes g and exceptional labels, so cannot be called hard for arbitrary algorithms. Finite first/second moment bounds do not bound variance of Psi; here variance in bad child equals D-1. Do not infer efficient empirical signed-moment approximation from normalized mu,nu alone. No general source contraction is supplied by Langlands same-seed pairing.

### C. Bounded occupancy continuation: alternative exact Clay-equivalent constructive geometry

Define B(s)=max(0,Psi(s))=1_[H_s=1]; retain H and signed fibres separately, so empty and H>=2 are not identified as underlying objects. Define U(u)=E[B(s)|seed extends u]. U>=V and U=(sum child U)/3, 0<=U<=1. Section51 good-k root U(empty)>1/12. Require uniform deterministic polynomial-time total selector T on proper prefixes, on promise U(u)>1/24 returns d with U(ud)>=U(u)-1/(24L), L full seed trits. Over L steps loss <=1/24, all calls in promise on good path, terminal U=1 gives singleton. Try all k<=n+1; Section52 rank-one singleton probes also work with U(parent)=1/3, terminal values 1 or 0. Compile chart uniquely, verify reconstructed original assignment, reject malformed/off-promise outputs; yields P=NP.

Conversely under P=NP, evaluate B(s) by SAT search for one original witness then SAT decision on source with blocking clause for that witness. Polynomial time on arbitrary completed seeds under hypothesis; count encodings of completions with B=1 as #P under that hypothesis. Stockmeyer relative approximate counting with polynomial hierarchy oracle as in Section53 (collapsed to P under P=NP), relative accuracy 1/(48L) gives additive error <=1/(48L) for normalized U in [0,1]. Select largest estimate; true loss <=1/(24L). Zero exactly. Thus polynomial bounded occupancy selector iff P=NP. This is an alternative to signed slack, not compulsory alongside it. It avoids rare-event variance: if B oracle supplied, Hoeffding/union bound estimates each child to epsilon with O(epsilon^-2 log(1/delta)) independent samples for failure probability delta, hence randomized selection on promise with inverse-polynomial additive error. But ordinary source-aware evaluation of B is not free, and random sampling does not establish deterministic selection. Arbitrary 0/1/>=2 capped source counting would itself decide SAT, so do not promote it to a supposedly cheaper compulsory primitive. For rare-event construction B good=1, B bad=1-1/D, so exponentially rare losses are no longer compulsory to distinguish at inverse-polynomial tolerance. This is a consumer-specific projection, not a claim that signed residual can be globally discarded.

An alternate sufficient split avoiding full uniqueness testing on arbitrary charts: a total polynomial clocked singleton witness producer W, plus uniform polynomial deterministic hitting construction for the polynomial-size seed predicate A(F,k,s) that compiles the chart, runs W and verifies the decoded ORIGINAL assignment against F and seed. On good k, acceptance probability >=1/12 from singleton probability (multi-witness successes also acceptable). One seed with verified success suffices; empty source gives no verified success. Hitting is only required for these explicit bounded-size verifier circuits of density >1/12 (not arbitrary black-box supports or exact PP counting). If P=NP, W exists and deterministic seed search for A=1 by SAT on its polynomial circuit gives hitting. Conversely W plus such hitting gives P=NP. This clarifies alternate gaps and avoids requiring an exact singleton certificate on bad charts. Neither W nor uniform hitting paid. Standard approximate counting and concentration results retain classical attribution; DASHI contribution is the particular source-indexed rare-event anti-control and endpoint-directed combination, not claim of literature priority.

### D. Reverse-solved complete remaining endpoint inventory

| Route / lemma | Exact deliverable | Owner / current boundary |
|---|---|---|
| C-A signed slack | Uniform ordinary polynomial total selector satisfying Section53 loss inequality on every promised positive parent | OPEN; iff P=NP, no PP exact comparisons necessary |
| C-B occupancy slack | Uniform ordinary polynomial total selector satisfying Section54C U-loss inequality | OPEN alternative to C-A, iff P=NP |
| C-C split | Polynomial clocked singleton W AND deterministic uniform hitting for its verified acceptance circuits | OPEN alternative; randomized isolation alone gives RP=NP if W exists |
| C-D direct | Uniform polynomial standard SAT solver or viable original prefix selector | OPEN alternative, BooleanFormulaSATSelfReductionExact transports decision to witness |
| C-weld | Actual implementation polynomial bit cost, original truth-graph compiler/unique extension, seed and output verification, original witness recovery | mathematical Sections49/52/53/54 supplied; attach to actual algorithm, no exotic prerequisite |
| S-A unrestricted | For every fixed c there exists satisfiable original F with kappa(F)>c log2(|F|+2), or equivalent unrestricted J obstruction | OPEN, Section47/49 transport; cannot derive from blind sampling or restricted representation |
| S-B alternate obstruction | Rule out every uniform polynomial C-A or C-B (not stronger exact PP selectors) or every ordinary polynomial SAT solver | OPEN, by exact BIDI equivalence; permits source-aware computation and arbitrary bypasses |
| S-weld | Standard model coverage, original SAT encoding/NP background, real cost transport to SATLowerBoundProducer | classical identity fallback and existing endpoint consumers; native concrete cost attachment not verified here |
| R-A full-code | Total computable deadline B(e) on full valid clocked candidate carrier bounding first genuine gain of each incomplete e | OPEN, G128 and Section50C; nested incomplete-only deadline insufficient |
| R-B alternate | Prove every clocked candidate incomplete / universal genuine gain search total, or every universal-budget residual nonempty | OPEN, same literal separation; do not presuppose witness needed by locate |
| R-weld | Genuine original failure/collision verification, explicit clock/anchor, decidable finite search to Bad(e), delayed-failure contradiction under hypothetical W_* | G122/G128 and existing clock/anchored owners; mathematical conditional transport, actual totality unpaid |
| Final | Self-contained standard-model proof and independent expert scrutiny; native formalization only after or where required for mathematical argument | OPEN; no Clay solvedness claim |

These are alternative endpoints and conditional transports, not a sequence of micro-gates. Strongest immediate constructive research target: source-aware bounded occupancy or signed slack selection without NP/PH oracle (or W plus verified-circuit hitting); strongest separation target: unconditional obstruction that includes all ordinary algorithms, not merely leaf sampling; reverse route: actual totality proof, not diagonal machinery reuse alone. Keep all three P0 exits in parallel. Do not infer geometric equivalence guarantees an efficient algorithm or a lower bound; these are exact formulations of the remaining major theorem. Existing constructors already provide much of the transport. No full epsilon evaluation, orbit inventory, monodromy refinement, FRACTRAN compiler, native proof inventory or exact PP comparison as compulsory gate.

### E. Fresh local execution

Executed /tmp/check_p0_bounded_occupancy_20261125.py under timeout90 in local container, Python exact rational arithmetic and SymPy. Git hash-object 5826e34cf9e72ebd6ff2ab4f5f9f900fede1da89; matching script scripts/check_p0_bounded_occupancy_20261125.py committed and read back both branches. 36 rare-spike cases, 199260 leaf evaluations, 108 normalized moment checks, 4368 actual Toeplitz canonical-lift checks, 7371 seed masks, all 255 nonempty 3-bit supports, 1700 perturbed bounded occupancy descent steps and 765 singleton bit probes. Symbolic signed spike identity. These are supplied-support / explicit finite checks, not production source-aware selectors, general SAT solver, native kernel or GitHub CI. No other programme modifications. All three Clay exits remain open.

## 55. P0 maximum cut — actual shared-seed factor contraction and approximate resource weld (2026-11-25)

Scope: literal Clay P vs NP exclusively, user reiterates P0 and supplies Section54 and Langlands R260–267 as inspiration. Verified starting P vs NP heads c60cb5cab407485388ff13e3660da090a445c9b4 / 8360b6edb7fd14a7ba54baa7dfda5bff583496fb. Actual Langlands Agda #1549 reopened at e8821c8bfc1819763da37f7648f530cfb7594446, roadmap blob a26fc6c33ac9db86e19f899a4747e2a0e9be186f through R267. R264–267 and shared-index R257 supply donor strategy, not a new Langlands endpoint. Actual same-branch source owners reopened DASHI/Core/QueryFactorisationSufficiency.agda blob 98c592232292bbb6c5f0df047c8df3fd42be30d3 (FactorsThrough, StaticSufficient) and DASHI/Core/ResidualFibreLowerBoundExact.agda blob b0fc9a0c998d0fc4d7ff0c3b224599f915cf78fe (ExactFibreReopening, exactResidualInjectiveOnEveryFibre, DynamicallySufficientPair). These are structural constructors; they do not construct polynomial-time SAT solvers or charged compressed messages. Reuse Section43 shared reverse scalar, Sections49/51/53/54 signed Toeplitz source and loss-tolerant endpoint. Classical sum-product, tree decomposition and variable elimination retain attribution; DASHI application is the explicit shared-seed source contraction and weighted mixed-width / approximate selector weld here. No claim of literature priority. Keep zero mode, signed residual, inhabited neutral, original source and independent seed/time/refinement/precision/resource indices.

### A. Actual two-copy source graph without an explicit inequality or pair enumeration

Given original Boolean width<=3 source F(x), n variables, k hash rows, L=n+2k-1 seed trits (Toeplitz diagonals and translation), prefix u, construct the actual mixed factor graph G_u. Domains binary x_i, ternary s_j and r_(i,j) accumulator. Use original clause indicator factors, unary prefix pins, r_(i,0)=0 and factors r_(i,j+1)=r_(i,j)+s_(i-j+n-1) x_j mod3, r_(i,n)+s_(n+k-1+i)=0. O(N+nk) variables/factors, constant factor arities; for each seed and original witness candidate there is exactly one accumulator lift before output constraints. Deterministic auxiliary gates of original source likewise have unique extension when compiled. Each completed seed contributes H_s original witnesses to first partition count Z1=sum G_u. Duplicate all witness and accumulator variables and their incident factors but SHARE the seed variables and prefix; second partition count Z2=sum G_u(s,x,r) G_u(s,y,r') equals sum_s H_s^2. D=3^(L-|u|), mu=Z1/D, nu=(Z2-Z1)/D, and V=(2 Z1-Z2)/D. This is exact same-seed tensor/diagonal transport of Sections52D/54 and R257, with the diagonal removed by subtraction Z2-Z1 rather than a global x!=y predicate, extra disequality circuit or explicit pair enumeration. No new arithmetic representation required. If using independent seed copies one instead obtains Z1^2, and normalized second moment then squares the mean, not mean of squares. Original source constraints and auxiliary provenance are retained even for H=0 or H=2. The factor graph is polynomial to construct but not generally polynomial to contract.

### B. Charged exact mixed separator bound and child marginal reuse

For any supplied polynomial-size tree decomposition of the first graph primal scopes, write a_B for shared seed vertices and b_B for all other vertices in a bag B. Replace B by shared seed set plus both labelled copies of nonseed vertices; all paired factors are covered and connected occurrence subtrees retained, giving a tree decomposition of the paired graph with weighted bag cardinality W=max_B(a_B+2b_B). No duplication of seed variables. Ordinary bottom-up sum-product messages over separator assignments compute both Z1,Z2, with local table cardinalities <=3^W. Assign each factor to a covering bag, count each internal coordinate once, propagate products and sums; isolated variables must be included in decomposition or charged domain factors. All intermediate integer values have O(poly(N)) bits (products/sums of nonnegative 0/1 factors and assignment counts, for polynomially many variables); polynomial bit arithmetic and polynomial decomposition/factor sizes included. Time poly(N)*3^W, memory similar, no seed enumeration mandated. For all three child values at a prefix, leave next seed coordinate uneliminated in both contractions, read three entries of final marginal vector, sharing all intermediate messages that do not depend on that coordinate. Adding that coordinate to every bag if necessary increases W by at most one. This is same conditional signed descent from Section53; exact contraction supplies maximum-child selector on promised parent whenever charged decomposition W=O(log N), with all relevant prefixes and chart/bit-probe costs likewise controlled for a whole-run algorithm. This does not establish a new general tractable SAT class (small original primal width already often suffices), nor existence/discovery of a suitable mixed decomposition on all inputs. Actual finite script uses greedy variable elimination separately for parent and children, not a supplied optimal tree decomposition or single marginal implementation; latter bound/algorithm is mathematical.

### C. Steelman raw-width obstruction and paid alternate bypass

For k=n>=2, take m=floor(n/2) consecutive original x_j, j=0..m-1. In the raw factor graph, x_j shares an accumulator-step factor with each seed diagonal s_d, d in [n-1-j,n+k-2-j]. Common interval [n-1,n+k-m-1] has k-m+1>=m diagonal vertices; hence primal graph contains K_(m,m). Contract m-1 disjoint cross edges to obtain K_(m+1) minor (remaining one vertex on each side still adjacent), so treewidth>=m. This holds even for empty conjunction F=true, with immediate all-zero original witness. Pinning/semantic contractions and alternative ordinary algorithms can bypass this raw graph; the lower bound is on its treewidth and explicit decomposition scheme only, not time required by arbitrary source-aware algorithms. Do not force k=n or a specific representation on the solver. Likewise the factorisation/reopening structural owners ensure adequacy of an already supplied representation with residual, not inexpensive construction. This is a scoped anti-control to inferring universal hardness from the large mixed graph, not a separation result. Exact general comparison is PP-level as Section53, so proving this exact contraction cannot be cheap would not on its own prove P!=NP.

### D. Reverse-solved approximate contraction weld, exact ordinary endpoint remains open

At every child of a positive parent Section53 gives normalized Z1/D=mu<3, (Z2-Z1)/D=nu<5, so Z2/D<8. If nonnegative approximations satisfy |Zhat_i-Z_i|<=eta Z_i (zero exact), then |Vhat-V|<=eta(2mu+Z2/D)<14eta. Choose eta=1/(768L), giving <1/(48L); choose max estimated child, true loss <=1/(24L). Whole-run signed slack selector is sufficient and necessary for P=NP as Section53. This is an alternative to approximate occupancy Section54, not an additional compulsory gate. For a contraction tree with Q local message operations, a sufficient representation-level weld is: each local operation given compressed nonnegative child messages and original local factors produces a compressed nonnegative pointwise approximation to its ideal sum-product, with envelope factor (1+delta) and reciprocal, exact zeros, delta=eta/(4 max(1,Q)). Products add log-errors from disjoint child subtrees and sums preserve common multiplicative envelope; hence induction gives root ratio bounded by (1+delta)^Q<=exp(eta/4)<=1+eta for eta<=1, and reciprocal below, yielding required relative error. If reuse a DAG, account for actual error multiplicities or prove a tighter bound, not simply count nodes when products repeat shared operands. Charge actual encoding, local factors, lookup/evaluation, local approximate contraction, arithmetic, message-size and construction costs polynomially, including any zero decisions and decompositions; no assumed free oracle for representation discovery. A polynomial-size tree decomposition alone does not pay local costs if bags are wide. The pointwise envelope criterion is sufficient, not necessary; a selector may compute only the final estimates or avoid moments entirely. No proof of general existence of those representations/operations; exact zero handling may itself encode hard source support. Existing FactorsThrough/ExactFibreReopening can attach semantic sufficiency once an actual approximation contract is proved, but do not supply uniform polynomial complexity. Preserve actual same-seed identity and original witnesses; do not identify residual neutral with absent support.

### E. Actual source-aware execution, not supplied-support evaluation

Executed locally under timeout90: /tmp/check_p0_shared_seed_contraction_20261125.py, Python exact integer/rational arithmetic and SymPy; Git blob 9e58f58ce6fe8ce7435e8385cc5b7713c9acd79f matches both committed scripts/check_p0_shared_seed_contraction_20261125.py. 36 seeded actual CNF/prefix cases n=1..3, k=1,2; 144 parent/child source graphs, 288 Z1/Z2 comparisons against independent brute enumeration; 36 conditional averaging identities, 80 parent/child instances with Z2*D != Z1^2 (shared seed essential). Actual 0/1 clause and ternary accumulator factors constructed from source, then greedy minimum local table cardinality elimination; no satisfying-support table fed to contraction. Maximum intermediate candidate row count 162 single, 5184 paired; total row visits 45312 single, 496340 paired (not wall time or full bit-operation count). Brute enumeration is independent reference only; algorithm uses no oracle. All assertions passed; symbolic identity checked. No GitHub CI, native kernel, actual WD computation or general polynomial bound claimed.

### F. Updated controlling deliverables

C-A: general loss-tolerant signed selector OPEN; A–B now give executable ordinary source-aware exact contraction on the charged mixed-width regime, D gives precise sufficient approximate-message/error/cost weld. Need a uniform polynomial contraction/selection for unrestricted source (or direct alternative), not another finite check or assume width bound. C-B bounded occupancy, C-C singleton+verified circuit hitting, C-D direct SAT remain alternative OPEN exits as Section54. S-A/S-B unconditional unrestricted witness-resource/selector obstruction OPEN; C's raw graph lower bound cannot replace it. R-A full-code deadline totality / R-B genuine gain nonemptiness OPEN; G128 and actual anchored constructors remain conditional transports, not new solved results. No new reverse totality or unrestricted separation lemma obtained in this cut. All endpoints remain P0 in parallel. Next substantial mathematical attack: find compressed nonnegative source-message operations that pay D, or a different source-aware selector/direct witness construction; attack unrestricted lower bound/full-code deadline in parallel, allowing ordinary sharing and bypasses. No Langlands or other branch edits; no infrastructure serial prerequisites.

## 56. P0 maximum cut — Toeplitz stationary elimination, source-only Fourier contractions and reverse resource weld (2026-11-25)

Scope literal Clay P vs NP exclusively. Verified starting #1548 head 3c58f71382775b579918f6119d6d8d281d0f96ec and #119 head fd9aa0b4c9004effd60cdfc56066dcd4016bb242. Reopened actual Langlands Agda #1549 at c3ddd98c337a9eb91782984f73282991f203b66d, roadmap blob 66eaae451d1e79ab643f36ff617e5b63cd0692c8 through R274. R268–269 stationary elimination is a methodological donor (eliminate an affine group using character orthogonality); no local-field epsilon is a SAT primitive. Reuse Section49 triangular Toeplitz pivot, Section51 conditional ranks, Section43 weighted source elimination/adjoints, Sections52–55 endpoint and shared-seed contraction, FactorsThrough and ExactFibreReopening owners audited in Section55. Standard finite Fourier orthogonality, Gaussian elimination, sum-product and tree decomposition retain classical attribution. The application below eliminates mixed seed graph inflation, not a new general complexity theorem. Preserve original witness coordinates, signed differences, zero and inhabited neutral, seed/coefficient/probe rank/source/time/precision indices separately.

### A. Exact triangular elimination of the entire free diagonal seed

Take A_(i,j)=a_(n-1+i-j) over F3 for 0<=i<k, 0<=j<n. Seed order is ascending n+k-1 diagonals followed by k independent translation trits. At a prefix fixing exactly the first p diagonal coefficients (0<=p<=n+k-1), all translations still free. For distinct original binary x,y let j be first differing coordinate and d=x-y in F3^n. In row i the largest diagonal with nonzero coefficient in A d has index n-1+i-j and coefficient d_j!=0; lower-index terms may depend on other free or fixed diagonals. Set t_j=min(k,max(0,p-n+1+j)). Exactly rows i<t_j depend wholly on fixed diagonals. If any such row does not vanish, A d=0 has no completion. Otherwise each row i>=t_j has a fresh unfixed pivot, in increasing diagonal order; choose all nonpivot free diagonals arbitrarily and solve these k-t_j pivots uniquely, including dependence on earlier pivots. Probability of collision conditional on diagonal prefix equals 3^(-(k-t_j)) times indicator of zero in the first t_j rows. This is a concrete specialisation and simplification of Section51 affine ranks, not general stationarity of arbitrary nonlinear constraints. All b free gives probability 3^-k of h(x)=0, and for distinct x,y probability 3^-k times that collision probability of both zero. Define m=|S_F|, C_j number of ORDERED satisfying pairs first differing at j and agreeing in the first t_j fixed hash rows. Then
 mu=m/3^k, nu=sum_j C_j/3^(2k-t_j), V=mu-nu.
No free seed variable, translation or accumulator occurs in these source consumers. At p=0 all t_j=0, sum C_j=m(m-1), recovering Section51. At p=n+k-1 the formula becomes fixed-A collision count divided by 3^k. Distinguish row count t_j (determines free pivot exponent) from rank of its fixed suffix map (determines Fourier cost); replacing t_j in the probability by row rank is in general wrong. Original difference sign retained even though equality is one consumer.

### B. Actual source-only character contraction, paid width bound

On first-difference sector j identify the two witness variables for each i<j (common original prefix), retain both copies for i>=j, and add a binary disequality factor on x_j,y_j only. Duplicate actual original clause factors with the relevant variable renaming. The fixed-row linear map B_j is t_j rows restricted to columns j..n-1, using fixed a coefficients. For omega^3=1 primitive, indicator B_j(x-y)=0 equals 3^-t_j sum_(lambda in F3^t_j) omega^(lambda^T B_j(x-y)). Each character factors as unary weights in exact ring Z[omega] on the two witness suffixes with opposite signs; evaluate each term by ordinary variable elimination over actual source clauses, then sum and divide exactly. Can replace B_j by independent row basis of rank r_j to reduce character enumeration to 3^r_j, keeping t_j in A's probability exponent. No assertion of polynomial evaluation on unrestricted source. Given a polynomial-size original primal tree decomposition with bag size b, duplicate only suffix vertices in bags, identify earlier vertices, and keep original bag structure. Both clause sets covered and each variable occurrence subtree connected; the disequality is covered by any bag containing original x_j. Max paired bag size <=2b, unary weights do not add edges. Time poly(N) 2^(2b) [1+sum_j 3^r_j] (and hence poly(N) 2^(2b) 3^k), exact cyclotomic arithmetic coefficients with polynomial bit lengths: each weighted sum is over at most 2^(2n) assignments of roots of unity and finite local factors; final denominators powers of3 have polynomial bits. Standard rooted-tree assignment sum implementation avoids duplicated counting. Direct elimination code below uses greedy local scope ordering, not optimal decomposition or a rank-basis optimized implementation. This removes all raw mixed seed-accumulator width inflation from Section55 but trades it for character rank and original-source contraction. For b,k=O(log N) a genuine polynomial regime; original small treewidth SAT already tractable, do not claim an unrestricted breakthrough. The Section55 raw K_(m,m) anti-control is bypassed here; it was never a universal time charge.

### C. Translation stage: one original-source histogram, no repeated paired contraction

For fully fixed A, W_A(v)=#{x in S_F:Ax=v}. Fourier transform W_hat(lambda)=sum_(x in S_F) omega^(lambda^T A x) is a single-copy original-source contraction with unary weights. Invert W_A(v)=3^-k sum_lambda omega^(-lambda^T v) W_hat(lambda). If A has rank r, find basis for its image and identify image with F3^r via effective linear coordinate maps, invert there with 3^r characters, retain original embedding and original labels. For a translation prefix b_0..b_(e-1), restrict histogram to v_i=-b_i for i<e (original codomain coordinates even if using image basis). D=3^(k-e) is number of ALL translation completions, including outside-image empty fibres. Conditional mu=sum W/D, nu=sum W(W-1)/D, V=sum W(2-W)/D on this restricted set. U=sum 1_[W=1]/D likewise. Once histogram paid, every remaining translation decision for either signed or bounded occupancy can be read without repeating source contraction; use exact prefix sums/tree or scan. Inverse finite Fourier via separable radix-three transforms O(poly(k)3^r) ring operations, or direct inverse O(poly(k)3^(2r)) as in finite checker. Original decomposition gives single-copy cost poly(N) 2^b 3^r plus transform and histogram output cost. At full translation root Parseval sum_v W(v)^2=3^-r sum_lambda |W_hat(lambda)|^2 on image coordinates. This removes explicit paired graph and yields nonnegative spectral square sum for second moment, not free evaluation of weighted source amplitudes. With full column rank A and complete b, unique candidate x follows by Gaussian elimination and binary/source verification; no independent singleton solver needed on this restricted chart. But for sparse support, full-rank k>=n translation hit probability m/3^k may be exponentially small, so cannot replace the good-k isolation guarantee. No assumption that a histogram yields original witness identity except where explicit injective map, or existing source reopening/verification supplies it.

### D. Reverse-solved approximation, steelman and actual missing computational theorem

Section53 positive-parent bounds and Section55 approximation transport remain controlling. In coefficient stage, if nonnegative estimates of m and C_j individually satisfy relative error <=eta (including zero), then |mu_hat-mu|<=eta mu, |nu_hat-nu|<=eta nu since all rank weights positive. Thus |V_hat-V|<8eta on children of positive parents, and eta=1/(384L) suffices for loss-tolerant selector. This applies when the child is still in the coefficient stage (including fully fixed A with all translations free). For translation stage use restricted histogram first/second counts or any Section53/55/54 sufficient consumer; no full histogram compulsory. Critically, Fourier evaluation uses signed/cyclotomic cancellation, not Section55 nonnegative message envelope. Relative error on individual signed Fourier terms does not automatically yield relative error on their sum, and zero can arise from cancellation of nonzero terms. Need direct nonnegative count estimates, rigorous absolute error budget on the final sum, or a different source-aware selector. For C_j computed as average of character terms, additive per-term bound eps_j gives additive error <=eps_j in C_j; charged requirement sum_j eps_j/3^(2k-t_j) plus first moment error <1/(48L). This is a sufficient budget, not proof of a polynomial precision/representation algorithm. Likewise histogram can contain exponentially many occupied image values; do not charge full output to an algorithm that only needs a child decision. The remaining mathematical gap is a uniform polynomial source-aware contraction/selection for arbitrary F without requiring large exact Fourier packet, raw width, or generic PP-level computation. Exact rank elimination pays the seed-side transport, not witness-side counting. A bound for the chosen Fourier or factorization algorithm is not an unrestricted lower bound: arbitrary sharing, input rereads, nonlinear bypasses and direct SAT allowed.

### E. Actual local exact execution

Executed /tmp/check_p0_toeplitz_eliminate_20261125.py with Python, exact rational/cyclotomic integer arithmetic and SymPy symbolic identity, timeout90. Git hash-object e86085cf5e31fa3529fc75d660acac3ee2c8d31b matches both committed scripts/check_p0_toeplitz_eliminate_20261125.py. 24 seeded CNF fixtures n=1..4, k=1..3; 108 diagonal-prefix first/ordered-collision moment comparisons, 456 translation-prefix moment comparisons, 312 histogram entries compared, 2400 actual weighted source contractions. Clause factors are built from actual original CNFs; no satisfying support supplied to Fourier/variable elimination algorithm. Independent reference enumerates original assignments and remaining diagonal seeds, and direct histograms; used only for validation. All assertions passed. Exact Z[zeta3] represented by integer coefficient pair. Checker performs full row character sum, naive inverse, greedy scope elimination; rank basis and fast transform bounds are mathematical algorithm variants, not benchmarked implementations. No CI, native proof-kernel, unrestricted scaling or production arithmetic claim.

### F. Controlling roadmap

C-A: source-side polynomial loss-tolerant signed continuation OPEN; seed elimination and source-only weighted factor construction established, approximate/selector cost unpaid. C-B bounded occupancy, C-C singleton+verified circuit hitting, C-D direct SAT OPEN alternatives. C-weld original unique extension and verification unchanged. S-A/S-B unrestricted superlogarithmic witness-resource or loss-tolerant selector lower bound OPEN; no restricted graph/character-width result can substitute. R-A/R-B full-code deadline totality/genuine gain nonemptiness OPEN; G128/Section50 and anchored failure constructors conditional, no new reverse totality proved. P0 literal Clay endpoints remain open. Next target genuinely polynomial source-aware selector or unrestricted lower bound/deadline proof, not more arithmetic factor inventory. No Langlands or unrelated branch changes. Geometry-forward, steelman, BIDI and reverse-solve remain governing; theorem mathematics before formalisation.

## 57. P0 maximum cut — target-conditioned cut-syndrome contraction and original witness reopening (2026-11-25)

Scope literal Clay P vs NP exclusively; both current pasted files read as continuation/inspiration, with Langlands R275–282 treated as donor in this P vs NP thread. Actual starting #1548 head 207cf59afc07043c1f064ec8c70e41b0e2f6afb8 and #119 head e3f7948cc7f369046b518873ddce5a06f133c1bd. Actual Langlands Agda #1549 reopened at 837871a02d986ab01e657d865d16a4a990d45c21, roadmap blob 87fbb7365c8dfa47c52618c1c6718b02b190b400 through R282. R277–279 output-specific indexed packet is methodological inspiration, not a prerequisite to P vs NP. Reopened original G79–81 least joint linear overlap and G83 anti-control in own roadmap; reuse their geometry, Section56 stationary seed elimination, Section55 shared-seed diagonal, Section53 loss-tolerant continuation and existing FactorsThrough/ExactFibreReopening owners. Standard Gaussian elimination, linear-code syndrome interfaces and separator dynamic programming retain established mathematical provenance; application here is the targeted Section56 two-stage contraction with grouped original coordinates and witness receipts, not a claim of literature priority. Preserve zero, signed residual, original source and independently indexed target, rank, cut, seed, time and precision.

### A. Target-conditioned affine interface, rather than full character rank

Consider original Boolean constraints F and affine syndrome Ax=v over F3. For a binary variable-partition tree node U, let B_U be original vertices inside U that occur in a factor meeting the complement; I_U=U minus B_U. Use actual domain groups D_i of size <=d (d=2 single source, <=4 paired original coordinates), each with contribution a_i:D_i -> F3^r lying in supplied linear span P_i. For ordinary single bit, P_i=span A_i; for a bundled pair, span of the two appropriate columns, or span of their sum when equality is required. All supplied columns/bases have polynomial encoding. Write P_I=sum_(i in I_U) P_i, Q=sum_(i outside U) P_i. Given boundary assignment b, interior syndrome t must satisfy t in P_I intersect (v-sum_(i in B_U) a_i(b_i)-Q). This is either empty or an affine translate of P_I intersect Q, dimension lambda_U=dim P_I+dim Q-dim(P_I+Q), computed by ordinary Gaussian elimination. The anchor can be found by solving the affine linear equation; subtracting it and retaining coordinates in an overlap basis is BIDI for this affine interface. Zero coordinate need not mean empty. The actual implementation below stores full polynomial-length syndrome vectors rather than explicitly projecting into a basis; the number of possible keys is still bounded by the affine dimension. Linear extendibility is a necessary filter, not sufficiency of actual outside Boolean completion. Actual nonnegative counts and original source factors enforce the latter at the root.

### B. Exact dynamic program and original witnesses

For each node store a table keyed by (boundary values b, total partial syndrome s=sum_(i in U) a_i(x_i)). Value is the number of partial assignments in that key satisfying every original factor wholly in U, subject to the necessary filter v-s in Q. Additionally retain one original-coordinate representative assignment or compact predecessor pointers for each nonzero entry. At a leaf enumerate its <=d local states, check all local factors, apply the filter. At join U=L disjoint union R, iterate child entries, multiply counts, add syndromes, and check all factors contained in U but not contained in either child. Every variable of a newly internal factor is in its child's boundary, since the factor crosses children. All parent boundary variables are likewise in child boundaries. Retain parent boundary assignment, apply parent linear extendibility filter, add counts into identical keys. For any parent assignment passing its filter, each child passes its own filter: the other child's actual syndrome plus a possible outside-parent linear syndrome lies in that child's outside span. Hence pruning loses no assignments represented in any retained parent key. Conversely every accepted child pair has disjoint original variable coordinates, gives exactly one parent assignment, satisfies the newly internal factors and meets the parent filter. This establishes exact count induction including zero and all inhabited fibres. At the root Q=0, B empty, so the entry with syndrome v gives exact count; absent entry gives zero. One stored witness is recovered by combining its labelled child witnesses, verify original factors and target. This is not an inverse from count to all original histories; retaining all valid predecessor edges or original source plus a rerun is needed for full enumeration. Do not materialize all witnesses if consumer needs only one.

Each message has <=d^|B_U| * 3^lambda_U keys, because fixing b fixes an affine coset of interior syndrome, translation to total s is injective. With b_max=max |B_U| and lambda_max=max lambda_U on a supplied polynomial-size partition tree, naive Cartesian child joins give poly(N)*d^(2 b_max)*3^(2 lambda_max) bit work; space poly(N)*d^b_max*3^lambda_max, allowing one polynomial-size witness per entry and polynomially many nodes. Matrix dimensions, factor checks, key length, count bit length, joins, construction and original verification are charged. For paired domains d<=4 gives poly(N)*2^(4 b_max)*3^(2 lambda_max). No full character enumeration, global syndrome histogram or exponential affine basis table is necessary. Tree discovery is not assumed free. This is an alternative exact count algorithm and upper bound, not a universal lower bound on other algorithms. An exponentially large state bound is not a proof of actual state size or required time.

### C. Apply the same original-coordinate constructor to both Section56 stages

For a diagonal coefficient prefix p, use Section56 A's t_j and rank weights. Compute m by single-source zero-row count, and C_j by bundled original (x_i,y_i) domains, restricted to equal pairs for i<j, distinct pair at j, both copies of F and linear equation B_j(x-y)=0 in first t_j fixed rows. For those rows only suffix columns j..n-1 need actual fixed seed coefficients, because the common prefix contributes zero. Then mu=m/3^k, nu=sum_j C_j/3^(2k-t_j). No mixed graph, no free diagonal enumeration, no 3^rank(B_j) Fourier loop. For fully fixed A and translation prefix b of e rows, let E select those rows. Use targeted single Z1 count of F(x) and EAx=-b; use targeted paired Z2 count of F(x), F(y), A(x-y)=0 and EAx=-b. The bundled columns of the latter are (A_i,EA_i) for x_i and (-A_i,0) for y_i. Each matching full syndrome determines exactly one translation completion; hence Z1 and Z2 are exactly sum H_s and sum H_s^2 over remaining translations, including empty fibres by normalization D=3^(k-e). V=(2Z1-Z2)/D. This avoids full syndrome histogram even during translation descent. A final selected singleton chart can reopen one original witness via the single-count table and verify directly if that table is paid; no separate singleton solver necessary on this restricted regime. A whole-run polynomial guarantee needs supplied/discovered partition trees with logarithmic combined interfaces for all queried counts, not just one favourable matrix. Since zero-row m already admits witness discovery on a bounded Boolean boundary tree, do not claim this is a fundamentally new general SAT tractability result. It is a concrete removal of auxiliary/global character-rank overhead from the actual chosen contraction route.

### D. Steelman and reverse-solve

High global rank need not create a large interface: for A=I_n, independent local column spans have zero intersection at every cut. With F=true and arbitrary fixed binary target, every node stores exactly one inhabited message. For the paired equation A(x-y)=0, grouping both variables for each original coordinate again gives disjoint coordinate spans; each node has a single zero-syndrome key whose count is 2^|U|. If separate x and y into different sides of a cut, overlap can instead be n. This exhibits a real cost difference from grouping and target conditioning; it also defeats inferring unrestricted hardness from global rank or a bad chosen partition. Even low syndrome overlap alone says nothing about arbitrary original Boolean constraints: take A=0, retain ordinary SAT. Source-aware decomposition discovery, arbitrary nonlinear bypasses and alternative solvers remain allowed.

Section55's nonnegative approximation transport now applies directly to these messages without the signed Fourier cancellation problem of Section56. Sufficient local contract: on the actual boundary-syndrome keys, each charged join supplies nonnegative multiplicative envelopes with controlled total error, summing only compatible original assignments. Section56's relative errors in m,C_j yield |Vhat-V|<8 eta on positive parents, while Section55 gives <14 eta using Z1,Z2. This is a sufficient condition only; exact-zero handling, constructing compact arbitrary messages, and combining them with polynomial bit cost are not paid by a dimension identity. In particular approximating all counts including exact zero may itself decide SAT, so a direct loss-tolerant selector remains an equally valid alternative. C-A/C-B open for unrestricted source; C-C singleton+verified-circuit hitting and C-D direct SAT alternatives unchanged. S-A/S-B unrestricted obstruction and R-A/R-B full-code deadline/genuine-gain nonemptiness remain open, with G128 and existing anchored constructors only conditional transports. No new unrestricted lower bound or totality proof. Endpoint mathematics first, not compulsory representation construction.

### E. Actual local exact execution and reproduction

Executed /mnt/data/check_p0_cut_syndrome_20261125.py locally with Python integer/Fraction and exact F3 Gaussian elimination, timeout90, no CI. 60 seeded original CNF fixtures (n=1..5,k=1..3, four per pair), 1,440 targeted single/paired count comparisons; 300 coefficient prefix and 180 translation prefix moment comparisons, 714 inhabited root witness receipts independently verified, 9,120 tree nodes and per-node message bound assertions, 15,338 stored table entries, 21,536 candidate joins, peak small-fixture table 64 entries. Reference enumerates original assignments and remaining diagonal completions separately; solver receives actual clause factors, matrix columns, domains and target, not support. For coefficient fixture reference constructs full A, but non-fixed prefix-coordinate columns cancel identically under bundled equality; only fixed suffix columns used nontrivially, so no dependence on unfixed entries in count. Uses balanced tree on supplied shuffled order, actual full syndrome keys, exact linear filter and one full partial assignment per nonzero key, not optimized basis packing or approximate implementation. Additional A=I rank16/32/64 controls with empty conjunction: single pinned count1, paired count 2^n, lambda_max=0, peak one table entry per node; at rank64 count 18446744073709551616, 127 stored entries across tree, 63 pair joins. Structural row counters not wall-clock or asymptotic proof. Local Git blob dbcb4f7802cee9532facf2053c35b4be64406a61; first remote upload omitted one blank line, corrected both branches then verified exact matching blob at Agda 1e54e6b2e45a1d7f5c5f55d185862e7babc975df and Lean 1ccb517a16731464fd06e4e013051a5d1e83004b. No native kernel, CI, new Langlands work or general polynomial-cost claim. Next substantive endpoint attack: a truly uniform source-aware polynomial selector or unrestricted obstruction/totality; the targeted overlap algorithm is a paid restricted construction, not another required gate. All Clay exits remain P0.
