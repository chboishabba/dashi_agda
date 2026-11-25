# **P vs NP — complete seven-route mathematical solution map**

The important distinction emerging from the repository audit is that **we do not have seven independent problems that must all be solved sequentially**.

We have several alternative formulations of the literal Clay endpoint, with substantial mathematical transport machinery already available. The remaining difficulty lies in producing universal, resource-controlled inhabitants of those interfaces.

I reopened the controlling Agda and Lean roadmaps, particularly Sections 47, 49, 51, 53, 60, 67, 77, 84–95 and G128.

The intended approach remains:

- **Steelman:** develop both a constructive P = NP route and an unrestricted P ≠ NP route without presupposing either conclusion.
- **BIDI:** preserve original witnesses, source semantics and computational resource costs through every geometric transformation.
- **Reverse-solve:** identify the weakest sufficient mathematical observation for the literal endpoint.
- **Geometry-forward:** exploit affine fibres, nonlinear compatibility, signed residuals, indexed hyperfabric, source-derived separators and exact contraction.

## **1. Overall dependency geometry**

C1a-bounded, C1a-signed and C2b are alternative constructive exits. C1c and C2a together supply another exit. S1 and R1 are equivalent separation formulations under the existing standard-model transport.

| Route       | Endpoint implication    |
| ----------- | ----------------------- |
| C1a-bounded | P = NP                  |
| C1a-signed  | P = NP                  |
| C1c alone   | Deterministic isolation |
| C2a alone   | RP = NP                 |
| C1c + C2a   | P = NP                  |
| C2b         | P = NP                  |
| S1          | P ≠ NP                  |
| R1          | P ≠ NP                  |

The implications in this table are mathematical consequences **conditional on the respective universal producer being established**.

We should therefore pursue the cheapest sufficient endpoint rather than unnecessarily requiring all intermediate representations, exact counts, full spectral reconstruction or global uniqueness certification.

# **Constructive lane**

## **2. C1a-bounded — deterministic verified success-mass continuation**

**Objective:** find a verified original witness without requiring exact model counting.

### **Existing construction**

Let \(S_F\) be the satisfying assignments of the original source \(F\). Write

\[ m=|S_F|. \]

Use our existing ternary Toeplitz affine hash:

\[ h_s(x)=A_sx+b_s\in\mathbb F_3^k. \]

Let \(H_s\) count original witnesses in its zero fibre, and define the bounded observable

\[ B(s)=\mathbf1[H_s=1]. \]

Our existing Sections 49, 51 and 86 establish pairwise independence and the good-root bound:

\[ \mathbb E[B]>\frac1{12} \]

for at least one \(k\) in the polynomial-size portfolio.

We do not need to know \(m\) to try that portfolio.

For seed prefix \(u\), define

\[ W(u)=\mathbb E[B\mid u]. \]

The three child potentials satisfy the exact parent identity

\[ W(u)=\frac{W(u0)+W(u1)+W(u2)}3. \]

### **Intended lemma chain**

| Lemma                            | Current disposition                                |
| -------------------------------- | -------------------------------------------------- |
| `ternaryHashPairwiseIndependent` | Mathematical construction supplied                 |
| `parsimoniousSeedChart`          | Original unique-extension transport supplied       |
| `goodRootOccupancyMass`          | Derived                                            |
| `boundedOccupancySourceContract` | Exact scoped contractions available                |
| `conditionalBoundedContrast`     | Error transport supplied; uniform producer open    |
| `uniformReachableProgress`       | Open                                               |
| `terminalVerifiedWitness`        | Existing rank-one probes and original verification |

The proposed names are mathematical target labels, not assertions that identically named native declarations exist.

### **Reverse-solve the exact error requirement**

Section 86 already gives a sufficient error ledger.

Let:

- \(\eta\) be the bounded surrogate's expected absolute error;
- \(\delta\) be the total variation error in the transported conditional measure;
- \(\rho\) be the numerical error in computing each parent-normalized child score.

Then selecting the largest computed score gives

\[ W(ud)\geq W(u)-(3\eta+6\delta+6\rho). \]

If the complete seed has length \(L\), it suffices to establish

\[ \boxed{ 3\eta+6\delta+6\rho\leq\frac1{24L}. } \]

The total loss over the complete descent is at most \(1/24\). Starting above \(1/12\), we remain above \(1/24\), eventually obtaining \(H_s=1\).

Existing rank-one singleton probes then recover the original witness.

### **Geometry-forward solution**

The intended geometric producer combines:

- The actual shared seed-action quotient.
- Exact clipped occupancy over the semiring \(\\{0,1,\geq2\\}\).
- Component and separator contraction.
- Parent-normalized conditional scores.
- Fast π-style adaptive error budgets and exact fallback.

The key is to avoid materializing every seed completion.

There is also a weaker and potentially more useful alternative already recorded in Section 87. Define

\[ J(s)=\mathbf1[\text{clocked solver returns a verified witness}]. \]

If we can establish inverse-polynomial root success mass for this actual solver, we only need to deterministically preserve sufficient success mass. We do not need to classify true singleton occupancy at all.

**Genuine remaining weld:** a uniformly polynomial-cost producer of sufficient conditional progress, or a deterministic hitting portfolio for verified success.

The conditional expectation identities and error propagation are already available. The universal source-derived approximation or selection theorem is not.

## **3. C1a-signed — contract the actual affected residual**

This is the signed counterpart of C1a-bounded, retaining the cancellation geometry rather than clipping multiplicity.

Define

\[ \Psi(s)=H_s(2-H_s). \]

Its values distinguish:

| Occupancy \(H_s\) | Signed potential |
| ------------------- | ---------------- |
| 0                   | 0                |
| 1                   | 1                |
| 2                   | 0                |
| 3                   | −3               |
| 4                   | −8               |
| 5                   | −15              |

We retain both the empty zero mode and inhabited neutral mode. They are not interchangeable.

For seed prefix \(u\),

\[ V(u)=\mathbb E[\Psi\mid u]. \]

Existing pairwise independence establishes

\[ V(\varnothing) =\frac m{3^k} -\frac{m(m-1)}{3^{2k}} >\frac1{12} \]

for a suitable \(k\).

### **Existing signed geometry**

Section 60 removes the common mode before contracting the source.

For the three child values \(V_d\), define

\[ \Delta_d=3(V_d-V(u)). \]

Equivalently,

\[ \begin{pmatrix} \Delta_0\\\ \Delta_1\\\ \Delta_2 \end{pmatrix} = \begin{pmatrix} 2&-1&-1\\\ -1&2&-1\\\ -1&-1&2 \end{pmatrix} \begin{pmatrix} V_0\\\ V_1\\\ V_2 \end{pmatrix}. \]

This operator annihilates the common mode and acts by multiplication by three on the signed zero-sum plane.

\[ \Delta_0+\Delta_1+\Delta_2=0. \]

The existing source-specific contraction already separates the affected coefficient sectors by first differing original coordinate and sign. Unaffected pair contributions cancel before computation.

### **Intended lemma chain**

| Lemma                              | Current disposition                |
| ---------------------------------- | ---------------------------------- |
| `signedRootMass`                   | Derived                            |
| `commonModeAnnihilation`           | Derived                            |
| `signedAffectedSectorContraction`  | Existing Section 60 implementation |
| `sharedResidualKeyContraction`     | Existing scoped machinery          |
| `weightedExceptionalContrastBound` | Open universally                   |
| `uniformContrastProgress`          | Open universally                   |
| `singletonBitProbeTransport`       | Derived                            |

### **Reverse-solve the terminal consumer**

We need only produce one trit \(d\) satisfying

\[ \boxed{ \Delta_d\geq-\frac1{8L}. } \]

This is equivalent to

\[ V(ud)\geq V(u)-\frac1{24L}. \]

That is substantially weaker than finding the exact maximum child or maintaining an exact fixed threshold.

Indeed, Section 53 already contains reductions showing that certain exact signed selectors are PP-equivalent. Requiring them would impose a stronger objective than necessary.

### **Why signed exceptional mass matters**

Unlike bounded occupancy, \(\Psi\) can have large negative magnitude. A rare exceptional sector can dominate the entire signed contrast.

The remaining bound must therefore control a weighted residual such as

\[ E_d= \sum\_{\omega\in\mathrm{omitted}} \mu(\omega)\\,|w_d(\omega)|. \]

If the retained contribution is \(A_d\), then

\[ A_d-E_d\geq-\frac1{8L} \]

is already sufficient for admission.

This is the direct SAT analogue of our fast π tail-budget observer.

**Genuine remaining weld:** uniformly obtaining a sufficiently small weighted residual bound with all source discovery and contraction costs paid.

### **Direct binary alternative**

Sections 93–95 establish a simpler bypass:

\[ \left| \widehat d-\frac{c_0-c_1}{c_0+c_1} \right|<1 \]

already suffices to select an inhabited original child.

Parity packets, projective signed counts, rational resolvents and direct affine witnesses can all feed this consumer.

This avoids the entire ternary seed continuation whenever original binary progress can be produced directly. It is not necessary to solve the weighted ternary problem if the binary alternative closes the endpoint.

## **4. C1c — uniform deterministic isolation**

**Objective:** construct a polynomial-size portfolio of original-source refinements, at least one of which contains exactly one satisfying assignment.

### **What is already solved**

Section 49 establishes that the ternary Toeplitz hash uses only

\[ L=n+2k-1 \]

seed trits and is pairwise independent.

For \(m>0\) original witnesses and \(q=3^k\),

\[ \Pr[H_s=1]\geq \frac mq\left(1-\frac{m-1}{q}\right). \]

Choosing \(2m\leq q<6m\) gives a constant success probability greater than \(1/12\).

We also already have the parsimonious Boolean compiler for these hash constraints. Each original satisfying assignment that survives the hash has exactly one auxiliary extension.

### **The precise distinction between existence and discovery**

Section 84 proves that polynomial-size nonuniform portfolios exist for all sources up to a given encoded length.

But it also proves that a fixed source-oblivious portfolio isolating every possible nonempty subset of the Boolean universe must contain at least \(2^n\) filters.

These are consistent results: a bounded-size source family is much smaller than the family of all possible witness supports.

Consequently, the intended solution is **source-dependent uniform isolation**, not a universal fixed list covering every abstract support.

### **Intended lemma chain**

| Lemma                             | Current disposition            |
| --------------------------------- | ------------------------------ |
| `pairwiseIndependentToeplitzSeed` | Supplied                       |
| `constantProbabilityIsolation`    | Derived                        |
| `uniqueAuxiliaryLift`             | Existing compiler              |
| `boundedSourcePortfolioExists`    | Derived nonuniformly           |
| `sourceDerivedSeedQuotient`       | Scoped constructions available |
| `uniformIsolatingPortfolio`       | Open                           |

### **Geometry-forward solution**

The intended procedure is to exploit the actual original support geometry through its constraints:

1. Eliminate forced affine directions and inactive seed coordinates.
2. Identify independent normal-space components and shared separators.
3. Contract seed-action directions that cannot affect the relevant witness fibre.
4. Use the existing signed or bounded conditional-progress machinery to choose the remaining seed directions.
5. Produce a polynomial-size portfolio without needing to certify which seed isolates.

With a C2a singleton solver, simply execute that solver on every portfolio member and verify against the original source.

### **BIDI resource equivalence**

Our Section 49 already reverse-solves this using the joint resource quantity

\[ J(F)= \min\_{s\text{ isolating}} \left[ \kappa\_{\mathrm{seed}}(s\mid F) +\kappa(H_s) \right]. \]

The existing two-way comparison is

\[ \begin{aligned} \kappa(F)&\leq C(J(F)+\log(N+2)),\\\ J(F)&\leq C'(\kappa(F)+\log(N+2)). \end{aligned} \]

The reverse direction uses a recovered original witness \(x\) to construct the identity hash with translation \(-x\), thereby isolating it.

**Genuine remaining weld:** produce an isolating seed, or a sufficient polynomial-size portfolio, uniformly at polynomial cost from the original source.

The existence theorem, randomized probability, source lift and resource correspondence are not missing.

## **5. C2a — polynomial singleton witness production**

This is the route where much of our recent geometric work becomes directly useful.

The original contract is:

\[ \boxed{ |S_F|=1 \Longrightarrow A(F)=x^\* \quad\text{within }\operatorname{poly}(|F|). } \]

Outside the singleton promise, the algorithm may return UNKNOWN or a verified witness. It must still obey its polynomial clock.

It does not have to prove that the source is a singleton.

### **Existing singleton output machinery**

| Existing construction                   | What it supplies                                              |
| --------------------------------------- | ------------------------------------------------------------- |
| Section 77 future-equivalence geometry  | Singleton semantic width at most two per layer                |
| Section 85 noisy marked decoder         | Exact witness recovery from sufficiently accurate marked bits |
| Section 88 affine retirement            | Original-coordinate marked projection                         |
| Sections 89–91 cofaces and dual moments | Exact affine packet compression                               |
| Section 92 primal–dual join             | Charged witness observation                                   |
| Section 93 strict selector              | Verified child progress                                       |
| Section 94 signed projective chart      | Deterministic even-occupancy repair                           |
| Section 95 affine resolvent             | Large-fibre rational observation                              |
| Langlands bounded-support decoder       | Recovery from sufficient spectral observations                |

### **Reverse-solve the weakest output contract**

For a singleton source with unique witness \(x^\*\), the original marked packet is simply

\[ W=(1,x^\*\_1,\ldots,x^\*\_n). \]

Thus one exact marked packet is sufficient.

But even that is stronger than necessary.

Section 85 already establishes that predicting at least \(15/16\) of an explicitly compiled set of marked bits correctly is sufficient. The existing Reed–Solomon/Hadamard construction transforms those noisy predictions into the exact original witness.

Therefore:

\[ \boxed{ \text{Polynomial noisy singleton producer} \iff \text{Polynomial exact singleton producer}. } \]

We need not solve every individual bit exactly in the source-side geometry.

### **The actual nonlinear core**

Section 67 already supplies a parsimonious embedding of arbitrary 3CNF into the genuine Toeplitz carrier

\[ A=[I_k\ I_k\ I_k\ 0] \]

with a 2CNF source and three nonzero Toeplitz diagonals.

The fixed ternary rows enforce exactly one selected literal per clause. Binary constraints ensure that this is the first true literal.

This gives a unique lift for every original satisfying assignment.

That means the nonlinear compatibility problem persists even after moving into a very structured affine-labelled carrier.

**We do not need another general SAT-to-geometric compiler.** We already have a relevant exact normal form.

### **Important new donor recovered during this audit**

The latest [Langlands PR #1549](https://github.com/chboishabba/dashi_agda/pull/1549?utm_source=chatgpt.com), now at `fb97d9a961d0`, contains two further constructions that directly address the previously outstanding component/separator work.

These are:

- [Intrinsic affine normal-space factorization](https://github.com/chboishabba/dashi_agda/blob/fb97d9a961d0c116a9d5c6bbffbd454a1341f185/Docs/roadmaps/ClayPNPIntrinsicAffineComponents.md?utm_source=chatgpt.com).
- [Normal-space boundary join](https://github.com/chboishabba/dashi_agda/blob/fb97d9a961d0c116a9d5c6bbffbd454a1341f185/Docs/roadmaps/ClayPNPNormalBoundaryJoin.md?utm_source=chatgpt.com).

They supply more than ordinary variable-incidence decomposition.

After eliminating required affine equations, represent each forbidden flat by its normal space \(W_j\). For a subset of constraints \(I\),

\[ U_I=\sum\_{j\in I}W_j. \]

The actual shared information across a cut is

\[ \boxed{ D_I=U_I\cap U\_{\bar I}. } \]

Its dimension is

\[ \dim D_I= \dim U_I+\dim U\_{\bar I}-\dim U\_{\mathrm{all}}. \]

Store only one feasible representative for each shared normal-space functional. Agreement on the intersection is sufficient for existential gluing.

This is precisely the kind of consumer-relative geometry we wanted.

For witness production, it is unnecessary to retain every local solution. One feasible representative per boundary functional suffices.

The donor establishes deterministic complexity

\[ O\left(\operatorname{poly}(N)(1+2^{2w})\right) \]

where \(w\) is the largest discovered normal-space boundary dimension.

### **Intrinsic boundary contraction cost**

Boundary dimension \(w\)

**8**

Boundary table entries

# **256**

Naive child-pair bound

# **6.554e+4**

Per contraction boundary, before polynomial source and discovery costs.

If \(w=O(\log N)\), this is polynomial.

The donor reports successful local acceptance on 640 random sources and twelve dense-cycle controls, including a rank-128 leaf. I inspected the proof and receipt documentation; I have not independently rerun those tests in this turn.

### **Revised intended C2a lemmas**

| Lemma                               | Status                          |
| ----------------------------------- | ------------------------------- |
| `parsimoniousNonlinearCore`         | Supplied                        |
| `intrinsicNormalComponentDiscovery` | Newly supplied by donor         |
| `boundaryFunctionalSufficiency`     | Newly supplied by donor         |
| `compatibleFunctionalGluing`        | Newly supplied by donor         |
| `originalCoordinateReopening`       | Newly supplied by donor         |
| `chargedLogWidthWitnessRecovery`    | Supplied conditionally on width |
| `uniformNonlinearCoreProgress`      | Open                            |

The remaining problem is no longer constructing the separator interface.

It is proving that every singleton source either admits affordable discovered contraction, yields a sufficient observation, or has another verified-witness bypass.

A universal logarithmic-width theorem is **not** mandatory.

## **6. C2b — globally sound relative-support discrimination**

C2b is distinct from C2a because it requires global soundness about the absence of additional witnesses.

### **Reverse-solve from an arbitrary SAT source**

Take any original formula \(G(x)\). Construct the guarded source

\[ H_G(s,x)= (\neg s\land x=0) \lor (s\land G(x)). \]

The deterministic gate compiler provides unique auxiliary extensions.

Consequently,

\[ \boxed{ |S\_{H_G}|=1+|S_G|. } \]

The source always has the known anchor witness \(s=0,x=0\).

**Guarded original source **\(H_G\)

**Anchor fibre**

\(s=0\)

Exactly one known witness.

**Residual fibre**

\(s=1\)

Original witnesses of \(G\).

Complete singleton

**G is UNSAT**

Additional original witness

**G is SAT**

This is already an exact reduction from arbitrary SAT to relative support beyond a known anchor.

### **Intended lemma chain**

| Lemma                            | Current disposition |
| -------------------------------- | ------------------- |
| `guardedOriginalSourceLift`      | Supplied            |
| `knownAnchorWitness`             | Supplied            |
| `relativeSupportCorrespondence`  | Derived             |
| `globallySoundCappedEnumeration` | Open                |
| `singletonCompletionCoverage`    | Open universally    |
| `guardedSATDecisionTransport`    | Derived             |

Suppose our polynomial-clock enumerator always returns either a complete correct list or UNKNOWN and guarantees completion on every singleton.

Then run it on \(H_G\).

- A complete singleton list proves \(G\) unsatisfiable.
- A complete list with multiple witnesses proves \(G\) satisfiable.
- UNKNOWN also implies \(G\) satisfiable, by the universal singleton-completion guarantee.

This gives a deterministic SAT decision procedure.

### **Geometry-forward solution**

There are several existing candidates for globally sound support discrimination:

- Exact clipped occupancy at two.
- Original-model cover with injective reopening.
- Exact signed integer contraction.
- Completed normal-space boundary joins.
- Rational support identities, provided that zero can be established identically rather than merely at one probe.

The new normal-space boundary join is particularly useful because it distinguishes completed empty support from exhaustion.

But we must preserve this distinction across the complete scheduler.

A zero modular moment, zero rational evaluation or failed witness search is not an emptiness proof.

**Genuine remaining weld:** globally sound completion on every singleton within a uniform polynomial clock, or direct deterministic discrimination of the punctured support.

# **Unrestricted separation lane**

## **7. S1 — universal Boolean-machine resource obstruction**

This route must quantify over arbitrary correct algorithms, not just the algorithms we have implemented.

That includes computations using alternative representations, nonlinear transformations, shared DAGs, arbitrary source rereads and recomputation.

### **Existing unrestricted resource geometry**

Section 47 defines

\[ \kappa(F)= \min\_{p\text{ verifies }F} \left( |p|+\lceil\log_2(t_p+1)\rceil \right). \]

Here \(p\) is an ordinary program receiving the original formula, and \(t_p\) is its actual execution cost.

The underlying feasible resource region is

\[ \mathcal R_F= \left\\{ (\ell,t): \exists p,\ |p|\leq\ell,\ p\text{ produces a verified witness within }t \right\\}. \]

Schematic only. The desired lower bound excludes all verified programs under a fixed polynomial resource budget, not just a particular contraction schedule.

For each fixed \(c\), use the budget

\[ b_c(N)=\lfloor c\log_2(N+2)\rfloor. \]

The existing universal bounded evaluator \(E_c\) enumerates eligible programs and executes each within its allocated budget.

For fixed \(c\), its total work is polynomial.

Therefore,

\[ \boxed{ P\ne NP \iff \forall c\ \exists F\in SAT: \kappa(F)>b_c(|F|). } \]

This equivalence is already recorded in the roadmap.

### **The exact remaining separation lemmas**

The geometric separation route requires four genuinely universal lemmas.

#### **U2 — unavoidable obligation attachment**

For an arbitrary correct polynomial SAT candidate, identify semantic obligations that its actual computation cannot avoid.

This is where `FactorsThrough`, consumer-relative non-descent and indexed residual geometry are relevant.

But proving that one selected observer loses information is insufficient.

We must establish that every correct computation pays for some relevant information, regardless of its representation.

#### **U3 — sharing-aware overlap charge**

Once unavoidable obligations are identified, assign their costs to actual computational events.

Let \(\gamma(j,v)\) be the charge from obligation \(j\) to event \(v\). Require

\[ \sum_v\gamma(j,v)\geq w_j \]

and

\[ \sum_j\gamma(j,v)\leq\operatorname{cost}(v). \]

The existing finite double-sum argument gives

\[ \sum_jw_j\leq \sum_v\operatorname{cost}(v). \]

The summation theorem is elementary and already available.

The missing theorem is constructing the required charge assignment for arbitrary correct Boolean computations, including shared intermediate results.

#### **U4 — global resource lower bound**

Prove that the necessary obligations accumulate on one actual worst-case run, or establish a legitimate averaging argument yielding such a run.

It is invalid to sum costs over exponentially many independent inputs and claim that the result is the runtime on one input.

#### **A2 — superpolynomial exclusion**

Finally establish, for every fixed correct machine \(M\) and every polynomial bound, an input length on which its unavoidable charged cost exceeds that bound:

\[ \forall c,k\ \exists N: B_M(N)>c(N+1)^k. \]

### **S1 existing and missing ledger**

| Lemma                                 | Status                         |
| ------------------------------------- | ------------------------------ |
| Standard-machine witness verification | Supplied                       |
| Polynomial resource transport         | Existing conditional machinery |
| Unrestricted budget evaluator         | Mathematically supplied        |
| `unavoidableObligationAttachment`     | Open                           |
| `boundedOverlapCharge`                | Open universally               |
| `globalCostLowerBound`                | Open                           |
| `superpolynomialExclusion`            | Open                           |
| Original Clay endpoint implication    | Existing native consumer       |

### **The critical steelman counterexamples**

The repository already contains several controls that prohibit false separation arguments:

| Large geometric quantity         | Why it is insufficient                          |
| -------------------------------- | ----------------------------------------------- |
| Exponential semantic width       | Can occur on sources with trivial witnesses     |
| High affine residual rank        | Can occur on easy planted singletons            |
| Exponential first spectral index | Occurs on a free Boolean cube                   |
| Large uniqueness certificate     | A known witness may still be trivial to produce |
| Exponential refinement tree      | Shared computation may bypass it                |

These are not obstacles to our geometric approach. They tell us exactly which quantities are not invariant enough.

The separation theorem must ultimately constrain actual paid Boolean computation, rather than an unnecessarily expensive representation.

## **8. R1 — unconditional full-code gain and resource closure**

This is our reverse-computability formulation of the separation endpoint.

### **Existing original-source gain construction**

Take a total clocked assignment producer \(W\), with original verification score

\[ A_W(F)=\mathbf1[F(W(F))=1]. \]

The existing fully pinned anchor overrides the candidate when all original variables are explicitly assigned.

For an original unit literal \(\ell\), define the gain

\[ G_W(F,\ell)= (1-A_W(F))A_W(F\land\ell). \]

A gain of one means the candidate fails to find a witness for \(F\), but succeeds after a legal original-source refinement.

That child witness already proves \(F\) satisfiable.

### **Existing BIDI theorem — G122**

Suppose \(W\) misses an inhabited formula \(F\), with actual witness \(x\).

Append the unit literals of \(x\) one at a time.

A missed inhabited source and a fully pinned accepting endpoint force an adjacent 0→1 revision somewhere on the witness pin path.

This gives

\[ \boxed{ W\text{ complete} \iff W\text{ has no gain}. } \]

The gain localization theorem is already available.

It does not, however, find the original missed witness unconditionally.

### **G128 — the full-code reverse endpoint**

Let \(e\) be a valid standard program with an explicit polynomial clock.

Define

\[ \operatorname{Bad}(e) \iff \exists F,\ell:\ G_e(F,\ell)=1. \]

Our existing G128 mathematics gives the following equivalences:

\[ \begin{aligned} P\ne NP &\iff \forall e:\operatorname{Bad}(e)\\\ &\iff \operatorname{Bad}\text{ is decidable}\\\ &\iff \text{a total computable first-gain}\\\ &\qquad\text{deadline exists}. \end{aligned} \]

The last deadline need not be polynomial.

This is the attractive part of R1: we do not need a polynomial-time algorithm finding counterexamples to polynomial SAT candidates.

A genuine unconditional computable bound on the first gain would suffice.

### **Existing reverse-solve through the halting problem**

The G128 converse already explains why this would be sufficient.

Assume P = NP and fix a complete polynomial witness producer \(W\_\*\).

For an arbitrary machine \(M\), construct a clocked candidate that:

1. Simulates \(M\) for a number of steps bounded by the original input length.
2. Uses \(W\_\*\) while \(M\) has not halted.
3. Switches to an incomplete fallback after detecting that \(M\) has halted.

If \(M\) never halts, the resulting candidate is complete.

If \(M\) halts, the resulting candidate has a genuine gain on sufficiently large sources.

Deciding \(\operatorname{Bad}(e)\) would therefore decide halting.

The conditional reduction is already available. The missing unconditional theorem is the decidability or totality itself.

### **The alternative native self-reference route**

I reopened these actual master owners:

| Owner                                                                                                                                                                                                                                             | Remaining obligation              |
| ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------- |
| [`PNotEqualsNPStandardMachineMaxCutClosureExact`](https://github.com/chboishabba/dashi_agda/blob/c36aa4a423091063bb3741cc74044726279b47c4/DASHI/Mathematics/Complexity/PNotEqualsNPStandardMachineMaxCutClosureExact.agda?utm_source=chatgpt.com) | Actual resource-closing compiler  |
| [`PNotEqualsNPPartialKleeneTerminationNoGoExact`](https://github.com/chboishabba/dashi_agda/blob/c36aa4a423091063bb3741cc74044726279b47c4/DASHI/Mathematics/Complexity/PNotEqualsNPPartialKleeneTerminationNoGoExact.agda?utm_source=chatgpt.com) | Non-circular termination theorem  |
| [`PNotEqualsNPFiniteTerminalTreeDirectDPExact`](https://github.com/chboishabba/dashi_agda/blob/c36aa4a423091063bb3741cc74044726279b47c4/DASHI/Mathematics/Complexity/PNotEqualsNPFiniteTerminalTreeDirectDPExact.agda?utm_source=chatgpt.com)     | Candidate-coupled progress        |
| [`PNotEqualsNPDirectSATLowerBoundExact`](https://github.com/chboishabba/dashi_agda/blob/c36aa4a423091063bb3741cc74044726279b47c4/DASHI/Mathematics/Complexity/PNotEqualsNPDirectSATLowerBoundExact.agda?utm_source=chatgpt.com)                   | Actual universal decision failure |

In particular, the finite terminal tree owner explicitly removes the earlier global terminal-correctness premise.

The remaining self-reference construction must produce one actual fixed machine whose execution consists of

\[ \text{quotation prefix} +\text{candidate simulation} +\text{negation suffix}. \]

Its total cost must close against precisely the same resource bound used in its own Cook–Levin formula.

The critical equation is not merely a symbolic fixed point. It is an actual same-object resource closure:

\[ T\_{\mathrm{prefix}} +T\_{\mathrm{simulation}} +T\_{\mathrm{suffix}} \leq T. \]

The formula supplied to the candidate must itself describe that same \(T\)-bounded execution.

Our existing partial Kleene no-go theorem explains why ordinary recursion machinery does not automatically establish this.

**Genuine remaining weld:** unconditional full-code gain totality, or a non-circular resource-closing progress theorem on the original self-referential execution.

# **Unified geometric solution strategy**

## **9. What we should actually implement and prove next**

The latest normal-space boundary construction changes the intended execution order.

We now have sufficient machinery to build a substantially unified source-derived solver without inventing another generic representation.

### **Unified original-source contraction**

**Original source and witness verification**

**Exact source normalization**

Affine elimination, forced equations, forbidden-flat cofaces, original-coordinate receipts.

**Intrinsic component and separator discovery**

Normal-space intersections, shared boundary functionals, retained residual DAG.

**Direct witness**

Component reopening or boundary gluing.

**Signed residual**

Projective contraction and sufficient lower bound.

**Spectral observation**

Parity or affine resolvent.

**Isolation**

Seed-action contraction and conditional progress.

**Exact original witness verification**

All paths must obey a shared charged clock. If the complete portfolio is inconclusive, return UNKNOWN rather than silently rejecting the original source.

### **A. Remove already-solved geometry from the open ledger**

We no longer need to separately solve:

| Previously outstanding construction  | Existing owner                    |
| ------------------------------------ | --------------------------------- |
| Affine-fibre moment contraction      | Section 95 resolvent              |
| Even-occupancy repair                | Section 94 signed normalization   |
| Odd-witness descent                  | Section 93                        |
| Nonlinear marked-bit decoding        | Section 85                        |
| Future-safe retirement               | Section 88                        |
| Basic coface contraction             | Sections 89–91                    |
| Intrinsic component discovery        | Latest Langlands donor            |
| Shared normal-space separator gluing | Latest Langlands donor            |
| Low-width witness reopening          | Latest Langlands donor            |
| Original unit-gain localization      | G122                              |
| Full-code deadline equivalence       | G128                              |
| Finite terminal semantic authority   | Master finite terminal tree owner |

These have different levels of mathematical and executable acceptance, but they should not be treated as wholly missing constructions.

### **B. Deterministic spectral visibility — a scoped additional route**

Even without a general deterministic rational hitting theorem, we have an elementary deterministic bypass for a sufficiently small XOR-affine chart.

Suppose

\[ \mathbf1_S(x)= \bigoplus\_{i=1}^{r}\mathbf1\_{B_i}(x). \]

Over the integers,

\[ \mathbf1_S(x)= \frac{1-\prod\_{i=1}^{r} (1-2\mathbf1\_{B_i}(x))}{2}. \]

Expanding gives

\[ |S|= \sum\_{\varnothing\ne I\subseteq[r]} (-2)^{|I|-1} \left|\bigcap\_{i\in I}B_i\right|. \]

Every intersection is affine and its cardinality can be calculated by Gaussian elimination.

This gives an exact deterministic support test in

\[ O(2^r\operatorname{poly}(N)). \]

It is polynomial when \(r=O(\log N)\), and it supports deterministic original-bit descent without rational hitting.

For a general polynomial-size chart, the expansion may still be exponential. Thus we should seek shared intersection compression or a direct witness bypass, not assume this identity supplies universal coverage.

This is a scoped mathematical deduction from the existing affine geometry, not a newly implemented or universally accepted producer.

## **10. The consolidated remaining theorem matrix**

| Proposed lemma                       | Relevant routes | Priority                     |
| ------------------------------------ | --------------- | ---------------------------- |
| `uniformNonlinearCoreProgress`       | C1a, C2a        | P0                           |
| `uniformVerifiedSuccessMass`         | C1a-bounded     | P0                           |
| `conditionalBoundedContrast`         | C1a-bounded     | P0                           |
| `weightedExceptionalContrastBound`   | C1a-signed      | P0                           |
| `uniformIsolatingPortfolio`          | C1c             | P0                           |
| `deterministicSufficientObservation` | C1a direct, C2a | P0 alternative               |
| `globallySoundRelativeSupport`       | C2b             | P0 alternative               |
| `unavoidableObligationAttachment`    | S1              | P0 parallel                  |
| `boundedOverlapCharge`               | S1              | P0 parallel                  |
| `globalCostLowerBound`               | S1              | P0 parallel                  |
| `superpolynomialExclusion`           | S1              | P0 parallel                  |
| `fullCodeGainTotality`               | R1              | P0 parallel                  |
| `sameObjectResourceClosure`          | R1/S1           | Alternative separation route |

There are substantial dependencies between these lemmas, but they are not thirteen mandatory serial deliverables.

## **11. Current repository reconciliation**

| Repository/PR                                                                                           | Inspected HEAD | Audit result                         |
| ------------------------------------------------------------------------------------------------------- | -------------- | ------------------------------------ |
| [Direct Agda #1548](https://github.com/chboishabba/dashi_agda/pull/1548?utm_source=chatgpt.com)         | `97d0753ad459` | Section 95, mergeable                |
| [Direct Lean #119](https://github.com/chboishabba/dashi_lean4/pull/119?utm_source=chatgpt.com)          | `718bc6720244` | Section 95, mergeable                |
| [Langlands Agda #1549](https://github.com/chboishabba/dashi_agda/pull/1549?utm_source=chatgpt.com)      | `fb97d9a961d0` | New intrinsic normal-space machinery |
| [Langlands Lean #120](https://github.com/chboishabba/dashi_lean4/pull/120?utm_source=chatgpt.com)       | `4689a27f8d34` | Companion branch                     |
| [Fast π #1546](https://github.com/chboishabba/dashi_agda/pull/1546?utm_source=chatgpt.com)              | `667026bfef46` | Existing adaptive residual donor     |
| [Indexed hyperfabric #1291](https://github.com/chboishabba/dashi_agda/pull/1291?utm_source=chatgpt.com) | `5f5c0e307d56` | Current donor head inspected         |
| Agda master base                                                                                        | `c36aa4a42309` | Native endpoint owners reopened      |

The previous direct-PR non-mergeability status has resolved at the latest inspection.

**Audit limitations:** I inspected the controlling roadmaps, relevant master theorem definitions and the latest Langlands component/separator proof documents. I did not exhaustively traverse every historical PR, independently execute the new donor checkers, run native proof kernels or modify repositories in this walkthrough.

## **12. Where the decisive mathematics now lies**

I would concentrate the constructive work on one maximum-cut theorem:

\[ \boxed{ \begin{gathered} F\text{ inhabited}\\\ \Downarrow\\\ \text{Polynomial-cost source-derived}\\\ \text{contraction, observation or bypass}\\\ \Downarrow\\\ \text{Original verified witness}. \end{gathered} } \]

The mathematical challenge is the first implication.

In parallel, the separation work should target either:

\[ \boxed{ \forall c\ \exists F\in SAT: \kappa(F)>c\log_2(|F|+2) } \]

or the equivalent unconditional full-code gain theorem.

We have already constructed much of the geometry surrounding both endpoints. The next breakthrough must establish universal progress or universal obstruction, rather than another conditional interface.

**P vs NP remains unresolved. But the latest repository audit does narrow the missing work: intrinsic component discovery, separator gluing, large affine-fibre contraction, witness decoding, semantic transport and the major endpoint equivalences are already available. The outstanding mathematics is their universal resource-controlled sufficiency—or an unrestricted proof that such sufficiency cannot exist.**

## Controlling maintenance note (2026-11-26)

This full solution map preserves the user-approved walkthrough. The shared ClayP0PolynomialCoverageEndpoint20261124 roadmap is the live phase and status authority; historical HEADs above are a snapshot. All proposed lemma names are contracts unless explicitly matched to existing declarations. No universal endpoint is claimed. In particular the bounded/signed rank-one bit recovery is conditional on the same uniform selector covering those probes, not merely a single successful seed path. Langlands latest transversal donor is recorded in the next controlling roadmap section. No random visibility, finite acceptance, or scoped width result is a deterministic universal theorem.


## Live delta — Section 97 (2026-11-26)

The main roadmap Section 96 remains the controlling phase matrix; Section 97 now pays three local donor lemmas (orientedDirectionExistentialProjection, nonGrowingDirectionDiscovery, orientedOriginalReopening) and four scoped direct lemmas (overlapForestPointwiseLowerBound, maxForestChildSuperadditivity, positiveForestOneChildDescent, cappedOriginalEscapePortfolio). Actual oriented donor imported from #1549 3b88da6a8aa8; new forest checker 02e8d01ab33a5cb0404f01c246f03e0b15b99fb1. For an affine fibre P, max over forests T of |P|-sum_i|P intersect B_i|+sum_edges|P intersect B_i intersect B_j| lower-bounds true support and is superadditive across binary restriction. Positive root implies deterministic one-child descent, with all affine pair overlaps charged; nonpositive root UNKNOWN. Integrated prior portfolio and new path tested locally (see Section97 precise counts and transcribed-helper limitations). This removes another local construction from the missing list, NOT any universal leaf. The thirteen exact universal targets above stay open. Focus uniformNonlinearCoreProgress on high-width deficient irreducible residuals or other verified bypass; forest positivity is not compulsory. Seed mass, weighted contrast, isolation and relative-support routes remain independent alternatives; unrestricted S1/R1 remain parallel. No native kernel/CI or claim of solvedness.


## Live delta — Section 98 (2026-11-26)

Reused actual latest Langlands collective uniform fibre escape and reopening (#1549 afe796918688, checker blob 8ed99bdfad926ed1ad52390c9111157fcd99ca49) on both direct branches. New checker 5a4249f82baa30d079c55359a1654f62286944ee: adjacentBagMergeMonotonicity, disconnectedActivationDefectExact, fixedCertificateOneChildDescent and boundedBagCertificateSingletonNoGo are supplied scoped mathematics, with capped collective portfolio tested locally (see Section98 exact counts and donor-transcription limitations). For partition into forbidden-event bags, signed forest certificate has exact defect max(0, number of connected active components minus one). Adjacent contraction improves this pointwise; exact fixed-certificate additivity yields deterministic descent. On a singleton, positive forest bound requires exact defect zero everywhere; independent forced-unit singleton with n>2b refutes universal positive b-bag certificate on raw sources, but is trivially solved by other preprocessing. No compulsory bag exactness, width, spectral scan or fixed normal form. The full thirteen universal targets and all seven routes remain OPEN; sourceDerivedCollectiveResidualAdmission only scoped. Master staged reference DirectDP constructor is already non-opaque; strict resource fit and actual candidate-coupled progress remain, not a missing finite terminal semantic proof. Continue Section96 phase matrix and actual original-source verified progress or unrestricted S1/R1. No native kernels/CI, no solvedness claim.
