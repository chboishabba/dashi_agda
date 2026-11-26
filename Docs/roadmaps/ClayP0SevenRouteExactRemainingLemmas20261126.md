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


## Live delta — Section 99 (2026-11-26)

Actual adaptive signed-escape donor (#1549 77f303bcd76d, checker ad87d2418009272dd8bf6e5f7e9ebd2901072342) copied unchanged into both direct branches. New correlated marginal checker 5b23aae5e102ca2ee06c74a0d5e22eaf06d0b0d4 supplies intrinsicSignedMinimumFactorization, minPlusBoundaryFunctionalSufficiency, hardDomainConditionalMinimum, monotoneComponentFloorAdmission, chargedCorrelatedCheckpoint and cappedCorrelatedOriginalPortfolio on scoped sources. For signed quotient marginal M(y), minimum over retained admissible domains factors across independent normal-space components; exact min-plus boundary receipts on each component replace conservative floors monotonically, stop at first positive certificate. Connected odd parity-cycle and complementary-slot controls admit with zero extra promotions, retained dimension through128, exact signed minimum and original reopening tested. Completed empty admissible quotient distinct from nonpositive min and exhaustion. Section99 has actual execution counts and donor-transcription limitations. No global polynomial bound or requirement to compute exact min universally.

Master fixed-width quoted reference progress (a6e929c2177f050e14e9724227b0f88d0650e002) already supplies strict charge fit and constructor progress; same structural root is variable-free tautology (semantic inertness cdda632df5b70d58b9785224bf730f07b986d034). Do not repeat inert-root progress as missing or treat it as opposite SAT. Native R1/S1 alternative still needs semantics-bearing own execution quotation, same-T actual resource closure, and ordinary model/NP background on that exact carrier. All thirteen universal targets and seven routes remain open; Section96 phase matrix controls. Next: group-relaxed signed floors on genuinely high-width projected domains or alternative direct verified nonlinear progress, alongside actual ternary seed obligations and independent unrestricted S1/R1. No new mandatory solver representation or endpoint claim. No native kernels/CI/default edits.


## Live delta — signed affine activation conflicts (2026-11-26)

P vs NP exclusively. Direct Agda #1548 and Lean #119 inspected at 22ccca1c0343 and ec2a2fec78e03; both reported mergeable at inspection. Correlated marginal consumer already implements hardDomainConditionalMinimum; the penalty encoding is an alternative, not a prerequisite. Keep Section 96 controlling and all thirteen universal contracts open.

For the explicitly retained signed marginal M=c+sum_i w_i 1_{D_i}, set b=c+sum_i min(0,w_i), and r_i=1 iff the preferred activation (active for negative w_i; inactive for positive w_i) is violated. Exactly M=b+sum_i |w_i|r_i. A conflict C of incompatible preferences gives sum_{i in C}r_i>=1. Nonnegative conflict charges lambda_C with sum_{C contains i}lambda_C<=|w_i| imply M>=b+sum_C lambda_C. Gaussian elimination with union provenance finds inconsistent negative-domain conjunctions or entailment of a positive domain by negative domains. Greedy minimum residual charge exhausts one term each step, at most m successful iterations; discovery, checking and integer arithmetic polynomial in explicitly represented chart size. This is a scoped weighted unsatisfiable-core packing bound, not a novelty claim about the classical charging inequality. Hard domains may be encoded by positive penalty K=1+|c|+sum|w_i|, and positive one-row domains can be rewritten as negative complements plus constants. Positive floor suffices for existing reopening on admissible quotient; it is vacuous if no admissible point exists. Nonpositive floor is UNKNOWN, not empty.

Standalone checker scripts/check_p0_signed_conflict_20261126.py, git blob 2a7e21bea2f81bef5d8520f42c61bf1bf22c49bf, SHA-256 61fb17df4dcdd1908a31889c83f90ed6f0c8e234f49a607573e7c55cdc5df477. Local execution: 1350 exact minimum comparisons, 930 strict improvements, 2442 full-packing receipts replayed, 1350 hard-conditioned fixture comparisons (all quotient points checked). Dense complete-graph inequality preference controls n=8,16,32,64, terms=28,120,496,2016, certified lower=6,23,77,234 vs exact=12,56,240,992. Rank-one complement, entailment and deliberate blind-spot controls PASS. Four positive rank-two domains partitioning F2^2 give true minimum 1 but conflict detector floor 0. These are structured marginal tests, not hard-SAT or full portfolio replay.

Proposed scoped contracts: signedPreferenceRegretExact, affinePreferenceConflictSound, sharedConflictBudgetLowerBound, greedyConflictPackingPolynomial, conditionedConflictFloorSound. Mathematical derivation and standalone executable checks supplied, not native kernel certificates. The next integration is a cost-accounted attempt before correlated min-plus with the existing Budget and original reopening; full donor integration and replay NOT performed in this delta. Group-relaxed min-plus remains complementary. No claim of polynomial chart construction or universal positive floor. S1 overlap charge may reuse the finite inequality only after independently establishing U2 unavoidable attachment to arbitrary computations; R1 fullCodeGainTotality/sameObjectResourceClosure remain open. No CI, native kernel or default-branch changes. Targeted master search found no exact matching implementation, not an exhaustive historical search.


## Live delta — grouped admissible signed quotient floors (2026-11-26)

[Exact grouped quotient proof, executed receipt and master audit](ClayPNPGroupedQuotientFloor.md). Section99 direct hard-domain conditional minimum and component floors already own conditioning; new penalty route reuses min-plus, and arbitrary-group minima relaxation now implemented (not independent normal components only). Store max(old summed floors,new sound group floor) at each merge, pair exact activation rank cells, bounded larger groups, charged candidate cache, first positive stops. Checker 2f27998672b958e39a439f6e57625cdb5b076c4a, adaptive admissible hook 76aba3c4cc42c1351384075568041cfa0079b4aa, direct thirteen-share dispatcher 8667554da87b2487bddc150e16550a2a4a4fae9a. Local 735 grouped comparisons, 150 actual composed donor cases, connected 32-slot quotient at zero promotions and 1060 floor events PASS; complete direct dispatcher replay still unpaid. Master fixed-width inert-root progress and actual-halting coded candidate coverage already paid; actual semantics-bearing own-Cook prefix/same-T closure, ordinary maps/verifier/certificates/guarded representation and NP background on exact carrier remain. All thirteen universal targets/seven alternatives stay open, not serial. Do not repeat local constructions or require compulsory positive forest/width/min. Section96 phase matrix remains controlling, S1/R1 independent. No kernel/CI/default edits.


## Collective preference conflict repair and partial quotient witness admission (2026-11-26)

[Exact proof, implementation and acceptance](ClayPNPPartialQuotientWitness.md). Actual signed-conflict donor 2a7e21bea2f81bef5d8520f42c61bf1bf22c49bf reused. Restrict positive domains to consistent preferred-negative intersection, group canonical normal spaces and recognize all RHS orientations without ambient enumeration; shared coefficient budgets and receipt replay preserve lower-bound soundness. New partial quotient gate Q=M times exact admissibility mask, or negative penalty M-K sum forbidden H when mask width fails. Positive signed integral on one offered affine cell suffices for one-child additive quotient descent and original fibre witness reopening; no global uniform minimum needed, no claim of exact existential projection or emptiness. New checker 14510ff3c94680dfd9ef68cc4c790453a23e0900, direct fifteen-share dispatcher f3ce26f8f06a6877a49c0acf15646badbf7a05ab. Local 280 conditioned floors/175 replayed receipts/560 probe evaluations/280 source fixtures (134 witness,142 exact empty,4 UNKNOWN, all four resolved by actual conflict-enabled fallback), four negative-root controls at k8..64 zero promotions, collective partition and guarded penalty PASS; explicit positive-singleton missed-probe no-go. Full direct historical dispatcher replay unpaid. All seven endpoint alternatives and thirteen universal targets OPEN; next actual uniform nonlinear progress, not compulsory global min or positive affine probe; actual weighted seed and unrestricted S1/R1 independent. Master targeted semantic-inertness audit retained, no CI/native/default edits.


## Adaptive signed Krylov moment inertia (2026-11-26)

[Exact finite-level inertia theorem, implementation receipt and endpoint barriers](ClayPNPSignedMomentInertia.md). Reconciled actual previous fifteen-share partial/conflict route and Karp quadratic positivity. For Q gated signed chart H_d[i,j]=sum Q^(i+j+1), positive direction a gives sum Q*p(Q)^2>0 and fixed weighted one-child original descent. Full column Vandermonde at d>=s-1 gives inertia equal signed distinct nonzero levels, not number of witnesses. Reuse charged affine power charts and exact rational congruence; no support-sound chart, full global min or positive individual probe required. Checker 6a8d55d87a0a757019f194b1a6633d38b48c19e1, existing block hook 42400570bdc6705f8d3c6a0e0d1bc1aa6a210b24, sixteen-share direct dispatcher 9cfefc2ac4bce7e40946394946ba690a5965ef45. Local 210 finite spectrum comparisons, 630 lower degree, 180 actual composed sources (103 verified/76 exact empty/1 UNKNOWN), prior partial regression, genuine five-dimensional block previously missed now degree2 witness at zero promotions PASS. Full dispatcher replay unpaid. Full moment sequence implies #SAT via interpolation; low-degree duplicate-unit obstruction requires d>=ceil(n/2), not computational separation. Actual remaining universal producer is affordable sufficient signed observation or bypass, not exact high moments. All thirteen targets/seven routes OPEN, independent S1/R1 and actual weighted ternary obligations retained. Master Karp signed/Levin/partition sources reopened; no new mandatory Karp or native framework. No CI/native/default/donor edits.


## Sharp-weight X3C — dyadic image, syndrome-star pair hull, original capacity (2026-11-26)

[Exact mathematical derivations, implementation and acceptance](ClayPNPX3CSharpWeightGeometry.md). Reconciled supplied carry-free X3C reduction and actual master Karp/Smith scoped owners; reuse generic affine and weighted boundary donors. On binary parity fibre, exact cover iff weight m/3; local pair one-hot labels matched by syndrome signatures, each complete bipartite class affine-generated by two stars (a+b-1 labels instead of ab), original hull rank increases at most n times. Exact mod2 image of Ax=b mod2^e by odd unit elimination with retained original parity pivots and even residual division; BIDI modular lift proof, necessary refinement not binary witness. Original row hitting set size<k excludes exact cover; fractional capacity inequality recorded. Checker ea46e409d6af8c3d02a82ae7a7fff9187359c7c1 locally executed and hash-verified both direct branches: 400 X3C fixtures 149 witness/251 completed empty, 1559 pair hull/10588 sharp-weight/200 exact modular projection checks PASS. Pair rank9->14 original witness, rank254 pair image 255 generators vs16384 labels, cyclic Latin q4/q8 pair stall rejected at dyadic e2/e3. All-moduli integer-solution m12,n136 countercontrol survives pair hull (rank13) but capacity3<k4 rejects. Scoped not universal. New X3C entry reuses min-plus and exact boundary fallback, general sixteen-share CNF dispatcher unchanged; no uniform SAT->X3C implementation or native/kernel/CI/default edits. All thirteen principal universal targets/seven alternatives remain open. Direct P0 target sharp nonlinear weight-k attainment or verified bypass on all actual sources, not compulsory modular/hull/capacity completeness. Actual ternary seed, globally sound relative support and independent unrestricted S1/R1 retain prior contracts. No claim of solvedness.


## Endpoint-first reconciliation — integer lattice binary image and signed sharp descent (2026-11-26)

Current audit entry: direct Agda #1548 131b81301924f6c7be5a782b61461721f0be0046 (mergeable), Lean #119 89d3edc67489397ac6455997e3cd284bfb27b56a (nonmergeable); Langlands #1549 b2691d0b01f1d1e3464cc9fec85096b147d64ea9 / #120 0746418d033c2567de05269b8cbce2ad5e518ecc (mergeable). Attachment circuit proof actually present in current direct roadmap (historical e3e36e4f7f3355bb860a96ba071f395431886a04; current main roadmap 5d49bec4e2462c7624eddac09539b2f117fc1f4e). Do not repeat circuit existence, disjoint-support decomposition, rank-only extraction given improving trade, strict gain identity, or <=floor((n-k)/2) improving iterations as missing lemmas. Existing partial quotient 42400570bdc6705f8d3c6a0e0d1bc1aa6a210b24, moment 6a8d55d87a0a757019f194b1a6633d38b48c19e1, signed min-plus e14ed3cefcc0502e1aec68b4be30272b4517b800, transversal dda415dad27971d6d91949103e9c8b63e5d5b755, signed conflict 2a7e21bea2f81bef5d8520f42c61bf1bf22c49bf and X3C ea46e409d6af8c3d02a82ae7a7fff9187359c7c1 actual source inspected. Master Karp21ExactHittingTransposeExact c4d5a1084ae204364cab81c594e98595e97287e2 owns same selected-index exact hitting/cover witness; not ordinary hitting set. Karp21HistoricalDagExact 0908581312dc7fa824a8593d1c110b864f6ca787 only historical graph reachability, not costed reductions. Langlands linear autarky d0a31b719677640424ecd35e1e1445b9f12eea78 owns numerical candidate + exact SymPy receipt pattern, not full X3C LP support closure. Prior master scoped Smith owner is not general HNF. Targeted searches, no exhaustive historical traversal.

New exact local mathematical weld: let L=A Z^n subset Z^m be actual integer column lattice, H a column Hermite basis of L, A=HC with C integral and columns generating Z^r, r=rank_Q A. Test b in L by Hc=b with integral c. If not, no integer or binary cover. Otherwise exact binary image of integer solution fibre is {x in F2^n:Cx=c mod2}. Forward reduce Cz=c; reverse choose binary representative x, c-Cx even, C:Z^n->Z^r surjective, hence choose t with Ct=(c-Cx)/2 and z=x+2t gives Az=b. Rank_F2 C=r, dimension n-r. This subsumes necessary modular depth escalation (and odd-prime/rational-span inconsistencies), with standard polynomial-bit Hermite normal form and exact rational coordinate algebra. It does not assert z binary/nonnegative. No native general HNF constructor claimed. Local standalone SymPy test 160 arbitrary small signed integer systems, 3598 exact binary-image comparisons using independent membership in 2L (HNF of 2A), 39 images differing from naive parity; odd torsion A=[3],b=1 survives every 2-adic modulus but integer lattice rejects; diagonal 2 and Latin orders4/8 controls PASS. Initial test adapter converted SymPy integers incorrectly for existing Python bitmask routine; corrected to int and reran successfully. No new committed executable in this delta; ordinary polynomial HNF theorem, not empirical timing, supplies bit complexity. Original X3C solver currently uses bounded dyadic projection, not this HNF route.

Capacity weld: on X3C Ax=1, x>=0, k=m/3. If y>=0, A^T y>=1 and sum y<k, exclude; if sum y=k, each strictly slack column A_i^T y>1 is forced x_i=0 by sum_i x_i(A_i^T y-1)=0. More general signed row multiplier lambda with A^T lambda>=0 and b^T lambda<0 is Farkas infeasibility; b^T lambda=0 forces every positive-slack column to zero. Rational LP can compute all forced-zero columns of nonnegative real fibre by maximizing each x_i (bounded by 1 for nonempty columns), then certify zero optima using rational duals. Forced-one pins follow where an incidence row has all other columns excluded. This is scoped sound preprocessing; neither LP feasibility nor integer-lattice membership implies binary feasibility. Reuse exact certificate checker pattern; no claim of implementing full LP producer. Intersect necessary pins with lattice image and exact-one pair hull; if using refined carrier for circuit trades, use kernel of ALL retained homogeneous rows, not just ker A. Every original cover remains, and parity ensures signed gains even. Polynomial number of strict rank or fixed-coordinate improvements; no guarantee these remove all residuals.

Decisive direct theorem (alternative to seed routes): one deterministic polynomial-clock producer T for all encoded X3C sources and retained parity-feasible x of weight>k, which on inhabited sources returns either an original verified cover or v in the actual retained kernel with G_x(v)=2|x intersect v|-|v|>0. On arbitrary sources it may return UNKNOWN, but all returned trades/witnesses checked and clock applies to all inputs. Iterating at most floor((n-k)/2) times, accepting only actual weight-k cover, rejecting at clocked failure, decides X3C. Conversely P=NP implies T via exact-cover decision self-reduction and difference to found witness. Thus universal affordable improving trade is equivalent to P=NP (using classical X3C NP-completeness), not an already-paid consequence of circuit existence. Given v, circuit extraction optional; arbitrary basis/local-radius no-gos retained. Existing positive_point consumes rank-one signed gain chart G_x directly; moment_point, min-plus on -G_x (exact negative min only, relaxed negative lower bound not sufficient), conflict packing and component boundary are donors. Need actual charged X3C gain adapter and composed replay, not rebuild their math. Exact signed chart G_x retains original sign cancellations; partial positive lower-energy error contract from prior moment route applies. New lattice and LP preprocessing not mandatory or a substitute for universal gain discovery. General direct CNF dispatcher unchanged; textbook reduction sufficient mathematically, native executable compiler/clock distinct. 

All seven endpoint alternatives and thirteen principal universal targets remain OPEN: uniformNonlinearCoreProgress / deterministicSufficientObservation (direct gain or bypass, C2a singleton promise version); uniformVerifiedSuccessMass + conditionalBoundedContrast (actual verified J, or uniform isolation probes); weightedExceptionalContrastBound (actual ternary first-difference weights); uniformIsolatingPortfolio + singleton recovery; globallySoundRelativeSupport (guarded anchor and total singleton completion); S1 unavoidableObligationAttachment, boundedOverlapCharge, globalCostLowerBound, superpolynomialExclusion for arbitrary computations; R1 fullCodeGainTotality or sameObjectResourceClosure. Local X3C gain is not R1 full-program gain. Master fixed-width quoted root semantic inertness cdda632df5b70d58b9785224bf730f07b986d034, standard max-cut closure 564f3f11ce56e228247992d2fd308f00fd70487f, coded actual-halting model 7d560a19dd5323f582760d02e01d65da904c0ce2 reopened: candidate coverage projection supplied, ordinary HaltingStandardCostClosure fields + guarded representation transport + standard NP background remain native model work; actual semantics-bearing own-Cook quotation and same-T resource closure still open and prior explicit-tableau padded-runtime obstruction retained. Do not derive unrestricted separation from failure of any capped geometric route. No native kernels/CI/default edits. Focus on actual universal gain producer or bypass and independent unrestricted S1/R1, not another compulsory representation. No Clay endpoint solved.


## P0 maximum cut — parity-derived capacity certificates and endpoint reconciliation (2026-11-26)

Endpoint-first. Current inspected heads Agda #1548 131b81301924, Lean #119 89d3edc67489, Langlands #1549 b2691d0b01f1 and #120 0746418d033c, all reported mergeable at entry. Reopened direct X3C checker ea46e409d6af8c3d02a82ae7a7fff9187359c7c1 (actual modular projection, one-hot pair hull, greedy row hitting capacity, signed min and exact boundary fallback), signed minimum e14ed3cefcc0502e1aec68b4be30272b4517b800, signed moment 6a8d55d87a0a757019f194b1a6633d38b48c19e1 and controlling seven-route map 811cbd7322387003900bec977d12aae0ef82bc37. Reopened master structural progress a6e929c2177f050e14e9724227b0f88d0650e002, semantic inertness cdda632df5b70d58b9785224bf730f07b986d034, standard closure 564f3f11ce56e228247992d2fd308f00fd70487f, direct lower-bound consumer 0838b3252b3ffb91993e4cb47a5d5c06a00e4fe1, original scaled partition a64a484c4ec39dec821194ed0e63ba1fecd86140. Do not redo existing affine, rank, signed, modular, witness consumers. No native acceptance or universal producer inferred.

Capacity equality: for original X3C A with 3k rows and column weight3, y>=0 and A^T y>=1 imply slack s=A^T y-1>=0. Exact cover obeys s^T x=sum y-k. Negative budget excludes; zero budget forces x_i=0 for all positive s_i. Rational LP on P={x>=0:Ax=1} can decide feasibility and all forced coordinates (x_i<=1 from incidence). This is necessary, not sufficient. Existing checker only greedy hitting-set capacity; fractional closure is a mathematical option, not another compulsory formalization.

New stronger cut: any original row subset r with odd cardinality gives binary check b=A^T r mod2, b^T x=1 mod2 on every original parity witness. Hence real inequality b^T x>=1 for binary witnesses. Even and other parity forbidden-pattern inequalities optional. Discover all checks of support at most fixed t by enumerating candidate column masks of size<=t and solving A^T r=b, 1^T r=1 over F2 (polynomial for fixed t; no enumeration of all row combinations necessary). For retained affine P, use the augmented parity rowspace similarly. Given B of such odd check supports, rational y unrestricted and lambda>=0 satisfying A^T y>=B^T lambda, every exact cover obeys sum y>=sum lambda. Strict opposite is exact UNSAT, equality forces positive column slack to zero and all positive-lambda cuts tight. This is classical redundant parity-check/LP dual geometry specialized to original incidence, not a claim of new general LP theory. Each sound pin can reuse existing pair-hull/dyadic restrictions and original witness reopening. Uniform bounded-support sufficiency is NOT established.

Exact stalled-control certificate, all coordinates zero-based. Universe 18, 30 triples in order:
(0,8,17),(2,9,14),(0,6,7),(4,13,15),(5,13,16),(3,4,13),(8,16,17),(2,6,16),(4,5,11),(10,15,16),(1,10,14),(4,14,16),(1,9,15),(6,11,17),(5,12,17),(1,7,12),(6,8,13),(5,8,12),(0,8,9),(0,12,14),(0,5,14),(2,10,11),(3,4,11),(9,10,15),(2,10,17),(2,3,7),(1,3,12),(11,13,15),(1,6,7),(3,7,9).
All row degrees 5, strict fractional x=1/5. Signed integer z=(-27,-6,12,30,5,1,23,7,-16,-20,21,-14,-9,17,-12,-11,-35,24,16,0,0,0,0,0,0,0,0,0,0,0) verified Az=1. GF2 row rank18: odd unit pivots lift every parity point modulo every 2^e (full row rank mod2 gives correction for each next bit). All 171 one-/two-row projected exact-one hull tests have full original parity projection dimension; independently enumerated 4096 parity points, min weight8 not target6; independent exact-cover DFS 170 cached residual subsets, zero covers. Thus original LP, every integer modulus feasibility, dyadic image and pair hull do not settle this source. There is one odd support3 check {0,19,27}; it cuts x=1/5 but LP remains feasible (exact rational point checked). All 45 odd checks of support<=5 give infeasible LP. Exact integer certificate uses only 12:
column supports/charges: (2,7,9,18,26):1; (3,7,19,20,21):3; (0,11,23,25,26):2; (3,10,11,24,25):2; (2,11,13,22,24):2; (3,5,12,13,25):4; (2,6,9,21,28):3; (1,7,17,22,23):1; (9,15,19,24,28):2; (7,9,20,26,27):3; (0,19,27):5; (2,8,14,15,22):4.
Corresponding original odd row subsets: (1,2,7,9,10); (3,5,6,7,11,12,13); (0,1,7,9,14); (2,3,5,6,7,11,12,13,14); (1,3,4,7,10,11,15); (2,3,4,5,6,7,10,12,13,14,15); (4,6,11,13,16); (0,1,3,7,8,13,14,15,16); (1,2,6,7,8,9,10,12,17); (2,3,5,8,9,11,13,15,17); (0,1,3,5,7,8,10,11,13,15,17); (0,2,3,4,5,9,11,12,15,16,17).
y=(6,1,4,2,3,-1,2,2,-1,-4,0,2,3,-1,1,7,2,2). All 30 column slacks A^T y-B^T lambda exactly zero. sum y=30, sum lambda=32 gives 32<=30 contradiction. Local Python/SymPy integer verification plus SciPy LP discovery; row span exhaustive only for finding the example and independently counting checks, not asserted as polynomial algorithm. Initial stronger conjecture that uniform fractional point survived all redundant parity checks was refuted (minimum odd support3). No full donor/dispatcher replay, no new executable or native proof module, no CI/default edits. Exact finite counterexample and certificate, not universal progress.

All thirteen principal universal targets remain OPEN; alternatives not serial. Constructive primary: uniformNonlinearCoreProgress / deterministicSufficientObservation on original inhabited residual (including X3C improving trade or verified bypass, at most floor((n-k)/2) moves). C1a-bounded uniformVerifiedSuccessMass + conditionalBoundedContrast or verified hitting portfolio; C1a-signed weightedExceptionalContrastBound or direct binary bypass; C1c uniformIsolatingPortfolio with C2a singleton recovery (C2a alone gives RP=NP); C2b globallySoundRelativeSupport with guaranteed singleton completion. S1 unavoidableObligationAttachment, boundedOverlapCharge, globalCostLowerBound, superpolynomialExclusion for arbitrary computations, not selected certificates. R1 fullCodeGainTotality (unconditional gain discovery for every valid clocked candidate, or decidability of Bad(e) via established reduction) or sameObjectResourceClosure with genuine opposite-SAT execution semantics and same actual clock; fixed-width structural fit already supplied but tautological. Explicit tableau padding obstruction retained. Native resource wrappers are endpoint admission only. Next investigate source-derived nonlinear improvement/contradiction beyond fixed-support parity cuts, not compulsory LP integrality or full moment recovery. No new Clay solution.


## P0 endpoint cut — incumbent-relative quotient and all-parity-capacity barrier (2026-11-26)

Endpoint-first, no further compulsory formalization. Inspected Agda #1548 c8f2ffe28801 (mergeable), Lean #119 3604c911f90f (nonmergeable), Langlands #1549 b2691d0b01f1 and #120 0746418d033c (both mergeable). Reopened actual direct X3C checker ea46e409d6af8c3d02a82ae7a7fff9187359c7c1, normal transversal dda415dad27971d6d91949103e9c8b63e5d5b755 and signed minimum e14ed3cefcc0502e1aec68b4be30272b4517b800; existing original-coordinate consumers retained. Previous parity-capacity certificate is sound but not a complete relaxation.

Incumbent-relative signed trade: Ax=1 mod2, S=supp x, U=complement. If selected columns A_S dependent, remove a nonzero dependency, strictly lowering weight without additions. Otherwise A_S is independent. Gaussian elimination with original-column provenance decomposes each unselected column a_j=q_j+A_S r_j over F2, q_j in a fixed linear complement of span(A_S). For addition set J subset U, a parity-preserving trade with exactly these additions exists iff XOR_{j in J} q_j=0; then its removal set is uniquely R(J)=XOR_{j in J} r_j. Exact gain |R(J)|-|J|. This eliminates independent enumeration of removals, not the remaining addition search. All one-add moves have q_j=0; two-add moves have equal quotient signatures. Enumerating addition sets of size <=t is polynomial for fixed t, and exact for that restricted move class. Any positive trade verified on original incidence can feed existing circuit extraction/bounded descent. The earlier rank-one large-support family also requires k additions from the weight k+2 right incumbent, so a fixed addition cap is not a universal theorem. Exact independent local Python tests (seed369, 400 planted random X3C sources, 851 above-bound parity points): 529 removal-only, 261 one-add, 55 two-add, 6 three-add improvements; 851/851 restricted detection comparisons against exhaustive alternative assignments, all recovered moves verified. Small planted fixtures, not hard-source acceptance or full donor replay.

Stronger exact counterexample to ALL redundant parity-check capacity constraints, not just fixed-support odd checks. Original X3C universe 18, 30 distinct triples, zero-based in order:
(5,13,17),(5,14,16),(3,10,17),(0,2,16),(3,4,16),(1,10,12),(0,7,15),(6,7,10),(1,12,13),(4,5,13),(1,3,12),(0,4,6),(8,10,17),(3,7,9),(1,14,15),(9,12,15),(2,13,16),(2,12,17),(2,5,15),(6,7,8),(6,7,14),(8,11,17),(4,11,15),(5,8,11),(2,3,9),(6,9,13),(9,10,11),(0,1,16),(0,4,14),(8,11,14).
Every original row degree5; x_i=1/5 is strict fractional Ax=1. Integer solution z=(0,0,1,0,1,0,-1,0,3,-2,-2,1,0,2,0,0,0,0,2,0,0,0,0,1,-1,0,0,0,1,0) verified exactly Az=1; HNF determinant3. GF2 rank18 so every parity point lifts mod every power of two. Exact parity enumeration 4096 points, weight multiplicities 8:54,10:246,12:642,14:1039,16:1202,18:658,20:206,22:40,24:8,30:1. No weight6; independent exact-cover DFS confirms zero covers. All 171 single/pair projected exact-one hulls have original full projected dimension, verified by enumerating original parity points and GF2 rank of each local admissible image. Full rowspace 262144 checks, 131072 odd; minimum odd support5, independently checked by both exhaustive rowspace and absence of all singleton/triple masks. Found by deterministic random search (seed369, trial1012 zero-based).

Why every parity-check polytope survives: for any row-space support b of size h, its RHS equals h mod2 (all original row degrees odd). The forbidden-pattern inequality for subset F of b with parity opposite RHS is sum_{i in F}(1-x_i)+sum_{i in b\F}x_i>=1. At x_i=1/5 LHS=(h+3|F|)/5. If h odd, h>=5 so inequality holds even F=empty. If h positive even, h>=2 and |F|>=1, hence LHS>=1. Empty even check vacuous. Thus ALL redundant parity-check forbidden-pattern inequalities and original LP constraints are feasible, not merely odd capacity inequalities. No parity-capacity LP dual of these constraints can prove this source empty. This is the classical parity polytope relaxation limitation specialized to original X3C; not a computational lower bound, not a barrier to arbitrary higher-order cuts, other affine contractions or exact search. Full dyadic lifting + pair-hull + all linear parity-check inequalities is not universally complete as tested here; do not make that closure a required theorem.

Genuine remaining constructive contract: uniform polynomial-cost signed improving trade or verified bypass on every inhabited above-bound source, with existing exact verification and floor((n-k)/2) iterations; or independent C1a/C1c+C2a/C2b sufficient observation. No compulsory exact optimization, all moments or LP integrality. S1/R1 remain independent; all thirteen universal targets and seven alternatives OPEN. Targeted repo source inspection; exact local Python/SymPy checks only, no new committed checker, native kernels, CI, default edits or full historical dispatcher replay. No Clay endpoint claim.


## P0 endpoint cut — lattice-saturated sparse Walsh collective gain (2026-11-26)

Endpoint-first; two user-supplied inspirations: HNF integer-fibre binary image and complete retained-kernel requirement (historical Agda 8ab44d798b1115568516fd804a760ffa6139aefe), and incumbent-relative quotient/all-parity-capacity barrier (live prior bfa874a24020). Current entry heads inspected: Agda #1548 bfa874a24020 (nonmergeable), Lean #119 829a79d46aa7 (nonmergeable), Langlands #1549 b2691d0b01f1 (nonmergeable), #120 0746418d033c (mergeable). Historical HNF roadmap at the exact cited ref fetched successfully, blob 7095b850a490525bb94ed96270a0b6ff46214026; live Agda controlling roadmap blob 49d51319ab195409a38f9d332f7ede2221b2065b did not contain its uniformAffordableImprovingTrade section. Preserve both lines of mathematical work; no branch reset/merge. Actual live X3C checker ea46e409d6af8c3d02a82ae7a7fff9187359c7c1 still uses modular_rows, not HNF. Master Karp21ExactHittingTransposeExact c4d5a1084ae204364cab81c594e98595e97287e2, partial quotient 42400570bdc6705f8d3c6a0e0d1bc1aa6a210b24, signed moment filter 6a8d55d87a0a757019f194b1a6633d38b48c19e1 (actual direction(H,B) congruence body recovered), signed minimum donor retained. Do not rebuild generic consumers.

Restore mathematical content from attachment without declaring executable integration: let H be a column-HNF basis of A Z^n, A=HC, b=Hc with c integral; otherwise exact emptiness. C:Z^n->Z^rank(A) surjective. Exact binary image {z mod2: Az=b,z integral}={x:Cx=c mod2}; reverse lift z=x+2t with Ct=(c-Cx)/2. Dimension n-rank_Q A. Recompute on residual pinned source if useful; does not enforce binary nonnegative feasibility. All original covers survive combined lattice image, pins and one-hot hull constraints P={x:R x=d mod2}. Trades must lie in ker R, not just ker original A. For independent selected columns use R's columns in the incumbent quotient; removals uniquely reopen from additions. Existing circuit decomposition and floor((n-k)/2) strict descent clock preserved.

Sparse Walsh specialization: write v=V z for retained kernel basis. Group equal nonzero row signatures s_i of V, w_s=sum_{i:s_i=s}(2x_i-1). G(z)=sum_s w_s 1_{s dot z=1}; remove zero signatures and zero weights. Define chi_s(z)=(-1)^(s dot z), F=2G=S-sum_s w_s chi_s, S=sum_s w_s, with coefficient f_0=S,f_s=-w_s. For ANY explicit dictionary T of Walsh indices, H_{tu}=f_{t xor u}=E[F chi_t chi_u] exactly. Thus a^T H a=E[F (sum_{t in T}a_t chi_t)^2]. Construct H by XOR lookup, not affine power charts or enumeration. Reuse actual exact rational direction(H,B), then fixed a; expand only the triple convolution of f and a twice (at most (m+1)|T|^2 terms before cancellation) or evaluate conditional energy from that sum; chi_s conditional mean is 0 unless s lies in restriction row span, then its fixed sign. One-child descent keeps positive mass to terminal F>0; lift, verify full retained kernel and original weight improvement. Polynomial in explicit dictionary size/source bits, rational elimination bit size bounded by integer minors. First automatic dictionary T={0} union supp(w), size<=n+1. Can enlarge by XOR pair sums (contains four-character indicator of any two-signature restriction, hence provably dominates those probes); fixed-degree sumsets polynomial, not known universally sufficient. Full dictionary all 2^d frequencies is complete by Walsh orthogonality/conjugation to diagonal F, but exponential. Positive root is sound, nonpositive matrix UNKNOWN. No new mandatory representation or exact moment recovery. This is a specialization of classical Fourier multiplication and existing quadratic-positivity/conditional-expectation machinery, not a general new theorem of complexity.

Actual independent local Python/SymPy tests, not donor replay: 160 small planted X3C sources, all 114 above-bound lattice-image points recovered by root/single/pair exact conditional gain probe. Second deterministic seeded test (20261126): 240 denser planted X3C sources, 1973 sampled above-bound points (samples can repeat), pair-or-less 1743, sparse Walsh dictionary 1858, Walsh-only 115, pair-only 0, both missed 115. Every returned trade checked full retained lattice-image kernel and strict original weight decrease. HNF factorization/integrality checked. Strict example m=6, indexed triples (3,0,4),(1,5,2),(3,0,4),(4,5,0),(2,4,5),(0,2,5),(5,3,0),(3,5,1),(2,0,4),(2,1,5),(1,4,3),(0,5,4),(0,2,3),(2,3,5),(3,2,5),(4,1,5); repetitions are distinct indexed choices. x bitmask 7520, trade 7680, dictionary size17; pair probes inconclusive, verified gain positive. Tests used independent exact rational congruence implementation, not charged donor import; no claim of benchmark generality, universal coverage, or actual integrated executable. The 115 misses explicitly preserve the open producer. Current X3C HNF/gain adapters remain uncommitted executable work; do not mistake roadmap edits for integration. No full historical dispatcher replay, native kernels, CI or default branch edits.

Exact endpoint remains uniformAffordableImprovingTrade (alias of direct uniformNonlinearCoreProgress/deterministicSufficientObservation): a fixed polynomial clock on every input, returns a verified improving trade in full retained kernel or original exact cover on every inhabited above-bound source. Bounded descent supplies P=NP; converse via ordinary SAT decision self-reduction. All thirteen principal targets/seven alternatives remain open. Independent S1/R1 unchanged; do not conflate assignment gain and full-code gain, nor infer separation from missed observations. Next investigate why actual residual dictionaries miss, source-derived Walsh frequency selection/collective contraction or verified bypass; no compulsory full Fourier support, HNF or LP integrality, exact moment sequence or bounded-support moves. No Clay solution claimed.
