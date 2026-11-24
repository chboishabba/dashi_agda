# NS R568 P0 — exact same-state Galerkin helical sign countercontrols and source field weld

## 23 November — coordinator source-derivative normalization and exact time-zero sign audit

**Canonical source-owner audit:** already merged R596 shows 4F = the complete Gram coherent work plus the weighted Gram-flux tangent. R597 defines coherent work as twice the real Hermitian cross, and R560/R388 prove the actual same-system double-mixed damping/forcing tangent. Thus defining the *raw* positive Cauchy quadratic

    Qraw(t)=sum_{alpha,beta in actual fibre} Re<M_alpha(t),M_beta(t)> / (r_alpha+r_beta)

and F(t)=sum K_ab Re<D_alpha,M_beta], where the source R388 law is M'_alpha = D_alpha-r_alpha M_alpha, gives the **finite exact normalized derivative**

    Qraw' = 2F - ||sum_alpha M_alpha||^2.

In the literal **R596 coherent-work** normalization Qsource = 2 Qraw, the equation becomes

    Qsource' = 4F - 2 ||sum_alpha M_alpha||^2,

exactly consistent with R596's original 4F normal form (its Gram pair is twice Re, not Re). No new Agda lemma or cutoff-independent estimate is claimed. Physical time realization requires R240/R560 derivative authority and R565 scalar FTC; an algebraic-time-zero identity cannot be promoted directly to time-integrated C1.

The exact source-produced checker was extended *in place* to compute both Cauchy raw Gram Qraw and its R388 mixed-product time derivative, independently through the actual RATE-BUCKET aggregation, and to verify equality with 2F−the original coherent self-norm for each test state. It also rigorously confirms Qraw positivity by outward rational real-algebraic intervals. Current Git blob **9b6ea0db5c9698623c92df5bee94b6b087abe721**, checked against a byte-identical locally reconstructed file. Previous blob efad812d7699118ccb0396eb0165d4e6ba323fa8 was the preceding successful script before this extra acceptance check and remains a historical version, not current.

**Two physical seed-time-zero receipts** (all signs rigorous exact Q(sqrt2,sqrt3) rational-enclosure arithmetic):

- Seed 61: F>0>L, Qraw between 113.549331294160 and 113.549331294219, while Qraw' between −725.464561557930 and −725.464561557598.
- Seed 63: F<0<L, Qraw between 69.022181372628 and 69.022181372642, while Qraw' between −554.916309290680 and −554.916309290471.

Thus Qraw can be positive while its derivative is strictly negative even when unweighted F>0. Neither raw Q positivity nor the R596 exact evolution controls F's signed spacetime integral without an upper bound for Q at the endpoint and the integrated mixed-product self norm, and additional independent R653 C2 strict-margin payment. The rate quotient is not a guaranteed bound for those quantities as C→∞. The positive self-norm is not a licence to replace all four signs by a positive estimate.

**Independent run bookkeeping:** **64/64 CURRENT-BLOB exact acceptance independently rerun as four 16-case checkpoints**, ranges 0–15, 16–31, 32–47 and 48–63, with full original projected Galerkin source, real-helicity curl eigenlaws, exact both-currency rate quotient, source four-copy/factor-eight weld, exact nonnegative Cauchy raw Gram and R388-normalized derivative. Each block PASSED. Strict reverse-sign count by block 0,0,0,2 (exactly witnesses 61 and 63). All checks executed on current blob 9b6ea0db5c9698623c92df5bee94b6b087abe721, locally reconstructed byte-identically. One contiguous 64-case command exceeded this session's execution cap; checkpointed exhaustive seeds are a full acceptance, not sample extrapolation. No Agda/Lean kernel or CI run. This is source-faithful algebra in E=Q(sqrt2,sqrt3), not a native rational-F Agda result.

**Coordinator gate mapping:** six-endpoint portfolio B1 is the ALREADY-REFUTED unrestricted R820/R823 positive signed auxiliary; portfolio B2 remains OPEN for valid signed W1/continuum. Portfolio C1/C2 are the 15-Nov CLASSICALLY closed selected R853 finite Galerkin ODE/rate gates under a Python/SymPy proof protocol, but native Agda field/time translation is OPEN. The local R568 C1/R653 C2 signed two-sided inequalities are entirely different objects, both ANALYTICALLY OPEN. The canonical JSON adds a nonterminal NS rate-sign-no-go record without altering four completed/11 active gate decisions or 0/6 original Clay endpoints.

**Already merged preferred potential B producer:** R681 p-dot-q geometry, R682 same live R408/R664/R665 trajectory, R683 signed cross-gradient vector convolution; all the algebra is already source-written. The actual quantitative signed cross-gradient compensation and cutoff-uniform aggregation, along with true field-extension/native acceptance and scalar FTC, remain unpaid. Do not reconstruct R596/R682/R683 or count the field gap as paid by an abstract generic carrier.



**23 November 2026. Original-source physical Fourier formula audit; independent finite algebraic verification; no claimed Navier–Stokes estimate or Agda/Lean kernel acceptance.**

## 0. High-alpha result and what is NOT claimed

Two *genuine finite physical phase-space inputs* with divergence-free conjugate-real Fourier velocities, complete original cutoff-1 ordered projected Navier–Stokes network, actual positive/negative curl helicity and the source R225/R388 doubled amplitude/forcing identities give **opposite strict signs** of the unweighted R568 Cauchy forcing pairing and its pair-rate lift. This is much stronger than the earlier freely assigned D/M proxy control and is a concrete countercontrol to any **pointwise sign-transfer claim** based only on real NS Fourier geometry. The two examples have different sign orientations.

Crucial: They are **one-time finite Galerkin states** in the exact real algebraic helicity scalar field E = Q(sqrt(2),sqrt(3)), with complexification E[i], rather than inhabitants of the currently hardwired **F=Q** in the R566/R567/R687 Agda owners. The source formula matches those owners coefficient for coefficient, but the certified field-extension/naturality bridge has **not** been installed in the native owner. No spacetime C1 or C2 sign/bound is being refuted. A local polynomial Galerkin ODE starting at each admissible initial state exists by standard finite-dimensional smooth ODE theory, and its strict signs persist on some sufficiently short time interval by continuity; **no explicit validated time interval or live R240 native proof is claimed**.

**Executable, byte-matched local run:** [scripts/check_ns_r568_physical_source_weld_exact_20261123.py](../../scripts/check_ns_r568_physical_source_weld_exact_20261123.py), Git blob efad812d7699118ccb0396eb0165d4e6ba323fa8, SHA256 **953fea1800e4cd8f5e2366a11debf7c9103930c8549461a70da181e657027e70** is the current executed byte-identical verifier, including the helical eigenspace acceptance checks.

**Independent native-port witness input manifest:** [26 explicit positive-mode integer complex-vector rows for seeds 61/63](../physics/NSR568OriginalPhysicalAlgebraicWitnessModes20261123.csv), exact Git blob `8b9942326e3e3fa96779c61b64cd13bb5117aef5`, byte matched against the local CSV and checked row-for-row against the script's deterministic seed generator. Every original nonzero mode is then u_k=P_k a_k (for the 13 lex-positive modes), u_-k=conjugate(u_k), and u_0=0. This removes dependence on Python's pseudorandom generator as a native Agda/Bishop fixture artifact, while retaining the independent seeded executable.

## 1. Source normalization — no proxy D/M independent of the velocity

Source ownership read on master, no numbered source modules were rewritten:

- NSTriadKNPhysicalTriadEnumeration / NSTriadKNPhysicalOutputFiber: all **p,q,k within the same cube** [-C,C]^3, with ordered p+q=k. Here C=1 and selected nonzero output k=(1,0,0). The complete fibre contains N=18 ordered original incidences and three actual masses m=|p|²+|q|² in {1,3,5}.
- NSTriadKNExactSignedGalerkinCoefficient / NSTriadKNComplex3GalerkinEquationAudit: for a single velocity state u, produce the *same-state* projected nonlinear force on every retained output by
  N_k(u) = sum_{p+q=k, ordered} -i P_k[(u_p dot q) u_q].
  There is NO extra 1/2, and no random arbitrary vector force. Zero mode is retained as bookkeeping with u_0=N_0=0.
- NSTriadKNPeriodicHelicalFourierInfrastructure: P_k is the exact Leray projector, and u_k^± = (P_k u_k ± i k×u_k/|k|)/2. The executable proves their **sum**, exact +/- curl eigenlaws and modeNorm*inverseModeNorm=1 on all nonzero retained modes, not merely uses a formal helicity label.
- NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact: actual doubleCell M_(p,q) = 2 (u_p^+×u_q^- − u_p^-×u_q^+).
- NSTriadKNLiteralMixedCellGramPairRound380Exact / NSTriadKNDoubleMixedPhysicalDampedTangentRound388Exact: actual doubleForcing
  D_(p,q) = 2 [R230.productRuleForce(p,q)+R230.productRuleForce(q,p)],
  R230.productRuleForce(p,q)=N_p^+×u_q^- + u_p^+×N_q^-.
  Both depend on THE SAME u and its full projected nonlinear N(u).
- NSTriadKNFactoredFullTransposeSymmetryRound566Exact, NSTriadKNFactoredFullCommutatorOnlyRound567Exact and NSTriadKNR650RateLiftedR568ToC2CommutatorRound687Exact: original literal forcingPair(a,b) = Re<D_a,M_b> / [nu(m_a+m_b)] on nonzero output. Here nu=1, and the pair-rate lift instead is L = sum_{a,b} Re<D_a,M_b>. The existing R687 identity becomes L = 8 W(Mixed,Commutator) with W(x,y)=2 Re<x,y> and folds sum_a D_a=4*Commutator, sum_b M_b=4*Mixed. The independent local checker verifies BOTH factor-four folds and the exact factor-sixteen scalar.

All modes and initial velocities are **exact**, not numerically rounded: for each lexicographically positive k, initialize a seed-generated complex integer vector a_k with real and imaginary parts in [-2,2], set u_k=P_k a_k, and set u_-k=conjugate(u_k); k=0 has u_0=0. Thus k dot u_k=0 and exact reality. The source N(u) has exact reality and is divergence free by independent checks. The same full u, not independently sampled G/D/M, produces every cell.

## 2. Explicit exact same-Galerkin-state certificates

Write t2=sqrt(2), t3=sqrt(3), t6=sqrt(6). Each exact value belongs to E=Q(t2,t3) and has a four-coordinate rational basis. The source-compatible physical state is fully reproducible from the script with Python random.Random seed; all 13 independent conjugate mode-pair coefficients are deterministic.

**Witness A: seed=61, cutoff C=1, output k=(1,0,0)**

F_61 = 329107/1080 − (1343/12)t2 + (986/9)t3 − (285547/2160)t6.

L_61 = 125159/54 − 945t2 + (7888/9)t3 − (56521/54)t6.

Outward exact rational square-root intervals establish

    12.393550440969 < F_61 < 12.393550441035
   −64.470874428377 < L_61 < −64.470874427859.

Thus **F_61 > 0 > L_61** on the same self-consistent projected NS state.

**Witness B: seed=63, same cutoff and same output**

F_63 = −2923/9 + (2003/36)t2 − (311/16)t3 + (60641/540)t6.

L_63 = −43123/18 + (3511/9)t2 − (311/2)t3 + (26065/27)t6.

Outward exact rational square-root intervals establish

    −4.686082065474 < F_63 < −4.686082065423
   251.309121575252 < L_63 < 251.309121575643.

Thus **F_63 < 0 < L_63**: both orientations occur. The source sign is NOT restored simply by imposing Leray projection, divergence freedom, exact conjugate reality, helical +/- decomposition, and full same-state nonlinear convolution.

### Independent local acceptance and reproducibility

- 64/64 deterministic (seeds 0..63) source-produced finite velocity/force states checked with EXACT eight-coordinate Fraction arithmetic and no external numerical libraries; all 64 have **nonzero** original unweighted pair F.
- 2/64 strict sign reversals (seeds 61 and 63), certified with outward **rational** sqrt intervals using integer isqrt, not a floating-point comparison.
- For every test, exact original N_k complete ordered pair network, transverse u and N, reality of u and N, exact helical plus/minus sum and eigenlaws, source R225 and R230/R542 **two independent factor-four vector folds**, R687 scalar factor-eight coherent-work identity, p/q swap of both physical currencies, and literal original O(N²) signed pair sum == independent rate-class grouping == exact full rate-average projector pairing.
- Each output fixed fibre: 18 original ordered incidences; 3 distinct positive masses; exact rational Cauchy rank 3 and nullity 15; 16 cells with nonzero D and 16 with nonzero M in witnesses.
- Run via python scripts/check_ns_r568_physical_source_weld_exact_20261123.py --seeds 64 ; exact witness certificate via --start-seed 61 --seeds 3 --require-opposite --print-certificate.
- Committed Git blob matches the executed local file via git hash-object. The printed decimal approximations are **only presentation**; every theorem-relevant equality and strict sign is checked exactly.
- No Agda/Lean kernel or GitHub CI run, no continuum cutoff limit, no quantitative trajectory-time validation.

## 3. Stronger exact analytic firewall and mathematical interpretation

The previous free-carrier two-rate Cauchy countercontrol showed arbitrary D/M can have opposite signs. The new witnesses demonstrate this survives imposing the original projected quadratic NS force and helical products at a finite physical state. Thus the proposed universal *pointwise* mechanism

    sign(sum_ab K_ab Re<D_a,M_b>)
         = sign(sum_ab Re<D_a,M_b>)

is **false even on physically generated static Fourier data** (in a lawful algebraic extension). Cauchy positive definiteness controls the *diagonal* quadratic pairing D^T K D, but not the sign of this *mixed* D^T K M, even after actual NS constraints.

This does NOT prove an R568 physical spacetime upper bound impossible: a time-integrated signed inequality might exploit dynamical cancellations, other output k, diagonal self-work, endpoint contributions, initial flux, viscosity, or a cutoff-dependent comparison absent from the simple pointwise sign conjecture. Nor does this solve C2's strict-margin lower bound. It **does require removing universal same-sign transport** as a valid candidate analytic lemma unless it carries a substantially stronger physical, time-integrated hypothesis.

## 4. Exact remaining native source / PDE payments

1. **Formal carrier transport:** construct a legal exact ordered real algebraic field E for the physical helical norms 1,sqrt2,sqrt3, embed rational original R566/R567/R687 pair algebra functorially, and prove the source products/reciprocals/cross and p/q output fibres commute with the embedding. This is not satisfied merely by running Python in E; native rational F=Q remains a different concrete owner. Prefer existing general-field R225/R230/R294/R388/R541 lemmas where reusable, and mark rational-specialized R567/R687 interfaces explicitly.
2. **Native seed-61/seed-63 witness:** attach exact positive-mode integer-velocity certificate, projection, reality, all 26 physical modes, N(u), helical eigenlaws, both scalar pair sums and the two rigorous rational strict signs to the actual Agda/Bishop carrier. This gives a kernel-certified obstruction to sign-only transport *if* native field bridge is paid; it is not the signed spacetime budget.
3. **Physical time:** instantiate a genuine R240/R405 trajectory beginning at the witness and prove its exact time-zero field correspondence; strict signs extend locally by finite ODE continuity, but a quantitative interval and the existing R495/R565 time integration remain independent obligations.
4. **New physically viable C1/C2 mechanism:** the genuine original target is R653's two-sided signed original-trajectory sandwich
      2 S_delta + G + H <= 4 F <= B(T,R,t).
   R568 upper C1, R653 strict-surplus lower C2, independent scalar FTC terminal and universal 3D PDE estimate remain OPEN. Search for compensation across outputs/time (R596/R624/R628/R634) or original paired rate/flux gradient (R681/R689), NOT unconditional pointwise sign transfer from R687.
5. **Attribution and names:** the R225/R230/R380/R388/R541/R566/R567/R568/R596/R624/R628/R634/R652/R653/R687–R689 algebra is prior original repo source; new contribution is an exact live-formula finite **countercontrol** with independently executable certificates and an explicit field-transport gap. The semantic-name registry is a separate owner, never mechanically rename the source-numbered chain.

**Outcome:** new source-consistent static sign counterexample to the proposed universal pointwise transfer, exact and independently executed; no native theorem and no physical signed spacetime payment. Original Clay NS problem remains OPEN.
