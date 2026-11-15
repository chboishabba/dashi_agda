# Clay #1499: F1 actual-halting standard-TM cost model, mathematical protocol

**15 November 2026.** F1 asks for the missing polynomial map, precomposition, verifier and certificate-bound closure and identification of the original coded finite-state actual-halting polynomial machine model with textbook deterministic polynomial time. This note gives the **classical constructive mathematical proof** under the user's explicit no-Agda/no-CI Python mathematical protocol. It does not purport to be an Agda proof term or to solve P≠NP. The machine compiler is specified as finite program operations and ordinary polynomial resource bounds, not as a self-quotational fixed point.

## Source-specific definitions inspected

- DASHI/Mathematics/Complexity/PolynomialReductionExact.agda: PR.PolynomialCostModel consists of polynomialTimeMap, polynomialTimeDecider, polynomialTimeVerifier, polynomialCertificateBound, identityMapPolynomial and deciderClosedUnderPrecomposition.
- CodedStandardHaltingPolynomialCostModelExact.agda: HaltingStandardCostClosure fields polynomialTimeMap, polynomialTimeVerifier, polynomialCertificateBound, identityMapPolynomial and precomposeHaltingDecider; the existing haltingStandardPolynomialCostModel projects those into PR.PolynomialCostModel.
- CodedStandardHaltingPolynomialDeciderExact.agda: finite coded deterministic TM, two nonblank distinct binary input symbols, an **actual exact canonical execution** to quiescence, acceptance-bit equality and physical run steps bounded by a polynomial in the **actual source encoded input length**. The actual quiescent length is unique.
- CodedStandardCanonicalInputExact.agda and CodedStandardGuardedExecutionCompilerExact.agda: ordinary implicit blank-tail input, plus an **already source-written** compiler from actual canonical runs to Cook-guarded runs with exactly the same physical step count and accepting state. Do not introduce formula-dependent padding as time.
- CodedFiniteStandardMachineExact.agda, StandardFiniteTapePresentationExact.agda and StandardSingleTapeMachineExact.agda: finite Fin-indexed state and symbol sets, actual finite first-match deterministic rules and conventional one-head split tape, with explicit Quiescent transition = nothing.
- PNotEqualsNPCookFormulaBinaryCodecExact.agda and PolynomialClockArithmeticExact.agda: original eight three-bit syntax tokens, exact encode/decode and bit length, and size-only clock c*(1+n)^d where n is the **literal source bit-code length**.
- PNotEqualsNPHaltingCodedCandidateBridgeExact.agda: automaticGuardedExecutionReceipt and haltingWitnessToPolynomiallyClockedCandidateAutomatic **already exist**, so candidate coverage is not re-proved.

## Construct the operational cost predicates

Let E(phi) be the existing exact source binary code of a Cook.BooleanFormula phi, and n=length(E(phi)).

1. Define **polynomialTimeMap(M)** as the type of a finite-program standard deterministic **transducer witness** with distinct binary/blank symbols, actual quiescent run from the canonical source input E(phi) on **every** phi, literal final output exactly E(M(phi)) in canonical form, and actual step bound t_M(phi) <= a*(1+n)^d for fixed natural constants a,d. This is a machine-bearing property of M, not arbitrary extensional computability or an oracle.

2. Define **polynomialTimeVerifier(V)** as the corresponding finite deterministic total standard TM property on a self-delimited pair E(phi) and enc_C(c). Include a *supplied* finite binary certificate encoding enc_C:Certificate->List Bool (with decode/injectivity when needed) and a fixed bound t_V(phi,c) <= a*(1+n+length(enc_C(c)))^d and exact output V(phi,c). The source cost-model field quantifies over arbitrary Certificate:Set. This operational predicate is permitted to be empty for unencodable Certificate types: no uniform coding of every Set is assumed.

3. Define **polynomialCertificateBound(A)** as the property of a supplied certificate encoding enc_C and constants b,e such that A(phi,c) implies length(enc_C(c)) <= b*(1+n)^e. This size property is distinct from, and composes with, the verifier time property. Neither asserts SAT correctness.

4. **identityMapPolynomial**: a single fixed finite-state identity transducer leaves E(phi) untouched, rewinds/halts quiescent, has exact output E(phi) and actual time <= a*(1+n). It is a concrete witness of field 1, independent of SAT or padding.

5. **precomposeHaltingDecider**: given a polynomial-time map witness M as above and a CookReadyHaltingPolynomialDecider D, compile a new single finite standard TM with disjoint tagged finite control phases. Run M on the literal canonical E(phi) until its real quiescent finish. Cleanup and rewind its exactly E(M(phi)) output on the tape. Switch into D's fixed finite control on that canonical output, run D to its real quiescent finish, and preserve its acceptance bit. The finite alphabet uses only finite track products and delimiter/phase markers, and finite rule dispatch is deterministic. Thus the composed actual output is D(M(phi)); no arbitrary time-budget field is passed to the machine. From its physical exact run, the already-source-written automatic guarded execution compiler produces the required CookReady conjunction without changing actual time or result.

    Let the individual actual-time bounds be
      t_M <= a*(1+n)^d,    t_D <= b*(1+m)^e,
    where m=length(E(M(phi))). One-head local writing/visiting bounds the output size by m <= n+t_M+O(1), with the fixed additive overhead absorbed into the map coefficient. Put N=1+n, h=max(1,d), H=h*max(1,e), B=2+a+b*(2+a)^e. Then, for every n and nonnegative coefficients,

      1+n+t_M+t_D <= B*N^H.

    Compile the fixed finite two-phase program onto one tape by finite track/head markers. Each simulated primitive step and phase reset can be performed by a bounded number of sweeps over at most O(1+n+t_M+t_D) occupied/visited cells. A conservative overall bound is C*(1+n+t_M+t_D)^3, with C depending ONLY on the two fixed constituent programs (not on phi). Consequently

      actualSteps_composite(phi) <= C*B^3*(1+n)^(3*H).

    This supplies a fixed **source size-only** polynomial clock, allowing the record's precomposition field to be inhabited in the classical operational semantics. The machine runs for its actual unique quiescent duration <= this bound, **not** for a padded counter forced to this bound. This is an effective finite compilation of two finite transition tables, not a self-quotation or an F2 resource closing compiler.

6. The existing haltingStandardPolynomialCostModel constructor plugs the fields above into exactly the original PR.PolynomialCostModel. The existing haltingCostCandidateCoverage is then a **source-written projection** of an actual polynomial SAT candidate; this gate does not reimplement it.

## Identify genuine textbook P and the selected SAT input encoding

On **the exact source bit-code input language**, a total finite deterministic single-tape actual-halting program with polynomial step bound is literally the standard single-tape definition of P. Any finite-state/tape-alphabet presentation is equivalent to a Fin-indexed state/symbol finite rule table with constant overhead. Standard deterministic fixed-k-multitape TMs reduce to such a single tape with a polynomial (at most quadratic) overhead: represent k tracks and k head markers in a finite product alphabet and sweep across the O(n+t) used region for each simulated step. Conversely a one-tape program is a trivial k-tape program. Thus the usual standard single-/multi-tape **polynomial** class agrees with this physical actual-halting coded model on the chosen source encoding.

**Encoding subtlety, not to be suppressed:** the Agda source serializes variable indices in **unary**, while a compact binary-indexed formula writes a number i in O(log(i+1)) bits. Direct translation from arbitrary compact variable i=2^s to source unary tokens can be exponential; do NOT assert that every arbitrary index-sensitive formula predicate has polynomially equivalent descriptions by this direct conversion.

For **SAT specifically**, alpha-normalize distinct variable names by first occurrence: on compact input length s, assign the j-th first-seen name index j (0<=j<v<=s). The renaming is a bijection on occurring variable names. Every assignment to those names transports back and forth along this bijection, so satisfiability is exactly preserved; no condition on the numerical size of original names is used. Repeated scans and finite comparisons of at most s binary names construct the renaming by a fixed TM in polynomial time. The source unary code of the result has at most s syntax nodes, at most s variable occurrences, and each new numeral has <s successors, yielding an explicit size <=3s(s+2) bits. The reverse source-unary to compact-binary translation is also polynomial in the original source length. Therefore

    SAT_compact ∈ P  iff  SAT_source ∈ P,

without claiming representation invariance for arbitrary index-sensitive predicates. This is sufficient to prevent a spurious source-encoding-only SAT lower bound from being mistaken for standard SAT∉P. It is NOT a proof of SAT∉P.

The multi-tape simulation theorem is standard mathematics; see Jeff Erickson, Models of Computation, https://jeffe.cs.illinois.edu/teaching/algorithms/models/06-turing-machines.pdf and the single-tape simulation proof in Hopcroft–Ullman, Formal Languages and Their Relation to Automata, time/tape-bounded machines.

## Executable exact regression and acceptance boundary

- scripts/check_clay_f1_standard_tm_model_20261115.py contains independent original 3-bit-token source coding/decoding, first-occurrence SAT alpha-normalization with full assignment equivalence on tested finite examples, the quadratic normalized-length ceiling, and exact integer checks of the universal polynomial composition bound on 2,800 coefficient/degree/length tuples.
- Independently executed local extended checker /mnt/data/check_clay_f1_standard_tm_model_20261115.py: PASS on 65 formula examples (including large compact variable indices), 2,800 time-cost tuples, and all SAT assignment interpretations for each finite example. **These samples are a regression, not a proof by finite enumeration of the general mathematical theorem**; universal proof is the finite-program/one-head-locality/clock derivation above.
- The original Agda source-specific target fields in HaltingStandardCostClosure have **not been constructed as typechecked Agda terms** and no Agda kernel run/Lean native axiom audit was done. The proof of standard P above is the classical **mathematical** implementation in the expressly user-approved no-Agda protocol; the unverified source-native compiler/record implementation remains formalization debt.
- F2 ResourceClosingCompiler (same candidate's own Cook formula with physically closing budget) remains OPEN and is not inferred from any P precomposition. F3 ∀ polynomial SAT decider, ∃ incorrect formula remains OPEN; the whole SAT-vs-P barrier is not weakened by renaming/choice of coding.
- No Millennium mathematical endpoint is closed.

**F1 mathematical result:** CLOSED_MATHEMATICAL_STANDARD_TM_PYTHON_PROTOCOL (not NATIVE_KERNEL_ACCEPTED). Together with P0, negative B1, C1 and C2, **5 of the 15 programme decisions are mathematically/source-resolved under the user protocol; 10 active gates and all 6 original endpoints remain open**.
