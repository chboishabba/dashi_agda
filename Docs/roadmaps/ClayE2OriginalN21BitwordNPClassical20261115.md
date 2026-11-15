# Clay E2 — Original N21 signed Max-Cut bitword NP, classical mathematical protocol

**15 November 2026. Verdict:** The *actual original* Elias-gamma-encoded, signed weighted Karp N21 graph-word language has an independent finite deterministic polynomial-time **bit verifier** and an original-graph-word-bounded sparse certificate. Its mathematical NP-membership proof instantiates the semantics of the *already source-written* conditional NP constructor under the user-approved Python/exact mathematics protocol, **not** an Agda-native checked PR.InNP term. This does NOT close E0, E1, NP-hardness, P!=NP, or any Millennium endpoint.

## Source-specific owners inspected in Clay PR #1499

1. Karp21GammaZigzagGraphWordDecodeExact.agda fixes original typed gamma(n+1), gamma(m+1), m triples gamma(u),gamma(v),gamma(zigzag(w)), and positive gamma(W); strict 0<=u<v<n, increasing (u,v), no duplicated/reversed edges or trailing input. Its LiteralN21 module is exactly the original typed graph-word predicate, not an invented simplified language.
2. Karp21SparseGraphWordNPBoundaryExact.agda provides exact original n21EncodedSparseWordBidi between typed signed Max-Cut YES and a bounded accepted two-bits-per-edge sparse certificate, and conditional karpWeightedMaxCutInNPFromMachineReceipts. The cost fields are PR.polynomialTimeVerifier cost verifyCanonicalSparseGraphWord and PR.polynomialCertificateBound cost canonicalSparseCertificateAdmissible.
3. Karp21NativeWholeBinaryGraphRuntimeExact.agda consumes source gamma bits with LE binary n,m and original bitwise 3m<=suffix-bit-length check **before** iterating. It decrements an actual binary m register and uses original input suffix length as structural fuel. Exponentially large n and m are never allocated as unary Nat or Fin.
4. Karp21NativeBinaryEndpointRawEdgeStreamExact.agda and Karp21NativeBinaryEndpointValidatorExact.agda parse u/v and signed zigzag w as finite binary words; u<v<n and strict lexicographic edge order use only native numeric LE comparison.
5. Karp21NativeWholeBinaryVerifierExact.agda is the actual executable binary-only source verifier: sparse 2m certificate cursor, original chronological endpoint history, two signed-magnitude ripple accumulation lanes, and original threshold comparison P >= N+W.
6. Karp21NativeWholeBinaryVerifierOriginalExact.agda and Karp21NativeWholeBinaryTypedAcceptanceExact.agda source-write pointwise all-word equality of the binary program with the *original typed* signed N21 verifier, **including malformed words**. This exact-head source proof still needs E0 pinned kernel acceptance.
7. Karp21NativeOriginalSparseCertificateBoundExact.agda proves the actual successful cursor consumes exactly two bits per original edge; Karp21NativeOriginalSparseCertificateTightBoundExact.agda strengthens accepted certificate length to |cert|=2m<=|original graph word| using the genuine original graph 3m budget and same-word parser transport. This remains source-written and kernel-unverified.
8. FiniteWordSizeExact.agda sets the original word and cert carrier to List Bool. PolynomialReductionExact.agda requires, for the same true machine cost model on BitWord, soundness, completeness, actual polynomialTimeVerifier and polynomialCertificateBound. The original exact typed assembler already exists.

## Explicit total standard bit verifier

Let n be the literal original graph-word length in bits, c the certificate length and S=1+n+c. The following is a **fixed** finite deterministic physical program, not a source AST fold charged unit cost.

- Read two original Elias gamma tokens with prefix-zero and exact remaining-payload scans. Return LE words for n,m using only subtraction of one from the binary gamma successor. Reject truncated, empty and unterminated headers.
- Compare 3m to the *actual remaining input-bit count* using LE addition/comparison, and reject when the bound fails. Thus every continuing branch has m<=n/3. The actual bitwise loop counts down m with at most the input-suffix-length fuel; no run performs exponential iterations through a gamma number.
- Parse exactly m successive source triples, each comprising gamma(u), gamma(v), gamma(zigzag(w)), into original native LE endpoints and sign/magnitude bit registers. Test original u<v<n, and strict ascending (u,v) with LE comparison. Read a strictly positive gamma(W); reject any extra suffix, malformed source token, nonpositive threshold, duplicate or reversed edge.
- Demand precisely 2m certificate bits, including rejection of every surplus/truncated certificate. For each edge, check both endpoint labels against **all** previous endpoint observations before recording both new observations in original chronological order. Reject inconsistent repeated-vertex labels. If the labels differ, ripple-add the unsigned magnitude to the appropriate positive or negative lane according to the source signed zigzag tag.
- Accept iff the positive lane satisfies P >= negative lane + W. Every comparison/addition is a bounded bit scan; there is no Nat/Fin/huge vertex-array allocation.

This finite bit program implements the same source algorithm as Karp21NativeWholeBinaryVerifierExact. The already-written B6 and typed all-word equality connect it to exactly the selected original N21 typed signed Max-Cut language. The proof uses these *existing equalities*, not the still-open E1 priority/FRACTRAN implementation.

## Constructive bit-memory and physical-time bound

On a successful parse, m<=n/3. Each source gamma operand and binary endpoint/weight has at most n digits. The complete edge-list bit storage is O(mn)=O(S^2), the original chronological endpoint history has at most 2m entries of width O(n)=O(S), hence O(S^2), and the two score registers have O(n+log(m+1))=O(S) bits: the sum of <=m magnitudes, each at most 2^n, has at most n+ceil(log2(m+1))+1 <=2n+2 bits. The threshold, binary count and graph input require at most O(S) bits.

Original repeated endpoint validation compares at most 2m preceding entries with both endpoints for at most m edges; a comparison on n-bit words is O(n) bit operations. Thus the dominant full verification work is O(m^2*n)=O(S^3). Parsing, m-count decrementing, signed ripple addition, suffix checking and handling malformed words all have at most polynomial bit time and **do not depend on decoded numeric n or m except via their <=n-bit representations**.

A fixed deterministic multitape implementation with explicit tracks, copies, header-fuel and phase resets has a conservative O(S^4) physical step budget and O(S^2) visited squares. A standard finite-track one-tape simulation with quadratic time overhead therefore has at most A*S^8 real finite standard-TM steps for some fixed program-dependent constant A and ALL original graph/certificate words. This is a physically halting size-only clock, not an abstract polynomial asserted for a List fold or a padded Cook run.

## Soundness, completeness, exact original certificate cost, PR.InNP

The repository's already written original n21EncodedSparseWordBidi proves:

    OriginalTypedN21YES(word)
       iff
    exists certificate: Word.BitWord,
       |certificate| <= |word| AND
       verifyCanonicalSparseGraphWord(word,certificate)=true.

For **soundness**, accepting all 2m certificate labels produces a consistent label on every graph vertex that occurs in an edge. Extend the assignment by false on all unused vertices (existential proof only; the verifier never constructs an n-element array). Every edge's original signed contribution agrees with the native score, and the original strictly positive W threshold holds. Malformed words are false in the original typed language and rejected by the bit parser.

For **completeness**, an arbitrary original typed full-cut YES witness induces its exact two-label-per-edge original sparse certificate. Its repeated occurrences are consistent, its signed score is the same original sum, and the original 3m graph budget entails |certificate|=2m<=|word|. This construction does not compute a huge full cut: completeness receives that cut from the existential YES proof.

Use the **actual-halting standard TM cost model on Word.BitWord**, constructed mathematically by the same finite-program map/verifier/certificate methods as the previous F1 source-independent model (which was for Cook.BooleanFormula, **not** for BitWord). Supply verifier polynomialTimeVerifier for this concrete binary function with O((1+n+c)^8), and certificate polynomialCertificateBound with the selected original admissibility |cert|<=|word| (degree one). The pre-existing original Karp21SparseGraphWordNPBoundaryExact.karpWeightedMaxCutInNPFromMachineReceipts then combines **both non-circular mathematical witnesses** and the exact source BIDI into original mathematical NP membership.

**Native firewall:** no Agda term inhabiting a complete PolynomialCostModel Word.BitWord, its two actual physical verifier/certificate evidence fields or the final typed PR.InNP was checked/written in this round. The source-written conditional assembler is not that unconditional theorem. E0 original B6/typed Agda source correspondence needs pinned Agda 2.9 kernel. E1 entire original N21 priority/FRACDASH/FRACTRAN bit-TM first-enabled step, full allocations and its particular physical clock remain OPEN even though a *different* conventional machine for the **same** verifier language exists. None of this proves NP-hardness or SAT not in P.

## Executable exact source regression

The committed script at scripts/check_clay_e2_n21_original_bit_np_20261115.py, Git blob **78427d9c75768602c7e38f3104814c14a35c0113**, was executed byte-for-byte locally. It has two independent reference paths: (i) gamma/LE-bitword original graph and certificate verifier including actual binary signed two-lane ledger and no unary endpoint decoding, and (ii) original direct signed-integer gamma/zigzag semantics with strict parser, identical certificate history and literal W test.

    PASS 478,508 original graph-word/certificate comparisons
    PASS original gamma+signed weights+positive threshold+malformed words
    PASS every accepted certificate exactly 2m bits and <= graph word
    PASS 3,189 actual accepted cases
    PASS all tested instrumented primitive-operation polynomial envelopes
    Observed maximum primitive charges 5,078; maximum bit-register width 21.

The sample tests are **regressions**, not proof by finite enumeration of universal correctness or real machine clocks; the general argument above is finite-program/one-head locality and polynomial arithmetic. No Agda checker was available here.

**Gate resolution under explicitly authorized Python mathematical protocol:** E2 status CLOSED_MATHEMATICAL_ORIGINAL_N21_BITWORD_NP, **not NATIVE_AGDA_INNP_ACCEPTED**. P0, B1 (negative refutation), C1, C2, F1 and E2 are mathematically/source-decided: **6/15 programme decisions, 9 active**; all six original Millennium endpoints remain unproved.
