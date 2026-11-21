# Alpöge/Claude RH–GRH × DASHI geometric transport (21 November 2026)

## Provenance and status

External claim: Levent Alpöge's 20 Nov 2026 announcement at https://alpo.ge/remark.pdf and byte-exact mirror https://github.com/Deicyde/riemann-hypothesis. MIT independent audit: https://math.mit.edu/~drew/grh/ (snapshot 20 Nov 22:05 UTC). The MIT audit reports compilation of 175,187 modules, leanchecker replay, con-leche and nanoda independent kernel acceptance, con-leche statement comparison against a separate challenge and only Lean foundational axioms. Further checks remained underway at that timestamp. These receipts were **not executed locally by DASHI**.

The five audited statements include Mathlib RiemannHypothesis and Dirichlet L-function zero-location/nonvanishing claims. This is **Dirichlet GRH**, not the extended hypothesis for all Dedekind or automorphic L-functions.

## New source owner

`DASHI/Analysis/AlpogeGRHGeometricTransportExact.agda` supplies `ExternalRHGeometricTransport` and `externalRHImpliesDashiRH`.

This is a deliberately conditional **typed transport theorem**, not an imported Lean proof, not a completed proof of DASHI's analytic substrate, and not a fresh Agda kernel acceptance. It demands three separable items: an external zero-location theorem; a same-object map from DASHI's complex plane to the Lean complex plane preserving nontrivial zeta zeros; and reflection of the critical-line predicate. There is no fabricated constructor.

## Integration map

1. **RH zero-location lane**: when an audited certificate for `leanRH` and an actual same-object transport are available, `externalRHImpliesDashiRH` discharges `RiemannHypothesisFor analytic` without re-proving zero-location.
2. **Our Weil/geometry lane**: `DashiWeilSquareBridge.agda` derives RH from convolution-square positivity plus an off-line separator. External RH does **not** construct `WeilPositiveDecomposition`, `DashiWeilSquareEncoding`, `WeilSquareOffLineSeparator`, a positive 3×3/3×3×3 geometry, or a spectral Gram identity. The reverse RH→Weil-positivity equivalence requires a separately identified genuine explicit-formula theorem and matching test spaces.
3. **Bishop/complex analysis**: external RH does not supply our constructive complex exponential/logarithm, finite rectangle-tail limits, or selected Kneser branches. Reuse only through exact function-identification lemmas.
4. **Karp-21 / algorithmic corollaries**: GRH-conditional primality, prime-in-progression and finite-field algorithms can be tracked as corollaries *after* their exact statements and complexity bounds are imported. Neither P≠NP nor the Karp native verifier gates follow.
5. **BSD / elliptic curves**: Dirichlet GRH is not GRH for all elliptic curve L-functions and does not settle BSD, Mordell–Weil rank, Sha, or leading coefficients.
6. **YM/NS/TSVF/KK**: no direct transfer to Clay Yang–Mills mass gap, 3D Navier–Stokes, or a measured microscopic Lorentz metric.

## Exact acceptance gates

- [ ] Freeze source archive SHA-256 and challenge export SHA-256 from the independent audit; maintain byte-exact, trusted source provenance and license separation.
- [ ] Reproduce checker verdicts on pinned Lean 4.33.1/Mathlib 4.33.1 and independent judge, including axiom audit, namespace/definition resolution, and challenge/solution comparison.
- [ ] Read the original proof's dependency graph: identify its *actual* geometric/analytic proof steps, rather than treating kernel acceptance as an explanation of mechanism.
- [ ] Produce independently checked `LeanNontrivialZero` and `LeanCriticalLine` matching the audited Mathlib theorem.
- [ ] Implement actual `toLean`, `zeroPreserved`, and `criticalLineReflected` against the original analytic substrate, not a record of unrelated abstract sets.
- [ ] Compile the new Agda source with the repository's pinned toolchain and publish a local exact-head kernel receipt.
- [ ] If pursuing geometric mechanism, separately prove RH→positive Weil square form on the genuine source test-function space and identify it with DASHI's spectralZeroForm. Maintain the existing coercivity and separator gates as open until directly discharged.

**Do not claim** that this conditional bridge imports an external proof or proves RH in Agda. It is a fail-closed consumer for such an import, with geometric dependencies explicitly preserved.


## 2026-11-21: Clay scope correction and complete screenshot consequence register

**Clay scope:** the classical RH for the Riemann zeta function is the **entire** Clay Millennium RH statement; Dirichlet GRH strictly strengthens it. It is inaccurate to imply that Dirichlet GRH somehow falls short of the Clay RH problem. Independently reviewed mathematical validity and official Clay recognition are separate gates. **Extended RH terminology** often refers to Dedekind zeta functions; abelian number fields are accessible through Dirichlet-L factorization, arbitrary number fields are not automatically settled. General automorphic-L RH is broader again. Source anchors: https://www.claymath.org/millennium/Riemann-Hypothesis/ and https://www.aimath.org/WWN/rh/rh.pdf .

The following table transcribes **every distinct mathematical/software/cryptographic claim in the four user screenshots**, including disclaimers. It is a **claims and audit register**, not an assertion that each consequence is unconditionally established, efficiently constructive, or a new result. All claimed consequences must be checked against the precise versions and hypotheses in their cited source theorems.

| ID | Screenshot claim | Audit disposition and required exact bridge |
| --- | --- | --- |
| C01 | Miller primality test deterministic without randomness | Classical conditional deterministic Miller bound under ERH/GRH; AKS already gives unconditional deterministic polynomial-time primality, so no new necessity for randomness |
| C02 | Square roots modulo a prime deterministic fast | Conditional algorithm, ensure prime field input, complexity model, factorization of p−1/nonresidue search and precise GRH assumption |
| C03 | Cube roots and other kth roots mod prime | As C02, but distinguish fixed k, varying k and factorization/character issues |
| C04 | Deterministic quasi-polynomial finite-field polynomial factorization | Verify named algorithm, field presentation, degree/characteristic encoding, and exact time bound; GRH is not a universal unconditional deterministic polynomial-time factoring theorem |
| C05 | Deterministic direct construction of any finite field | Specify p^n, representation, output size and actual construction algorithm, not just existence (all finite fields already exist) |
| C06 | Integer factoring reducible to computing Euler's phi(n) deterministically | For standard n>1, known deterministic polynomial-time Turing reductions (unconditionally, via number-theoretic algorithms) require careful theorem/version check; avoid implying that RH makes general factoring polynomial-time from n alone |
| C07 | Prime congruent to a mod q of size roughly O(q² log²q) under GRH | GRH least-prime-in-progression bounds usually include log factors; 'about q²' hides these. Search to that upper bound is not polynomial in log q when done naively |
| C08 | Polynomial system solvability drops from PSPACE to AM | Identify the *Hilbert Nullstellensatz* decision problem over C with sparse/binary encoding; GRH-conditional AM upper bound, not arbitrary polynomial equations over arbitrary rings |
| C09 | Algebraic Valiant P vs NP linked to ordinary P vs NP over C | Check exact hypotheses and which class collapses/implications (VP, VNP, algebraic circuits, GRH bridges); do not claim equivalence without source |
| C10 | A known 744-state Turing machine runs forever | Need precise machine transition table and statement; if purportedly conditional on GRH, identify its reduction; no universal halting oracle follows |
| C11 | PARI/GP and Magma results labelled 'assuming GRH' gain unconditional status | Only for results whose **sole** remaining hypothesis matches the proved formal GRH (not ERH for arbitrary number fields) |
| C12 | Class-group algorithms receive guaranteed bounds | Check number-field discriminant, ring-of-integers, ERH/GRH of required Dedekind/Hecke L-functions, and input/output cost |
| C13 | Elliptic-curve parameter generation receives guaranteed runtimes | Check source, CM algorithms, primality assumptions and elliptic-curve L-functions; Dirichlet GRH is not blanket guarantee |
| C14 | Hard discrete log on one curve implies hardness on most related curves | Need a precise isogeny-family/degree/distribution theorem; neither generic ECC security nor average-case hardness follows just from RH |
| C15 | Quantum attacks on selected lattice systems gain proven success | Identify attack, parameters, prime existence condition, GRH scope and circuit complexity; not an attack on all lattice cryptography |
| C16 | Quantum isogeny attacks gain guaranteed runtimes | Same scope discipline: explicit field/family and number-theoretic corollary |
| C17 | BIKE/code-based cryptography special primes guaranteed to exist | Verify exact congruence and bound needed by relevant parameter families, not merely Dirichlet's existence theorem |
| C18 | Next prime within about √p log p | Standard RH prime-gap estimates require verifying precise log factors and domain; a scan of √p candidates is **exponential in input bit-length**, so it is not an efficient bit-complexity algorithm |
| C19 | Does not solve classical P versus NP | Correct: no such implication |
| C20 | Does not make integer factoring efficient from n alone; RSA/ECC remain safe | First clause generally correct as a GRH implication; 'remain safe' is overstated: security depends on separate assumptions and known/future algorithms |
| C21 | Does not intrinsically speed practical randomized algorithms | Typically conditional derandomization gives proof guarantees, not necessarily runtime improvements; application-specific benchmarking still needed |
| C22 | Ramanujan graphs, expanders, AG codes unaffected, relying on proved finite-field RH | Finite-field Weil/Deligne analogues are already established; distinguish their scope from number-field RH and avoid blanket 'unaffected' for all constructions |

### Owners, source routes and required deliverables

- **RH/Weil/Lean Clay rollups**: `DASHI/Analysis/RiemannAnalyticSubstrate.agda`, `RiemannZetaProgramBoundary.agda`, `RiemannWeilSquareCriterion.agda`, `DashiWeilSquareBridge.agda`; Lean rollup https://github.com/chboishabba/dashi_lean4/pull/108 and RH frontier https://github.com/chboishabba/dashi_lean4/pull/50 . Audit *their branch heads and actual theorem source* rather than infer completion from PR title.
- **Computability / Karp-21**: C01–C10, C18–C19 to Karp-21/FRACDASH; separate conditional algorithmic consequence, complexity-class transfer and same-verifier-step obligations. C08 concerns HN over C; does not prove P≠NP.
- **Number theory / constructibility**: C02–C07, C11–C13, C17–C18 to Bishop arithmetic, modular j/CM and class-group computation; some class-group guarantees require more than Dirichlet GRH.
- **Cryptography**: C14–C17, C20–C21 to explicit curve/lattice/isogeny/BIKE hypothesis ledgers; do not mark hardness or attacks proved generically.
- **Finite-field geometry**: C04–C05 and C22 to finite-field square/cube carriers; finite-field RH is not classical/Dirichlet RH.
- **Yang–Mills/Clay**: https://github.com/chboishabba/dashi_agda/pull/1444 carries distinct original physical covariances, lattice continuum, OS and CMP gates. RH/GRH import does **not** pay E1/D1/D2/N1/G1. Look for reusable **commuting operator identities** or positive Gram transport, never identify unrelated quadratic forms.
- **Cross-domain physical interpretation**: no implied result for Navier–Stokes, BSD, Yang–Mills, Lorentz/KK or observer identification.

## Commuting cube and actual geometry: new targeted max-cut

Do not silently equate the native 9 (= actual 3×3 sheet) or 27 (= actual 3×3×3 cube) with `Z/27`, a 27-dimensional Hilbert space or a modular/Monster order-27 orbit. Canonical evidence: `docs/369-27-cube-geometry-modular-carrier-disambiguation-20261024.md`. The **native cube has 27 positions and 54 undirected edges**; its adjacency graph and the 27-cycle have different spectra and no adjacency-preserving chart. Reuse `DASHI/Physics/Limits/PhysicsLimitCommutingSquare.agda`'s `ExactCommutation` and `ResidualControlledCommutation`.

Proposed genuine theorem target (not yet proved):
```
   arithmetic/analytic producer X  --zero-spectrum form-->  spectral evidence S
                 | encode / compare                         | identify observable
                 v                                          v
   native 3×3×3 geometric state G --native transport-->      geometric evidence T
```
Demand `observableArithmetic(x) = observableGeometry(encode(x))` on a stated and identified source domain, or a **quantified** residual controlled in the relevant scaling limit. Provide an explicit (Q_{Weil}) and (Q_{DASHI}) form, a structure-preserving map, and bilinear/quadratic isometry or a defect ledger. A set bijection / dimension count / symmetric picture does not pay this obligation. If the square fails, retain the exact counterexample as a useful no-go boundary.

**Relevant newest source paths to audit**: `DASHI/Physics/Limits/PhysicsLimitCommutingSquare.agda`, `DASHI/Core/CommutingProvenanceBidiCrossPollination2026Exact.agda`, YM #1444, Lean #108, Agda https://github.com/chboishabba/dashi_agda/pull/1291 (cube roadmap), and `Docs/support/reference/YMRHGlobalGoalParetoBoard.md`. Exact PR head and compiler receipts remain to be checked.

## Verification priority

P0: audit original Alpöge/Claude proof dependency graph and independent statement comparator; distinguish Clay RH from GRH/ERH.
P1: instantiate RH into the original analytic substrate via same-object mapping, not a postulated proof.
P2: inspect actual recent commuting cube and RH/Clay rollup theorem bodies.
P3: source-audit C01–C22 one by one against original papers / exact hypotheses and attach tests where tractable.
P4: explicit-formula / Weil-square ⇄ original cube observable commute-or-residual proof.
P5: only then promote downstream claims to native Lean/Agda accepted instances.
