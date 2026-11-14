# Six-frontier original-source maximum cut — implementation rounds 9–10
**Date:** 14 November 2026
**Owner:** Agda Clay PR #1499 and Lean Clay PR #108 (both source rollups); historical owner branches are donors only.
**Trust:** every linked source-written Agda/Lean candidate is **NOT**
kernel-accepted in this round; local exact-rational regressions PASS.
No Clay problem or NP-completeness consequence is claimed solved.

## Canonical PR topology and execution contract (rollup revision)

The active work destination is **one open draft PR per repository**:
Agda **#1499**, `chatgpt/clay-20261112-four-frontier-fail-closed`
against `master`; Lean **#108**,
`chatgpt/clay-continuous-fifth-sign-20261112`
against `main`.
The former per-lane PRs are source/provenance donors, **not** active
destinations for new work. Their histories are not Git-merged or closed.
All transferred files have retained their content-addressed Git
blob SHA; overlapping paths are deduplicated or reconciled explicitly.

The original round-9 donor groups now co-reside in the rollups:
- Agda: 661 donor-file transfers; 25 BSD Agda blobs already
  identical and additional original YM/NS files already present.
  Donors #1444, #1498, #1503 (YM), #1474, #1502 (Karp),
  #1478 (Bishop), #1500 (BSD), #1501 (NS).
- Lean: 56 original donor files from #107 BSD, #50 RH, and
  #109 NS; additional Route B cutoff/three-producer proof is
  source-written directly on the Lean rollup. The two divergent
  RH existing files were retained, with the useful missing
  Route B consequence in a nonbreaking new module.
- Shared critical global surfaces were deliberately NOT
  overwritten: `CHANGELOG.md`, `TODO.md`,
  `scripts/run_agda29_parallel_check.sh`,
  `.github/workflows/ym-native-maxcut-exact-agda.yml`,
  `Synthesis.lean`, and stacked external LeanDojo
  comparator files. These are explicit integration review items.

The **single-rollup** acceptance driver is
`scripts/check_clay_sixfrontier_physical_local_20261114.sh`.
Run it from the checked-out Agda #1499 worktree, pointing only to
the Lean #108 worktree:

```bash
DASHI_CLAY_LEAN_WORKTREE=/path/to/dashi_lean4-clay108 \
  CLAY_SIX_SOURCE_ONLY=1 \
  bash scripts/check_clay_sixfrontier_physical_local_20261114.sh
```

Omit `CLAY_SIX_SOURCE_ONLY=1` to request pinned local source
Agda/Lean checks; the script fails closed when kernels/toolchains
are unavailable. The script never treats the finite-only run as
a proof of any physical/analytic C gate. Kernel exit zero still
requires the original Agda golden and Lean `#print axioms` /
transitive trust audit before admission.

Full precise donor head hashes, transfer counts, incomplete global
surface inventory, source trust, and promotion booleans:
`Docs/roadmaps/ClayPortfolioPinnedIntegration20261114.json`.

The native source still owns its declared blame and attribution:
separate proofs for direct finite arithmetic, original-carrier
identification, analytic estimates, physical dynamics and kernel trust.
A theorem candidate, a synthetic sample and an unproved source
inequality never become one another through naming or a Boolean flag.

## Yang–Mills — PR #1503

**Already owned:** F19/P0 original Wilson finite cylinder,
normalized Haar and polymer/relative-density source, R445 exact
finite TV obstruction, covariance compiler, conditional mixture
inference; new exterior influence bound script
`scripts/check_ym_r445_weighted_exterior_influence.py`.

**Round 9 source:** `check_ym_r445_interacting_transfer_contraction_20261114.py`
uses the genuinely correlated two-state transfer matrix
`[[3/4,1/4],[1/4,3/4]]`. It computes
`D_k=(1/2)^k` at 41 exact rational distances and the summable
geometric tails at 30 cutoffs. The actual physical Yang–Mills
Wilson conditional law has not been identified with this
auxiliary model.

**Original max-cut leaves:**
`originalWilsonConditionalSameOutside`,
`originalWilsonExteriorInfluenceBound`,
`originalWilsonLocalizedDkBound` with cutoff-uniform
summable k, original uniform RG moment/covariance decay,
E1 interacting continuum, D1 continuum physical decay,
D2 same-E1 OS gap. Do not infer E1/D1 from a finite
transfer matrix or from local TV alone.

## Karp-21 — PR #1502

**Already owned:** literal 3-state finite gamma table,
`physicalAllLengthGammaRunSameOriginalPositive` for
positive gamma payloads, original raw first-enabled rule,
bit-native to raw first-enabled nonterminal correspondence,
source graph termination ≤edges+1 and signed ledger word bound.

**Round 9:** `Karp21NativeGammaPhysicalAcceptanceObservationExact.agda`
distinguishes halted-and-accepted work-head Blank from
halted-and-rejected Mark and instantiates exact positive gamma
payloads plus malformed empty/lone-zero input. Independently,
`check_karp21_literal_gamma_allwords_20261114.py`
replays all 32,767 words of 0..14 bits against the original
source gamma first-field parser and suffix.
`check_karp21_allwords_physical_local.sh` owns all six Agda
finite gamma roots.

**Original max-cut leaves:**
`physicalGammaAllInputsMatchesOriginalParser`
(no per-word exhaustive test substitutes for this universal theorem);
`nativeN21PhysicalFieldStreamSameOriginal`;
`originalBitTapeStepSimulatesN21Rule` on all phases,
including terminal observation quotient;
`nativeN21CompleteLiveHeapPolynomial` with input,
history, ledger, threshold, scratch/copies/heads;
`karpFractranBitMachineClockPolynomial`,
`karpFractranDecodePreservesAcceptance`,
`originalN21InNP` and original F3/F4 polynomial bit clock.
The token-only gamma fuel bound is not the whole verifier clock.

## BSD K1–K5 — dashi_lean4 PR #107

**Original curve:** `E : y²=x³−x`; field `ℚ_[2]`.
Existing `cmQ2SquareRoot3705` Hensel candidate consumes
the actual unit 3705≡1 mod8 for x=39.

**Round 9:** true Q₂ Hensel **source candidates**:
`cmQ2SquareRootOfOneModEight` (integer units 1 mod8),
`cmActualCurveQ2PointAt39`, and
`MillenniumBSDCMQ2EightLocalPointWitnessesExact.lean` for

| x | c with x³−x = c²u | u ≡ 1 (mod 8) |
|---|---|---|
| 28 | 2 | 5481 |
| 31 | 8 | 465 |
| 33 | 8 | 561 |
| 39 | 4 | 3705 |
| 41 | 4 | 4305 |
| 112 | 4 | 87801 |
| 1/4 | 1/8 | −15 |
| 1/16 | 1/64 | −255 |

The exact Fraction implementation of the eight actual
`(squareclass(x−1),squareclass(x),squareclass(x+1))`
triples uses `(v₂ mod 2,odd unit mod 8)` and proves all
eight **pairwise distinct**. It checks 2,732 locally compatible
integer x between −16,384 and 16,384, producing only six
triples on the integer slice; the two rational x above add
the missing two. Finite exact arithmetic is PASS. The
generalized Hensel Q₂ point and eight-point Lean sources
have no pinned kernel receipt.

**Original open leaves:** kernel acceptance of Hensel source,
reified `E(Q₂)` and true Kummer map to
`H¹(G_{Q₂},E[2])`; rigorous eight-class *exhaustion*,
real Kummer source, continuous restricted localization,
Selmer² and `Sha(E)[2]` LES, faithful MW finite generation
and rank, K4 eta/Mellin/same-object positivity, odd-primary
Sha/full BSD K5. Eight distinct image witnesses alone
do **not** establish full H¹ or the Kummer image upper bound.

## Navier–Stokes — PR #1501

**Already owned:** R71 exact physical finite cutoff RHS,
transverse/reality source, degree-two polynomial representation,
R74 finite rational coordinate chart, R853 same-packet
selected normal form
`r=6(12*C-P+(2ν−δ)*D)`, R829 initial arithmetic
`r₀=−28273644/125`, and R854/R855 exact conditional
negative affine-integral scalar arithmetic.

**Round 9:** rational sparse-polynomial
`check_ns_r853_quadratic_lie_derivative_20261114.py`
derives `L_F r=Σ ∂_i r F_i` exactly for a supplied
`F=quadratic` and selected `C,P,D`, with a
coefficient sup-box bound checked against the R854/R855
constant budget. Two exact arithmetic controls PASS;
they are **synthetic** until the actual R71 chart and
R853 same-observable source identities are produced.
It cannot replace real C¹ Picard or a negative true rate.

**Original open leaves:**
`originalR71R74PhysicalRHSIsRealQuadraticField`,
`originalR71RealGalerkinLocalSolution` on original R830
fixed horizon, `originalR853SignedRateAlongGalerkinSolution`,
`originalR828R854RateLipschitzAlongSolution`
(or R855 relaxed proven source bound), and
`nsR854OriginalRealRateIntegralStrictlyNegative`.
The original R823 reserve counterexample is also open.

## Bishop/eta — PR #1478

**Already owned:** selected original negative-log power
series `sourceCanonicalNatLogCandidate`; P1 complex
factorial-exp native source-weld; original finite Abel source;
original paired eta prefix and odd/even raw cutoff
decomposition; exact finite negative-log dyadic and
discrete incremental regression; 936 trig Cauchy coefficient
checks and 1,300 factorial tail cases.

**Round 9:** source-written
`BishopOriginalEtaRawSeriesOfSameSourceExact.agda`
identifies both coordinates of the original raw partial sum
with literal Murray `Sequence.SeriesOf`, instantiated with
actual selected `OriginalRound11DirichletEta.sourceTerms`.
It is now target 16 in
`scripts/check_bishop_eta_native_exp_cross_pr_local.sh`,
not a kernel receipt.

**Highest-alpha alternative:** prove
`originalCanonicalNatLogSuccessorIncrementSandwich` on
original Bishop setoid via the exact finite -log polynomial:
`1/(m+1)≤L(m+1)−L(m)≤1/m`.
This gives `L(2^k)≥k/2` and an original dyadic
geometric Abel modulus for every raw odd/even cutoff,
without first requiring continuous real FTC or exact
dyadic Nat-log equality *for eta convergence*.
Remaining: original expC addition/modulus/difference,
`originalRound11EtaDyadicGeometricVariation`,
`originalRound11EtaCompactUniformConvergence`,
trig addition, independent canonical log identity,
parameter derivative/real-variable FTC and analytic
holomorphic-limit transport. The original analytic
convergence and any RH consequence are OPEN.

## RH A2/G3 / Route B — dashi_lean4 PR #108, Agda #1499

**Already owned:** A2 exact four-coordinate scalar
`LocalPositiveDebt + literalFarExactAt <
compensationTargetThreshold + LocalMuGain`,
G1 constructed witness with an explicit coarse
uniform `fourthLipschitz < 4e9` and quantitative
strip compiler; A2 leading positive eighth-cap requires
a MUCH sharper same-witness threshold ~737.365
or a signed eighth treatment; original
`signedFifthCorrelationGapAt =
signedFifthPhysicalCapInteriorAt +
outerVerticalAbsoluteBudget −3eps`.

**Round 9:** `RiemannA2ActualSelectedIntervalDecisionExact.lean`
on the actual W, rho, EV, n has exact conditional
interval PASS, pointwise interval NO-GO and
eventual cofinal NO-GO compilers without absolute-value
replacement of FarExact. The rational interval regression
checks 4 exact synthetic cases and explicitly tags
source inputs as UNVERIFIED. No selected-zero curvature
nor completed compensation bound has been produced.

**Original open leaves:** selected
`fourthLipschitz` sharp enough on the ACTUAL W;
`HorizontalFarCurvatureBound CH`; original zero-shell
bound and completed N-mu compensation;
`originalSelectedA2StrictSignedCompensation`
OR a genuine same-zero-carrier cofinal inverse no-go.
Route B separately requires true eventual signed physical
cap gap, upper-boundary decay, outer-terminal convergence.
A substitute Möbius heat spectrum, negative bare-pole
sample or all-frequency Fourier sign-change cannot settle
these exact zeta-zero propositions.

## Zero-promotion ledger

| Lane | New source candidate | Finite diagnostics | Pinned kernel | Original endpoint |
|---|---|---|---|---|
| YM | finite interacting inference benchmark | PASS | not applicable | OPEN |
| Karp | gamma acceptance observation | PASS | PENDING | F2/F3/F4/NP OPEN |
| BSD | generic Q₂ Hensel + eight real curve points | PASS | PENDING | H¹/Kummer/Sha² OPEN |
| NS | polynomial R853 Lie compiler | PASS | not applicable | real flow/rate OPEN |
| Bishop | literal raw SeriesOf carrier | PASS | PENDING | eta uniform OPEN |
| RH | actual A2 signed interval decisions | PASS | PENDING | selected-zero sign OPEN |

**Next proof acceptance priority:**
BSD generic Q₂ Hensel and eight point source; Karp
F1 universal parser observation; Bishop raw SeriesOf
and finite Abel on pinned Agda; RH original
interval compiler; then invest in BSD Q₂
H¹ image upper bound and Bishop original
Nat-log incremental source transport.
All source-owned comments must retain known methods/authorities
(Bishop/Murray; Karp/Elias/Conway; Hensel/Kummer/Selmer;
Wilson/Bałaban; Navier–Stokes/Galerkin; Weil/Riemann)
and declare which gates were paid versus merely reduced.


## 14 November 2026: irreducible NEW-mathematics audit (C-min)

**Scope.** This section is a strict *novelty* cut, not the A/B/C source-implementation backlog above. Classify `VERIFY` (native kernel), `FORMALISE` (established mathematics), `SOURCE` (prove the same existing mathematical object is represented), and `NEW` (an unconditional, original-source estimate or universal theorem not supplied by a known result). A `SOURCE` proof can require hard engineering/analysis without being a new mathematical discovery. Existing scripted finite examples are not terminal theorems.

| Lane | Existing/known mathematics not to reopen as NEW | Minimal genuinely NEW mathematical leaves | Why they are independent |
| --- | --- | --- | --- |
| **Yang–Mills** | F19/R445 finite density, weighted-coupling TV, SU(2) uniform plaquette-deficit/density bounds, reflection Gram algebra, Haar and Wilson finite identities | `originalR445PhysicalExteriorInfluenceSiteBound` **and** `originalR445GenuineScaleIrrelevantContraction` for the actual renormalised Wilson effective/target pair; a cutoff-uniform interacting local-correlation estimate on the same physical continuum E1 source; nontrivial E1 limit with preserved OS positivity; physically uniform mass gap and compact-simple-group coverage | Full-volume TV, one-site plaquette density and finite transfer contraction do not establish local connected-polymer summability. Even decay of an approximate bare action is not E1 projective consistency, nor a continuum D1/D2 result. |
| **Karp-21** | Gamma parser, physical bit tape, costed simulation, NP membership are classical computability/complexity constructions; the repo's F2/F3/F4 are implementation/formalisation leaves | **None for proving N21 ∈ NP.** Separate unsolved Clay proposition `UniversalPolynomialSATDecisionFailure` (`∀ D ∈ P ∃ φ, D(φ) ≠ SAT(φ)`) only if pursuing P≠NP | Polynomial N21 verification does not imply SAT∉P. Original same-word physical correctness and bit-clock still need completion, but are not new mathematical barriers. |
| **BSD selected E: y²=x³−x** | Standard local Kummer/H¹/Selmer exact sequences, Mordell–Weil, modularity, rank-zero Kolyvagin finiteness, published CM level-32 special value and Rubin's CM odd-prime BSD theorem | **No novel number-theory theorem is presently identified for this one curve.** K1–K4 and the remaining two-primary / odd-primary K5 are application and faithful formalisation of known theorems, subject to their exact hypotheses | Universal BSD for arbitrary E/Q remains new mathematics and must be a separate gate; selected-curve completion does not solve it. |
| **Navier–Stokes** | Finite quadratic Galerkin ODE local C¹ flow, chain rule, the R853 pointwise polynomial rate, and local negative integral from a negative initial value plus continuity | `originalR736SignedCollarAbsorbable`, actual remote boundary/collar flux control, and a **cutoff-uniform global a-priori/continuation estimate for the original 3D PDE** | A negative integrated rate for one fixed finite Galerkin system or a fixed R854 horizon is not global regularity; it needs only classical ODE analysis once its source is identified. |
| **Bishop eta** | Classical Abel summation, the finite negative-log increment sandwich, dyadic bounds, exponential variation, locally uniform eta convergence on Re(s)>0, holomorphic-limit theorems | **None for ordinary eta convergence.** `originalCanonicalNatLogSuccessorIncrementSandwich`, `originalRound11EtaDyadicGeometricVariation` and `originalRound11EtaCompactUniformConvergence` are important original-carrier *formalisation* targets, not newly unknown analysis | The source's Bishop setoid/order/completion and native complex exp identities must be inhabited faithfully. This is not a RH proof. |
| **RH** | G1 coarse witness, finite A2 PASS/NO-GO compilers, parity/IBP controls and selected finite-polynomial bounds | Actual-zero `originalA2FarExactZeroShellBound` + full `originalSelectedA2StrictSignedCompensation` (or a same-zero-carrier no-go to **that route**, not to RH); alternatively Route-B `originalSignedFifthPhysicalCapEventualGap` with controlled actual boundary terms; actual G3 strict signed residual | These require nontrivial signed estimates on the real Riemann-zeta zero carrier. A generic pole, coarse witness, synthetic interval or different heat spectrum does not pay them. |

### BSD K5 short route: theorem reuse, not a newly invented odd-primary lemma

For the *actual* selected curve, LMFDB `32.a3` / Cremona `32a2`, not `32.a4` / Cremona `32a1`, gives `E: y²=x³−x`, rank 0, `E(Q)_tors ≅ (Z/2)^2`, `c₂=2`, and the **exact analytic BSD order** 1 (an *analytic prediction*, not a Sha proof). With the **standard full** period Ω, its rigorously computed modular-symbol ratio is `L(E,1)/Ω=1/8` (do not replace this exact theorem by a decimal). The rank-zero formula would require `#Sha = (L/Ω)*16/2=1`.

Under the **exact applicability hypotheses** of John Coates, *Lectures on the Birch–Swinnerton-Dyer Conjecture*, Theorem 32 (Rubin), a nonzero CM central L-value gives the BSD p-part for every odd prime here (`K=Q(i)`, no extra p=3 exclusion); hence each odd-primary Sha order is 1 when the normalized analytic ratio is 1/8. Rank-zero modularity/Kolyvagin supplies finiteness. If the *classical, same-object* Selmer sequence and actual cardinalities show `Sha(E)[2]=0`, finiteness gives the entire 2-primary part zero. Since a nontrivial finite abelian group has a prime-order element, all parts zero imply Sha trivial. This is a **conditional proof plan using established theorems**, not a kernel proof or a claim the source hypotheses are discharged.

Exact remaining selected-curve *formal* lemmas: `originalSelmerTwoEqualsKummerKernel`, `originalShaTwoExactSequence`, `cmOriginalLevel32LValueOverFullPeriod_eq_oneEighth` (target, modular-symbol / CM result with correct nonoptimal curve period), `cmOriginalAnalyticRankZeroShaFinite_fromKolyvagin` (target), `cmOriginalOddPrimeBSD_fromRubin` (target, with theorem hypotheses), and `cmOriginalShaTrivial_of_classicalTwoSelmer_and_Rubin` (target). **These are not novel arithmetic discoveries.** The existing period-normalisation and Gamma-candidate positivity modules are not L-value equalities.

Sources: https://www.lmfdb.org/EllipticCurve/Q/32/a/3 ; https://www.lmfdb.org/knowledge/show/rcs.rigor.ec.q ; John Coates, *Lectures on the Birch–Swinnerton-Dyer Conjecture* (2013), Theorem 32, https://intlpress.com/site/pub/files/_fulltext/journals/iccm/2013/0001/0002/ICCM-2013-0001-0002-a005.pdf . Existing local owner: Lean Clay #108, with donors Lean #107.

### NS and Karp promotion firewall

- `r(0)<0` and continuity of the same finite-Galerkin rate imply an interval `[0,ε]` on which `r(t)<0`, hence a negative integral. This **does not** imply the prescribed R854 fixed-horizon bound, nor 3D PDE continuation. No novel differential inequality should be charged to this local sign consequence.
- The actual N21 polynomial verifier remains uncompleted and must pay physical F2/F3/F4; classify it as **FORMALISE/SOURCE**, regardless of engineering difficulty. Reserve **NEW** exclusively for the universal SAT lower bound. Do not conflate original N21 NP membership with P≠NP.

### Next max-cut deliverables without theorem duplication

1. `VERIFY`: pinned Agda/Lean exact heads, `--safe` / trust and transitive axioms, before promoting any source candidate. No CI prerequisite.
2. `SOURCE/FORMALISE`: Karp actual F3 with heap+bit clock; BSD local `Q₂/R` H¹ and classical Sha; Bishop original Nat-log increment and eta limit; NS actual R71→R853 real flow; YM original R445/F19 effective/target identity; RH selected witness curvature.
3. `NEW`: focus mathematical research on **actual interacting Wilson summability/continuum/mass**, **actual Riemann-zero signed compensation or sign no-go**, **3D NS cutoff-uniform global reserve**, and **universal SAT lower bounds**. Universal BSD is separately open and cannot be inferred from one CM curve.

**Status:** documentation-only mathematical source audit. No source theorem, original C estimate or pinned kernel acceptance is promoted by this amendment. Attribution remains with Wilson/Bałaban, Karp/Cook–Levin, Kummer/Selmer/Kolyvagin/Rubin, Bishop/Abel, Navier–Stokes/Galerkin and the RH zero-analysis sources; DASHI's original-source adapter work remains separately attributed.


## 14 November 2026: external OpenAI YM existence intake, source-precise

**Source now PUBLIC, not just the 26 October announcement.** The October 28 OpenAI
Wilson construction was released via the Yang--Mills shepherding group on
11 November: `yang-mills-group/OpenAI-YM-20261028@3456e5e7...` (Lean 4.32.0),
reviewed independently in `yang-mills-group/YM@55ba9fc3...`, with
`YMReview.Acceptance.combined_acceptance` and separate
`YMReview.OPE.constructed` evidence. Review checks report that the combined
single Wilson family, phase-averaged table, fixed-volume UV and extracted IR
hierarchy, scalar OS, stress Ward, operator dictionary and short-distance trace
satisfy their **stated formal interfaces**. External independent validation is
not a native DASHI kernel receipt. Source details and limits:
`Docs/roadmaps/OpenAIYangMills2026SourceExactMaxCut20261114.md`.
Machine source/claim manifest:
`Docs/roadmaps/OpenAIYangMills2026ProofIngest20261114.json`.
Typed Agda source bridge:
`DASHI/Research/OpenAIMath/OpenAIYangMills2026SourceIntakeExact.agda`.

**Effect on cut:** E1 must now be split into
(1) **external released/reviewed candidate existence theorem** on its
specified Wilson family, construction and permitted gauge groups;
(2) **unpaid original DASHI F19/R445/P0-to-upstream same-source carrier**
and native Agda/Lean kernel transport; and
(3) independent **original physical D1/D2/N1/G1 and mass gap**.
This can significantly shorten original E1 discovery work **if** same-source
correspondence succeeds. It does not pay the same-family mapping, a unique
infinite-volume limit, full-field OS matching, D1 mass decay, D2 same-H gap or
Clay Yang--Mills. The published review expressly excludes these broader claims.

**Other OAI proof ingest integrated:** exact Git blobs from Agda #1212
`OpenAIMathUpstreamReceiptExact`, `OpenAIMathPriorityAtlasExact`,
`OpenAIMathSourceAtlasExact`, `OpenAIMathSourceAtlasRegression`
are now colocated on the **same Clay rollup #1499**; OpenAI's older
`openai/math` (`1581d4cb...`, Lean 4.34.1) remains **distinct**
from the new Yang--Mills submission (Lean 4.32.0). Local Lean world-builder
#1495 uses Lean 4.28.0; source-only manifest cannot be promoted to an
accepted DAG or a native kernel proof. Source identity before proof identity.
