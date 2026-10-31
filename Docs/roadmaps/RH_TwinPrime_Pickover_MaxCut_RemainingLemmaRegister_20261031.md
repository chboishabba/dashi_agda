# Max-cut remaining-lemma register — 2026-10-31

**Scope:** This register accompanies `RH_TwinPrime_Pickover_SixDirectionBidiLemmaRoadmap_20261031.md`. Every entry is classified as `REUSE` (existing owner), `SOURCE` (written, kernel pending), `FINITE-TEST` (executed finite computation), or `OPEN` (not proved). A reused owner may itself have unproved fields. The three mathematical endpoints **RH / TP / Pickover** remain separate; all six cross-directions remain conditional unless a real reduction is proved.

## Canonical proof-owner crosswalk

| Group | Existing code / original roots | Status and precise unmet obligation |
|---|---|---|
| F01–F05 | `C3FourierConjugationExact`; PR #1140 `OggPrimeFourierWindingExact`; PR #1272 `FourierPixelBidirectionalExact`; existing finite Fourier modes | REUSE for native C3/4-site cases; OPEN for arbitrary-size exact cyclic analytic scalar with no-wrap and true shift-two consumer |
| F06–F08 | `WaveAlgorithmLift.Trit`; `ConsumerIndexedResidualRefinementExact`; `TwinPrimeResidualMangoldtBidiExact`; `TwinPrimeTernarySignedShellHistoryBidiExact` | REUSE + SOURCE; need proof that concrete complex shell phase, real sign and interval status descend through **actual** Fourier reconstruction |
| F09–F11 | `RTXLightTransportRefinementExact`; `JInvariantBishopTrigUnitPhaseExact`; Bishop complex / real libraries and `bishop.agda-lib` | REUSE for source carriers; OPEN rigorous bound for concrete finite arithmetic transform and giant-angle interval arithmetic |
| F12–F13 | `JInvariantAnalyticHyperformChartGluingExact`, `JInvariantSheafHyperformAdmissibleDescentExact`, `TypedHyperfabricPantsGluingBridgeExact`, `QueryFactorisationSufficiency` | REUSE for typed interfaces; SOURCE `TwinPrimeActualPairSectionGluingExact`; OPEN global analytic chart section and kernel/Lean compilation |
| R01–R02 | `RiemannVonMangoldtSpecification`, `RiemannTrackedToVonMangoldtBridge` | REUSE for exact type-level `Lambda`; OPEN instantiate ordered real log and full endpoint-aware `psi` |
| R03–R08 | existing zeta/RH analytic programme | PARTIAL REUSE; OPEN globally valid explicit formula, truncation/zero list and RH equivalence on the true analytic scalar |
| R09 | RH PR #642 signed Schur/Gram, PR #1026 marked fourth-harmonic | REUSE respective owners and receipts; OPEN signed zero-minus-background estimate; do not transfer Lean receipts to Agda |
| R10–R12 | RH admissible signed zero-cloud bias route | OPEN off-critical zero exclusion, BIDI to classical `psi` bound, countermodel audit |
| T01–T03 | `TwinPrimeMangoldtPrimeErrorFiniteSplitExact`, `TwinPrimeResidualMangoldtFiniteSumBidiExact`, `TwinPrimeActualPairSectionGluingExact` | REUSE + SOURCE; OPEN faithful *real* `S=P+E` finite and asymptotic ordered bound + exact signed cyclic reconstruction |
| T04–T08 | Keating–Smith 2019 heuristic inverse pair correlation; true analytic-j/pants/consumer descent owners | OPEN true *joint* arithmetic/zero-pair producer, seam coincidence, smoothing/inversion, singular-series normalization |
| T09–T10 | true shift-two signed residual and prime-only cofinal witness | OPEN Hardy–Littlewood `o(X)` signed remainder or weaker infinitude lower bound |
| T11–T16 | `TwinPrimeSixWheelExact`, `TwinPrimeMangoldtNonzeroPrimeSumWitnessExact`, `TwinPrimeSOTABoundedGapBidiExact` | REUSE finite/cofinal BIDI; OPEN analytic hypotheses and kernel-checked partial summation/liminf/limsup transfer |
| P01–P05 | `PickoverAnalyticJHistoricalPhaseConsumerExact` PR #1260; `JInvariantBishopTrigUnitPhaseExact` and Bishop vendor | REUSE phase/trig; OPEN practical giant exponent winding producer and precision-certified power evaluation |
| P06–P12 | Pickover retained phase + signed zero-exclusion consumer | OPEN effective distance bound, exact sign-separated interval at `99^(9999!)`, independent checker |
| W01–W03 | `SignedSSPFRACTRANWeaveExact`; `OggPrimeFourierWindingExact`; cyclotomic C3 | REUSE; SOURCE mathematical symbolic derivative jet specification |
| W04 | `scripts/check_ssp15_c3_winding_jet_rank.py` | FINITE-TEST: exact rational rank m=9 is 14 and m=10 is 15; OPEN Agda/Lean kernel determinant/rank witness |
| W05–W07 | `ConsumerIndexedResidualRefinementExact`, `QueryFactorisationSufficiency`, original retained hyperfabric | OPEN explicit 9-jet collision witness, 10-jet FactorThrough proof and well-conditioned rational/interval measurements |
| W08 | actual von Mangoldt / true all-prime producer | OPEN proof that SSP15 finite inverse offers relevant **uniform** arithmetic two-point estimate; finite rank alone says nothing about infinitely many primes |

## Exact structural facts for the W-series

Canonical SSP15 splits into mod-3 residue groups `r0=[3]` (1 lane), `r1=[7,13,19,31]` (4 lanes), and `r2=[2,5,11,17,23,29,41,47,59,71]` (10 lanes). For `zeta=exp(2*pi*i/3)` the signed `k`-th jet `i^-k Z^(k)(2*pi/3)` equals `A_k+B_k*zeta` with
`A_k=sum_{r0} v_p*p^k-sum_{r2} v_p*p^k`,
`B_k=sum_{r1} v_p*p^k-sum_{r2} v_p*p^k`.
The **actual** rank sequence over rational coefficients for depth m=1,...,10 is
`2,4,6,8,10,11,12,13,14,15`.
A 15×15 nonsingular minor from m=10 produces an explicit rational left inverse and proves uniqueness for signed integer valuations. Depth 9 has a nonzero *rational* kernel; after clearing denominators, distinct signed integer valuations collide. If one insists on nonnegative valuations only, translate both sides of that integral kernel into nonnegative coordinates, still giving a collision (not necessarily an SSP-smooth input bounded by 1000). This is an algebraic rank conclusion, not a theorem about the physical conditioning of approximate derivatives.

## Remaining high-alpha *exact* implementation steps

1. **W04–W05:** materialise the 15×15 minor/integer nullvector proof certificate, check finite algebra with the canonical cyclotomic carrier; write the actual 9-jet collision and 10-jet reconstruction proof in Agda/Lean.
2. **T03/F03–F05:** exact *finite* cyclic correlation / nonzero-frequency signed phase theorem, with all overlapping shell cross terms; instantiate real `Lambda` only after exact scalar obligations are satisfied.
3. **T04–T08:** actual two-point zeta-zero **joint section** and arithmetic Fourier inversion over a common analytic scalar; define and pay overlap/cocycle, smoothing and singular-series error debts.
4. **T10/T09:** strongest feasible *unconditional* prime-specific lower bound first (T0); continue to (S(X)=2C_2X+o(X)) only as stronger steelman.
5. **P03–P10:** certificate for the original giant Bishop sine; a practical truncation/interval enclosure is meaningful only when it actually excludes 0.
6. **R09–R10:** signed fourth-harmonic analytic producer and actual global off-line-zero contradiction; no false projective-balance positivity.
7. **All:** kernel check exact heads; provenance of original Hardy–Littlewood, Keating–Smith, Bishop, Ogg/Monster, previous Ibrahim 3B, repo-specific proof owners; protected ESD import-only.

**Completion acceptance:** no invented axioms, no SOTA promotion from finite signals, every proof must name the actual terminal consumer and both directions of BIDI; terminal RH/TP/P9999 statuses stay OPEN until genuine certified theorems are produced.
