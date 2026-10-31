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


## 2026-10-31 W05 constructive collision is now explicit (commit 3b0e4e457e93)

The canonical rational nine-jet matrix `M9` has a **primitive integral** nonzero null direction in SSP prime order (2,3,5,7,11,13,17,19,23,29,31,41,47,59,71):

`v=(-360448,0,1136200,0,-2624622,0,4499352,0,-4686825,2499640,0,-807576,374946,-32890,2223)`.

Direct exact integer arithmetic shows `M9*v=0` while tenth-jet A-coordinate `(M10*v)[9]=-571323080827699200 != 0`. Splitting `v=v_plus-v_minus` with `v_plus,v_minus>=0` supplies **two distinct nonnegative SSP valuations** whose first nine complex Eisenstein-valued winding jets agree but whose tenth-jet differs. This is a concrete consumer-relevant collision even with nonnegative factor multiplicity. The numerical values are exact integers, not floating approximations. An updated regression `scripts/check_ssp15_c3_winding_jet_rank.py` checks both equalities and rank-15 inverse.

**Status change:** W05 explicit finite witness from OPEN to **FINITE-TEST/CONSTRUCTED**, Agda kernel formalisation still **OPEN**. W04 rational inverse remains exact linear-algebra check, also kernel-pending. These counterexamples concern the *finite truncated jet observer*, not an individual state with no history; full winding histories remain the canonical starting point. Next higher-alpha frontier is certified conditioning/real analytic and actual infinite-prime two-point bounds (W06–W08, T04–T10), not more claims that one-point histories fail.


## 31 October: 369 SSP hyperfabric / 13-of-27 / 5-of-9 / nine-sheet transport / existing jets — direct source audit

**Confirmed exact owners (read the Agdas):**
- `DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact`: genuine `TriTruth ↔ KernelTrit ↔ SSPTrit` round trips, `NineSheet ↔ PantsPath 2` round trips and `Ternary27Point ↔ PantsPath 3` round trips. A **six-state signed wheel** sits in a **nine-sheet** with explicit neutral completion. The nine-sheet and cube are typed carriers, not automatically the same representation or an analytic global section.
- `DASHI.Reasoning.Trialectic369OutgoingResidualSheet9BidiExact`: outgoing residual `Triadic.NineSheet ↔ Codec.Sheet9` with both inverse laws, carrying `PhaseOrbit15 × Sheet9`. Use existing BIDI instead of a new sheet decoder.
- `DASHI.Moonshine.Base369P2FiveOrbitOrientationGroupoidsExact`: five global-inversion classes of a nine-sheet; gauge versus **retained** orientation distinguish five versus ten connected-component targets. Arithmetic/Fricke consumer must select the intended quotient; cannot silently gauge out the sign.
- `DASHI.Wikimedia.IbrahimA027907PathCubeTernaryExceptionalThirteenSnowballExact`: non-periodic 27 path-cube spectral multiplicities `1,3,6,7,6,3,1`, 13 as `1+6+6=(27-1)/2` and `1+3+9`. This is arithmetic/combinatorial; explicitly **not** same-object evidence for exceptional representation or a signed analytic prime correlation.
- `DASHI.Foundations.Base369Ternary27StratumStabiliserFibreAdmissibilityExact`: base-point stabilisers differ inside the same geometric stratum, hence the exact fine point must survive admissibility/quotient decisions.
- `DASHI.Geometry.AdmissibilityJetSpec`: typed finite jet order/redundancy/invariant-generator table, with physical-derivation flag false. Jet order is selected for the actual consumer, not a magical universal depth.
- Existing related `DASHI.Moonshine.JInvariantSheafHyperformAdmissibleDescentExact`, `DASHI.Moonshine.JInvariantAnalyticHyperformChartGluingExact`, `DASHI.Core.QueryFactorisationSufficiency`, `DASHI.Core.ConsumerIndexedResidualRefinementExact` remain the gluing and consumer-descent owners.

**Resolve the user's '9 → 18 → 27' as typed transitions, not one count identity.** Confirmed `NineSheet` (two trits), its two possible orientation lifts (up to eighteen states when orientation is independent), and `Ternary27Point` (three trits). A bijection from 18 to 27 does **not** exist. A valid *admissible join* must choose an embedding/partial map, provide a nine-element complement or a residual to distinguish the omitted third-coordinate sector, and preserve signed orientation and terminal consumer. The existing 5-of-9 groupoid quotient is a **different** quotient with separate gauge/retained semantics. The 13-of-27 combinatorial spectral decomposition is **another** coordinate count, not a proof that all 13 supported states are admissible. No cardinality welding.

**Re-scoped concrete lemma dependencies (H-series):**
- H01 (REUSE) nine-sheet/kernel/codec/pants BIDI with exact round trips;
- H02 (REUSE) original oriented six-wheel inclusion and neutral nine-sheet completion;
- H03 (OPEN exact instantiation) define which polarity/orientation 18-state lift is intended and exhibit signed consumer compatibility for that lift;
- H04 (OPEN exact instantiation) 18→27 injection/partial relation and explicit complementary nine-point face; prove no claimed 18↔27 isomorphism;
- H05 (REUSE arithmetic) path-cube spectral 13-of-27 multiplicity and 5-of-9 orbit class owners, with types and non-identity faithfully preserved;
- H06 (OPEN concrete) verify a specified *actual* spectral/prime/SSP signed consumer factors through each proposed quotient; otherwise construct collision and retain necessary residual;
- H07 (OPEN) admissible seam/pants join with exact base stabiliser, sign, provenance, and analytical Fourier phase;
- H08 (OPEN) projective transition compatibility/commuting square across 9→18→27 and back, with history and residual, not just cardinality;
- H09 (REUSE) prior `AdmissibilityJetSpec`, Bishop phase/complex analytic and SSP C3 Fourier owners;
- H10 (OPEN) embed W04/W05 **concrete** C3 derivative jets into the existing typed finite-jet surface; jet depth=10 rank sufficient for SSP15, but neither finite-jet admissibility nor stable inversion follows from dimension alone;
- H11 (OPEN quantitative) condition numbers and certified finite precision for jet reconstruction, including rotations/chirality and cross-sheet errors;
- H12 (OPEN analytic) only after completed H06–H11 connect actual all-prime signed `Lambda(n)Lambda(n+2)`, zeta-zero pair statistics or huge Pickover Bishop phase. These require independent real analytic bounds.

**Highest-alpha next cut:** concrete consumer-indexed `NineSheet × Orientation → Ternary27Point` implementation that chooses an explicit third-trit face and proves preservation, followed by gluing of signed SSP Fourier jets with actual overlap and conditioning. In particular, *history is prior state*, not an afterthought to a one-sample quotient. Preserve Ibrahim source ownership and prior Monster-3B provenance. No ESD changes.

All preceding 61 IDs remain in the register; H01–H12 expand the canonical tracked dependency inventory to **73 IDs**. The 73 are **not** 73 unproved theorems; many are reused existing owners. Source inspection does not imply Agda kernel verification.


## 31 October concrete H03/H04 oriented-face implementation

Added `DASHI/Moonshine/Base369OrientedNineSheetInto27BidiExact.agda` (commit `98526c8fdb90323d9ada65ceac49d57e39472e6c`) reusing `Triadic.NineSheet`, `Mobius.OrientationPolarity`, `Wheel.kernelToSSP`, `Wheel.sspToKernel` and the original 27-point geometry. The module sends `(a,b,positive/negative)` to cube `(a,b,+/-)`, proves the embedded sheet round trip, orientation determination, image injectivity and disjointness from the neutral z-face. The neutral plane is parametrised by the full nine-sheet; the joined carrier is **18 oriented face points plus nine neutral points**, never 18≅27. This is explicitly a *face* and consumer-transport structure, not proof of global analytic spectral gluing. Source-written Agda; kernel verification pending.

H03/H04 promoted from 'OPEN exact instantiation' to 'SOURCE implementation; kernel-pending'. H06-H08, H10-H12 remain concrete outstanding proofs. Key next max-cut: compare the existing `NineOrbit` five-of-nine quotient with these *retained* oriented faces, preserving the label of gauge-vs-observed orientation; then build a typed map carrying 10-jet **full signed vector** as residual along each sheet. Still no uniform all-prime correlation estimate.


## 2026-10-31 correction: canonical 27 = 1 + 13×2 antipodal *symmetry* carrier (user-highlighted prior owner)

Directly inspected the following existing Agdas:
- `DASHI.Foundations.BalancedTernaryAntipodalOrbitExact`: strict global SSP-trit sign inversion, unique zero fixed point, and concrete `AntipodalClass27` quotient. Its 27 quotient classifications include the 1+9+3+1 = 14 orbit classes, i.e. thirteen nonzero pairs plus centre.
- `DASHI.Foundations.BalancedTernaryAntipodal369OrbitHierarchyExact`: explicit pre-existing exact hierarchy `3=1+1*2`, `9=1+4*2`, `27=1+13*2`; 2/5/14 quotient orbit classes.
- `DASHI.Foundations.BalancedTernaryHypercubeAntipodalOrbitCountExact`: generic n-dimensional `3^n=1+2*P(n)`, `2*O(n)=3^n+1`. No new orbit machinery should be introduced.

**Priority correction:** the canonical antipodal decomposition of the 27-cube is `{fixed zero} ⊎ (13 nonzero orbit classes × retained orientation)`. The previously added `Base369OrientedNineSheetInto27BidiExact` is an **alternative coordinate slicing** into two signed z-faces (18) plus a neutral z-plane (9). It is *not* the symmetry quotient, not the 13×2 decomposition, and not a replacement for the canonical antipodal reconstruction. The 13 derived from the `A027907` alternating path-cube spectral multiplicity is likewise a distinct count: equality of 13s is not a consumer-preserving same-object theorem.

**Revised H-series leaf requirements:** H03/H04 source-written z-face embedding stays as a supplementary chart, while canonical H05 must import existing `AntipodalClass27` and the 3/9/27 hierarchy. H06 must require an actual **sign-retaining lift of a nonzero antipodal class**, and special handling of the unique centre. H07/H08 must prove that switching between z-face chart and canonical 13-pair chart preserves the original SSP signed valuation/fine point/terminal consumer, with transition cocycle and typed admissibility. No arbitrary choice of positive representative unless an explicit section/reconstruction proof exists. H10/H11 then transport exact SSP15 jets through this **canonical sign-retained antipodal fibre**, not by regarding a face count as an orbit count.

**Next concrete proof:** instantiate the exact canonical nonzero orbit representative/sign decoder and demonstrate a commuting square from full `TritTriple` through antipodal class+orientation back to the full 27 state. Treat fixed centre as its own constructor, not as two signed zero copies. If the original Agda owner already contains the appropriate decoder/round trip, import it verbatim and do not duplicate it. Proof-check after wiring. Keep all analytic RH/twin/Pickover quantitative gates independent.
