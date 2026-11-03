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


## 31 October: integrate p-adic hypervoxel/cubie transport INTO BOTH canonical steelmen

**Twin-prime steelman owner:** `Docs/papers/TwinPrimeSteelmanAsymptoticBidiTarget20261031.md` updated with TH01–TH08; forward/backward consumer-indexed hypervoxel signed two-point gluing, original shift relation and quantitative Hardy–Littlewood T0/T3 acceptance.

**Pickover steelman owner:** `Docs/papers/TwinPrimePickoverRTXRetainedSignedMatrixMaxCut20261031.md` updated with PH01–PH08; actual Bishop phase, exact exponent/winding, p-adic/refinement address reconstruction, antipodal signed 13-orbit + centre, error propagation and certified terminal zero-excluding interval.

**Verified source owners:** `DASHI.Foundations.RecursiveRadixHypervoxel` (parent/fine suffix and `fineAddressIsJoin`), `DASHI.Geometry.HypervoxelAdicYoungFibonacciBridge` (p-adic chart, braid and explicit relation—not analytical identity), `DASHI.Foundations.TrialecticStageThirteenMarkedC3CubieExact` (27 cubie C3/reflection), antipodal 3/9/27 owners, existing Bishop actual-phase owner. No duplicate carrier. Neither the name Stage-13 nor 13 paired antipodes establishes a Monster representation or prime theorem.

**New explicitly tracked obligations:** TH01–TH08, PH01–PH08. These are further **cross-linked acceptance checkpoints**, not 16 distinct new foundations; previous F/R/T/P/W/H 73 labels remain authoritative for technical dependencies. Key unproved cut: instantiate the *true* analytic signed pair and the *true* Bishop terminal phase and pay quantitative error/margin estimates. SOURCE-WRITTEN docs only this update; no kernel validation or solution to RH/twin/Pickover claimed.


## 2026-10-31 complete two-steelman source edition and implementation status

**Canonical full formalisms updated in-place**, not merely cross-referenced:
1. `Docs/papers/TwinPrimeSteelmanAsymptoticBidiTarget20261031.md` — v3 TP-A…TP-G, exact original history, true `Lambda(n)Lambda(n+2)`, FTT signed complex shell cross terms, recursive hypervoxel/antipodal signed joining, rigorous forward/backward target, positive signed arithmetic estimate.
2. `Docs/papers/TwinPrimePickoverRTXRetainedSignedMatrixMaxCut20261031.md` — v3 P9-A…P9-H, true Bishop exponential, full 99^(9999!) exponent history, adic-vs-archimedean separation, hypervoxel refinement, telescoping transfer/norm budget, genuine terminal sign-separated interval, reverse precision bound.

**New shared Agda source:** `DASHI/Core/TwinPickoverHistoryHypervoxelTransportExact.agda`. Exact `TransportHistory` carrier deliberately retains the **original State** and original consumer; `RetainedVoxel` uses pre-existing `RecursiveRadixHypervoxel` coarse/suffix and `fine=joinAddress`. `forwardConsumer`/`backwardConsumer` are *definitional original-readout* equalities, not nontrivial factor-through proofs, signed estimates or an analytic reconstruction. Existing `TwinPrimeActualPairSectionGluingExact` is the true abstract von Mangoldt endpoint instance; Pickover actual Bishop analytic historical consumer remains in PR #1260 (not silently imported into PR #1408). Kernel typecheck not run by request; retain status SOURCE.

**Implementation boundary:** exact native history representation plus generic joins and actual pair endpoint have been source-written. The complete terminal proof specifications are printed in the two steelman docs, but the true analytic estimators TP-E and P9-D/E/F (also RH off-line exclusion) are not implemented or proved. Do not call the terminal theorems complete because the specification is now complete. User plans to run/verify; give no CI claims.


## 31 October current-turn max-cut: genuine two-sided arithmetic encoding plus hypervoxel history

**Committed source:** `DASHI/Arithmetic/TwinPrimeHypervoxelPeriodConsumerBidiExact.agda` at `8a4db720cd01557bd8cce7f992650b49ab096287`. Unlike the prior generic history record whose forward and backward readouts are definitionally equal, this owner proves *two distinct representation functions* `encode` and `decode` are inverses, by importing the already existing `decodeEncodeNatPeriod270` and `encodeDecodeNatPeriod270`. Source declarations: `ArithmeticHistory` with original integer and retained recursive coarse/suffix; `EncodedArithmeticHistory` with period code and those same hypervoxel fields; `decodeEncode`, `encodeDecode`, `refinedAddress`, `finePreserved`, generic `consumerForward`/`consumerBackward`, and `actualMangoldtPairForward` for **the canonical arithmetic pair consumer**. The original shifted relation is preserved because the entire input integer can be recovered, not because a marginal happens to match. **No new generic fibre ontology.**

**Both steelmen updated in place:** twin-prime document commit `73048016162d05d3a3a4b247ce2586a917ef8e23`; Pickover document commit `89afea555183ea7f48974cc956b4e4282e93a932`. The Pickover note explicitly forbids replacing real-angle phase by mere Nat-period residues.

**Verification:** source definitions and import theorem names were fetched and checked against GitHub; Agda kernel **not run**, CI ignored by user request. No claim that arbitrary chart coarsening is consumer-sufficient, or that RH/twin-prime asymptotics/Pickover terminal sign have been proved.

**Next source-to-kernel leaves:** typecheck the current head on user's machine; instantiate the original Bishop complex signed interval consumer from PR #1260 on the new *retained history* (without copying/rewriting the owner), construct the true exact finite shift-two signed Fourier correlation and the scalar-order connection, then pay the mathematically open analytic bounds. These are terminal work items, not missing representation folklore.


## 31 October continued max-cut — original hypervoxel join and exact consumer descent

Added `DASHI/Core/TwinPickoverHypervoxelAdmissibleJoinExact.agda` (`df1cbbc2880aa964d846916747324c800dd61e40`) importing the canonical `RecursiveRadixHypervoxel` owner rather than inventing a new sheaf. The source-written proofs are `fineAgreement` (parent/suffix equality implies identical joined address), `addressConsumerDescent` (any consumer of that exact fine address agrees), and `seamConsumerAgreement` (the original `CrossObjectJoin.interfaceCompatible` implies equality for any postcomposed joined consumer). These are **genuine transport laws conditional on given endpoint/overlap equalities**, but do not create those equalities or establish global analytic gluing.

This upgrades existing TH03/TH04 and PH03/PH04 *generic join* ingredients to SOURCE; instantiation for actual Mangoldt two-point and Bishop complex spectral histories, quantitative error propagation, and kernel acceptance remain explicitly OPEN. The earlier `TwinPickoverHistoryHypervoxelTransportExact` only preserved the entire original state definitionally; do not misrepresent that trivial readout as analytic factorisation.

CI/Agda compiler intentionally deferred at user's request; file has not received a kernel receipt. Preserve all downstream terminal requirements and source provenance.


## 31 October highest-alpha consumer descent implementation (1c7129e, 5e901f6)

`DASHI/Core/TwinPickoverHypervoxelAdmissibleJoinExact.agda` now defines `FineAddressFactorisation` with *nontrivial domain witness* `consumer h = decodeFine(joinAddress (coarse h) (suffix h))`. From this supplied **actual** factorLaw it constructs `retainedPairSufficient` using congruence over the paired observer, `canonicalResidualRepair` importing the original `ConsumerIndexedResidualRefinementExact.ResidualRepair`, and `retainedSuffixSeparatesConsumerCollision` using the original necessity theorem. Unlike the older `readRetained=readOriginal` tautology, these claims are conditional sound preservation and a genuine collision/separation obligation.

**Pivotal distinction:** `FineAddressFactorisation` is NOT automatically inhabited for either terminal consumer. True Mangoldt pair correlation and Bishop imaginary phase must each provide `factorLaw` and a decoding scalar with correct analytic meaning. A finite bit-address alone cannot encode arbitrary real analytic phase without retained mathematical residual. Next TP/PH implementation cut is to connect canonical actual-history/actual-scalar proof owners with those factorisation witnesses, not assume them.

**Status:** source committed, no holes or new axioms in the new statements; no Agda kernel run (user requested verification later). TH04/PH04 generic necessity/repair laws now source-written. Terminal TP-E, P9-D/E/F and RH zero exclusion remain open.


## Exact finite shift-two cyclic group-ring witness

Added `scripts/check_twin_prime_cyclic_group_ring_shift_two.py` (commit `a92de769fb5b0a205ea043171327d32bd9bf84ef`). Checks the precise `t^{-2}` coefficient of `F(t)F(t^{-1})` in an integer cyclic group ring, with zero padding and all signed mixed shell terms; uses prime-indicator windows, **not** `Lambda` log weights. `DASHI.Physics.Closure.NSTriadKNLuoFiniteFourierParsevalFromInversionExact` is an inspected existing rational finite-Fourier source. TP-B/T03 now have a committed finite-experiment witness, but no general Agda cyclic DFT proof; T09/T10 prime-distribution estimates remain OPEN. Script existence is not an execution receipt.


## Verified in-repo jet owner audit — 31 October 2026

Correction: **do not propose a new generic SSP-jet architecture**. The existing Agda surfaces include:
- `DASHI.Geometry.SSP369Ultrametric`: exact `Address d`, `PrefixMatch`, `agreementDepth`, `distance` and prefix soundness.
- `DASHI.Geometry.AdmissibilityJetSpec` + `DASHI.Geometry.Admissibility369UltrametricBridge`: jet-order/redundancy/field/invariant-generator discipline and a concrete 369 ultrametric depth bridge (explicitly not a physical identity).
- `DASHI.Biology.OrientedZeroJetTransitionExact`, imported by `ConsciousAccessRound5CompletionBoundary` beside `SignedSSPFRACTRANWeaveExact`, `SSPHyperfibreSymmetryTowerExact` and `TernaryHypercubeHyperfabricExact`.
- `DASHI.Analysis.RiemannQuarticSignedPoleJointHorizontalJetExact` and `RiemannQuarticSignedPoleBidiMarkedFourthExact`: the real joint horizontal/vertical quartic and even 0/2/4 marked moment owners; their sign/cancellation estimates remain explicitly open.
- `DASHI.Physics.YangMills.BalabanWilsonBivariateMarkedJetExact` and `BalabanWilsonMarkedClusterJetExact`: exact mixed coefficient bivariate jet and finite coefficient extraction, with actual analytic producer still separate.
- `DASHI.Moonshine.OggPrimeFourierWindingExact` from PR #1140: existing exact finite SSP/Ogg winding and C3 conjugation owner.

The ten-derivative SSP15 Eisenstein winding *rank experiment* in `scripts/check_ssp15_c3_winding_jet_rank.py` is a specific new exact finite certificate. Searches did not locate a pre-existing source file formalising precisely this ten-derivative **15×15 inverse**, so the narrow remaining task is a concrete kernel-checked adapter to the above existing jet owners, **not** 'integrate jet machinery' wholesale. Neither a bivariate Wilson jet nor a finite SSP rank proof automatically gives uniform arithmetic pair-correlation estimates.


## 31 October: universal finite SSP15 C3 ten-jet inverse certificate

New owner `scripts/check_ssp15_c3_winding_adjugate_inverse.py` (commit `662b4e4125d4eefb004da566f89ed60c4873041c`) implements the **all-input** rational inverse law, improving on a sample-vector test. For `M=M10[0:15,:]` (the first ten A-rows plus first five B-rows, in SSP prime order), exact determinant:
`det(M)=-68973567202690493145068231495208746474043983233237147979454873600000000 != 0`.
The universal identity `adj(M)*M=det(M)*I_15` yields `v = adj(M)*selectedJets/det(M)` for EVERY signed rational/integer 15-lane valuation history. The script also checks an explicit **nonnegative** nine-jet collision with tenth-jet separation. The finite C3 winding derivative transport now has a constructive algorithmic decoder rather than mere injective rank evidence. This does **not** prove an arbitrary analytic infinite Fourier transform, a uniform stable numerical inverse, or a prime-pair lower bound. Kernel formalisation of this integer matrix identity remains a narrow outstanding W04 task, not a missing generic SSP jet framework. No CI/compiler claimed.


## 31 October: ten-jet versus existing ten-state/rank-ten owner disambiguation

**Repository and PR search performed:** exact aliases `ten jet`, `10-jet`, `tenJet`, `TenJet`, `SSP15Jet`, `winding derivative`; SSP/rank owners; ten-jet PR title/body. No existing *identical* Agda theorem of the **15-lane, ten-derivative, full-rank rational Eisenstein winding inverse** was located by these searches. This is a limited negative search result, not a claim that the proof does not exist under another name or branch.

**Actual nearby owners inspected:**
- `DASHI.Moonshine.JInvariant369TenRankSeventeenHyperformalismExact`: **ten-state** completion 9+1, 5×2, rank indexing to 17, SSP signed-FRACTRAN fine fibre; 'ten' does not denote ten Fourier derivatives.
- `DASHI.Moonshine.JInvariant369C6TenRankWeightTwelveCrossPollinationExact`: same ten-state completion, distinct C6 reflection/phase structure, not the SSP15 jet inverse.
- `DASHI.Biology.SSP15JCoarseFineIntegratedExact`: actual per-prime nine-observer atlas, p=9q+r address, j-coarse/fine evaluation.
- `DASHI.Biology.SSP15NineObserverAtlasExact`: lane-specific observer distinctions; actual quotient semantics require specific projections.
- Previously indexed `SSP369Ultrametric`, `Admissibility369UltrametricBridge`, `OrientedZeroJetTransitionExact`, `OggPrimeFourierWindingExact` (#1140), RH quartic and YM bivariate jets.

**New minimal finite proof certificate:** `scripts/check_ssp15_c3_winding_modular_inverse.py` (commit `da059117d6ae062a8157316d56643418da143d08`) constructs the exact selected 15×15 `M10` submatrix and verifies `det(M) mod 101 = 98`. This independently implies `det(M) ≠ 0` over integers, hence rational full rank. The modular residue **does not itself reconstruct signed integer histories**; the existing exact rational adjugate formula supplies that. To kernel-check the narrow inverse, it suffices to compute a nonzero minor modulo 101 in the existing finite matrix owner then lift nonzero integer determinant and exact rational injectivity. Avoid a new generic jet algebra.

**Corrected next highest-alpha:** (1) import any *actual* existing finite modular-matrix determinant owner, (2) instantiate this concrete 15×15 and prove the residue 98, (3) lift to Q and prove the inverse, (4) signed SSP history/hyperfabric factor-through in the real observer, (5) return to genuine arithmetic/analytic terminal estimates. The code is source-written, no CI or kernel proof claimed. Do not collapse ten-state completion with ten derivative samples.


## 31 October Pareto correction: SSP ultrametric is the owner, not a missing generic ten-jet system

Per the existing `DASHI.Geometry.SSP369Ultrametric`, the relevant theorems already establish `distance-zero→equal`, prefix agreement/distance bounds and an ultrametric triangle law. `DASHI.Geometry.SSPJetExistingOwnerTransportExact` now contains actual source-written generic consumers `zeroDistanceConsumerAgreement` and `consumerDifferenceForcesPositiveResolution` (commit `0462d6cdcbc35404bb471ae1d11b2dbc71bce39d`). Thus full-address zero distance entails identical downstream consumer values; a coarse nonzero-radius ball does not entail sufficiency. This is a precise bridge to consumer-indexed refinement and makes ultrametric *resolution*, rather than abstract jet naming, the primary historical observer.

Independent local exact integer computation recomputed the same chosen 15×15 matrix determinant `-68973567202690493145068231495208746474043983233237147979454873600000000` and `det mod 101 = 98`. The Python modular verification source was committed separately earlier but its full command-line run is not claimed. The 10-derivative SSP15 full-rank consumer is a **narrow** finite specialization; it must not displace existing SSP369 ultrametric, `SSP15JCoarseFineIntegratedExact`, or oriented-zero / C3 winding owners.

**Next real proof cut:** (a) *actual original SSP15 signed-valuation history → address plus retained residual* factorisation, including 9-jet collision, (b) exact kernel-formal finite-matrix modular certificate and rational inverse, (c) consumer-specific genuine real arithmetic/Bishop phases. These are not yet completed by a generic zero-distance theorem. Attribution and no-ESD boundaries unchanged; no CI/kernel claimed.


## Faithful SSP ultrametric observer: max-cut status

New source `DASHI.Geometry.SSPJetExistingOwnerTransportExact` defines `FaithfulSSPAddress`, `faithfulAddressConsumerSufficient`, and `coarseCollisionRequiresAddressDistinction` by reusing canonical `SSP369Ultrametric` and `ConsumerIndexedResidualRefinementExact`. The theorem is conditional on an injective encoding of the original History; finite fixed-depth trits cannot automatically encode arbitrary unbounded integer histories or real Bishop phases. For such consumers retain residuals or variable depths. Source-written on PR #1408 (commits f753662b and 3e46cac8), not kernel checked. Specific bounded signed-SSP history instances, terminal estimates and verified ten-jet inverse remain open.


## 31 October actionable handoff: native signed SSP15 source, no duplicate jet system

`DASHI.Biology.SSP15SignedHistoryConsumerBidiExact` is now source-written over **existing** `SignedSSPFRACTRANWeaveExact.SSPValuation`. Its `encode` retains sign orientation and the original signed multiplicity as an explicit residual, `decodeEncode` preserves the original, `retainedObserverSufficient` yields all-consumer sufficiency, and `signCollisionForcesSignedResidual` pays the native consumer-collision necessity condition. It is lossless rather than minimal and does **not** pretend a finite address contains every unbounded magnitude. In parallel the existing `SSP369Ultrametric` remains the primary observer/refinement owner; the C3 ten-derivative matrix is a specialized finite certificate, **not** the original notion of jet.

**Practical verification and future-work entrypoint:** `Docs/roadmaps/SSP15_Ultrametric_Jet_Consumer_Handoff_20261031.md` contains source ordering, Python commands, Agda commands, the typecheck/safety boundary and precise remaining kernel/analytic cuts. This is a source-ready handoff, not an Agda-kernel-verified or terminal-conjecture-complete proof.


## Structural SSP15 10-jet theorem (Vandermonde max-cut; 31 October)

The previously introduced arbitrary 15x15 determinant computation is now supplemented by a **short all-input injectivity proof** committed as `scripts/check_ssp15_c3_vandermonde_structural_inverse.py` (commit `4eb11d1fbad5a7130957f21f88f5004d3927df45`). Define residue-group moments `G_r(k)=Σ_{p≡r mod3} v_p p^k`, so at the C3 point the two rational/Eisenstein jet components are `A_k=G_0(k)-G_2(k)`, `B_k=G_1(k)-G_2(k)`. The canonical SSP15 partitions into residue classes 0:{3}, 1:{7,13,19,31}, 2:{2,5,11,17,23,29,41,47,59,71}.

**Proof of 10-jet injectivity:** if `A_k=B_k=0` for k=0,…,9, then `G_0(k)=G_1(k)` for k=0,…,4. The corresponding signed weight on the five **distinct** nodes 3,7,13,19,31 has zero first five moments; the ordinary 5×5 Vandermonde determinant is nonzero, so those five weights vanish. Thus `G_2(k)=0` for k=0,…,9; the 10×10 Vandermonde matrix on the remaining ten distinct nodes is nonsingular, so all remaining weights vanish. This gives injectivity of the 10-jet map over Q (and Z), without requiring expansion of any 15×15 determinant. An independent selected-minor calculation gives `det ≡ 98 (mod 101)`.

**Optimality:** barycentric rational weights `w_p=1/∏_{q≠p}(p-q)` on the ten residue-2 nodes satisfy `Σ_p w_p p^k=0` for k=0,…,8 and `=1` for k=9 (Lagrange interpolation). Clear denominators and divide by the gcd to get a nonzero primitive integral nine-jet kernel. Split its signs into two nonnegative histories with identical nine-jet readouts and distinct tenth derivative. This exactly certifies minimal jet depth **10** among these equispaced derivative-observer prefixes. All exact arithmetic (including the barycentric vector and its tenth moment) has been independently recomputed locally.

**Kernel-proof remaining cut is now smaller:** re-use a proved generic Vandermonde distinct-nodes theorem or instantiate the two explicit five/ten Vandermonde determinants in Agda/Lean; verify the barycentric moment identity. No generic jet algebra needed; no postulates should be inserted. The source-written Python script is not itself an Agda kernel receipt.

**Terminal analytic wall not erased:** ten exact C3 derivatives recover finite SSP15 valuations only. They do not yield the missing unconditional all-prime shifted-correlation bound, Pickover giant-real-phase sign, or RH global zero-exclusion. Mathematical proof completion for these three targets is not currently established.


## 2026-10-31 analytic continuation: unconditional prime-power contamination estimate

Committed `scripts/check_twin_prime_prime_power_contamination_bound.py` (commit `921af0b023a7f10c9967dbad2cfde04f40b7a474`) with finite exact combinatorial cross-checks, plus the following mathematical argument. For `X>=4`, let `T(X)=sum_{2<=n<=X-2} Lambda(n)Lambda(n+2)` and `P(X)=sum_{n,n+2 prime and n+2<=X} log(n)log(n+2)`. Writing `Q(X)` for distinct proper prime powers `p^k<=X,k>=2`, nonnegativity of genuine von Mangoldt weights gives `0<=T(X)-P(X)<=2 Q(X) (log X)^2`. Each proper power can contaminate at most two shifted pairs (as left or right endpoint). Counting all *integer* bases gives `Q(X)<=sum_{k=2}^{floor(log_2 X)} floor(X^(1/k))<=floor(sqrt X)floor(log_2 X)`. Therefore `T(X)-P(X)=O(sqrt X (log X)^3)=o(X)` unconditionally. The only analytic inputs are the usual actual von Mangoldt definition and elementary logarithmic growth; the finite script checks representative incidence combinatorics and is not a proof of a new prime-gap lower bound. This shows that an eventual positive linear lower bound for the actual shifted Mangoldt sum immediately yields the same positive linear lower bound for prime-only weighted twins, but **does not itself provide that lower bound**. No synthetic positive pair correlation substituted.


## Actual Pickover analytic progress: exact sine interval certifier (2026-10-31)

Added `scripts/check_pickover_integer_sine_taylor_interval.py` (commit `2e286fd4bd093a43379aa7f98805c3ecec4b9b40`), a proof-producing **exact rational sign decision** for an integer n whenever its Taylor enclosure excludes zero. The kth enclosure is centered on `S_k=Σ_{j=0}^k (-1)^j n^(2j+1)/(2j+1)!` with rigorous radius `R_k=n^(2k+3)/(2k+3)!` by the full real Taylor remainder theorem (using the identically zero even Taylor term). In exact rational comparisons, `S_k−R_k>0` proves `sin n>0`, and `S_k+R_k<0` proves `sin n<0`. There is a termination proof for fixed nonzero integer `n`: `R_k→0`, `S_k→sin n`, and `sin n≠0` since `n=kπ` would contradict irrationality of π. This proves **decidability**, not tractability: with `n=99^(9999!)` naive Taylor at the unreduced argument is astronomically infeasible. The unsolved computational cut remains an effective certified argument reduction / fast sine phase enclosure for this actual huge integer. No claim that Pickover sign was computed.


## New analytic-work cut: Machin phase/winding enclosure and evidence boundaries

`scripts/check_pickover_machin_phase_interval.py` computes rational Machin pi intervals, an integer winding, rational reduced-phase interval and exact Taylor/Lipschitz sign enclosure. The actual phase sign is certified only when the interval excludes zero. Local exact-rational calculation confirms negative `sin(99)` with q=16. This is not a computational certificate for `sin(99^(9999!))` and does not remove the giant integer-bit/phase precision barrier.

External 2026 research reference to inspect (do not assume full RH): OpenAI `The Quasi-Riemann Hypothesis (alternate 11/12 proof)` (October 5, 2026) reports zero exclusion for Re(s)>11/12. Before reuse, validate its proof authority, exact theorem statement, and functional-equation transport; compare only to the existing `RiemannQuarticSignedPoleJointHorizontalJetExact` and corresponding zero-exclusion obligations. This reported region does not establish RH or the terminal joint-quartic sign estimate.

## 2026-10-31 MAX-CUT RECONCILIATION — exact remaining lemmas, acceptance, owners

This supersedes older vague “finish representation” notes. Status labels: **REUSE** = file inspected/owner present; **SOURCE** = code committed but not kernel-checked; **EXECUTED** = specific local exact calculation observed; **OPEN** = no adequate proof; **EXTERNAL-CLAIM** = requires independent manuscript verification. Neither source-writing nor finite testing proves a terminal analytic estimate.

| ID | Owner / existing donor | Exact theorem obligation (not just module name) | Acceptance criterion | Status |
|---|---|---|---|---|
| K01 | `SSP369Ultrametric`, `SSPJetExistingOwnerTransportExact` | Correct original jet/depth projection and zero-distance consumer sufficiency | Agda typecheck, safe-import closure honest; no metas/postulates | SOURCE (projection/pragma repaired `08459ff6`) |
| K02 | `SignedSSPFRACTRANWeaveExact`, `SSP15SignedHistoryConsumerBidiExact`, consumer-indexed residual | Exact faithful original signed valuation BIDI and sign-only collision necessity | Agda typecheck; every source consumer factors and genuine collision retained | SOURCE |
| K03 | `OggPrimeFourierWindingExact`, SSP15 scripts, finite matrix/Vandermonde owners | C3 ten-derivative 15-lane linear map injective over Q; nine jets not injective | Instantiated existing Vandermonde proof over five nodes {3,7,13,19,31} and ten nodes {2,5,11,17,23,29,41,47,59,71}; integral 9-jet collision; kernel check | Structural mathematical proof + Python SOURCE; kernel OPEN |
| K04 | `DepthTwoNonaryResidueFibreExact`, `ZetaIrrationalFibreCommutingSquareBidiExact`, `QuadraticIrrationalSignedApproximationFibreExact` | Compatible rational approximations with quantitative Bishop-real Cauchy modulus, actual same-object limit; finite stage square preserved by continuous zeta consumer | Constructed sequence, supplied modulus and continuous zeta realization, commuting diagrams verified on actual carrier | Generic SOURCE, analytic instantiation OPEN |
| K05 | `BishopMachinArctanConstructionExact`, `BishopMachinQuarterAngleBranchExact`, `JInvariantBishopTrigUnitPhaseExact` | Machin Bishop-real equals actual trigonometric π with correct branch and exact sine phase semantics | Prove tangent/addition and branch identification, full typecheck | REUSE + OPEN seam |
| P01 | `check_pickover_compressed_rational_phase_obstruction.py`, Bishop π / Fibonacci/SSP ultrametric owners | Exact compact N mod M for N=99^(9999!); **actual** reduced phase differs from rational surrogate by certified amount | Target-specific rigorous interval excludes zero on the actual sin N, end-to-end reproducible checker | Modular SOURCE; terminal OPEN |
| T01 | `PrimeCountingFunction`, `PrimeCountingAnalyticBridge`, `SixWheelSieveCountExact`, `FinitePrimeProductSieveExact`, dashifine/dashitest valuation benchmarks | Connect exact sieve verification and genuine von Mangoldt Λ(n)Λ(n+2) arithmetic, with no-wrap endpoint filter; do not promote a learned kernel predictor to exact sieve | Explicit producer equality and finite exact checker, typed kernel proof | REUSE + SOURCE + OPEN |
| T02 | `TwinPrimeActualPairSectionGluingExact`; prime-power bound script | Prove 0≤T(X)-P(X)=O(√X log³X) for actual Mangoldt, with exact powers/prime weights | Real analytic inequalities on same producer, not only finite script | Argument written; kernel OPEN |
| T03 | Actual shifted-prime Mangoldt producer, prime sieve and correlation | A new proven positive lower bound / infinitude criterion for gap exactly 2 | Genuine unconditional correlation lower bound implying infinitely many actual prime pairs | OPEN |
| R01 | OpenAI 2026-09-30 7/8 preprint; OpenAI 2026-10-05 11/12 preprint | Independently check each distinct manuscript theorem and dependencies (Hecke→Dirichlet→ζ), preserve source ownership | Auditable analytic source proof or formal port; named exact assumptions | EXTERNAL-CLAIM, proof audit OPEN |
| R02 | `RiemannXiSymmetryExact`, `RiemannReflectionOrbitDefectExact`, `RiemannQuasiRHXiSymmetryReuseExact` | Reuse actual critical reflection σ↦1−σ and identify right exclusion with left exclusion on the **same actual zero carrier** | Establish reflectedZero analytic closure, true zeta-coordinate realization, correct inequality and kernel check | Native rational geometry REUSE; new adapter SOURCE; analytic attachment OPEN |
| R03 | `RiemannBishopPositiveHeightSymmetryCutExact` | Separate ± ordinate symmetry t↦−t from left/right critical strip, and trivial zeros Re<0 | Prove same-object conjugation and signed-height witness, not conflated with σ−½ | REUSE, analytic contracts remain |
| R04 | `RiemannQuarticSignedPoleJointHorizontalJetExact`, G2 Clay terminal owners | Quantitative true same-object joint-remainder estimate and off-line defect exclusion α²=0, not merely α↦−α | New unconditional zero-exclusion on critical line, with actual completed ζ analytic semantics | OPEN |

**Cross-lane max-cut:** arithmetic or categorical sieves are structurally different; a typed interpretation preserving precomposition/pullback is required for Grothendieck-site covers. Fibonacci Cassini sign/defect and 369-27 pants charts are real finite donors, but neither by itself yields π winding nor an analytic zeta limit. C3 numerical matches do not establish Monster/Hecke same-object semantics. Attribution original math and dates; imported OpenAI claims remain externally owned; DASHI ownership limited to independently authored adapters and checked theorem code. Import-only ESD.

**Operator handoff:** `python scripts/check_ssp15_c3_vandermonde_structural_inverse.py`; `python scripts/check_ssp15_c3_winding_modular_inverse.py`; `python scripts/check_pickover_machin_phase_interval.py 99`; then Agda with repository's agda-lib environment on `DASHI/Geometry/SSPJetExistingOwnerTransportExact.agda`, `DASHI/Biology/SSP15SignedHistoryConsumerBidiExact.agda`, `DASHI/Analysis/ZetaIrrationalFibreCommutingSquareBidiExact.agda`, and `DASHI/Analysis/RiemannQuasiRHXiSymmetryReuseExact.agda`. These commands are instructions, not executed receipts. No CI claimed.


## 31 October follow-on: exact prime-counting across time-indexed fibre gluing

Commit `589a27760c2a56c51a0c2ca4573cb09938e57687` extends `DASHI/Analysis/ZetaIrrationalFibreCommutingSquareBidiExact.agda` with `primeCountStableAcrossOneStep` and `primeCountStableAcrossTwoSteps`. Both consume the canonical `PrimeCountingFunction.primeCountLE` and a *supplied* coherent retained Nat readout; the proofs are `cong` and `trans` along actual stage-equality witnesses, not a synthetic prime theorem. This closes exact one/two-stage equality of the finite prime-count consumer **conditional on the history's coherence**, while the essential genuinely varying approximants/real zeta limit, analytic PNT estimates, actual shifted-prime correlation, RH zero exclusion and Pickover irrational-winding sign still need their own substantive mathematical producers. Source-written only; kernel check remains outstanding by the user's no-CI instruction.


## 2026-10-31 finite/convergence cut: genuine nonconstant rational Machin history

New executable exact-arithmetic `scripts/check_machin_fractran_cauchy_history.py` (commit `f22a521c`) is a mathematical producer beyond merely prescribing a limit attachment. Define for n>=1

`q_n=16 Σ_{j<n} (-1)^j/((2j+1)5^(2j+1)) -4 Σ_{j<n} (-1)^j/((2j+1)239^(2j+1))`.

The alternating-series theorem yields `|q_n-π|<=e_n`, where `e_n=16/((2n+1)5^(2n+1))+4/((2n+1)239^(2n+1))<=4/25^n`. Thus `|q_j-q_k|<=8/25^n` for all `j,k>=n`; this is a **quantified Cauchy modulus**. `q_(n+1)-q_n = (-1)^n/(2n+1)*(16/5^(2n+1)-4/239^(2n+1)) !=0`, so this history is explicitly nonconstant. Each `q_n` is rational and therefore has a finite signed prime-valuation encoding, including residual primes not in the SSP15 dictionary. Local exact rational checks for eight stages and prime reconstruction for the first two stages were executed; the committed script checks 24 stages without expensive factorisation. The convergence proof relies on the classical Machin identity and alternating remainder theorem; the existing Bishop Machin construction supplies the intended real producer. **Still required:** proof in the actual Agda/Bishop setoid that these rational stages map into that canonical Bishop real and satisfy its located-Cauchy modulus, and a continuity/analytic producer attaching a zeta consumer. Exact exponent/rational-history compression does not decide the real Pickover sign.

The terminal analytic obligations (actual twin-prime correlation, RH zero exclusion, and the requested Pickover sine sign) remain explicitly OPEN; this finite construction should be used as a real constructive donor, not as a replacement analytic theorem.


## 2026-10-31 terminal analysis follow-on: explicit true-carrier results

The detailed proof ledger and attribution is `Docs/papers/TwinRH_PickoverTerminalAnalyticActualCertificates20261031.md` (commit `917a503d4cf4905deef482c05ecfe065a3b2217f`). Updated source/acceptance matrix:

| ID | Exact mathematical achievement or remaining theorem | Evidence / owner | Status |
|---|---|---|---|
| TA1 | **Unconditional actual twin correlation upper:** T(X)=Σ_{n≤X-2}Λ(n)Λ(n+2)=O(X), from Brun's established π₂(X)=O(X/log²X) plus explicit o(X) proper-prime-power correction. This is an UPPER estimate, not T(X)≥cX. | Brun original theorem (external established math); existing Mangoldt and prime-power arithmetic owners | Mathematical derivation valid, Agda analytic port OPEN |
| TA2 | **Explicit unconditional elementary two-point estimate** π₂(X)≤z+X(1/2)∏_{3≤p≤z}(1-2/p)+2·3^{π(z)-1}, with X≥z+2. Gives explicit true Mangoldt upper via prime-power correction. | `scripts/check_twin_prime_two_point_crt_sieve_estimate.py`, CRT/exclusion/inclusion-exclusion proof and independent small finite checks | SOURCE + local exact checks; proof Agda OPEN |
| TA3 | **Positive shifted-pair lower** that forces infinitely many pairs of exact gap 2. Distinguish unconditional upper from required lower and classical parity barrier. | True Λ(n)Λ(n+2) producer and existing six-wheel/Brun/Maynard donors | OPEN |
| RA1 | Actual completed xi nontrivial-zero reflection via functional equation and conjugation; requires explicit zero-value interpretation, not a rational-coordinate stand-in. | `DASHI/Analysis/RiemannQuasiRHActualXiZeroReflectionExact.agda` (`7bdbd9eb`), native `RiemannAnalyticSubstrate` | SOURCE; Agda kernel check OPEN |
| RA2 | External seven-eighths result as imported proof with correct original authorship: `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` in `openai/math/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean`, depends on `Detector/FinalAssemblyUnconditional.lean`; comparator theorem contains intentional placeholder `sorry`. October 5 11/12 companion distinct and weaker. | OpenAI source Lean `lean/docs/003.md`, `ComparatorChallenges/QuasiRiemannHypothesis.json`; original paper 2026-09-30 | EXTERNAL Lean source; independent semantic import and Agda port OPEN |
| RA3 | **Terminal RH:** exclude all nontrivial off-line zeros remaining in 1/2<Re(s)≤7/8 and their reflected partners by an actual analytic estimate; do not equate 7/8 and 1/2. | Existing G2/G3 true joint quartic producer | OPEN |
| PA1 | Exact rational Machin π enclosure, modular `pow(99,m,2a)`, plus rigorously bounded drift `((b·99^m/a)+2)δ` and Taylor/Lipschitz real sine interval. Fail closed when not sign-separated. | `scripts/check_pickover_certified_compressed_modular_phase.py` (`296b6317`, target mode `9fcd03d2`), independent rational checks m=1,2,3,4,6,8 | SOURCE + local exact arithmetic; target OPEN |
| PA2 | **Terminal Pickover:** a compact *special-argument* proof/certificate with rational bounds of the actual sin(99^(9999!)) excluding zero; naive π approximation needs O(99^m) phase sensitivity and cannot be faked by finite modular residue. | Bishop Machin, Bishop trig, SSP/FRACTRAN retained history | OPEN |

Precise cross-lane acceptance remains: golden Agda proof without new postulates/metas, exact mathematical semantic bridge from external Lean to original zeta, and honest executed verification receipts. No CI was requested or run. Do not mark OPEN terminal proofs as complete because of a finite test or a source-written file.


## 2026-10-31 concrete infinite fixed-sieve failure certificate

New `scripts/check_twin_prime_finite_screen_infinite_composite_witnesses.py` (commit `0c9e12545cbc535c4f5c38ea1568df44abc8c354`) constructs a proof-bearing **infinite family of composite false positives** for each fixed finite set F of primes containing 2 and 3. Set W=∏_{p∈F}p, choose distinct P,Q>max(F), and CRT-solve n≡−1 (mod W), n≡0 (mod P), n≡−2 (mod Q). All n=n0+tWPQ for t≥1 survive every p∈F while n and n+2 are both composite. For full canonical SSP15 F, one locally independently checked example is n=13050476785267491359789, with 73|n and 79|(n+2), yet no SSP15 prime divides either endpoint. This is a theorem for arbitrary fixed F, with one test example, and completely rules out *fixed-screen survivor counting alone* as a twin-infinitude proof. It does NOT rule out genuinely dynamic or parity-breaking prime-distribution mathematics. The remaining lemma T03 must inject genuinely global arithmetic beyond any fixed finite chart.

New actual xi zero-carrier adapter, explicit Brun upper estimate, and Pickover fail-closed phase test are detailed above. The original terminal goals remain RH at 1/2, positive gap-two lower correlation, and the true giant sine sign, none of which is accomplished by this finite-sieve no-go.

## 31 October — max-cut T0/M16: actual certified count-jump ⇔ cofinal window ⇔ twin-infinitude (source-written)

The cofinal *arithmetic* endpoint is now bidirectional using **original proof-bearing Nat prime certificates**, not wheel/SSP survivors:

- `TwinPrimeConditionalUnboundedFromCountJumpsExact.certifiedCountJumpsFromTwinInfinitude` proves the previously absent reverse direction. For each cutoff `N`, invoke an assumed `TwinPrimesInfinitelyOften` witness at `suc (suc N)` to exclude indices 0 and 1, then instantiate `TwinPrimeCertifiedCountJumpBidiExact.twinCountChangesAtCertifiedTwin`. The proof carries `N ≤ p` through original Nat-order transitivity.
- `twinInfinitudeGivesUnboundedCertifiedCountJumps` and `certifiedCountJumpInfinitudeBidi` complete the two logical directions with the existing `twinPrimesUnboundedIfCountJumps`.
- `TwinPrimeStrongWeakMaxCutBidiExact.cofinalWindowToCertifiedCountJumps` / `certifiedCountJumpsToCofinalWindow` identify the third exact form using the original `TwinPrimeMangoldtNonzeroPrimeSumWitnessExact.TwinInInterval` carrier.
- Both owners are imported by the three canonical TOE roots; original finite prime counter and prime predicate are not duplicated.

**T13/M16 logical equivalences: SOURCE-WRITTEN, kernel PENDING.** The real weighted `P(X)` ↔ finite count-growth consumer still needs its genuine positive ordered-real log weights and bounded-window comparison. **T10 / CT15: OPEN MATHEMATICALLY**; there is no constructed cofinal count jump, no new lower bound, no twin-prime theorem. Do not mistake an equivalence with a proof of either direction's premise.

**T02 quantitative normalization:** prior 31 October arithmetic work already sharpened the proper-power envelope to `B(X)=(⌊√X⌋−1)+max(⌊log₂ X⌋−2,0)(⌊X^(1/3)⌋−1)`, `0≤E(X)≤2 B(X)(log X)^2=O(√X log² X)` for the true classical Λ producer. Older O(√X log³ X) is a valid weaker bound, not the best currently documented envelope. The real ordered-scalar Agda proof remains open, and neither bound yields positive `P(X)`.

**Next Pareto cuts:** (1) exact-head kernel check on the new BIDI and original imported count owner; (2) ordered-real `ΛΛ`/prime-only weight comparison and actual `P(X)`↔count-growth bridge with endpoint-safe finite intervals; (3) genuinely new unbounded prime-specific positive correlation or cofinal nonzero prime-only increments; (4) separately K04/K05 Bishop Machin setoid limit and zeta consumer, R04/R10 actual off-line exclusion, and P03/P10 huge-phase sign certificate. External source attribution and ESD import-only boundary unchanged.

## 31 October — K04 source-root re-audit and finite-time closure (post-T0 follow-on)

The source-first audit corrected a formerly broad handoff: **the Bishop-real Machin construction and convergence are NOT missing foundations**. In `DASHI.Foundations.BishopMachinArctanConstructionExact`, the original `atanSignedTerm`, `atanSeriesConvergent`, `bishopAtanHalfBallConverges` and `bishopMachinPi` already give bona fide Bishop-series and a constructed real. `DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact` already instantiates the actual two Machin arctangent convergence witnesses and uses that same `bishopMachinPi` in the Round11 complex transcendental owner. The rational tangent arithmetic and constructive branch window already have separate original owners `BishopMachinRationalTangentAlgebraExact`, `BishopMachinQuarterAngleBranchExact`, `BishopMachinPiRationalWindowExact`. `DASHI.Interop.BishopMachinPiLeanSemanticReceiptExact` tracks the source-written Lean classical-π semantic theorem, explicitly WITHOUT a kernel/same-object cross-prover receipt. Do not reimplement these owners or count source flags as kernel evidence.

**Concrete new source-written finite-stage work** in `ZetaIrrationalFibreCommutingSquareBidiExact`: `stageIndexAfter`, `readoutStableAcrossFiniteSteps`, `consumerStableAcrossFiniteSteps`, `primeCountStableAcrossFiniteSteps`. Induction composes the original adjacent-stage equality for arbitrary finite steps and arbitrary retained-Nat consumer, not just 1/2 steps. This proves *only* compatible integer readouts; nonconstant rational approximants, Bishop Cauchy convergence and analytic zeta values remain separate.

**Dependency repair** in `QuadraticIrrationalSignedApproximationFibreExact`: fixed malformed nested constructor signatures for `SqrtThreeHalfDefect` and `GoldenRatioDefect` (each direction now ends in its correctly indexed datatype). That is source syntax repair of an imported dependency, not a new irrational limit theorem. No ESD changes.

**K04 now decomposes into EXACT missing lemmas:**
- K04a, SOURCE mathematical / Agda OPEN: `q_n` from `check_machin_fractran_cauchy_history.py` equals the chosen canonical rational partial sums `16·SeriesOf(atanSignedTerm bishopOneFifth)−4·SeriesOf(atanSignedTerm bishopOneTwoHundredThirtyNinth)` under the existing Bishop rational embedding, with truncation and endpoint convention fixed.
- K04b, OPEN: apply the existing two genuine Bishop arctangent convergence theorems plus continuity of the linear combination to obtain a proof-bearing `ConvergesTo` for that *same* `q_n`, including explicit `4/25^n` modulus, not a newly invented `Real`/limit interface.
- K04c, OPEN: prove actual source/target signed FRACTRAN encoding/decoding for each `q_n` with residual primes outside SSP15; no constant retained-Nat-readout hypothesis substitutes for changing rational stages.
- K04d, OPEN: prove analytic zeta continuity and consumer commuting square on the actual named complex/meromorphic domain (including pole exclusion), with same-object equality.
- K05, OPEN: establish trigonometric classical-π characterization in **Agda** through the original branch and tangent/sine/cosine owners; the independently source-written Lean theorem is not automatically an Agda proof.

**Evidence:** all newly added Agda source is committed but not kernel checked; the older individual Bishop modules report own prior proof levels, not a check of this branch. The only global terminal analytic hard gates remain T10, R10, P10.

## 31 October — K04a concrete source stage (after canonical Bishop reuse)

New `DASHI.Analysis.BishopMachinSignedFiniteHistoryExact` imports the ORIGINAL `Machin.atanSignedTerm` at the real embedded (1/5) and (1/239), and `BishopFiniteSeriesDifferenceExact.finiteSeriesDifference`. It gives `machinFifthWeightedTerm` (16×), `machin239WeightedTerm` (4×), `machinSignedTerm` (their signed difference), `machinSignedPartialStage` (original Bishop `SeriesOf`), and the for-all-n theorem `machinSignedPartialIsOriginalDifference`. This is the actual **finite Bishop signed-series history** and exact decomposition, not another abstract carrier or a proof of `q_n` rational embedding.

**K04a refined:** actual source series and finite signed decomposition SOURCE-WRITTEN; still OPEN the rational `q_n` ↔ Bishop `SeriesOf` embedding with coefficient/denominator and finite-sum normalization. **K04b:** explicit quantitative Cauchy modulus plus same-object convergent series limit OPEN even though both original per-atan Bishop convergence proofs already exist. **K04c/K04d/K05:** residual-complete signed valuation, actual meromorphic `ζ` continuity, and Agda trigonometric/classical π identification OPEN. No synthetic source witness or third-party Lean receipt substituted. The new leaf is imported into all three canonical TOE roots, kernel pending, no CI.

## 2026-11-01 K04a–K05 direct implementation and acceptance audit (PR #1408)

This section supersedes the earlier *K04a only finite signed stage* handoff. The following names are actual committed Agda source definitions, not pseudocode and **not Agda-kernel receipts**. No CI was run. External mathematical authors, pinned Bishop library, canonical 15-prime SSP owner and original repo proofs retain independent attribution.

| ID | Exact Agda owner / actual new source | Source-level progress | Exact OPEN acceptance |
|---|---|---|---|
| **K04a** | `Analysis/BishopMachinRationalStageEmbeddingExact.agda`: `qPow`, `qSign`, `qAtanTerm`, `qMachinTerm`, `qMachinStage`, `qAtanTermEmbeds`, `qMachinStageEmbedsAsOriginalBishopPartial` | Real recurrence on `ℚᵘ`, all-stage Bishop-`≃` proof via original `⋆-distrib` laws, preserving signed coefficient and `SeriesOf` prefix. The previous `BishopMachinSignedFiniteHistoryExact` remains the canonical unscaled/weighted Bishop-term consumer. | **Kernel-check** both files with pinned Bishop; verify no incorrect conflation of `ℚᵘ.≃`, Bishop setoid equivalence, and Agda `≡`. |
| **K04b1** | `BishopMachinSignedFiniteHistoryExact`: `leftScaledSeriesConverges`, `machinFifthPartialConverges`, `machin239PartialConverges`, `machinSignedPartialConvergesToOriginalMachinPi`; `BishopMachinRationalStageEmbeddingExact.rationalMachinStagesConvergeToOriginalMachinPi` | Actual *same Bishop-sequence carrier* limit theorem terms, assembled by source-owned `Series.xₙyₙ→x₀y₀`, `Series.xₙ+yₙ→x₀+y₀`, `Series.-xₙ→-x₀`, `Series.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀`; no new convergence axiom. | **Kernel-check** actual dependent import closure. |
| **K04b2** | `scripts/check_machin_fractran_cauchy_history.py`; existing `BishopArctanHalfBallInterlacingExact` and `BalabanBishopAlternatingBracketFromMonotoneLimitsExact` | Classical alternating-remainder argument: `e_n=16/((2n+1)5^(2n+1))+4/((2n+1)239^(2n+1))`. Universally for n≥0, `e_n ≤ (16/5+4/239)/25^n = (3844/1195)/25^n < 4/25^n`. For j,k≥n, `|q_j-q_k|≤8/25^n`. Exact finite rational checks extended; the inequalities are mathematically elementary, but not Agda-kernel proofs. | **OPEN Agda:** use original alternating first-omitted bracket and Bishop real order to prove `|⋆q_n−bishopMachinPi|≤⋆e_n≤⋆(4/25^n)` with actual source limit/partial stage, and strict/nonconstant same-object stages if required. |
| **K04c1** | `BishopMachinPrimeFactorStageExact.agda`: `factoriseOrZero`, `factorListAllPrime`, `decodeFactorisationCorrect`, `canonicalStage` | Actual `q_n` signed rational numerator/denominator; proof-carrying **arbitrary-prime** factor lists via existing Hecke/stdlib `factorise`; explicit zero case, sign retained, reconstruction. | Kernel-check definition of `↥`, `↧ₙ`, `NonZero (suc n)` instance and original factorisation proof signatures; separate numerator sign remains part of complete codec. |
| **K04c2** | `BishopMachinSSP15PrimeDictionarySplitExact.agda`: `isSSP15Prime`, `CertifiedSplit`, `splitCertified`, `stageSSP15Codec`, `numeratorProductBidi`, `denominatorProductBidi` | Partitions certified prime-factor multiplicity lists via ORIGINAL `canonicalSSPPrimes`; proves total source-product equality and prime certificates on each branch, retains negative denominator codes. Genuine adversarial q1=`3804/1195` has 317 and 239 outside SSP15. | Kernel-check split proof; if a single compact source/codec BIDI is required, add actual equality from signed rational to full decoded product and zero-case handling, not an abstract isomorphism. |
| **K04d1** | `BishopMachinZetaRegularHalfPlaneExact.agda`: `stagePoint`, `limitPoint`, `realPartConverges`, `imaginaryPartConverges`, `zetaAtStage`, `originalZetaEqualsDirichletAtStage`, `originalZetaEqualsDirichletAtLimit` | True `RiemannBishopComplexAnalyticCarrierExact` source complex points and the original `CompletedRiemannZeta.zeta`; conditional same-original-function half-plane equality reusing the original agreement theorem. **n=0 is NOT in σ>1.** | **OPEN** prove `Re(q_n)>1` for n≥1 using actual Bishop rational order/interlacing (and `3<pi_M` for the limit), plus a concrete implemented `AnalyticSubstrate` (not only an abstract input). |
| **K04d2** | Actual `CompletedRiemannZeta` and `ZetaHalfPlaneLayer` sources | The abstract analytic carrier names `Meromorphic` and half-plane Dirichlet/Euler identities but does not expose continuity/uniform convergence as a proof. | **OPEN** local uniform convergence of actual Dirichlet series on a compact σ>1 neighborhood of π; zeta continuity there on actual Bishop complex/setoid values; prove `ζ(⋆q_n)→ζ(pi_M)` and quantitative propagation without assuming it as a free record field. |
| **K05a** | `BishopMachinConfiguredTrigPiExact.agda`: `configuredMachinPiIsOriginal`, `configuredFourTimesQuarterIsPi`, `configuredPiComplexReal`, `configuredPiComplexImaginaryZero` | Exact original Round11 sine/cosine dataSet names the **same original constructed Machin real**; original quarter-angle branch and exact rational tangent witness retained. | Agda kernel verification; this is configured identity, NOT independent characterization of geometric pi. |
| **K05b** | Original `BishopMachinQuarterAngleBranchExact`, `BishopMachinRationalTangentAlgebraExact`, `BishopPowerSeriesElementaryBridgeExact`, `BishopExponentialCauchyProductExact` | Genuine Bishop sine/cosine series and finite branch/tangent algebra available, plus source-written Lean `eval_machinPi_eq_real_pi` as an independent mathematical comparison. | **OPEN in Agda:** true sine/cosine addition or tangent semantics for the same Bishop functions; quarter-angle `sin θ≃cos θ`, correct constructive branch; `sin_B(pi_M)≃0` and `cos_B(pi_M)≃−1`; an independent positive-period/π characterization and same-object equality. Never promote the Lean source to an Agda kernel receipt. |

**Pareto revised:** Focus typechecking **K04a/K04b1/K04c1–2/K04d1/K05a** before opening new wrappers. For mathematical completion, attack **K04b2 Bishop error order**, **K04d2 actual Dirichlet-series uniform convergence**, and **K05b Bishop sine/cosine/tangent characterisation** directly. The three cross-program terminal gates T10/R10/P10 remain independent and OPEN. Original ESD import-only rule preserved.

### 2026-11-01 K04b2 direct Bishop-order partial closure (after K04a–K05 audit)

New source-written `DASHI.Analysis.BishopMachinQuantitativeOmittedTailExact` imports and **instantiates** the original actual `BishopArctanHalfBallInterlacingExact.atanInterlacing`, `BalabanBishopAlternatingBracketFromMonotoneLimitsExact.bishopAlternatingBracketsFromInterlacing`, and `BalabanBishopSetoidAlternatingFirstOmittedExact.bishopAlternatingBracketsGiveFirstOmittedTail`. Generic `actualArctanEvenRemainderBound` and `actualArctanOddRemainderBound` are the true Bishop `_≤_` inequalities between the original limit and `Sequence.SeriesOf` even/odd partial prefixes, bounded by first omitted `Machin.atanMagnitudeTerm`. Four concrete specializations cover BOTH genuine 1/5 and 1/239 Machin series. No new real carrier, invented alternating axiom, or synthetic source identity.

**K04b2 precise last mile (still OPEN):** (i) prove quantitative `atanMagnitudeTerm (⋆(1/d)) n ≃ ⋆(1/((2n+1)d^(2n+1)))` from original power/embedding laws; (ii) combine the 16/4 signed two-series tail inequalities into `|⋆q_n−bishopMachinPi|≤⋆e_n` with actual Bishop order and no sign coercion; (iii) prove `e_n≤(3844/1195)/25^n<4/25^n` as all-n `ℚᵘ` inequalities and transport through original `p≤q⇒p⋆≤q⋆`; (iv) prove 2-ended Cauchy interval estimate at j,k≥n from true triangle inequality. This is now a SMALL explicit analytic-order cut, not a missing general alternating-remainder theorem. All newly introduced source still needs Agda kernel checking.

### 2026-11-01 K04b2 magnitude conversion now source-written

The same `BishopMachinQuantitativeOmittedTailExact` now additionally imports K04a `Rational.qPowEmbeds`, the ORIGINAL `BishopConcreteSineCosineInterlacingExact.powNonnegative`, `RealProperties.⋆-distrib-*` and the source `Machin.inverseOddRational`. `atanMagnitudeIsEmbeddedRational` proves for every certified nonnegative rational input x and every k that original `atanMagnitudeTerm (⋆x) k` is Bishop-setoid-equal to `⋆(inverseOddRational k * qPow x (2k+1))`. Specialized `fifthFirstOmittedEqualsEmbeddedRational` and `twoHundredThirtyNineFirstOmittedEqualsEmbeddedRational` pay the original 5/239 input side conditions without an additional assumption. **All source-written, Agda kernel pending.**

**K04b2 revised last exact steps:** (a) scale and combine both first-omitted signed Bishop bounds into `|⋆q_n−pi_M|≤⋆e_n`, for both parities, with correct source-real subtraction/absolute-value transports; (b) verify rational first-omitted formula reduces to `1/((2n+1)d^(2n+1))` and all-index `e_n≤(3844/1195)/25^n<4/25^n` by stdlib exact-rational order; (c) derive all j,k≥n Cauchy from Bishop triangle inequality; (d) run pinned Agda compiler. Do not re-open the already constructed generic alternating or nonnegative-rational power bridge.

### 2026-11-01 K04c3 zero-sensitive numeric reconstruction source completed

`BishopMachinSSP15PrimeDictionarySplitExact` now source-writes `factorisationZeroOrProduct` **over the actual indexed `Raw.FactorisationOrZero` datatype**, using stdlib `Fact.isFactorisation` in its forward direction, and `numeratorMagnitudeZeroOrReconstructs` / `denominatorMagnitudeZeroOrReconstructs` composition with the genuine dictionary/residual product equality. The disjunction is mathematically exact: factorization of zero cannot claim empty product 1. The original signed numerator remains in `Raw.CertifiedRationalStage`; no missing SSP15 prime is silently dropped. **Agda kernel pending**; source-level case proof does not independently establish numerical denominator nonzeroness or all fields of an explicit rational codec inverse.

## 2026-11-01 second K04/K05 max-cut: true combined Bishop error, universal Nat envelope, eventual half-plane, quartic phase (source-level)

The following changes were committed to the existing PR #1408 branch and are **source-written Agda candidates, not kernel-verified**. The exact Fraction regression was separately executed locally for n=0..100, bounded-window j/k Cauchy comparisons, including q1=3804/1195; it does not replace Agda proof. Attribution: original Machin (1706), Bishop & Bridges (1985, DOI 10.1007/978-3-642-61667-9), Murray (2022, arXiv:2205.08354), pinned viktorcsimma/bishop, original DASHI/YM alternating-series and tangent proof owners, stdlib Nat and prime-factorisation, independent Lean source (NOT an imported Agda proof). The original ESD is untouched.

### Newly exact theorem owners

| ID | Source file / exact symbols | Proven *within the written candidate*, pending golden Agda check |
| --- | --- | --- |
| **K04b2a** | `DASHI/Analysis/BishopMachinCombinedRemainderBoundExact.agda`: `sourcePartialAgreement`, `weightedErrorIdentity`, `evenArctanAbsoluteError`, `oddArctanAbsoluteError`, `weightedAbsoluteTriangle` | Relates ORIGINAL `bishopMachinPi − Signed.machinSignedPartialStage` to signed 16/4 weighted arctangent source errors, and combines the actual Bishop absolute/order bounds without new abstract analytic axioms. |
| **K04b2b** | Same: `machinEvenRationalError`, `machinOddRationalError`, `parityComplete`, `machinRationalAllStagesRemainder` | Every natural stage (including q0) satisfies the **actual Bishop real-order first-omitted estimate** `|pi_M−⋆q_n| ≤ 16*m5(n)+4*m239(n)`; total Nat parity bridge is explicit, no implicit even-stage restriction. |
| **K04b2c** | `DASHI/Analysis/BishopMachinGeometricEnvelopeNatExact.agda`: `pow25BelowPow57121`, `combinedNumeratorBelowBase`, `machinGeometricEnvelopeCrossMultiplied` | All-`n` Nat arithmetic cross-product `3824·57121^n+20·25^n ≤(2n+1)·4780·57121^n`. This is the exact normalized numerator comparison for the classical `e_n≤4/25^n` rational remainder. Not yet the same Bishop-order comparison. |
| **K04d1** | `DASHI/Analysis/BishopMachinEventualHalfPlaneExact.agda`: `bishopConvergenceEventuallyAbove`, `machinRationalStagesEventuallyAboveThree` | Generic, genuine Bishop convergence ⇒ eventual preservation of any strict lower bound. From original source's `threeBelowMachinPi`, eventual `3<⋆q_n` (a stronger eventual statement than merely `1<⋆q_n`). It does not prove the original analytic substrate's *opaque* `realPartGreaterThanOne` predicate. |
| **K05a repair** | Existing `DASHI/Foundations/BishopMachinQuarterAngleBranchExact.agda`: `fourthPositive`, `quarterTimesThreeEquivalentThreeFourths`, `quarterTimesTwentyTwoSeventhsEquivalentElevenFourteenths`, corrected `threeFourthsBelowQuarter`, `quarterBelowElevenFourteenths` | Replaces **invalid attempted strict comparisons of equal rational endpoints** with positive quarter scaling of the original `3<pi_M<22/7` and true rational setoid normalization. Previous source may not have kernel-checked despite a `machineChecked` label; source labels are not verification receipts. |
| **K05b algebra** | `DASHI/Analysis/BishopMachinQuarterPhaseQuadruplicationAlgebraExact.agda`: `sinDoubleIsOneAtEqualUnitPhase`, `cosDoubleIsZeroAtEqualPhase`, `sinFourfoldIsZeroAtEqualUnitPhase`, `cosFourfoldIsMinusOneAtEqualUnitPhase`, `quarterUnitPhaseGivesFourfoldEndpoint` | Proves the fourfold sine/cosine **polynomials** equal 0/−1 from actual same-Round11 quarter-angle `sin θ≃cos θ` and unit-phase Pythagoras. These two source *analytic* predicates are still required. |
| **K05c setoid transfer** | Same: `quarterSemanticBridgeToActualMachinPi` | Transport through original `fourTimesQuarterIsMachinPi` and original concrete Round11 sine/cosine congruence proves `sin_B(pi_M)≃0` and `cos_B(pi_M)≃−1` **conditional on explicitly stated original analytic quarter-angle and fourfold identities**. Not an unconditional K05 result or a geometric π uniqueness theorem. |

### Exact terminal acceptance cuts after these implementations

- **K04b2-DENOM**: prove that original `Machin.inverseOddRational n * Rational.qPow (1/d) (2n+1)` is rational-setoid equal to `1/((2n+1)d^{2n+1})`, for d=5,239, with positive denominators. Normalize `16*m5+4*m239` to embedded `e_n`, then use `machinGeometricEnvelopeCrossMultiplied` via `Data.Rational.Unnormalised.*≤*` and `RealProperties.p≤q⇒p⋆≤q⋆`, proving the full desired `|⋆q_n−pi_M|≤⋆(4/25^n)`. Finish `|q_j−q_k|≤8/25^n` by original Bishop triangle and monotone power bounds. This is still OPEN in Agda.
- **K04d-HALFPLANE**: identify `RiemannAnalyticSubstrate.ZetaHalfPlaneLayer.realPartGreaterThanOne` on the actual `BishopComplex` point with `Bishop.1ℝ < BishopComplex.re point`. Currently this generic predicate is opaque and an actual `CompletedRiemannZeta` realization has not been shown. The new eventual bound avoids requiring the q0 stage or every finite prefix in the domain.
- **K04d-CONTINUITY**: construct true complex Dirichlet terms n^{-s} with Bishop exp/log, local compact `Re(s)>1` uniformly convergent tails (including branch, function/complex setoid semantics), and genuine zeta continuity there; then derive `ζ(stagePoint n)→ζ(limitPoint)` using the existing original analytic zeta and the proven sequence convergence. Naming `Meromorphic` is not a continuity proof. This is the largest unclosed **same-object analytic construction**, not a finite stage identity.
- **K05-TRIG**: prove actual sine/cosine series addition or fourfold identities on Round11's concrete series, plus `quarterSin≈quarterCos` from the original rational tangent parameter =1 with the nonzero-cosine/domain/branch proof, and actual unit Pythagoras at that quarter. Apply `quarterSemanticBridgeToActualMachinPi`, then prove independent classical-geometric/trigonometric pi uniqueness if required. **Not solved** by the polynomial quadruplication alone; source-written Lean equality is NOT an Agda proof.
- **Verification:** Agda goldens for all new files + all three TOE roots; inspect imports, overloaded mixfix operators, bound direction, elaboration, normalization and termination. Source review and local Python are not kernel acceptance. No CI was run, at user request.

**Pareto next cut:** 1. Kernel-check and repair **K04b2a–c**; 2. finish K04b2-DENOM; 3. K04d-HALFPLANE and actual Dirichlet-series continuity; 4. K05-TRIG analytic quadruple/branch + independent π identification. Keep T10 twin-prime lower bound, R10 RH middle zero exclusion, P10 giant-sine sign OPEN and separate.

## 2026-11-01 third max-cut: direct Bishop 4/25^n and 8/25^n, eventual actual zeta domain (NEWEST STATUS)

**Latest source owner:** `DASHI/Analysis/BishopMachinGeometricBishopRateExact.agda`. It reuses the ORIGINAL `BishopMachinArctanConstructionExact.atanMagnitudeSuccessorBelowSquare`, `BishopMachinCombinedRemainderBoundExact.machinRationalAllStagesRemainder`, `BishopMachinPiRationalWindowExact`, and the Bishop/Murray pinned `RealProperties`. Every item below is committed as **source-written Agda proof, kernel verification NOT performed**, no postulate introduced.

**K04b (source proof now written end-to-end, pending Agda compiler):**

1. `one239BelowOne5Rational` and `abs239BelowAbs5` derive the true native rational and Bishop input comparison. `square5EqualsOneOver25` and `square239BelowOneOver25` prove the 1/25 upper bound on both actual Bishop input squares; the denominator 239 and missing SSP residual are not discarded.
2. `magnitudeStepAtOneOver25`, `geometricMagnitudeBound`, `fifthGeometricMagnitudeBound`, `twoHundredThirtyNineGeometricMagnitudeBound`, `weightedMagnitudeBishopGeometric` prove actual Bishop magnitude decay at rate `pow (⋆(1/25)) n` for both original 5/239 arctangents, using source nonnegative multiplication and the original 16/4 factors.
3. `atanMagnitudeZeroIsInput` identifies each source magnitude at index 0; `weightedInitialRational = 16/5 + 4/239 = 3844/1195`, `weightedInitialRationalBelowFour` consumes the stdlib's exact rational inequality decision, and `weightedInitialBishopBelowFour` transports this to the same Bishop carrier. This supplies the previously missing numerical coefficient.
4. **Desired actual same-object K04b estimate:** `machinBishopFourOver25Pow` is source-written for **every Nat n**, including n=0:
   `|bishopMachinPi - ⋆(qMachinStage n)| ≤ pow (⋆(1/25)) n * ⋆4`.
   `machinBishopFourOver25RationalStage` additionally identifies the exact rational-stage power `⋆(Rational.qPow (1/25) n)`.
5. `rateSuccessorBelow`, `rateBelowOne`, `rateAntitone` prove nonincreasing native Bishop powers. `machinTwoIndexBishopError` applies the original Bishop triangle inequality. **Desired two-index target:** `machinBishopEightOver25PowCauchy` is source-written for every n,j,k with n≤j, n≤k:
   `|⋆q_j-⋆q_k| ≤ ⋆8 * pow(⋆(1/25)) n`.
6. Historical K04b Nat denominator route `BishopMachinGeometricEnvelopeNatExact` remains an independent exact check and is no longer the sole proposed Bishop-order bridge. Exact Python Fraction bounded regression now tests 64 stages and 475 Cauchy pairs. **No Python check substitutes for kernel validation.**

**K04d partial advance:** `BishopMachinZetaRegularHalfPlaneExact.AtActualBishopCarrier` now proves `oneStrictlyBelowThree` via exact rational order and `actualStageRealPartEventuallyAboveOne` from actual `machinRationalStagesEventuallyAboveThree`. `actualStageEventuallyInOriginalZetaDomain` and `actualZetaEqualsOriginalDirichletEventually` then reuse the actual original completed-zeta equality, **conditional on the original opaque analytic field's domain predicate being implied by true Bishop Re>1**. This is an explicit assumption at the true field boundary, **NOT** a proof that the generic `ZetaHalfPlaneLayer` has been concretely realized. Existing `Meromorphic` still supplies no continuity. OPEN exact analytic construction: genuine Bishop-complex `n^{-s}` exp/log, locally uniform σ>1 Dirichlet convergence, original completed-zeta setoid continuity and `ζ(q_n)→ζ(pi_M)`. The original generic constructed-real `PowerSeriesTranscendentals` lacks a proved same-object Bishop equivalence; `LegacyDASHIRealEquivalenceAuthorityExact` is explicitly an uninhabited equality/equivalence interface, not a proof. Do not coerce it.

**K05 remains mathematically open:** `BishopMachinQuarterPhaseQuadruplicationAlgebraExact` source-writes ring quadruplication and the conditional authentic Round11 endpoint. The original Bishop exponential Cauchy product is true and reusable, but it does **not** automatically furnish the required same-carrier sine/cosine addition identities or prove `quarterCos≈quarterSin` from the rational tangent arithmetic. Required source proofs: construct signed factorial sine/cosine convolution/Cauchy product at actual Bishop stage; show sine/cosine double/quadruple-angle on actual Round11 terms, Pythagorean unit phase and tangent/branch identification; conclude `sin_B(pi_M)=0` and `cos_B(pi_M)=−1`, then prove independent geometric-period π uniqueness. Independently written Lean is not an Agda kernel receipt.

**Mandatory acceptance:** run the authoritative pinned Agda Track A on all new K04/K05 leaves and canonical TOE root, repair type/termination/qualified-import/solver issues, then independently verify source ownership and kernel receipts. The extensive new source is **not yet verified by Agda**, and no CI was run as requested. T10 prime-pair lower bound, R10 RH zero exclusion and P10 giant-sine sign remain independent and OPEN; do not claim those from K04b.

## 2026-11-01 fourth max-cut — source-owner reuse, actual K04d epsilon-delta consumer, K05 shared trig weld

This tranche continues existing PR #1408. The new modules are **source-written Agda candidates only; no Agda kernel invocation or CI**. Native exact-arithmetic Python assertions have independently executed for 64 Machin stages and 475 two-index Cauchy pairs. Source attribution is preserved: John Machin (1706), Riemann (1859), Bishop/Bridges (1985, DOI 10.1007/978-3-642-61667-9), Murray (2022, arXiv:2205.08354), original pinned Csimma/Murray Bishop library, DLMF §4.21.12, and original DASHI proof/weld authors. ESD is not modified.

**K04d1 — actual epsilon-delta to true zeta limit.** New `DASHI/Analysis/BishopMachinZetaSequentialContinuityReducerExact.agda` defines `BishopContinuousAt f point` as a genuine modulus-quantified Bishop real epsilon-delta property (a positive δ for every positive ε and all nearby x). `bishopContinuousImageConverges` SOURCE-PROVES the sequential-continuity theorem via original `Sequence.fast-ε-from-convergence`, `Sequence.con*`, and strict-to-nonstrict Bishop order. The actual source `AtActualCompletedZeta` then names precisely the existing `CompletedRiemannZeta.zeta` evaluated on the original `bishop-complex x 0ℝ` line, with the original `BishopMachinRationalStageEmbeddingExact.qMachinStage` and original `bishopMachinPi`. It gives `realComponentConvergesFromActualContinuity` and `imagComponentConvergesFromActualContinuity` for the true original zeta evaluations — **conditional only on actual epsilon-delta continuity of each specified component**. These do not assert that the abstract `Meromorphic` evidence entails continuity. Completed-zeta realization, local σ>1 exponent/logarithm Dirichlet tails, and component continuity remain the genuine **K04d terminal open gate**.

**K05 — reuse shared object weld, not duplicate trigonometric source axioms.** New `DASHI/Analysis/BishopMachinQuarterSharedTrigWeldBidiExact.agda` imports the EXISTING `BishopRound11ClassicalTrigObjectWeldExact.Round11ClassicalTrigObjectWeld` and `compileRound11Pythagorean`. Its `AtExistingRound11Weld.quarterUnitFromOriginalSharedWeld` transports the actual Round11 sine²+cosine²=1 to the EXACT `BishopMachinQuarterPhaseQuadruplicationAlgebraExact` quarter values (commuted order). Its `quarterWeldedTrigEndpoint` invokes the already source-written actual Bishop sine(π_M)=0/cosine(π_M)=−1 reduction, now **without requiring an independent new Pythagorean premise**. The weld itself remains an EXPLICIT input: its source-backed DLMF theorem does not automatically establish classical/Bishop same-object equality. Remaining genuine **K05 terminal open gate**: inhabit the same-object trig weld, prove the Machin quarter sine=cosine using original rational tangent plus branch, derive the actual Bishop sine/cosine addition/fourfold equations, and independently prove positive-period/geometric π uniqueness. **No arbitrary source-worded Pythagorean receipt is promoted.**

**K04b correction:** The previous geometric error/Cauchy program remains source-written only. Current owners are `BishopMachinCombinedRemainderBoundExact` and `BishopMachinGeometricBishopRateExact`. The source-based full 4/25^n and two-index 8/25^n claims have a successful exact-rational bounded regression, but NOT Agda kernel acceptance. The priority local gate is the golden typecheck and repair of all transitive leaves, including original square contraction, coefficient zero-step normalization, qualified rational order, and two-index ≤ transport.

**Exact Pareto remaining:** (1) pinned Agda kernel test/repair of K04a–b and the newly imported all-TOE roots; (2) concrete original Bishop log/exp/Dirichlet n^(−s) realization and local uniform σ>1 continuity for K04d, then apply the new explicit epsilon-delta-to-sequential theorem; (3) genuine Bishop sine/cosine Cauchy-product addition + shared classical object weld + correct quarter tangent/branch/π uniqueness for K05. T10, R10, P10 remain unrelated OPEN terminals.


## 2026-11-02 K04b/K04d/K05 commuting-square implementation (source-written)

- **K04b-SQUARE**: `DASHI/Analysis/BishopMachinQuantitativeZetaCommutingSquareExact.agda` now composes the **actual** rational `qMachinStage n` with the source `machinSignedPartialStage n`, genuine Bishop complex stage `Z.stagePoint n`, and the original completed-zeta function. The `finiteStageSquare` is proved on the original real setoid; `stageSquareRate` reuses the independently source-written `machinBishopFourOver25Pow` (4/25^n), and `stageSquareCauchy` reuses the original 8/25^n two-index bound for *all* n≤j,k. `stagePointRealConverges` is the actual Bishop sequence theorem. **K04b-DENOM** (separate Nat cross-product to unnormalised rational denominators) remains an *independent proof path*, not needed logically to obtain the same bound if the stronger Bishop rate source kernel-checks. Do not call the older denominator transport completed merely because the target estimate has another owner.
- **K04d-SQUARE**: The same module proves `limitInsideRealHalfPlane` (`1 < Re(pi_M + 0i)`) from the actual Machin window. It obtains eventual `completed ζ(q_n)=halfPlane ζ(q_n)`, at-limit equality, per-coordinate pointwise commutation, and convergence of the **original completed-zeta stage evaluations** from its `AnalyticSameObjectGate`. The gate names three obligations: the real-part domain predicate bridge, actual real-component epsilon-delta continuity, and actual imaginary-component epsilon-delta continuity. The earlier continuous-image reducer discharges the convergence *if* those premises hold. No proof of the predicate bridge or completed-zeta continuity is claimed.
- **K04d-CONTINUITY still OPEN**: Construct a genuine Bishop-complex exp/log version of n^(−s), branch-controlled log for each positive natural n, and uniformly convergent Dirichlet tails on every compact subregion Re(s)≥1+δ. Identify the corresponding concrete function with the ORIGINAL `ZetaHalfPlaneLayer.zetaHalfPlane` and `CompletedRiemannZeta.zeta` on that domain. Establish the two actual epsilon-delta component continuity theorems; then inhabit `AnalyticSameObjectGate`. Opaque record fields `Meromorphic`, `DirichletSeriesConverges`, `ZetaEqualsDirichletSeries` alone do not discharge these theorems.
- **K05 DOUBLE→QUAD**: `BishopMachinQuarterPhaseQuadruplicationAlgebraExact.Round11BishopDoubleAngle` now expresses *one* sine/cosine double-angle law on the original Round11 series. `actualSineFourfoldFromDouble`, `actualCosineFourfoldFromDouble` prove the two original fourfold identities from that uniform law by same-series congruence, polynomial congruence and `2(2θ)≃4θ`; `actualMachinTrigEndpointFromDoubleAngle` composes these with the previous endpoint. `BishopMachinQuarterSharedTrigWeldBidiExact.quarterWeldedTrigEndpointFromDoubleAngle` additionally consumes the **same original explicit** classical/Bishop Pythagorean weld. This reduces formerly independent fourfold identity premises to **one coupled double-angle law**. It does not construct the double-angle law or the weld.
- **K05-TRIG still OPEN**: Prove native signed-factorial sine/cosine Cauchy products to inhabit `Round11BishopDoubleAngle`; prove actual quarter-angle `cos θ≃sin θ` from Machin's rational tangent subtraction using nonzero cosine and interval/branch control; inhabit the original same-object classical/Bishop trig weld without source-claim promotion; prove independent geometric positive-period π uniqueness. The source-written endpoint is not an unconditional `sin_B(pi_M)=0` theorem.

**Status:** all above are authored GitHub Agda **source candidates** attached to all three canonical TOE roots. No pinned Agda kernel check, local compilation or CI was performed; source/readback is not acceptance. T10, R10 and P10 terminal conjecture cuts remain OPEN. Sources: Machin (1706), Riemann (1859), Bishop/Bridges (1985), Murray (2022), original pinned Bishop library and original DASHI owners.


## 2026-11-02 K04d Dirichlet reuse max-cut (source-written, not kernel-accepted)

**Correction to proposed standalone Dirichlet implementation:** this repository already has the exact constructive Basel comparison compiler. Reuse `DASHI/Mathematics/Automorphic/EllipticDirichletBaselMajorantExact.baselDominatedDirichletSeriesConvergent`, which directly consumes original `DASHI/Foundations/BishopBaselReciprocalSquareConvergenceExact.baselSeriesConvergent` and pinned `Sequence.proposition-3-5`. No second convergence/completeness authority may be added.

**NEW K04d-BASEL owner:** `DASHI/Analysis/BishopRiemannDirichletBaselSameObjectExact.agda`, with a literal original `BishopComplex`-valued `Nat` Dirichlet term function, `BishopDirichletBaselMajorantAt` (per-component eventually `|term|≤1/(n+1)^2`), `realDirichletConvergent`, `imagDirichletConvergent`, `dirichletValue` (native Bishop `Sequence.lim`), and `dirichletPartialConverges` (actual constructive coordinatewise convergence). It also exhibits a **real, source-owned integer-two Basel fibre** `baselComplexTerm`, `baselComplexPartial`, `baselIntegerTwoComplexConverges`. This integer-two series is NOT automatically the abstract analytic substrate's ζ(2), nor ζ(π_M). The model uses the exact original complex carrier, not the legacy ConstructedOrderedCompleteReal.

**NEW K04d-ORIGINAL AGREEMENT:** `OriginalHalfPlaneDirichletAgreement` names the exact termwise/model-identification and actual *value* setoid equality with the original half-plane function. `AtOriginalCompletedZeta.originalCompletedZeta{Real,Imag}AgreesWithDirichlet` proves the two paths commute under the supplied original source domain predicate and genuine value agreement. It does **not** replace the opaque `ZetaEqualsDirichletSeries` field with a trivial boolean/Set or declare source claims proved.

**SAME-OBJECT CONSUMER:** `DASHI/Analysis/BishopMachinQuantitativeZetaCommutingSquareExact` now imports this owner. `originalCompletedZeta{Real,Imag}EqualsSummedDirichletAtStage` and `...AtLimit` are exact specializations to the original Machin rational stages and actual Machin π; the original completed ζ is evaluated, not a synthetic zeta symbol. All three TOE roots import the new owner and the existing square.

### Source-owner / Pareto register (search-first; do not conflate)

| Original source | Actual proven reuse | Unpaid semantic or quantitative gate |
| --- | --- | --- |
| `Foundations/BishopBaselReciprocalSquareConvergenceExact` | Native Bishop convergence of Σ(n+1)^(-2), source `baselTerm`, `baselLimit` | No generic complex logarithm |
| `Automorphic/EllipticDirichletBaselMajorantExact` | Any real term family dominated eventually by Basel has convergent original `Sequence.SeriesOf` | No global coefficient domination for original elliptic L; no zeta n^(-s) term constructor |
| `Foundations/BishopNatRealReciprocalSquareBaselExact` | Identifies inverse of native positive Nat real squared with **same literal Basel term** | Only exponent 2; cannot substitute π_M without exponentiation/log |
| `Foundations/BishopExponentialCauchyProductExact` | Actual Bishop **real** exp additivity and exp(x)exp(−x)=1 | Still need same-carrier Bishop **complex** exp/log and positive-natural log |
| `Mathematics/NumberTheory/FiniteMultiplicativeDirichletExact` | Exact finite factor/Dirichlet monomial multiplicativity | Its local analytic weights are supplied, not canonical n^(−s) |
| `Mathematics/NumberTheory/FiniteEulerProductExact` | Finite semiring Euler-product expansion | Infinite zeta Euler product and same-object convergence remain unpaid |
| `Analysis/AbelZeta` | Algebraic Abel/eta sample values at nonregular integers | Not zeta in Re(s)>1; cannot establish Dirichlet convergence at π_M |
| `Analysis/ConstructiveSeries`, `PowerSeriesTranscendentals`, `PrincipalComplexLog`, `RiemannConstructedComplexExpAddReductionExact` | Useful **constructed-real** convergence/complex exp/log interfaces and reductions | `LegacyDASHIRealEquivalenceAuthorityExact` has no inhabited same-object carrier bridge; do not silently coerce |
| `Physics/YangMills/BalabanPositiveRGDirichletGeometryExact` and PDE Dirichlet boundaries | Boundary-value/spectral geometry, useful in their own PDE lanes | **Not** complex Dirichlet L-series or Riemann ζ |

### Remaining exact source/kernel obligations

- **K04d-TERM:** On the original `BishopComplex`, construct `log(n+1)` for every positive Nat and the *actual* `exp(−s log(n+1))` with branch and multiplication laws. Prove its coordinate majorant ≤ `Basel.baselTerm` for all points of a neighborhood of π_M, using Re(π_M)>3. A concrete pointwise all-n bound is required to invoke `BishopDirichletBaselMajorantAt`; no fabricated witnesses.
- **K04d-UNIFORM:** Prove a single local uniform tail estimate on an open neighborhood with Re(s)>1 (or the stronger Re(s)>3 neighborhood of π_M), then derive the actual completed-zeta component continuity by uniform limits of continuous terms. Pointwise Basel comparison alone does **not** prove continuity, and the endpoint's `AnalyticSameObjectGate` therefore remains uninhabited.
- **K04d-SAME:** Prove the source's `ZetaHalfPlaneLayer.realPartGreaterThanOne` matches genuine `Re(s)>1`, and construct `OriginalHalfPlaneDirichletAgreement` for the exact n^(−s) value with the original `CompletedRiemannZeta.zeta`. Then the existing actual Machin square yields ζ(q_n)→ζ(π_M).
- **K04b:** Original 4/25^n and 8/25^n same-object bounds exist as source-written Agda, but all transitive imports require pinned golden Agda kernel test; independent Nat denominator normalization is still owed if retaining that proof route.
- **K05:** Need original Round11 sine/cosine signed-factorial addition/double-angle, quarter rational tangent+branch, inhabited classical/Bishop weld, and uniquely characterized trig π; finite polynomial quadruplication is not an unconditional analytic theorem.

**Verification:** new files/bridges and TOE imports are source-written and read-back from GitHub only; no Agda kernel execution or CI. T10, R10 and P10 remain OPEN. The original source and repository authors retain distinct attribution.


**Further 2026-11-02 finite true-fibre closure:** `BishopRiemannDirichletBaselSameObjectExact` now constructs an *actual* `BishopDirichletBaselMajorantAt` instance for the original Basel integer-two terms (real component `baselTerm`, imaginary component zero), using `Basel.absoluteBaselTerm` and `Basel.baselTermNonnegative`. `baselCompiledRealLimitIsOriginal` and `baselCompiledImagLimitIsZero` use the source's `Sequence.uniqueness-of-limits` to identify the newly compiled sum with the **original Basel limit and zero**, not a new free limit. This closes the concrete integer-two comparison-to-original-limit square as Agda *source*, kernel verification still pending. It does **not** prove the original abstract `CompletedRiemannZeta.zeta` agrees at s=2 or provide n^(−π_M).


## 2026-11-02 K04d exp/log source-reuse recut (newest)

**K04d-COMPLEX-REP closed in source, kernel pending:** `DASHI/Analysis/BishopRiemannAnalyticSetoidExpReuseExact.agda` proves literal inverse conversions between the already-existing `BishopSetoidComplexExact.BishopComplex` and `RiemannBishopComplexAnalyticCarrierExact.BishopComplex`, including definitionally equal zero, one, Cartesian addition, multiplication, negation and conjugation. It reuses original `BishopSetoidComplexExact.expC` as `bishopAnalyticComplexExp` on the genuine Riemann-Bishop carrier with exact real/imag coordinates and original exponential setoid congruence. **Do not** add a second complex exp implementation; do not confuse this with inhabited generic `AnalyticSubstrate.Function`.

**K04d-EXP-TERM constructed in source, kernel pending:** `DASHI/Analysis/BishopRiemannDirichletExponentialTermExact.agda` defines the literal `bishopNegativeSLn` with real/imaginary components `−Re(s)·logNat(n)`, `−Im(s)·logNat(n)`, and `bishopDirichletExponentialTerm` via that original Bishop complex exp; both real and imaginary coordinate identities reduce by `refl` to source Bishop exp, cos, sin. It composes with the original Dirichlet/Basel comparison to prove actual coordinatewise convergence when the literal all-index Basel majorant is supplied. The new `natLogArgument k = (k+1)/(k+2)` is the exact rational input for `log(k+2)=−log(1−(k+1)/(k+2))`. `natLogViaOriginalNegativeLog` uses the pre-existing **Bishop negative-log-one-minus series** at each such rational point, with zero at `log 1`; `natLogSuccessorHasOriginalSeriesConvergence` reuses the original Bishop convergence theorem. The necessary original unit-interval membership is explicit; mere convergence does not identify exp(log m) with m.

**Exact remaining K04d max-cut after maximal reuse:** (1) prove all-native `InOpenUnitInterval` membership of `natLogArgument k` for the configured original Round11 dataset; (2) prove this literal original Bishop negative-log candidate is a positive-Nat logarithm with `Exp.bishopExp (natLogViaOriginalNegativeLog T inside n) ≃ natReal(n+1)` and the source exp/log injectivity/monotonic laws; (3) derive `|Re/Im(exp(−s log(n+1)))| ≤ Basel.baselTerm n` for the genuine σ≥2 neighborhood (Machin π>3); (4) establish a uniform local n-tail modulus, original half-plane domain and **true original** zeta value agreement, giving real/imag continuity and inhabiting the earlier `AnalyticSameObjectGate`; (5) run pinned Agda golden kernel on all imports. The legacy `InverseLogarithmFromExponential` and `EMLPositiveRealAnalyticPackage` are informative but apply to **other/axiomatic** real carriers and need a genuine weld before reuse. The legacy `RealElementaryFunctionsCanonicalInstanceExact` explicitly declares `postulate`s and cannot discharge a native Bishop proof.

K04b Nat-denominator-route kernel verification, K05 native trig addition/quarter/uniqueness and T10/R10/P10 are independent gates still OPEN. Source attribution retained.


**Newest explicit K04d source consumer:** `BishopMachinQuantitativeZetaCommutingSquareExact.AtOriginalCompletedZeta.sourceExpDirichletTerms` specializes the original-completed-zeta commuting square to the **literal** original Bishop setoid complex exp, using the actual Bishop negative-log-one-minus finite input `natLogArgument k`. `originalCompletedZetaMatchesSourceExpAtStage` and `...AtLimit` now give BOTH original complex coordinates for this specific constructed term source, subject to exact configured unit-interval membership, original half-plane agreement, and the earlier analytic domain/continuity witness at the limit. These are source-written reductions, **not** evidence that the original analytic `ZetaHalfPlaneLayer` has been inhabited or that actual same-object ζ continuity is proved.


## 2026-11-02 K04d Bishop-Dirichlet proof/coherence max-cut

**Source commits:** `dade5e6b1de7d8c4e7a8f5d88eb8b6167c204c12` and
`5d31292146f630b37403ee8db420cdb26c6dd46a` on PR #1408.

**Reuse-first search:** `BishopBaselReciprocalSquareConvergenceExact`,
`EllipticDirichletBaselMajorantExact`,
`BishopNatRealReciprocalSquareBaselExact`,
`BishopFiniteSeriesExtensionalityExact`,
`BishopExponentialSeriesConvergenceExact`,
`BishopExponentialCauchyProductExact`,
`BishopExponentialNonnegativeMonotoneExact`,
`BishopRiemannDirichletExponentialTermExact`,
`BishopRiemannDirichletBaselSameObjectExact`,
`BishopMachinQuantitativeZetaCommutingSquareExact`,
`BishopMachinQuarterPhaseQuadruplicationAlgebraExact` and
`BishopMachinQuarterSharedTrigWeldBidiExact`.
Preserve these original theorem/code owners and historical Dirichlet,
Riemann, Machin, Bishop/Bridges and Murray attribution.

**New actual Bishop proof terms, source-written (Agda unchecked):**

- `dirichletRealValueIndependentOfMajorant` and
  `dirichletImagValueIndependentOfMajorant`: two Basel comparison
  witnesses for the *same* original real/imaginary term series yield
  equivalent Bishop limits by `Sequence.uniqueness-of-limits`.
  The `dirichletValueIndependentOfMajorant` pair is the complex
  proof-witness coherence square.
- `dirichletValuesRespectTermwiseEquality`: given two actual complex
  term families at the **same** original Bishop analytic argument,
  pointwise Bishop setoid equivalence in both coordinates, and each
  side's proven Basel domination, reuse the original
  `BishopFiniteSeriesExtensionalityExact.termwiseEquivalentSeriesHaveEquivalentLimits`
  to identify their two infinite-series values. It does *not*
  assert the missing termwise `exp(-s log(n+1)) = (n+1)^(-s)`
  theorem or value agreement with the original opaque analytic zeta
  function.

**Exact outstanding cut, without pretending that a conditional field is a proof:**

1. **K04d-LOG-INTERVAL:** `BishopPowerSeriesElementaryBridgeExact.InOpenUnitInterval`
   is a configurable predicate in the original Round11
   `BishopElementaryPowerSeriesData`, not definitionally the pair of
   Bishop inequalities. Prove the indexed rational argument
   `(n+1)/(n+2)` lies strictly between 0 and 1 **and** supply a
   verified bridge from those order proofs into this particular
   configured `InOpenUnitInterval` field. A mere inequality does not
   inhabit the field.
2. **K04d-EXP-LOG:** Prove on the *original* Bishop power-series
   functions that `exp_B(log_B(n+1)) ≃ n+1`, including zero/one
   indexing, branch, positivity, and exponential additivity. Reuse
   `BishopExponentialCauchyProductExact.bishopExpAdd` and the
   already source-owned positive/nonnegative order facts.
3. **K04d-TERM-DOMINATION:** Identify the actual configured
   exponential terms with the intended Dirichlet coefficients and
   prove the all-index `1/(n+1)^2` bound in a uniform neighborhood
   where `Re(s)>2`. The existing pointwise Basel comparison is
   proved; a supplied `BishopDirichletBaselMajorantAt` field is
   not a proof that these exponential terms satisfy it.
4. **K04d-UNIFORM/CONTINUITY:** Prove one neighborhood-wide tail
   modulus and termwise continuity for these same source terms;
   infer continuity of the concrete summed function. Finally prove
   same-object agreement with
   `ZetaHalfPlaneLayer.zetaHalfPlane` and transport through the
   actual `CompletedRiemannZeta.agreesWithHalfPlane` field.
   Pointwise convergence or the word `Meromorphic` cannot replace
   these arguments.
5. **K04b-DENOM:** The direct original-Bishop `4/25^n`
   rate and `8/25^n` two-index Cauchy estimate are source-written
   in `BishopMachinGeometricBishopRateExact`. Keep the separate
   unnormalised rational cross-product-to-Bishop-order denominator
   certificate open until the literal denominator-normalization and
   positivity proofs are accepted by the pinned Agda environment.
6. **K05-TRIG:** Derive the actual Round11 sine/cosine addition law
   from signed-factorial Cauchy products. Its single double-angle
   consequence feeds the existing quadruplication square. Separately
   prove the actual quarter-angle `sin_B=cos_B` from Machin's
   rational tangent calculation with correct branch control, then
   independent trigonometric pi uniqueness. The current endpoints
   consume explicit hypotheses, not completed trigonometric proofs.
7. **KERNEL:** Source readback and no-hole text inspection do not
   establish typechecking. Independently typecheck the focused
   K04/K05 import root using the repo's pinned golden Agda/Bishop
   environment. Resolve errors and attach exact theorem/commit/checker
   receipts before promoting any new status to `KERNEL`.

**Further K04d exp/log reuse (commit `37375de6af5b40eeff9b9d318180be6dcce3247e`):**
`BishopRiemannDirichletExponentialTermExact` now constructs
`negativeExponentialAtNatLogIsCanonicalReciprocal` and
`negativeExponentialAtNatLogIsEmbeddedReciprocal`.
The former combines the existing
`BishopExponentialCauchyProductExact.bishopExpTimesNegativeIsOne`
with `BishopInverseSquareProductExact.inverseFromCancellation` and
`BishopNatRealPositiveExact.natRealSuccessorStrictlyPositive`.
The latter uses
`BishopNatRealReciprocalSquareBaselExact.natRealInverseIsEmbeddedReciprocal`.
Thus the selected source value
`exp_B(-log_B(n+1)) ≃ (n+1)⁻¹` is now formally *reduced*
to the single precise hypothesis `exp_B(log_B(n+1)) ≃ n+1`.
It is not supplied as an unconditional theorem; the original
power-series logarithm inverse, rational configured interval witness,
and all-index/sigma-neighborhood majorant remain OPEN.

**Verification:** GitHub writes and exact-path readback are receipts
for source contents only. The current execution container lacks an
`agda` executable and the pinned vendored Bishop checkout; therefore
there is no actual golden kernel acceptance in this tranche.

**Acceptance state:** the two new convergence coherence results are
`SOURCE`; all seven terminal K04b/K04d/K05 obligations above
remain `OPEN` wherever they require independent new mathematics
or an actual kernel check. RH, twin-prime infinitude and giant-angle
Pickover sign remain unrelated terminal `OPEN` gates.


## 2026-11-02 K04d rational interval and exponent-two follow-on

**Source commits:** `fdfbaa0144e650a161a5a0ed13fb413b012e055b`,
`f6ec49f3674bb64c67a4b2f69e82a0745b0182a8`,
`cdfba07ca02a4d5c749703e9df5144303f32b4e7`,
`cd84bc2a665364b331c5f09393766df17e1d1ce6`,
`a6567975415756490fd29b05a999958dd113cd73`.

Reuse path: original `BishopMachinArctanConstructionExact` and
`BishopMachinPiRationalWindowExact` for constructive Machin history;
`BishopExponentialCauchyProductExact.bishopExpAdd`,
`BishopExponentialPositiveOrderExact.bishopExpZero`,
`BishopInverseSquareProductExact.inverseFromCancellation`,
`BishopNatRealReciprocalSquareBaselExact`,
`BishopBaselReciprocalSquareConvergenceExact` and
`BishopFiniteSeriesExtensionalityExact` for the Dirichlet analytic series.

**Source-written new exact lemma cuts** in
`BishopRiemannDirichletExponentialTermExact.agda`:

- `natLogArgumentPositiveRational` and
  `natLogArgumentBelowOneRational` prove the all-index strictly
  positive unnormalised rational
  `0 < (n+1)/(n+2) < 1`. The corresponding
  `natLogArgumentPositiveBishop` and
  `natLogArgumentBelowOneBishop` transport both inequalities to
  the original Bishop reals.
- `configuredNatLogArgumentsInside` consumes the *one remaining
  actual configured predicate bridge*, mapping these strict Bishop
  inequalities into the Round11 data field
  `InOpenUnitInterval`. This field was user-configurable, so the
  lemma must NOT claim it is definitionally the order interval.
- `originalNatLogAtOneExpIsOne` closes the first Nat coefficient
  from `log_B(1)=0` (by construction) and the independent original
  `bishopExpZero`. Thus
  `originalNatLogInverseFromPositiveSuccessors` reduces the entire
  Nat-log inverse to genuine positive-successor instances.
- `negativeDoubleNatLogExponentialIsBasel` and
  `negativeTwoNatLogExponentialIsBasel` compile the actual
  original exponential Cauchy-product law and inverse-square
  embedding into
  `exp_B(-2 logNat(n)) ≃ Basel.baselTerm(n)`, conditional only on
  `exp_B(logNat(n)) ≃ n+1`.
- `originalSeriesNatLogAtTwoIsBasel` specializes that statement
  to the *same convergent Bishop -log(1-x) series* already used in
  the original completed-zeta commuting-square candidate.

**Remaining precise analytic cut:**

1. Instantiate the configured unit-interval predicate for the
   selected Round11 instance using the now proven Bishop order bounds.
2. Supply the original Bishop `exp_B(-log(1-x))` inverse theorem
   at all positive-successor arguments. The n=0 base is paid.
3. Identify the complex exponential at real `s=2` with its
   real `exp_B(-2 logNat(n))` coefficient, including the original
   Bishop sine/cosine at zero and correct index.
4. Prove a whole-neighborhood coefficient domination (not just
   equality at `s=2`), a **uniform** Basel-tail modulus
   and continuity, and same-object equality with
   `CompletedRiemannZeta.zeta` via the original half-plane record.
5. K05 still needs one real Round11 signed-factorial addition theorem,
   the actual quarter-angle tangent/branch identity and trigonometric
   pi uniqueness. K04b-DENOM's separate unnormalised denominator
   route is still pending despite the already source-written direct
   Bishop `4/25^n` and `8/25^n` results.
6. **Kernel verification** remains unperformed: this environment has
   no pinned Agda/bishop execution checkout or compiler. No source
   commit is represented as an accepted Agda elaboration.

**Evidence:** SOURCE-WRITTEN; GitHub readback and a limited exact
rational arithmetic regression are not a proof of kernel acceptance.
Nothing here establishes full RH, twin-prime infinitude or the Pickover
giant-angle sign. Preserve external historical and original in-repo
ownership separately.


## 2026-11-02 Bishop/Cauchy source-native max-cut follow-on

Implementation on PR #1408: `c80a70e7088b0c7486f495410f35ad68b3661ac6`,
`53fac955ac98a7576a2bba34db51af1e5a7ac1cd`,
`a302769fc752ed777e1ea2ab65ca08a26db26928`,
`a659878ccf8df19a7b08c3092fa1e488931e090c`,
`fd684576364447edf21d37a2f86fee2034a33029`;
all three TOE root imports added in following commits. Classification:
SOURCE-WRITTEN, NOT AGDA-KERNEL-VERIFIED. CI intentionally not run.

### K05/K04d: actual Round11 sine/cosine at zero

`DASHI/Foundations/BishopRound11TrigAtZeroExact.agda` builds
`sineSignedTermAtZero` and `cosineSignedTermAtZeroHead/Tail`
from the original parity-indexed factorial terms. It derives
`sinePartialAtZero` and `cosinePartialAtZero` for literal finite
Bishop series, then uses
`BishopConcreteTrigSeriesConvergenceExact` and the vendored
`Sequence.uniqueness-of-limits` to establish
`round11SineAtZero` and `round11CosineAtZero`. No classical
sine/cosine oracle, differentiation assumption, or new real carrier.

### K04d: actual complex source at exponent two

`DASHI/Analysis/BishopRiemannDirichletExponentialTermExact.agda`
now has:

- `sourceExponentTwo`: exact original Bishop analytic complex
  pair `(2,0)`;
- `sourceExponentTwoImaginaryArgumentZero`: algebraic
  zero imaginary exponent for arbitrary Nat-log candidates;
- `sourceExponentTwoRealIsBasel` and
  `sourceExponentTwoImagIsZero`: termwise complex exponential
  values `(Basel.baselTerm n,0)` for EVERY n, provided the
  explicit source `exp_B(logNat n)≃n+1` inverse;
- `sourceExponentTwoBaselMajorant`: constructs the actual
  `BishopDirichletBaselMajorantAt` from those native term
  identities, rather than taking a free majorant field;
- `sourceExponentTwoSumIsOriginalBasel`: invokes existing
  `dirichletValuesRespectTermwiseEquality` and Basel limit
  uniqueness to identify both actual summed coordinates with
  the original `BishopBaselReciprocalSquareConvergenceExact`
  limit and zero;
- `originalSourceExponentTwoSumIsBasel`: same result with the
  actual configured convergent -log(1-x) construction, not an
  arbitrary NatLogCandidate.

**No analytic zeta equality is inferred**: this is the concrete
complex Dirichlet series `Σ(n+1)^(-2)`, conditional on the
native Bishop exp/log inverse, not the separate
`ZetaHalfPlaneLayer.zetaHalfPlane` function.

### K04b: normalized cross inequality to the actual Bishop order

`DASHI/Analysis/BishopMachinCrossEnvelopeBishopOrderExact.agda`
imports the original all-n `machinGeometricEnvelopeCrossMultiplied`,
reuses `FiniteNatFractionOrderExact.natFractionLe` and the
original vendored `RealProperties.p≤q⇒p⋆≤q⋆`.
This yields `normalizedNumeratorBelowDenominator`,
`normalizedRationalOrder`, and `normalizedBishopOrder`
for the explicit cross-product form
`3824·57121^n + 20·25^n ≤ (2n+1)·4780·57121^n`.
It is a genuine compiler of the NORMALIZED integer certificate,
but does not yet prove the original three rational remainder
fractions all equal that single normalized quotient under
strictly positive common-denominator cancellation.

### Pareto/max-cut remaining and verification

1. **K04d-LOG:** actual configured `InOpenUnitInterval`
   bridge and a **source-native** proof
   `exp_B(-log(1-x)) ≃ 1-x` with the correct sign/orientation,
   yielding `exp_B(log_B(n+1))≃n+1`.
   The n=0 Nat-log base is already paid.
2. **K04d-NBD:** extend the explicitly constructed exponent-two
   complex Basel majorant to a neighborhood of the *actual
   Machin real* with `Re(s)>2`. Pay monotonic negative
   exponential, the original sine/cosine modulus bound, termwise
   input continuity, and a shared uniform tail modulus.
3. **K04d-OWNER:** identify the original analytic
   `realPartGreaterThanOne` predicate, then prove the
   concrete convergent source function agrees pointwise with
   `ZetaHalfPlaneLayer.zetaHalfPlane` and hence the selected
   `CompletedRiemannZeta.zeta`. The generic substrate's
   `DirichletSeriesConverges` and `Meromorphic` Set fields do
   not themselves discharge these theorems.
4. **K05-CAPSTONE:** derive the full signed-factorial
   Bishop sine/cosine addition law via the existing Cauchy
   triangle/rectangle/wing machinery and coefficient identities.
   Then prove arctan-to-tangent transport, Machin quarter-angle
   branch selection and independently characterized trig pi.
   Only the **origin special case** is now paid, not the
   general addition law.
5. **K04b-DENOM:** pay literal unnormalised rational
   common-denominator identity and positive-normalization,
   then transport the original remainder fraction into the
   source-written normalized Bishop inequality. Direct
   Bishop `4/25^n` and `8/25^n` estimates remain an
   independent already source-written path.
6. **KERNEL:** user explicitly deferred CI; no compiler,
   library resolver or pinned Agda kernel acceptance was
   run in this tranche. The SOURCE-WRITTEN claims require
   independent elaboration, and any failure must be repaired
   before declaring the gate complete.

Original ownership: John Machin; classical Dirichlet/Riemann;
Bishop and Bridges; Zachary Murray's analysis; pinned
`viktorcsimma/bishop` gitlink
`240e38c7f6938f20f865b1f956c5f084da48bd54`.
DASHI owns the above new composition proofs.

## 2026-11-02 K04b denominator and K04d uniform-tail max-cut

### Implemented source-written lemmas; no CI

- `DASHI/Analysis/BishopDirichletUniformBaselTailsExact.agda`
  reuses the ORIGINAL pinned `vendor/bishop/Sequence.agda` operators
  `∑-triangle-inequality`, `∑-mono-≤`,
  `neg-flips-∑`, and `cauchyConvergenceTest-if`.
  `baselUniformTailCutoff` extracts an actual Nat threshold from
  `BishopBaselReciprocalSquareConvergenceExact.baselSeriesConvergent`.
  `baselDominatedFiniteTailSmall` proves the same
  (1/k) bound for every finite tail, in either endpoint order,
  of every Bishop real term family dominated at ALL indices by
  the original Basel coefficients. Both `regionRealUniformFiniteTail`
  and `regionImagUniformFiniteTail` use precisely the same
  cutoff for every selected complex point in the supplied region.
  `regionPointwiseMajorant`, `regionDirichletValue`, and
  `regionValueConvergesCoordinatewise` build actual Bishop
  componentwise sums and limits from one region-wide certificate.
  This is substantive constructive local-uniform *finite-tail*
  machinery, not yet continuity of the original analytic zeta owner.

- `DASHI/Analysis/BishopRiemannDirichletExponentialTermExact.agda`
  specializes this theorem to both actual complex coordinates at
  (s=2) through `sourceExponentTwoUniformFiniteTails`
  and the actual configured -log series via
  `originalSourceExponentTwoUniformFiniteTails`.
  In both cases the already explicit same-object
  `exp_B(log_B(n+1))≃n+1` premise remains OPEN.
  All three TOE roots import the uniform tails owner.

- `DASHI/Analysis/BishopMachinCrossEnvelopeBishopOrderExact.agda`
  now proves `sourceCommonDenominatorFactor` by the existing
  `Data.Nat.Solver` and `sourceCommonDenominatorCleared` by
  the existing `BishopMachinGeometricEnvelopeNatExact`
  all-index Nat inequality. It has the LITERAL source denominator
  `(2n+1)*5*239*25^n*57121^n` and proves
  `(3824*57121^n+20*25^n)*25^n ≤ 4*D_n`
  for every n. This is a genuine denominator-cleared
  INTEGER theorem. The equality of the ORIGINAL two unnormalised
  rational fractions with the displayed common fraction, the
  positivity instances for their denominators, and final
  setoid/Bishop real order transport remain OPEN.

**Correction: the negative-log power series** \(L(x)=-\log(1-x)\) is positive, so the correct
inversion route is \(\exp_B(-L(x))=1-x\) and
\(\exp_B(L(x))=(1-x)^{-1}\).
Earlier draft wording `exp_B(-log(1-x))=1-x` is ambiguous
because the symbol `log` could denote either the conventional
logarithm or the *negative*-log series. Always write `L(x)`
and the two explicit identities above. The actual value
`natLogViaOriginalNegativeLog` is the positive `L(x)`,
so the logical premise is precisely
`exp_B(natLog(n))≃n+1`.

### Still open and distinct

1. **K04d-LOG:** discharge configured `InOpenUnitInterval`
   for the original selected Round11 data and prove the native
   -log/exp inverse for all successor rational arguments.
2. **K04d-REGION:** construct, for the actual exponentials
   `ExpBridge.bishopAnalyticComplexExp` near Machin `pi_B`,
   the regional all-index bound consumed by the *now implemented*
   uniform tail compiler. Pay trigonometric coordinate
   bounds, negative-exponential order, and termwise continuity.
3. **K04d-SAME-OBJECT:** prove literal equality with
   `ZetaHalfPlaneLayer.zetaHalfPlane` and identify the
   original opaque half-plane predicate. Do not substitute
   the mere existence of an uninhabited analytic record.
4. **K05:** signed-factorial sine/cosine Cauchy
   addition, quarter-angle tangent and branch, independent
   trigonometric π uniqueness. Native sine/cosine at zero and
   the polynomial quadruplication endpoint are separately paid.
5. **K04b-DENOM:** rational common fraction equivalence
   with positive variable denominators, followed by embedding
   into the same original Bishop real order. This is
   independent of the existing direct (4/25^n) and
   (8/25^n) estimates.
6. **KERNEL:** deferred by explicit user request; SOURCE
   statuses do not become Agda kernel acceptance without
   elaboration. No CI check was run.

Attribution: original Machin, Dirichlet and Riemann mathematics,
Bishop/Bridges, Zachary Murray and `viktorcsimma/bishop`
at the recorded pinned gitlink; reused DASHI theorem owners
and newly committed DASHI source code are distinct.

## 2026-11-02 K04b variable-denominator rational weld

**Source-written commits:** `0aca247e88e82e5380f96de92f14f9f41819cb3d`,
`2910dcc005e80f99c97e545ff9118cfcb68c9681`,
`e071bffd32a4b1ea04e45532ec27be470cbe22cf`.
No CI or Agda compiler was run. All claims remain SOURCE, not KERNEL.

The original `BishopMachinCrossEnvelopeBishopOrderExact.agda`
now includes proof-producing **variable Nat nonzero** instances for:
`25^n`, `57121^n`, each original
`(2n+1)*5*25^n` and `(2n+1)*239*57121^n`
denominator, and their shared product. It reuses the stdlib
`Data.Nat.Properties.m^n≢0` and `m*n≢0` rather than
hiding positivity in an arbitrary record.

The source fractions are literal `Data.Rational.Unnormalised`:
`sourceOmittedRationalEnvelope` is the actual
`16/[(2n+1)5*25^n] + 4/[(2n+1)239*57121^n]`;
`sourceCommonRationalEnvelope` is
`(3824*57121^n+20*25^n)/D_n`;
`sourceGeometricRationalEnvelope` is `4/25^n`.
The newly source-written
`sourceOmittedRationalIsCommonRational`
uses the existing **integer polynomial solver** to verify exactly
the full cross-product rational equality (no cancellation of a
variable denominator). The Nat-cleared all-index inequality is
transported by `FiniteNatFractionOrderExact.natFractionLe`
to `sourceCommonRationalBelowGeometric`, and by
`Data.Rational.Unnormalised.Properties.≤-respˡ-≃`
to `sourceOmittedRationalBelowGeometric`. The original
Bishop rational embedding then yields
`sourceOmittedBishopBelowGeometric`.

**What remains for the separate K04b-DENOM route:** prove,
on the SAME original Bishop objects, that the actual
weighted first omitted magnitudes
`16*M.atanMagnitudeTerm bishopOneFifth n +
4*M.atanMagnitudeTerm bishopOneTwoHundredThirtyNinth n`
are Bishop-setoid equivalent to
`R._⋆ (sourceOmittedRationalEnvelope n)`, including
positive-power absolute value, signed factorial exponent,
rational exponent/reindex equality, and both positive base
embeddings. The already source-written DIRECT Bishop
`machinBishopFourOver25Pow` and
`machinBishopEightOver25PowCauchy` avoid this alternate
route. Do not treat equivalent end bounds as the proof of
this literal source-term representation.

Other outstanding frontiers unchanged:
K04d source exp/log inverse; all-index regional domination
and term continuity near Machin; literal original completed
zeta same-object continuity; K05 Round11 full trig addition,
arctan-tangent branch and independent trig pi; focused Agda
kernel verification (deferred by explicit user instruction).


## 2026-11-02 K04b source-native actual error and K04d all-real-axis coefficient

**Source commits:** `7579f7fdc6c966d91cd8d23f46ac2f3b5f2dd934`,
`23c35547354e1915a780723fef90cff12f75bbed`,
`fc5ac99cdbf6f051449df7c772975f7985e3eef1`,
`c6ab34505aa49f2e1be03a557a73e69cadff9d8a`,
`61be29b0ba65f056b4b2dcecccfdc5f5c1d0cce9`.
All source-written; no CI or Agda elaboration was run.

### K04b independent unnormalised-denominator path: end-to-end SOURCE

`BishopMachinCrossEnvelopeBishopOrderExact` now reaches
the full original source bound, not just normalized Nat arithmetic.
`magnitudeIsEmbeddedOmittedPower` converts the actual Bishop
arctangent FIRST OMITTED magnitudes to existing `Stage.qPow`
rational powers with original absolute-value/nonnegative powers.
`oddNaturalPowerFactor` proves for every Nat n both
`5^(2n+1)=5*25^n` and
`239^(2n+1)=239*57121^n`.
`rationalReciprocalPower`,
`fiveOmittedPowerIsOriginalFraction`, and
`twoHundredThirtyNineOmittedPowerIsOriginalFraction`
then identify the exact original qPow coefficients with
the original rational positive denominators for ALL indices.
`sourceWeightedPowerEqualsOriginalFraction` and
`sourceWeightedOmittedIsEmbeddedOriginalFraction` weld both
weighted ORIGINAL Bishop magnitudes to the exact source
unnormalised rational envelope. Finally
`sourceOriginalOmittedBishopBelowGeometric` bounds these
magnitudes by embedded `4/25^n`, and
`machinActualCrossDenominatorFourOver25` composes the literal
original all-stage
`Combined.machinRationalAllStagesRemainder` to prove
`|bishopMachinPi - embed(qMachinStage n)| ≤ embed(4/25^n)`.
This is mathematically the same original Bishop target as the
independent direct geometric proof
`BishopMachinGeometricBishopRateExact.machinBishopFourOver25Pow`.
The alternate rational-certificate completion should not yet
be labelled Agda KERNEL; SOURCE code has been committed without
an Agda checker execution. The existing direct real Cauchy
`machinBishopEightOver25PowCauchy` remains available.

### K04d source complex Dirichlet real-axis coordinate identification

`BishopRiemannDirichletExponentialTermExact` now has
`sourceRealAxisExponent`,
`sourceRealAxisExponentialRealCoefficient`, and
`sourceRealAxisExponentialImaginaryZero`. Reusing actual
Round11 `round11SineAtZero`, `round11CosineAtZero` and
`BishopSineCosineSetoidCongruenceExact`, they prove the
literal original source complex exponential at *every Bishop
real sigma* has real coordinate
`exp_B(-sigma*logNat(n))` and imaginary coordinate 0,
without needing to assume exp/log inversion or zeta
owner agreement. This closes the carrier/coordinate starting
point for a real-σ half-plane comparison, but does NOT
establish uniform decay over complex σ+it nor continuity.

### Outstanding actual mathematical owner cuts

1. K04d-LOG source configured interval proof and exp/log inverse
   for all positive Nat successors; the integer zero base is paid.
2. K04d COMPLEX REGIONAL DOMINATION of literal
   `exp_B(-(σ+it) logNat(n))` real/imag coordinates in a
   neighborhood of the actual Machin limit with `Re(s)>2`,
   including concrete unit-magnitude trig estimates. The
   `BishopDirichletUniformBaselTailsExact` compiler already
   supplies one cutoff after this region-wide inequality.
3. K04d actual summand continuity, uniform-limit
   continuity, `realPartGreaterThanOne` predicate bridge,
   and completed-zeta *same-object* identification on the
   original `ZetaHalfPlaneLayer` carrier.
4. K05 mixed signed-factorial Cauchy coefficient identities,
   general sine/cosine addition, arctan-tangent branch,
   and independent trig-pi uniqueness. Existing native trig at
   origin, quadruplication polynomial identities, finite
   Cauchy wings and exponential additivity are reused, not
   a same-object replacement for the missing mixed identity.
5. Agda kernel acceptance intentionally deferred by user
   direction. No CI run; the source commits and GitHub
   readback are NOT evidence of Agda elaboration.

Preserve attribution and ownership: Machin (1706), Dirichlet,
Riemann, Bishop & Bridges, Murray, pinned Viktor Csimma Bishop,
and existing DASHI original theorem owners.

## 2026-11-02 K04b source rate exact same-object weld

Source commit `b7aff799ceb4bf14bebdfbd388654eaba0785623`
adds `sourceGeometricRationalAsQPow`,
`sourceGeometricAsOriginalBishopPowerRate` and
`machinActualCrossDenominatorFourOver25Pow` to the original
same-object denominator module. These transport the literal
unnormalised rational source bound `4/25^n` through the
*existing* `Stage.qPow` source owner and its Bishop embedding
to the identical power-rate expression
`pow_B(embed(1/25),n) * embed(4)` targeted by the
independent `BishopMachinGeometricBishopRateExact` owner.
The alternative cross-denominator derivation is now
source-written end-to-end in the actual source Bishop carrier
and represented geometric rate; the independent direct Bishop
derivation remains separate. Do not mark either derivation KERNEL
until actual Agda elaboration, deliberately skipped by user request.

Remaining mathematical max-cut is K04d configured exp/log inverse,
literal complex regional Basel domination and continuity/actual
zeta same object; K05 full signed-factorial addition and
Machin quarter-angle independent trigonometric π uniqueness.


## 2026-11-02 K04d/K05 exact-source max-cut follow-on (uniform to-limit and origin laws)

Implementation branch: `feat/twin-prime-six-wheel-bounded-gap-reuse-20261028`,
PR #1408. This tranche explicitly searched the existing repo
`InOpenUnitInterval`, `negativeLogOneMinus`, `expLog`,
`logarithmExponentialInverse`, `ZetaHalfPlaneLayer`,
`realPartGreaterThanOne`, `dirichletValue`, `sinAdd`,
`cosAdd`, `BishopFiniteCauchy`, `quarterAngle`,
`Machin tangent`, `BishopExponentialFiniteCauchyCoefficient`,
`BishopExponentialBinomialCoefficient`, and
`BishopMachinZetaSequentialContinuityReducerExact` owners.

### K05 / concrete Round11 addition boundary paid

Commits `f880f20a4a1eba52cc3f3e683c8cf3feb1c8028f`,
`4ad768bbeac663ad830ce26c23d221fc1fed199e`
extend the existing original
`DASHI/Foundations/BishopRound11TrigAtZeroExact.agda`:

- `round11SineAdditionRightZero`,
  `round11CosineAdditionRightZero`,
  `round11SineAdditionLeftZero`,
  `round11CosineAdditionLeftZero`: both actual configured
  Round11 sine/cosine addition formulas at zero on either side.
  These compose existing ORIGINAL signed-factorial
  `round11SineAtZero`/`round11CosineAtZero`, native
  `bishopSinCongruent`/`bishopCosCongruent` and the pinned
  Bishop real ring solver; no general addition theorem assumed.
- `round11SineAdditionOpposite`: actual anti-diagonal
  `sin_B(x+(-x)) ≃ sin_B(x)cos_B(-x)+cos_B(x)sin_B(-x)`
  compiled from ORIGINAL `BalabanBishopSeriesParityAndLimitExact`
  parity lemmas, zero-angle theorem and ring normalization.
- `round11CosineAdditionOppositeFromPythagorean` makes
  the counterpart precisely conditional on the actual
  same-object Pythagorean equation at x. This is a reduction,
  NOT an independent proof of `cosAdd` or Pythagorean.

**Do not mark full K05 closed.** The arbitrary x,y
signed-factorial Cauchy coefficient identities and subsequent
Mertens/finite-wing limit passage remain genuine obligations.
The earlier `PowerSeriesTranscendentals.TrigonometricFunctionalLaws`
has `sinAdd`/`cosAdd` as *input fields*, not constructed
inhabitants for selected Round11. Next: instantiate existing
`BishopExponentialFiniteCauchyCoefficientExact`,
`BishopExponentialBinomialCoefficientExact`,
`BishopFiniteCauchyRowReindexExact` and
`BishopFiniteCauchyWingAbsoluteBoundExact` for the concrete
sine/cosine parity coefficients; prove actual quarter-angle
tangent/branch and independent trigonometric pi uniqueness.

### K04d / strengthened quantitative uniform-to-limit compiler

Commit `48601aa0b7966a5fbafa03d818e8fa64e4e4f9b5`
extends `BishopDirichletUniformBaselTailsExact.agda` with:

- `partialMinusIsFiniteTail` for the vendor's *actual*
  `Sequence.∑` operator;
- `baselDominatedUniformLimitError`: once the original
  Bishop sequence is proved convergent by the ORIGINAL
  `BishopBaselReciprocalSquareConvergenceExact`
  comparison owner and terms are dominated pointwise
  by `baselTerm`, the SAME `baselUniformTailCutoff`
  proves `|lim - partialSum_m| ≤ 1/k` uniformly for
  all m beyond that cutoff, using genuine vendor
  subsequence limit, absolute-value continuity,
  and order closure under limits.
- `regionRealUniformLimitError` and
  `regionImagUniformLimitError`: the one cutoff
  controls BOTH source Cartesian coordinates and EVERY
  point of any region satisfying the explicit
  `RegionBaselDomination` premise.

This now goes beyond finite-tail Cauchy control to a
*common uniform actual-limit error modulus*. It does
NOT construct `RegionBaselDomination` for the original
selected Machin neighborhood, and it does NOT prove
continuity of arbitrary `ZetaHalfPlaneLayer` values.

Commit `c0800b29a32a93698cab7e77e74a7094ab83b0e9`
uses original `BishopMachinPiRationalWindowExact`
`threeBelowMachinPi` to establish
`twoBelowMachinBishopPi` and
`machinSourceRealPartAboveTwo` for the ACTUAL Bishop
Machin real in the ACTUAL Riemann pair carrier.

Commit `3e924d3e16f4866a8ab277104dbe276ef2c1e8cf`
adds `sourceExponentTwoUniformLimitError`:
at s=2, the actual configured Round11 complex exponential
Dirichlet sum has both coordinate limit errors bounded
by the common `1/k` after the Basel cutoff, conditional
on the genuine original source exp/log inverse.

### Source-observed limits of reuse (do not silently promote)

- `BishopElementaryPowerSeriesData.InOpenUnitInterval`
  is a *free configured predicate*, not definitionally
  `0<x<1`. The previously proved true rational/Bishop
  inequalities need a selected field-bridge or a concrete
  source-native configured record to inhabit it.
- The original generic `InverseLogarithmFromExponential`
  uses `expOntoPositive` as a field of a generic
  exponential package. Its constructed inverse is **not
  proven equal to the selected original Bishop
  `bishopNegativeLogOneMinus` series**. It cannot
  close K04d-LOG without same-object transport.
- `RiemannAnalyticSubstrate.ZetaHalfPlaneLayer` exposes
  `zetaHalfPlane` and `realPartGreaterThanOne`
  as free abstract fields. Existing Dirichlet sum
  comparison and its uniform limit modulus cannot prove
  pointwise equality with an arbitrary selected
  `zetaHalfPlane`; actual function identification
  and finite-term continuity are still required.
- `PowerSeriesTranscendentals.TrigonometricFunctionalLaws`
  has `sinAdd` and `cosAdd` as unfilled **fields**;
  the abstract generic log-exponential and trig package
  is not native proof of selected Round11 functions.

### Remaining exact post-max-cut gates

1. **K04d-LOG-INSTANCE**: instantiate selected
   `InOpenUnitInterval` from actual Bishop strict
   inequalities; prove the original positive-successor
   `exp_B(L((n+1)/(n+2)))≃n+2`, where
   `L(x)=-log(1-x)` is the actual negative-log series,
   not a generic inverse.
2. **K04d-REGION-DOMINATION**: native
   `|Re/Im(expC(-s*L_n))|≤BaselTerm n` for every n
   and every complex s in a selected neighborhood
   of Machin with Re(s)≥2 (a strict Re(s)>2
   interior is already established at Machin).
   The quantitative common cutoff and to-limit
   bound **are paid conditional on this bound**.
3. **K04d-FINITE-CONTINUITY**: prove native exp/sin/cos
   term continuity in Bishop s for each fixed n;
   combine with now-available uniform limit error
   to obtain epsilon/delta continuity of the actual
   constructed Dirichlet sum.
4. **K04d-ZETA-SAME-OBJECT**: identify concrete
   half-plane series and actual function value of
   ORIGINAL `ZetaHalfPlaneLayer.zetaHalfPlane`,
   including real domain predicate and the original
   completed-zeta continuation value. Do not use
   a generic opaque `ZetaEqualsDirichletSeries`
   Set as if it were this same-object theorem.
5. **K05-GENERAL-ADD**: actual signed-factorial
   convolution coefficient equations and full
   x+y sine/cosine addition, then native arctangent
   derivative/inverse tangent identity, positive
   branch and independent trigonometric pi uniqueness.
6. **KERNEL**: all above new declarations are
   SOURCE-WRITTEN; zero literal Agda proof holes
   in changed files was checked by source readback,
   but no Agda kernel or CI was run (per user direction).
   No kernel-accepted theorem receipt is claimed.

Historical attribution: John Machin; Dirichlet and
Bernhard Riemann; Errett Bishop and Douglas Bridges;
Zachary Murray's Agda constructive analysis;
Viktor Csimma's pinned `vendor/bishop`; earlier
DASHI source theorem owners. New source composition
in this tranche is attributed to DASHI, not silently
credited to an external theorem as an Agda proof.


### K05 anti-diagonal equivalence refinement

Source commit `c745667872e52b76c32b80e1d7233575ea88fd5f`
extends the true Round11 zero/parity proof owner with
`round11PythagoreanFromCosineAdditionOpposite`. Together
with the previously source-written
`round11CosineAdditionOppositeFromPythagorean`,
this establishes a **two-way equivalence** between
the native Round11 cosine addition equation at
`(x,-x)` and the *original same-object*
Pythagorean identity `cos_B(x)^2+sin_B(x)^2 ≃ 1`.
The proof uses the ORIGINAL `Round11.round11ParityInputs`,
`bishopSinNeg`, `bishopCosNeg`,
`round11CosineAtZero` and pinned Bishop real
polynomial normalization. It is not a proof of
arbitrary two-variable `cosAdd` or a proof of
Pythagorean itself. Status: **SOURCE-WRITTEN,
Agda kernel unchecked**, as requested.


## 2026-11-03 K04d source-log geometric convergence, integer Basel slices and K05 imaginary phase max-cut

Branch `feat/twin-prime-six-wheel-bounded-gap-reuse-20261028`,
PR #1408. Source-written, **NOT Agda kernel-accepted**.
No CI executed, per user direction. All claims are about the actual
pinned Murray/Bishop backend; external paper theorems and generic
record fields are not treated as inhabited source results.

### Explicit repository term archaeology

GitHub default-branch symbol searches (plus direct PR-branch
source fetches) included:
`InOpenUnitInterval`, `negativeLogAbsoluteConvergence`,
`negativeLogOneMinusTerm`, `expLog`, `logExp`,
`expOntoPositive`, `bishopNegativeLog`,
`BishopNaturalLog`, `bishopExpAdd`, `expStrictMonotone`,
`complex exponential modulus`, `normSqC`,
`trigonometric unit phase`, `cosineMagnitude`,
`phase modulus`, `cosAdd`, `sinAdd`,
`sineSignedTerm`, `cosineSignedTerm`,
`CauchyProduct`, `FiniteCauchy`,
`arctan tangent`, `tangent branch`,
`first cosine zero`, `pi uniqueness`,
`zetaHalfPlane`, `ZetaEqualsDirichletSeries`,
`locally uniform`, `uniform limit continuity`,
`BishopContinuousAt`, `bishopExpPositive`,
`expPositiveAll`, `positiveExponential`,
`BishopExponentialGlobal`,
`negativeExpBelowOne`, `BishopGeometricSeriesConvergence`,
`GeometricDominationConvergence`,
`BishopReciprocalCoefficientConstructionExact`,
`BishopGeometricMajorantSeriesConvergenceExact`,
`BishopPolynomialGeometricDominationConvergenceExact`,
`BishopFiniteSeriesExtensionalityExact`.
Search was rate-limited for several terms; key named owners
were also explicitly fetched by exact branch path. No claim
of a globally exhaustive repository scan is made.

### K04d-LOG source native convergence and positivity PAID IN SOURCE

New `DASHI/Foundations/BishopNegativeLogGeometricSourceConvergenceExact.agda`
commits `19b22586d3067cdd42a730087d2638fa6c100b61`,
`d126ba2afd4366ad4e3f8c65fc58022c09d430c4`,
`ff171df816c05b2367d88a63bb066f3dd9665fd0`.

- `sourceNegativeLogTerm x n = x^(n+1) * embed(1/(n+1))`,
  specifically with the EXISTING `BishopNatRealReciprocalSquareBaselExact`
  rational reciprocal owner, not an invented new rational codec.
- `sourceNegativeLogAbsoluteBelowGeometric` proves all-index
  `|sourceNegativeLogTerm x n| <= x*x^n` for nonnegative x.
- `sourceNegativeLogAbsolutelyConvergent` compiles 0<x<1
  into real **Bishop absolute convergence** through existing
  `BishopGeometricMajorantSeriesConvergenceExact.seriesConvergentFromScaledGeometricMajorant`,
  which itself uses vendored Bishop ratio and comparison tests.
- `sourceNegativeLogValue`, `sourceNegativeLogValueConverges`:
  actual native Bishop negative-log series limit and convergence.
- `sourceLogValueEqualsConfiguredBishopLog` uses ORIGINAL
  finite-series extensionality to prove source-native and
  configured series values equivalent whenever the real configured
  interval witness AND literal coefficient identity are given.
  Neither of those inputs is inferred from an abstract record field.
- `sourceLogPartialIncreasing`,
  `sourceLogFirstPartialEqualsX`,
  `sourceNegativeLogAtLeastPoint`, and
  `sourceNegativeLogStrictlyPositive` use the ORIGINAL
  Bishop nonnegative term order and monotone-limit theorem
  to prove `L(x)>=x>0` for all genuine 0<x<1.
- Foundations rollup import attached by commit
  `ba7b0613226f4fd80e6233fb8cdde6ba79003693`.

`DASHI/Analysis/BishopRiemannDirichletExponentialTermExact.agda`
commit `63d4988c0973b2d4244c6861e6d42cfeafaba6c9` adds
`sourceCanonicalNatLogCandidate`,
`sourceCanonicalNatLogSuccessorConverges`,
`sourceOriginalConfiguredNatLogAgreement` and
`sourceCanonicalOriginalExpLogInverseAtOne`. Therefore the full
canonical `log(n+1)` history is constructed directly from the
convergent native source term for EVERY n, **without** the opaque
`InOpenUnitInterval` requirement used by the *different*
`natLogViaOriginalNegativeLog T inside` candidate.

Commit `275c6a8d8bed0c35a05157ac3fd6d707379ff370` adds
`sourceCanonicalNatLogSuccessorPositive` and the actual
`sourceCanonicalNatExpNegativeRatio{Positive,BelowOne}`
using existing global negative exponential unit-interval proof
from `BishopNegativeExponentialGlobalUnitIntervalExact`.
It also builds the original `BishopUnitIntervalRatio` and
`sourceCanonicalNatExpNegativeGeometricConverges`.
This certifies, **without an inverse assumption**, that
`0 < exp_B(-L_n) < 1` for canonical positive successor logs,
NOT that `exp_B(-L_n)=1/(n+1)`.

**K04d-LOG inverse still OPEN:** prove for all n positive
successors that `exp_B(sourceCanonicalNatLogCandidate n)`
equals the original embedded `NatReal.natReal(suc n)`.
Separately, identify the Round11-configured log coefficient
family with `sourceNegativeLogTerm` and supply its
`InOpenUnitInterval` evidence or make the selected record
interpretation concrete and prove source coincidence.
Neither a generic `InverseLogarithmFromExponential.expLog`
record field nor arbitrary conditional evidence pays this.

### K04d-REGION integer exponent subfamily PAID IN SOURCE

`DASHI/Foundations/BishopNatRealReciprocalSquareBaselExact.agda`
commits `828642348b447fbbc393e98209fd830893693a43`,
`8e75c14b4a4d0572f594977a6ed106802ad16329`:
`reciprocalAtMostOne`, `reciprocalNonnegative`,
`oneToAnyNatPower`, `reciprocalPowersAtMostOne`,
`reciprocalExtraPowersBelowSquare`.
For each positive-Nat reciprocal `q=1/(n+1)`
and *every* Nat `k`, prove `q^(2+k)<=q^2` on the
actual embedded Bishop real carrier.

`DASHI/Analysis/BishopRiemannDirichletExponentialTermExact.agda`
commits `9be263273c85fec13084eb18789d6087f3345b56`,
`a1f790da88991ee980ba1c8cd68b69b1c1c7d68f`,
`d93262e33de4921ad15776f9c6e57900be09d16c`,
`6cd1823abab8b6a145f130e946a70a758c6f3ea8`:

- Actual Nat reciprocal and conditional negative exponential
  closed-unit-radius theorem,
  `sourceNatLogNegativeExponentialUnitInterval`.
- `sourceNegativeLogSum` is repeated *actual original* negative
  logarithm input; `sourceExpNegativeLogSumIsReciprocalPower`
  is proved by induction through the ORIGINAL
  `BishopExponentialCauchyProductExact.bishopExpAdd`.
- `sourceNegativeLogSumAboveTwoBaselMajorant` and its
  absolute-value version prove that for every integer exponent
  `2+k`, `|exp_B(-(2+k)logNat(n))|<=BaselTerm(n)`
  **assuming the genuine Nat exp/log inverse**.
- `sourceIntegralExpTerm{Real,ImagZero}`,
  `sourceIntegralExp{Real,Imag}BaselMajorant`,
  `sourceIntegralExpFamilyMajorant`, and
  `sourceIntegralExpFamilyConverges` lift this to *both*
  actual Round11 Bishop complex exponential coordinates and
  the existing native Basel series convergence compiler.
  The fixed-integer term family is **not falsely advertised**
  as the full complex-variable `zetaHalfPlane`.

**K04d-REGION continuous complex neighborhood still OPEN:**
one still needs the original exp/log inverse, proof of
`|sin_B(theta)|<=1`, `|cos_B(theta)|<=1` (a native
Pythagorean-square order proof is a natural donor),
global monotonicity/multiplicative order of exp on
noninteger real exponents and resulting uniform all-index
domination near the ACTUAL Machin `pi`.
The quantitative region finite- and to-limit Basel
cutoffs are already source-written conditional on that.

### K05 pure-imaginary exponential equivalence PAID IN SOURCE

`DASHI/Analysis/BishopSetoidComplexExact.agda`
commit `160293411730cae5a4a09cbaf47e3a256c4e166b`
implements actual same-object two-way bridge:

- `imaginaryPhase`, `pureImaginary`,
  `imaginaryExponentialIsPhase` using ORIGINAL
  `BishopExponentialPositiveOrderExact.bishopExpZero`
  and selected original sine/cosine term limits;
- `BishopSineAdditionAt`, `BishopCosineAdditionAt`
  are **the actual source equations** for the same dataset;
- `imaginaryPhaseProductFromAddition`,
  `imaginaryPhaseProductGives{Sine,Cosine}Addition`;
- `imaginaryExponentialProductFromAddition`,
  `imaginaryExponentialProductGivesPhaseProduct`,
  `imaginaryExponentialProductGivesAddition`.

Thus `expC(i(x+y))≈expC(ix)*expC(iy)`
on original Bishop pairs is *equivalent* to both native
Round11 sine/cosine additions. This does NOT pay
the infinite-series multiplicativity itself; its
remaining genuine proof is the signed-factorial mixed
complex Cauchy coefficient identity and exact convergence
of its finite rectangle/triangle reindexing.

### Exact remaining terminal cut after this tranche

1. **L-INV**: `exp_B(L((n+1)/(n+2)))=n+2` for the concrete
   positive-successor Bishop source negative-log power series,
   all n; same-object configured `negativeLogOneMinusTerm`
   and interval `InOpenUnitInterval` witnesses.
2. **D-COMPLEX-NEIGHBORHOOD**: all-index Basel majorant
   for `expC(-s L_n)` on an actual open complex region
   about `(pi_M,0)`. Integer nonnegative/real fibres and
   common uniform tail limit bounds are now source-written,
   not the full neighborhood.
3. **C-CONTINUITY**: native finite-term exp/sine/cosine
   epsilon/delta continuity and Bishop uniform-limit
   continuity on that same region. The source quantitative
   uniformly common limit-tail modulus is owned.
4. **Z-SAME-OBJECT**: *pointwise actual function equality*
   of the constructed complex Dirichlet sum and the selected
   `Analytic.ZetaHalfPlaneLayer.zetaHalfPlane`,
   `realPartGreaterThanOne` predicate bridge,
   and the original completed-`zeta` value
   from `CompletedRiemannZeta.agreesWithHalfPlane`.
   Generic `ZetaEqualsDirichletSeries : Complex→Set`
   is not evidence for this.
5. **T-MIXED-Cauchy**: prove finite signed-factorial
   mixed complex exponent coefficient identities for all
   x,y, combine already owned Bishop Cauchy wing/tail
   convergence and the exact phase bidirectional reduction,
   thereby obtain genuine sine/cosine addition.
6. **T-ATAN-PI**: prove actual arctangent tangent law and
   branch selection at the Machin quarter, native
   Pythagorean and trigonometric first-positive-zero
   uniqueness; preserve the already proved rational
   tangent arithmetic and interval (3/4, 11/14).
7. **KERNEL**: no Agda checker or CI ran. All new code is
   source-written with no intention to claim kernel
   acceptance, even if GitHub source readback succeeds.

Historical attribution: John Machin (1706), Dirichlet,
Riemann (1859), Bishop & Bridges (1985), Zachary Murray
(2022, arXiv:2205.08354), Viktor Csimma's pinned
`vendor/bishop`, and relevant original DASHI theorem
owners. Any new reductions are owned by the
DASHI formalisation project; external generic theorem
reports must never be recorded as kernel proof receipts.


### 2026-11-03 final source-readback and explicit import fixes

Post-tranche source hygiene commits:
`2df7a6fc8d6c6e9b45a39d1f93a4cb4d4acd4c75`
explicitly imports the Nat reciprocal rational-order
constructor `Int.+≤+` in the original
`BishopRiemannDirichletExponentialTermExact`;
`f8ef6a4bed6145a747a09ee51087a05d8af6783e`
explicitly imports Nat addition `_+_` in the
vendor-subsequence-based `BishopDirichletUniformBaselTailsExact`.

The GitHub connector read back all 7 changed source/rollup
and roadmap paths after these commits. The new declared
names are present. The edited source does not contain a literal
`postulate` declaration or an Agda `{! !}` source hole.
A static delimiter count checked balanced `()` and `{}`
in the key mathematical modules. Those checks are *not*
Agda parser, elaborator, positivity, termination, safe-mode,
dependency or kernel receipts. This is an intentional
SOURCE-ONLY state under the instruction to skip CI;
the canonical mathematical terminal proof gates above
remain exactly as recorded.


## 2026-11-03 K04d canonical Round11 configuration and K05 full complex exponential transport

This follow-on is **SOURCE-WRITTEN**, not Agda-kernel verified; CI left
untouched. It closes explicit small same-object and reusable
Cartesian boundaries, not the terminal analytic open cuts.

### K04d: construction of a concrete configured interval and same-object log

`DASHI/Analysis/BishopRound11CanonicalNegativeLogSameObjectExact.agda`
(commit `ab838741905676085eb960f7f61c642b85368273`,
then `f6258148800b6c0f39c871d24900624f3bc5c8e5`)
reuses the earlier geometric-series owner, original
`Round11BishopCutset`, and vendored Bishop
`Sequence.uniqueness-of-limits`.

- `canonicalNegativeLogDataSet old` builds a
  `BishopElementaryPowerSeriesData` with the literal predicate
  `InOpenUnitInterval x = (0<_B x) × (x<_B 1)`.
  Its logarithm terms are the original coefficient expression
  `x^(n+1)·embed(1/(n+1))`; the previously proved native
  `sourceNegativeLogAbsolutelyConvergent` supplies an actual
  convergence witness for this definition.
  Sine, cosine and exponential terms and their original
  absolute-convergence sources are reused unchanged.
- `canonicalNegativeLogRound11 inputs` constructs a genuine
  Round11BishopCutset. The existing configured sine/cosine
  propositional term definitions are preserved.
- `canonicalUnitIntervalWitness inputs n` constructs an
  ACTUAL selected predicate witness for every original
  `natLogArgument n=(n+1)/(n+2)` using native Bishop order.
- `canonicalNatLogFromConfiguredSource` now uses the
  original `natLogViaOriginalNegativeLog` evaluator with
  this inhabited concrete field, not an uninstantiated
  `inside` assumption.
- `canonicalNatLogIsOriginalBishopSum` proves equality of
  the canonical-configured negative-log result and
  `sourceCanonicalNatLogCandidate` on the same Bishop real,
  by original series extensionality.
- `canonicalSineSameOriginal`,
  `canonicalCosineSameOriginal` and
  `canonicalExponentialSameOriginal` prove the original
  selected nonlogarithmic Bishop limits are unchanged
  despite the selected log-field reconstruction. This
  does not assume definitional equality of the limit
  witnesses themselves.

**Critical distinction:** This creates a compatible, now
CONCRETE Round11 data record; it does NOT prove that an
arbitrarily supplied earlier `elementarySeries inputs` has
the same `negativeLogOneMinusTerm` and
`InOpenUnitInterval`. The backward identification requires
a real termwise equality and a bridge to that previous
predicate; neither follows from an abstract record field.
The independent true source exponential inverse
`exp_B(L(x)) = 1/(1-x)` remains mathematically OPEN.
The generic `expLog` authority is not substituted for it.

### K05/K04d: general complex exponential homomorphism reducer

`DASHI/Analysis/BishopSetoidComplexExact.agda`
(commit `978d33b5241b9d2e3ad4f5216382a07b32c99637`)
now includes:

- `expCAddFromRealAndTrigAddition`, proving the full
  original Bishop complex equation
  `expC(x+iy+a+ib) ≈ expC(x+iy) *C expC(a+ib)`
  from the **already proved** real
  `BishopExponentialCauchyProductExact.bishopExpAdd`
  and the actual Round11 sine/cosine addition equations.
  All Cartesian normalisation is done with the original
  Bishop real polynomial solver.
- `expCAddFromImaginaryMultiplicativity` shows that
  the original pure-imaginary multiplication equation
  (for every real pair y,b) is enough to prove
  multiplicativity on ALL of the original Bishop complex
  carrier. This consumes the already proved bidirectional
  sine/cosine-phase reduction.

The combined cut is now precise: **one actual pure-imaginary
signed-factorial Cauchy-product theorem** supplies BOTH
native general trig addition identities AND full complex
exponential multiplicativity. Neither implication proves
that outstanding complex product law by itself.

The existing `DASHI/Foundations/BishopNatRealReciprocalSquareBaselExact.agda`
and `DASHI/Analysis/BishopRiemannDirichletExponentialTermExact.agda`
continue to provide integer real exponent Basel domination,
but no open complex neighborhood estimate is inferred.

### Max-cut still required

1. **K04d-LOG-INV:** prove the actual source native log inverse
   for all positive successors. The canonical configured
   instance is now source-written, but the inverse analytic
   identity is not.
2. **K04d-COMPLEX:** obtain all-index coefficient majorant
   on an actual complex neighborhood near the Machin π
   for noninteger real and arbitrary imaginary parts,
   paying the signed-factorial trigonometric modulus
   and real-exponential order estimates.
3. **K04d-CONTINUITY:** prove finite-term continuity,
   apply existing uniform limit modulus, identify
   same-object actual selected half-plane and completed
   zeta functions and predicate.
4. **K05-PUREIMAG:** prove the original mixed signed-factorial
   Cauchy coefficient identity and limit passage, then
   tangent/arctan branch and independently characterized π.
5. **KERNEL:** kernel acceptance, dependency resolution
   and any elaboration repairs still required; no Agda
   checker or CI was run in this turn.

Preserve ownership and provenance for Machin, Riemann,
Dirichlet, Bishop & Bridges, Zachary Murray, Viktor Csimma
and the preexisting DASHI proof owners. Source-written
conditional reductions must not be promoted to theorem
completion without proving their exact input predicates.


## 2026-11-03 K04d/K05 source-native order repair and noninteger-complex region compiler

Branch `feat/twin-prime-six-wheel-bounded-gap-reuse-20261028`,
PR #1408. Explicitly searched original theorem owners and followed
the vendored Bishop `RealProperties`, `Sequence`, `Inverse`,
finite exp/binomial Cauchy coefficient, Round11 signed-factorial
series, source complex exponential, Machin arctan/quarter window,
Bishop norm-square reflection, Moonshine unit phase and selected
Riemann half-plane interfaces. NO CI / NO AGDA ELABORATION; all
new status here is **SOURCE-WRITTEN**.

### Corrected invalid earlier Bishop left-setoid order orientations

Earlier source code was NOT ready to be called kernel accepted.
The exact pinned vendor signature is
`≤-respˡ-≃ : _≤_ Respectsˡ _≃_`. A proof of
`y ≃ z` and `y ≤ x` yields `z ≤ x`, not the reverse
direction. Earlier code used the symmetric orientation in several
source lemmas, so *we did not simply append another layer*.

- `127406c51087a64924e3d6b75aa21b5ab918c07a` repairs
  `BishopNegativeLogGeometricSourceConvergenceExact`
  at the absolute source-term bound, double-absolute
  geometric comparison, monotone prefix, and first-prefix
  to-log-limit order.
- `2a205d3cde69486db23dad33811cf2de1a516117` repairs
  `BishopNatRealReciprocalSquareBaselExact`
  power-product transport to `q^(2+k) ≤ q²`.
- `30cfa68e9fcbf14dd2848bd8325c261d21030418`
  repairs `BishopRiemannDirichletExponentialTermExact`
  negative exponential unit order, scalar integer Basel bounds
  and literal complex real/imag Basel component orders.

These are source-level repairs based on *actual* vendor
definition, not postulates. Agda elaboration is still outstanding.

### K04d-LOG genuine source-native order theorem

Commit `f41ee599504d07fc4018ac5b6f34884d1e892497`
adds original canonical power-series
`sourceNegativeLogTermMonotone`,
`sourceNegativeLogPartialMonotone` and
`sourceNegativeLogMonotone`:
for `0<x≤y<1`, the *same actual Bishop series limits*
satisfy `L(x)≤L(y)`. This uses
`Sequence.x≤y∧nonNegx⇒xⁿ≤yⁿ`,
the original nonnegative reciprocal coefficient,
`Sequence.∑₀-mono-≤`, and
`Sequence.xₙ≤yₙ⇒limxₙ≤limyₙ`.
Neither native exponential inversion nor the arbitrary
Round11 log record is assumed.

**Still open:** `exp_B(L(x)) = 1/(1-x)` for the canonical
series (at least each Nat argument) and general equality with
an arbitrarily preselected Round11 negative-log coefficient family.

### K04d-REGION new all noninteger complex-s comparison compiler

Commit `ae2aacf1b1bd744e6955c66772f7d6a765a0a095`
extends `BishopRiemannDirichletExponentialTermExact` with
`sourceRealExponentAboveTwoFactor`,
`sourceAboveTwoExtraFactorPositive`,
`sourceAboveTwoExtraFactorBelowOne`,
`sourceRealExponentAboveTwoBasel`, and
`sourceCanonicalNonintegerRealBaselTail`.
The original **real** Bishop exp product is split exactly:
`exp_B(-σ L_n) ≃ exp_B(-2 L_n)*exp_B(-(σ-2)L_n)`.
For all `σ>2` and `L_n>0`, the second factor is
strictly below one using the *already proved* original
global negative exponential theorem. Thus the scalar
Basel bound works for every **noninteger Bishop real**
`σ>2`, not just the earlier integer fibre.

Commit `015678d7d878cabcaf01a168a9a8b94d75134b57`
adds `BishopRound11TrigModulusFromPythagoreanExact.agda`.
The repo already owns the ACTUAL Bishop phase
`cos_B θ + i sin_B θ`, constructive norm-square/component
comparison, and nonnegative square-order reflection.
The new `round11ModulusFromPythagorean` proves
`|cos_B θ|≤1` and `|sin_B θ|≤1`
from the *same-object original Round11*
`cos_B² θ+sin_B² θ≃1`. It does not assume those
separate modulus facts in an opaque record.

Commits `0fa51db0c4dc7e362b9942ca09ebd1fb8ac85a5d`
and `150477bf2ecc8a89d73e71a3b16812dc2bc96b4f`
add `BishopRiemannComplexAboveTwoBaselExact.agda`.
The new
`sourceComplexAboveTwoCoordinateBounds`,
`sourceComplexAboveTwoMajorant` and
`sourceComplexAboveTwoConverges` prove the literal
ORIGINAL variable-complex-s term bound and actual
Bishop coordinate convergence throughout
`Re(s)>2` (arbitrary imaginary component), for every
positive successor n, **conditional on** the genuine
canonical Nat exp/log inverse and original Round11
Pythagorean at the actual source phase. No synthetic
integer-exponent term family or replacement complex exp.

Commits `43fb31f013de75c81796448c2a5116136a6de850`
and `fe091fba3d691b222545fbefc312184581cecb84`
extend the same owner: `sourceComplexZeroRealIsOne`,
`sourceComplexZeroImagIsZero`, and
`sourceComplexZeroBaselBound` handle literal
`log(1)=0` and source `exp_C(-s·0)=(1,0)`.
`sourceComplexAboveTwoMajorantAllIndices`
then supplies the all-index comparison. The genuine
`sourceRegionWideBaselCertificate` converts two explicit
mathematical hypotheses (canonical exp/log inverse for
all n; native Round11 all-angle Pythagorean) into a
region-wide `RegionBaselDomination` for the **same
actual original Bishop variable-s complex Dirichlet series**.
`sourceRegionUniformDirichletValue` and
`sourceRegionUniformLimitError` reuse the existing
Bishop comparison compiler to produce the TRUE
one-cutoff uniform coordinate limit errors over all
complex `s` with `Re(s)>2`.

All three TOE import roots now import the new proof owners.
**These statements remain CONDITIONAL** on the original
native inverse and Pythagorean theorems; the missing
assumptions have been reduced to independently named
same-object analytic facts, not made to vanish.
No kernel elaboration has occurred.

### Exact final mathematical cut (not closed)

1. **L-INV:** actual canonical Bishop
   `exp_B(L((n+1)/(n+2))) ≃ n+2`, all n; independently
   identify the previous arbitrary selected Round11
   negative-log coefficient family where required.
2. **T-PYTH / MIXED-CAUCHY:** original signed-factorial
   complex imaginary exponential coefficient convolution,
   rectangle/triangle limit transport and full
   pure-imaginary multiplicativity. From this obtain actual
   Round11 `sinAdd`, `cosAdd` and `sin²+cos²=1`.
3. **K04d REGION:** now **closed conditionally in source**
   for all complex Re(s)>2 including n=0 and a common
   uniform to-limit modulus, subject to 1 and 2. No
   unconditional neighborhood result yet.
4. **CONTINUITY:** original native termwise exp/sin/cos
   continuity, resulting sum continuity via the new
   source uniform errors, real-half-plane predicate
   identification, and same-object equality with the
   original opaque `ZetaHalfPlaneLayer.zetaHalfPlane`
   and completed zeta.
5. **K05-ATAN-PI:** source rational arctan-tangent
   law, analytic quarter branch and independently
   characterized first positive trigonometric π uniqueness.
6. **KERNEL:** SOURCE-WRITTEN only. A repository file
   and absence of a literal Agda `postulate` or `{! !}`
   is not a typecheck or a proof of a mathematical proposition.

Citations/credit: Machin; Dirichlet; Riemann; Bishop and
Bridges; Zachary Murray; Viktor Csimma's pinned Bishop
gitlink; and existing DASHI foundational/analytic
theorem owners. The new compositions belong to DASHI.


## 2026-11-03 full theorem-owner archaeology: genuine Bishop vs abstract/logically weaker models

Follow-up to the K04d/K05 source-native max-cut. PR #1408, branch
`feat/twin-prime-six-wheel-bounded-gap-reuse-20261028`.
This search was explicit over the ORIGINAL feature branch and the
default-branch GitHub code index, including:
`bishopExpLog`, `expLog`, `logExp`, `expOntoPositive`,
`logOneMinus`, `negativeLog`, `logFromExponential`,
`exponentialInverse`, `powerSeriesLog`, `inverseLogarithm`,
`logarithmSeries`, `geometricDerivative`,
`BishopExponentialCauchy`, `BishopBaselSineProductCoefficient`,
`BishopTrigonometricAddition`, `TrigonometricFunctionalLaws`,
`BishopConcreteSine`, `BishopRound11FactorDerivative`,
`BishopFactorDerivativeAt`, `BishopPowerFirstOrderDifferenceFactorisation`,
`signedFactorial`, `imaginaryExponential`, `complexCauchy`,
`complexExponential`, `sinCosAddition`, `Pythagorean`,
`phaseUnit`, `ZetaHalfPlaneLayer`, `zetaHalfPlane`,
`analytic zeta`, `DirichletAgreement`, `sameObjectZeta`,
`Bishop continuity`, `uniformLimit`,
`uniform convergence continuity`, `firstPositiveZero`,
`pi uniqueness`, `BishopMachinQuarterAngleBranchExact`.
No global repository-text exhaustiveness is claimed: GitHub code
search indexes the default branch and may rate limit; original owner
files were additionally fetched explicitly from the feature branch.

### Exact source/evidence classification

| Owner | What the exact source provides | Why it does not alone pay the terminal same-object gate |
| --- | --- | --- |
| `DASHI/Analysis/InverseLogarithmFromExponential.agda` | Constructed-real exp/log inverse from `expOntoPositive` | `expOntoPositive` is an input field of a separately selected constructed-real exponential; no pinned Bishop instance equating its `log` to the canonical negative-log series |
| `DASHI/Analysis/OrdinaryTranscendentalRealization.agda` | `PositiveExponentialInverseAuthority` and `TrigonometricPowerSeriesAuthority` compilation | `expLog`, `logExp`, `sinAdd`, `cosAdd`, `pythagorean` are supplied as record fields; not independently generated from the selected Bishop series |
| `DASHI/Analysis/PowerSeriesTranscendentals.agda` | Formal series-to-exp/trig construction and finite coefficient/limit compiler | `ExponentialOrderLaws.expOntoPositive`, `TrigonometricFunctionalLaws.sinAdd`, `cosAdd`, `pythagorean`, `firstZero` are still input witnesses; not a source-native Bishop Nat-log inverse or source trig Cauchy product |
| `DASHI/Analysis/TerminalConstructedAnalyticModel.agda` | Actual, no-postulate constructed model with `expLog` and `expOntoPositive` | Explicitly a **one-point** `Real=⊤` model, NOT the Bishop real carrier or standard analytic zeta |
| `DASHI/Foundations/RealElementaryFunctionsCanonicalInstanceExact.agda` | Legacy compatibility names and postulated elementary authorities | Declares a literal `postulate` block; **not Golden Agda evidence** for a selected Bishop theorem |
| `DASHI/Foundations/BishopElementaryTailEvidenceExact.agda` | Evidence-bearing interface with `logarithmExponentialInverseEvidence` | This is a *field asking for a proof*, not that proof |
| `DASHI/Foundations/BishopExponentialCauchyProductExact.agda` | Actual Bishop `bishopExpAdd`, inverse-product and finite Cauchy reindexing | Fully reusable; does not identify `exp_B(L_n)` for the negative-log series |
| `DASHI/Foundations/BishopExponentialBinomialCoefficientExact.agda` and `BishopExponentialFiniteCauchyCoefficientExact.agda` | True factorial/binomial coefficients and finite exp(x+y) Cauchy identity | Source coefficient proof applies to the real exponential, not yet the signed sine/cosine mixed complex convolution |
| `DASHI/Analysis/BishopRound11FactorDerivativeInterchangeExact.agda` and `BishopRound11TrigSetoidInterchangeInstanceExact.agda` | True literal sine/cosine finite derivative and pointwise convergence chain | Actual infinite limit-derivative interchange requires `SineInterchangeControlAt` and `CosineInterchangeControlAt`; generic DLMF source is not a native same-object witness |
| `DASHI/Analysis/BishopRound11ClassicalTrigObjectWeldExact.agda` | Shared source-backed DLMF trigonometry/derivative interface | `SameClassicalAndBishopTrigObject` must still be proved; `sameTrigObjectWeldClosed=false` |
| `DASHI/Moonshine/JInvariantBishopTrigUnitPhaseExact.agda` and `BishopNonnegativeSquareReflectionExact.agda` | Same Bishop complex norm algebra and constructive square-reflection | Native phase modulus follows from a supplied `BishopTrigPythagoreanAt`; there is no independent Pythagorean inhabitant in that owner |
| `DASHI/Foundations/BishopBaselSineProductCoefficientBoundaryExact.agda` | Actual same-Bishop Basel/sine coefficient cancellation after a limit witness | `SineProductCoefficientLimit.finiteProductLinearConvergesToSineCoefficient` is a still-unpaid proof field |
| `DASHI/Analysis/RiemannAnalyticSubstrate.agda` | Original `ZetaHalfPlaneLayer` and `CompletedRiemannZeta` typed interfaces | `ZetaEqualsDirichletSeries : Complex→Set` is unconnected to an equality until an explicit function-value bridge is built; `agreesWithHalfPlane` is a field, not proof that the original zeta is our selected Bishop sum |
| `DASHI/Analysis/RiemannZetaProgramBoundary.agda`, `Mathematics/NumberTheory/RiemannCompletedZetaBoundary.agda` | Explicit zeta continuation, Euler-product and completed-zeta input contracts | Neither constructs the concrete Bishop Riemann analytic substrate; Abel values and finite results do not pay continuity or selected function identity |
| `DASHI/Analysis/BishopMachinConfiguredTrigPiExact.agda` | Configured Machin real equals the original Bishop Machin series value and original quarter angle | Explicitly does NOT prove independent first-positive-zero trig π characterization |
| `DASHI/Analysis/SineNaturalMultiplePiZeroBidiExact.agda` | Forward indexed sine-zero induction on a supplied constructed trig package | Reverse sine-zero classification remains source-backed; the package's trig addition/π zero fields are assumed for that carrier |

### New owned common-cut composition

Created `DASHI/Analysis/BishopRound11ImaginaryProductPythagoreanReuseExact.agda`,
commit `ddbc0d896e14b139cdb970a7b9aabf23361ab5d4`;
fixed private Round11 local sine/cosine abbreviation in commit
`c495358321bea47167b5fce3fe51470af6e48763`.

Its literal `Round11ImaginaryExpMultiplicative inputs`
is the original Bishop phase product, not a generic Set
authority for a different carrier.

- `round11PythagoreanFromImaginaryProduct` uses the actual
  `BishopSetoidComplexExact.imaginaryExponentialProductGivesAddition`,
  the anti-diagonal source `BishopRound11TrigAtZeroExact.round11PythagoreanFromCosineAdditionOpposite`,
  and original concrete Round11 parity, proving
  `sin_B²(theta)+cos_B²(theta) ≃ 1` from a SINGLE genuine
  signed-factorial imaginary product witness.
- `round11ModulusFromImaginaryProduct` reuses the already
  proved native nonnegative-square reflection and Bishop phase
  norm to derive `|sin_B(theta)|,|cos_B(theta)| ≤ 1` on the
  exact selected Round11 dataset, without an independent
  Pythagorean input.
- `sourceRegionWideFromSingleImaginaryProduct` imports
  the previous all-index `Re(s)>2` complex Basel compiler.
  **Only two** genuine source proof families are now
  independently owed for original complex-s uniform
  Dirichlet convergence: (i) `exp_B(L_n)=n+1` on
  the original Bishop canonical Nat log series, and
  (ii) `expC(i(x+y)) ≈ expC(ix)*expC(iy)` on ALL
  original Bishop real x,y (the signed-factorial Cauchy
  product). Pythagorean and phase modulus no longer
  demand additional independent proof input.

Commit `f80ffe498671ccf5957c16546c7595a4be357d7f`
and operator-token correction
`e69bbda2a0ea8b0b687a1dfcf7958179cb99a965`
extend that **same** source owner:

- `round11DoubleAngleFromImaginaryProduct`: constructs
  the ORIGINAL `BishopMachinQuarterPhaseQuadruplicationAlgebraExact.Round11BishopDoubleAngle`
  with sine and cosine projections of the same product.
- `round11MachinTrigEndpointFromImaginaryProduct`:
  `sin_B(pi_M) ≃ 0`, `cos_B(pi_M) ≃ -1`
  using ONLY the common product law and the still-owed
  **original Machin quarter-angle semantic equality**
  `cos_B(theta_M) ≃ sin_B(theta_M)`; the Pythagorean
  premise is derived, not independently passed.
- `round11SineShiftByMachinPi`,
  `round11CosineShiftByMachinPi`: source sine/cosine
  sign changes under translation by the SAME
  `Machin.bishopMachinPi` from that endpoint and
  source sine/cosine addition. This is not an
  independent first-positive-zero π uniqueness proof.

All three TOE roots import the new owner, commits
`2c3b2f3d015038f829cc801204d682a3c4f49f37`,
`d990c971b59e06a6f8cf55c0dbdf3d9923cd0e08`,
`61f60270abb4a7dceed7d98ab7e2160ddabbb295`.

### Exact remaining non-duplicated kernel and math cut

1. **LOG-NATIVE**: prove for the actual Bishop reciprocal
   power-series `L(x)` the source inverse law
   `exp_B(L(x))=1/(1-x)` (at least at the required
   `x=(n+1)/(n+2)`), and compare an arbitrary earlier
   configured negative-log term family by real termwise equality.
   The abstract `expOntoPositive` and singleton terminal
   model do not pay this.
2. **K05-MIXED**: prove the actual original all-(x,y)
   signed factorial Cauchy coefficients + limit reindexing
   for `expC(i(x+y))≈expC(ix)expC(iy)`.
   Once paid, **all native trig addition, Pythagorean,
   modulus, double-angle and π-shift** are covered by
   the new reusable source reductions.
3. **K04d-CONTINUITY**: prove finite term continuity on
   the Bishop variable-complex carrier, combine with
   already owned one-cutoff regional uniform errors to get
   continuity of the sum, and select a genuine analytic
   function object on the exact same carrier.
4. **K04d-ZETA-SAME-OBJECT**: prove actual identity with
   the original selected `ZetaHalfPlaneLayer.zetaHalfPlane`
   and `CompletedRiemannZeta.agreesWithHalfPlane`.
   A `ZetaEqualsDirichletSeries` Set-valued field with a
   witness of that Set is NOT automatically a function
   equality; these are independent evidence obligations.
5. **K05-QUARTER-PI**: actual native atan/tan link giving
   `cos_B(theta_M)≃sin_B(theta_M)`, establish the branch
   using the already proved 3/4<theta_M<11/14 window,
   and prove independent first-positive-zero π uniqueness.
6. **AGDA-KERNEL**: Source-written terms are NOT kernel receipts.
   No Agda compiler or CI run was executed. Neither
   syntactic absence of holes/postulates nor a file name
   ending in `Exact` certifies a theorem. Audit the
   Golden `--safe` transitive imports before elevating this
   source to authoritative proof status.

Attribution retained: Machin (1706), Dirichlet, Riemann,
Bishop and Bridges, Murray, Viktor Csimma's pinned
vendor/bishop and all reused in-repo original owner paths.


## 2026-11-03 Bishop K04d/K05 same-object minimum cut

See [the audited theorem-owner and exact-lemma map](BishopK04dK05SourceNativeMaxCut20261103.md).
Source-written on PR #1408: `BishopMachinTwoPiPeriodFromImaginaryProductExact.agda` derives original Round11 sine/cosine two-Machin-pi periodicity from the **single** pure-imaginary exponential multiplication hypothesis and original quarter-angle sine/cosine equality. It does not prove either premise or least-positive-period uniqueness.

Reconciled live gates: **(1)** source-native exp_B(log_B(n+1))=n+1 for n≥1, **(2)** same-Round11 mixed signed-factorial Cauchy/exponential product for all x,y, **(3)** native finite-term plus uniform-limit continuity and selected same-object ZetaHalfPlaneLayer/completed-zeta weld, **(4)** arctangent-to-tangent quarter-angle equality and *independent* trigonometric pi characterization. Pythagorean, original phase-modulus, noninteger Basel comparison, Machin π-shift, and the new 2π period are **downstream**, not separately assumed. Source readback only; no Agda kernel acceptance claimed.


## 2026-11-03 second K04d/K05 max-cut — native Agda and faithful Lean

See `Docs/roadmaps/BishopK04dK05SourceNativeMaxCut20261103.md` for exact source/theorem ownership and unreduced gates. Golden Agda PR #1408 adds `BishopNegativeLogExponentialReciprocalFromCancellationExact` (native source exp(-L(x))=1-x -> original Bishop exp(L(x))=inverse(1-x) via exact real Cauchy + inverse uniqueness), and `BishopMachinFirstPositiveSineZeroFromNativePhaseExact` (Machin strict positivity and first-positive-sine-zero under original K05 imaginary product, quarter equality and native interval sine sign). All three TOE roots import them. **Neither input theorem is fabricated or proved by a Set flag.**

Lean PR [#104](https://github.com/chboishabba/dashi_lean4/pull/104) adds source-faithful *separate* semantic proofs for original negative-log successor inverse, original sine/cosine imaginary product, source quarter equality/first sine zero and genuine Mathlib zeta + completed zeta continuity at evaluated pi. A direct Agda proof-term importer or Agda native proof remains outstanding. New Lean modules are not yet kernel-receipted. Updated live gates: (1) source exp(-L(x))=1-x; (2) native signed-factorial finite Cauchy/limit proof; (3) native Bishop finite-term/uniform-limit zeta continuity and original selected half-plane/completed zeta same-object weld; (4) native quarter atan/tan and native strictly positive sine on (0,pi_M), followed by original pi characterization. Do not claim any of the four unconditionally complete.
