# Twin-prime steelman BIDI: exact decision target and asymptotic programme

**31 October 2026.** Attribution: Hardy–Littlewood (1923) original prime-pair asymptotic conjecture; Brun, Chen, GPY, Zhang, Maynard–Tao and Polymath8 for sieve and bounded-gap developments; Axiom Math PrimeGapsLib and OpenAI PrimeGaps186 for independently authored formalisation. Existing DASHI arithmetic/Agda owners remain intact. This document adds an unproved research *target*, not a theorem claiming twin primes.

## Keep two targets, not a movable goalpost

- **Acceptance / exact BIDI (T0)**: actual twin-prime infinitude iff real prime-only weighted correlation `P(X)` is unbounded iff infinitely many disjoint dyadic start-point slabs carry positive prime-only weight. The last statement uses **infinitely many**, not merely some slabs, and exact Nat prime ownership.
- **Positive limsup sufficient (T1)**: `limsup S(X)/X > 0`, plus independently proved `E(X)=o(X)`, implies T0. Neither T0 nor the logical equivalence implies T1.
- **Uniform positive density sufficient (T2)**: `liminf S(X)/X > 0` implies T1. This is stronger and remains open.
- **Hardy–Littlewood asymptotic steelman (T3)**: `S(X) ~ 2 C_2 X`, where `C_2 = product_{p>2} [1 - 1/(p-1)^2]`. Under the conventional Hardy–Littlewood singular series normalization, `2C_2 ≈ 1.3203236317`. This implies T2. It is a conjectural goal, not a proved result.
- **Twin counting asymptotic (T4)**: `pi_2(X) ~ 2 C_2 * integral_2^X dt/(log t)^2` (equivalently `~ 2 C_2 X/(log X)^2`). This implies T0; the exact equivalence of T3 and T4 is **not assumed** without a separate weighted-to-unweighted transfer theorem and prime-power control. T3's weighted P asymptotic can imply T4 via partial summation under established weight comparison, but reverse implications require care at error scale.

Classical `S(X) = sum_{n+2<=X} Lambda(n)Lambda(n+2)`, `P(X) = sum_{p+2<=X, p,p+2 prime} log(p)log(p+2)`, and `E(X)=S(X)-P(X)>=0`.

The proper-prime-power support bound
`E(X)=O(sqrt(X)log²(X)+X^(1/3)log³(X))=o(X)`
is elementary and independent of Hardy–Littlewood. Its analytic paper derivation should not be mislabelled kernel-certified Agda. Distinguish genuine PrimeNat certificates from an abstract Mangoldt carrier and real weights.

## Bidirectional proof-search protocol

**Forward (SOTA to target):** import bounded-gap theorems at their *exact* logical strength. H1<=246 and conditional Lean H1<=186 control two primes with an offset bounded by B, **not** offset exactly 2. Chen's almost-prime endpoint is not necessarily prime. No such theorem directly supplies T0 or any positive twin-pair asymptotic.

**Backward (target to minimal lemma):** for T3, the singular-series main term requires a prime-pair correlation cancellation / distribution theorem at exact shift +2 and a remainder `R(X)=o(X)` in `S(X)=2C_2 X+R(X)`. Do not simply define `R=S-2C_2 X` and call it small. For T0, an unbounded nonnegative prime-only weight or cofinally nonempty certified twin windows is sufficient and necessary; a mere infinite sieve survivor sequence is not.

**Discriminator**: any graph/FRACTRAN/CRT/residual transfer must preserve true prime-one labels and sign/weight. Explicit double-composite survivors defeat an argument relying solely on finite modular information. A synthetic receipt or numerical match to 2C2 cannot be promoted to a distribution theorem.

**Steelman bidirectional acceptance:** require (i) exact provenance, (ii) a source theorem's assumptions, (iii) a map to the actual shifted Mangoldt real scalar, (iv) sharp distinction T0 versus T1–T4, (v) a finite adversarial countermodel or obstruction test, and (vi) kernel receipt for formal claims.

## Precise SOTA status

Polymath8b unconditional H1<=246. PrimeGaps186 GitHub README and formalization.yaml declare its 186 result proved in Lean **conditioned** on three external inputs: hyper-Kloosterman estimate, Kloosterman correlation estimate and numerical physical-integral/cap bounds. Thus a successfully checked conditional theorem is not an unconditional H1<=186 proof, much less T0–T4.

References:
- https://github.com/openai/PrimeGaps186
- https://github.com/openai/PrimeGaps186/blob/main/formalization.yaml
- https://annals.math.princeton.edu/2015/181-1/p07
- https://en.wikipedia.org/wiki/Twin_prime#First_Hardy%E2%80%93Littlewood_conjecture

**Proof status:** specification and research plan. Neither T0, T1, T2, T3 nor T4 has been discharged for actual primes. No ESD changes.


## Hyperfabric / hypervoxel / p-adic / cubie strengthened twin-prime steelman (31 October)

**Actual source owners inspected (not invented):**
- `DASHI.Foundations.RecursiveRadixHypervoxel`: rank-vs-depth indexed `TernaryAddress`, `coarsen`, `fineBlock`, `AddressSuffix`, `joinAddress`, and `SubSuperVoxel.fineAddressIsJoin`.
- `DASHI.Geometry.HypervoxelAdicYoungFibonacciBridge`: distinct hypervoxel `Cell/Scale/State`, `AdicChart` valuation/residue/parent and BT braid/shadow; this is a typed relational bridge, **not** an asserted analytic isomorphism between number-theoretic p-adics and spectral measures.
- `DASHI.Foundations.TrialecticStageThirteenMarkedC3CubieExact`: actual 27-cubie rotation, reflection, order-three and conjugation laws; the Stage-13 name/number does **not** identify an Ogg, Monster, or Hardy–Littlewood object.
- `DASHI.Foundations.BalancedTernaryAntipodalOrbitExact` + `BalancedTernaryAntipodal369OrbitHierarchyExact`: canonical `27=1+13×2` antipodal quotient, centre fixed, retained sign on 13 nonzero orbits. This is distinct from the `9×2+9` oriented z-face chart and the A027907 spectral 13 count.
- `DASHI.Moonshine.JInvariantSheafHyperformAdmissibleDescentExact`, `JInvariantAnalyticHyperformChartGluingExact`, `QueryFactorisationSufficiency`: chart restriction/overlap and consumer factor-through owners.

**Original state is history-rich.** It is not an isolated prime sample. Represent a pair state by the original `n`, the actual `Lambda(n)` and `Lambda(n+2)`, its *shift-two relation*, signed complex phase and shell cross-terms, a variable-rank/depth hypervoxel address, canonical antipodal orbit+sign (with independent fixed centre), and the residual suffix required to reopen every projected chart. Quotienting to one-point marginals is explicitly **inadmissible** for the pair consumer and should never be the main proposal.

**Forward BIDI (typed goals, not new axioms):**
`actual Lambda paired state` → `(coarse hypervoxel address, relative suffix, signed antipodal orbit and fine phase)` → `admissibly glued local signed two-point sections` → `global C_2(n)=Lambda(n)Lambda(n+2)` → `S(X)=sum C_2(n)`.
The former three arrows demand source-level exact reconstruction and typed seam cocycles; the last demands real finite-sum/ordered-ring interpretation.

**Backward BIDI:** specify the actual prime-pair consumer first. Derive minimal acceptable chart/jet/depth, splitting a fibre whenever two *histories* carry equal coarse charts but different pair readouts. Use `FactorsThrough` and consumer-indexed collision from existing owners. Derive the inverse transform and numerical conditioning requirements from a specified signed remainder **before** declaring a chart sufficient.

**Quantitative steelman:** retain all real signed correlations across scales; require a uniform bound on the *actual* arithmetic signed remainder, or unbounded positive prime-only correlation. A finite 13×2 antipodal/cubie or 10-jet SSP representation cannot by itself imply infinitely many prime pairs. In particular, one cannot identify all arithmetic primes with the 15 SSP lanes. Riemann–von Mangoldt and Keating–Smith zero-pair inversion must be instantiated on a genuine global analytic scalar with correct smoothing/tails/singular series.

**Additional acceptances**: TH01 imported parent/suffix BIDI; TH02 actual 13-pair+centre sign chart; TH03 signed relation-preserving 9/18/27 and cubie transition; TH04 typed overlap cocycle and consumer descent; TH05 finite Fourier shifted pair reconstruct; TH06 certified norm/error propagation across adaptive depth; TH07 joint zeta-zero/arithmetical two-point smoothing and inversion; TH08 actual `P(X)` unbounded (T0) or `S(X)~2C2X` (T3). TH01–TH04 reuse owners but require actual twin-prime instantiation; TH05–TH08 remain theorem obligations. No ESD edits.


## Complete executable-facing formalism — twin-prime steelman v3

### 0. Original history and signature

Let `H_n` be the entire admissibly transported *original* arithmetic history, including `n`, its full relevant prime-power provenance, `Lambda(n)`, `Lambda(n+2)`, the shift-two edge, signed complex harmonics, multiplicity, resolved/unresolved status and recursively refinable hypervoxel address. The scalar `Lambda` is the actual `RiemannVonMangoldtSpecification` producer once a faithful ordered real/log implementation is supplied. A bare input `n` or a one-point quotient is not the state.

For each rank `r` and depths `d,e`, reuse `RecursiveRadixHypervoxel`:
`coarse : TernaryAddress r d`,
`suffix : AddressSuffix r e`,
`fine = joinAddress coarse suffix : TernaryAddress r (d ⊕ e)`.
Do not identify radix with primality; p-adic `AdicChart p` is a separately typed refinement and may require a domain-specific intertwiner.

### 1. Consumer and exact finite identities

`pair(H_n) := Lambda(n)*Lambda(n+2)`.
`S(X):= sum_{n+2<=X} pair(H_n)`.
`P(X):=sum_{p+2<=X; p,p+2 prime} log(p)*log(p+2)`.
`E(X):=S(X)-P(X)`; prove `E(X)>=0` for the genuine real `Lambda` and `E(X)=o(X)`, treating proper prime powers explicitly.
`Pi2(X) := #{p <= X-2 : p,p+2 prime}`.
Exact T0: `(forall B, exists p>B, prime(p) & prime(p+2)) <=> P(X) unbounded`.
Strong T3: `S(X)=2*C2*X + o(X)`, where `C2=prod_{q>2}(1-1/(q-1)^2)`.
T3 ⇒ T0 after `E=o(X)`, and ⇒ twin-pair counting asymptotic by rigorous weighted partial summation.

### 2. Genuinely joint Fourier/winding object

For a window `W_X`, `f_X(n)=Lambda(n)*1_W(n)` on a cyclic group of length `M>2X+4` with zero padding. `F_X(k)=sum_n f_X(n) exp(-2*pi*i*k*n/M)`. Define
`S(X) = (1/M) sum_k |F_X(k)|² exp(-4*pi*i*k/M)`
under the exactly specified no-wrap window and index convention, with real extraction. A Littlewood–Paley shell decomposition `F=sum_j F_j` requires the **full mixed terms** `F_j conj(F_l)`, not only `|F_j|²`. All signed terms plus phase, overlap, shifted pair provenance and remainder survive each quotient. The winding derivative history at C3 is the existing finite SSP15 pilot, not an all-prime transform.

### 3. Canonical symmetry and hyperfabric joining

For the 3-trit cubie, `T3^3 = {0} ⊎ (AntipodalNonzero13 × Sign2)`; the unique centre is not double-covered. The nine-sheet has five antipodal orbit classes. Preserve choice of gauge versus retained sign as a **consumer-driven decision**. The z-face decomposition 9×2+9 is a chart, **not** this quotient. A join `G(U,V)` is admissible only if: (i) signed fine sections agree after restriction to overlaps, (ii) witness `joinAddress(coarse,suffix)=fine`, (iii) cocycle compatibility holds on triple overlaps, (iv) the genuine pair consumer factors through the retained join, and (v) a uniform analytic remainder bound is carried through the join. Existing `JInvariantSheafHyperformAdmissibleDescentExact`, `QueryFactorisationSufficiency`, `BalancedTernaryAntipodalOrbitExact` own the generic terms; instantiated arithmetic estimates are not inherited from them.

### 4. Forward / backward BIDI proof graph

Forward `H -> refinable (coarse,suffix,13-sign orbit,complex phase) -> admissible joined history -> exact pair consumer -> cyclic Fourier reconstruction -> signed global S(X) -> T0 or T3`.

Backward `target T0/T3 -> required uniform arithmetic error budget -> zero-pair/prime-pair correlation strength -> admissible Fourier shell and overlap requirements -> minimal consumer-sufficient hypervoxel depth/jet and preserved residual -> H`.

Fourier coefficients must reconstruct the true arithmetic **joint** observable; do not infer positivity from an individual sample or from unsigned shell energies. Keating–Smith zero-pair inversion (2019) motivates the missing analytic producer but is heuristic until quantitative smoothing/inversion/singular-series error terms are discharged.

### 5. Concrete reusable implementation owners and final lemmas

`DASHI.Core.TwinPickoverHistoryHypervoxelTransportExact` is a shared history/voxel transport source module, using `RecursiveRadixHypervoxel.joinAddress`, `coarsenAfterRefine` and exact original consumer. `TwinPrimeActualPairSectionGluingExact` instantiates the actual abstract von Mangoldt pair consumer; `TwinPrimeResidualMangoldtBidiExact` owns exact period/residual transport. Together with the canonical antipodal owners, these implement finite representation contracts.

Remaining **specific mathematical lemmas**:
- TP-A: kernel-check all source-written import and typed joining interfaces, including generic history transport.
- TP-B: finite cyclic exact complex Fourier autocorrelation at shift two, with shell cross-terms and no-wrap.
- TP-C: build genuine prime-weighted scalar, endpoint convention and `E(X)=o(X)`.
- TP-D: actual two-point zero-pair ↔ prime-pair transform with smoothing/regularisation, overlap cocycles, and error bound.
- TP-E: demonstrate *arithmetic* signed remainder `o(X)` or at least infinite prime-only positive slabs; this is the terminal **hard open theorem**.
- TP-F: weighted/unweighted asymptotic and reverse T0 BIDI, with explicit multiplicative constants.
- TP-G: quantitative conditioning/interval error of the 10-jet finite SSP pilot and a justified transfer to the all-prime producer if such a map exists.
No assumptions or Boolean status receipts may stand in for TP-E.

## Implementation continuation: exact arithmetic-history ↔ period-code hypervoxel BIDI

New `DASHI.Arithmetic.TwinPrimeHypervoxelPeriodConsumerBidiExact` reuses the original `NatPeriod270` period/residual codec and `RecursiveRadixHypervoxel` address/suffix objects; this is materially stronger than a tautological consumer equality on one retained state. Its `encode` and `decode` have actual inverse laws `decodeEncode` and `encodeDecode`. Both original `n` and coarse/fine suffix survive exactly, and `finePreserved` proves exact refined-address reconstruction. The generic consumer forward/backward laws apply to the **actual pair** via `actualMangoldtPairForward` imported from `TwinPrimeActualPairSectionGluingExact`.

Crucial distinction: no proof of `FactorsThrough` for a *coarse-only* observer and no arithmetic positivity. Original histories and fine residuals survive without collapsing into marginal signals. This closes a meaningful representation-side obligation; the remaining analytical steelman is unchanged: exact signed Fourier shift-two reconstruction, faithful real `Lambda`, unbounded prime-only correlation and/or `S(X)=2C2X+o(X)`. Source-written, not compiler verified.


## Exact group-ring shift-two finite verification — 31 October continuation

`scripts/check_twin_prime_cyclic_group_ring_shift_two.py` is a concrete integer-only finite check of the group-algebra identity: in `Z[t]/(t^M−1)` with `F(t)=Σ f_n t^n`, the coefficient of `t^{M−2}` in `F(t)F(t^{-1})` is `Σ_n f_n f_{n+2}` provided the zero-padded support avoids wrapping. Fourier evaluation at Mth roots of unity transforms the same product to `|F̂(k)|²` and gives its familiar signed-phase inverse after proving complex character orthogonality. The script checks prime-indicator samples and explicit mixed-shell `g,h` terms. This is an exact **finite** group-ring precursor to TP-B; it does not instantiate the real-log `Lambda` producer, prove general Agda DFT inversion, or discharge the analytic asymptotic TP-E. Existing `NSTriadKNLuoFiniteFourierParsevalFromInversionExact` is a separately inspected finite rational Fourier owner; do not duplicate generic algebra unless necessary.


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


## 31 October latest Pareto cut — faithful SSP ultrametric necessity (source-implemented)

`DASHI.Geometry.SSPJetExistingOwnerTransportExact` now reuses original `SSP369Ultrametric` and `ConsumerIndexedResidualRefinementExact`. It defines `FaithfulSSPAddress` as an explicit, **non-automatic** injective map from an arbitrary actual history carrier to `SSP.Address depth`; `faithfulAddressConsumerSufficient` proves that such an encoding preserves **every** consumer of the original history; and `coarseCollisionRequiresAddressDistinction` imports the existing necessity theorem to prohibit two consumer-relevantly different histories from having the same faithful encoded address. Existing `zeroDistanceConsumerAgreement` also transports zero ultrametric distance to all consumers on the finite typed address.

This is an actual consumer-indexed statement but it is intentionally **conditional**: neither an arbitrary signed SSP15 valuation history nor real Bishop sine phase can inject into a fixed finite 3^depth address. They need a bounded-history domain, a variable-depth representation, or a retained unbounded residual. Thus proving such a faithful encoding for the full unbounded terminal consumers remains OPEN; do not assume it simply by declaring an address. These source changes do not establish a ten-derivative analytic jet inverse or uniform prime-pair asymptotic.

No CI or compiler run. Source written on PR #1408 at commits `f753662b046a2018e997c56d0f989aeb8252969c` and `3e46cac8253638931a25bbb1f6e8c07814cba756`, kernel verification pending. Further work should first reuse existing `SSP15PrimeValuedStateExact` and `SignedSSPFRACTRANWeaveExact` to specify the faithful *bounded* historical domain and only then project to C3 jets.


## 31 October actionable handoff: native signed SSP15 source, no duplicate jet system

`DASHI.Biology.SSP15SignedHistoryConsumerBidiExact` is now source-written over **existing** `SignedSSPFRACTRANWeaveExact.SSPValuation`. Its `encode` retains sign orientation and the original signed multiplicity as an explicit residual, `decodeEncode` preserves the original, `retainedObserverSufficient` yields all-consumer sufficiency, and `signCollisionForcesSignedResidual` pays the native consumer-collision necessity condition. It is lossless rather than minimal and does **not** pretend a finite address contains every unbounded magnitude. In parallel the existing `SSP369Ultrametric` remains the primary observer/refinement owner; the C3 ten-derivative matrix is a specialized finite certificate, **not** the original notion of jet.

**Practical verification and future-work entrypoint:** `Docs/roadmaps/SSP15_Ultrametric_Jet_Consumer_Handoff_20261031.md` contains source ordering, Python commands, Agda commands, the typecheck/safety boundary and precise remaining kernel/analytic cuts. This is a source-ready handoff, not an Agda-kernel-verified or terminal-conjecture-complete proof.
