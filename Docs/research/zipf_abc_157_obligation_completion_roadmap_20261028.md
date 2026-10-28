# Zipf family / original ABC and 27 cube: bounded release obligation manifest

**Reviewed 28 October 2026, PR #1275**, source head `8deaa303da109ef220cea308a211781aecf130b9` before this roadmap commit. This document is a **dependency and verification contract**, not a proof receipt or a claim of discovering classical laws. There are **157 named top-level obligations**: finite F01–F24, optional analytic F25–F27, history H01–H16, sampling S01–S28, completion C01–C18, ABC/369 A01–A30, original subject T01–T27, optional physical/TOE B01–B11.

**What is implemented:** all T01–T27 have an operational source/API and negative-control coverage. The original Sept-2026 SSSP ABC six-permutation, 6→3 minimum and reversible 3×2 tail code are REUSED, not reauthored. F13b `ConcreteAddLaw` is now source-written using existing Agda stdlib reduced/unreduced rationals; finite Hurwitz fold consumes it. H08 all-prefix extremal and S24 full-history majorization have executable exact rational constructions. The 27→5→4 equality-pattern / Heaps observation factor and S2/S3 collision moments have source-written/finite implementations. **No exact-head Agda compilation**: NONE of these new source-written statements is promoted as kernel-checked. The existing probability identity-paid Bool remains false. Earlier local mathematical checks are not a full checked-out branch test receipt.

## Explicit completion requirements

A numbered row is complete at the **finite formal theorem tier** only when its exact Agda statement imports the earliest compatible original source owner, typechecks without postulates/holes/unsafe escapes at a frozen SHA, and the corresponding executable consequence (when applicable) passes against the same exact HEAD. For observational T rows, completion of the finite *contract* is different from authentic empirical replication. Never promote synthetic examples, shared integers or a fitted exponent to a physical or Monster same-object proof. CI green is not required; a direct local compiler transcript is.

| Lane | Named obligations | Present source status | Actual blocker |
|---|---:|---|---|
| F01–F24 | 24 | finite arithmetic/PNF source terms; F13b written | compatible exact-HEAD Agda kernel |
| F25–F27 | 3 | finite tail numerical checks and analytic domain ledger | optional real/complex analytic results, not finite release |
| H01–H16 | 16 | executed finite witnesses; H13–H15 source-written | general Agda H08/H10/H12 and kernel receipt |
| S01–S28 | 28 | finite exact PMFs, S24 rational pair/chain certificates | universal Agda measure/sampler/quantile/gluing proof |
| C01–C18 | 18 | finite exact Python completion and rare-tail proofs | reusable Agda inclusion–exclusion/stability |
| A01–A30 | 30 | original SSSP reuse plus new ABC/27/5→4 adapters | compile new Agda terms; formalize general RGS/moment laws where claimed |
| T01–T27 | 27 | operational subject/source registry | immutable full-corpus and held-out empirical claims distinct |
| B01–B11 | 11 | existing independent external/repository owners, optional | prohibit unjustified physical/RH/Monster same-object weld |

## Exact lemma checklist

### F lane

- **F01** — rank-positive.
- **F02** — integer power positivity.
- **F03** — positive-denominator raw fraction interpretation.
- **F04** — positive denominator product.
- **F05** — normalized rational addition homomorphism F13b.
- **F06** — raw finite-sum homomorphism.
- **F07** — positive shifted rank weight.
- **F08** — source weight equals ℚ reciprocal.
- **F09** — finite Hurwitz denominator nonzero.
- **F10** — K>0 positive normalizer.
- **F11** — normalized mass nonnegative.
- **F12** — finite mass sum=1.
- **F13** — actual PNF ProbabilityAtom bridge.
- **F14** — q=0 unshifted Zipf specialization.
- **F15** — CDF prefix identity.
- **F16** — CDF bounds and monotonicity.
- **F17** — quantile least-crossing proof.
- **F18** — finite moments exact.
- **F19** — shifted integer-binomial moment identity.
- **F20** — finite Hurwitz split.
- **F21** — one-term Hurwitz recurrence.
- **F22** — head conditioning and TV vs L1.
- **F23** — frozen-label likelihood with zero-data refusal.
- **F24** — rare tail absent h^t.
- **F25** — optional real-exponent rank PMF.
- **F26** — optional correctly shifted infinite Hurwitz tail.
- **F27** — optional analytic Hurwitz difference.

### H lane

- **H01** — histogram invariant under token permutation.
- **H02** — binary novelty increments.
- **H03** — sorted-count prefix capacity.
- **H04** — sharp lower prefix envelope.
- **H05** — sharp upper prefix envelope.
- **H06** — grouped lower-curve witness.
- **H07** — first-appearance upper-curve witness.
- **H08** — joint all-prefix sharp bounds.
- **H09** — birth-time sum identity.
- **H10** — integrated Heaps area gap.
- **H11** — count majorization/transfer equivalence.
- **H12** — envelope/area Schur order.
- **H13** — histogram cannot determine chronology.
- **H14** — full Heaps curve ↔ novelty flags.
- **H15** — full curve+histogram cannot recover repeated identity.
- **H16** — unigram does not determine block entropy.

### S lane

- **S01** — finite IID word-law normalization.
- **S02** — IID absence geometric power.
- **S03** — IID expected vocabulary.
- **S04** — IID expected novelty increment.
- **S05** — IID expected second difference nonpositive.
- **S06** — two-draw collision power sum.
- **S07** — IID exact occupancy variance.
- **S08** — uniform physical-token permutation projection.
- **S09** — hypergeometric absence.
- **S10** — permutation expected vocabulary.
- **S11** — permutation two-draw collision.
- **S12** — permutation occupancy variance.
- **S13** — two-sampler two-draw expected difference.
- **S14** — IID full distinct-count PMF coefficient.
- **S15** — permutation full distinct-count PMF coefficient.
- **S16** — PMF normalization and moments.
- **S17** — positive concentrating count transfer.
- **S18** — common pair versus other draw schedule.
- **S19** — pair second-type switch law, separate samplers.
- **S20** — switch-tail convexity/Pascal inequality.
- **S21** — positive HLP transfer-chain reachability.
- **S22** — expected vocabulary Schur concavity.
- **S23** — single-time stochastic dominance.
- **S24** — simultaneous full-prefix path coupling and gluing.
- **S25** — Zipf-exponent likelihood ratio/majorization.
- **S26** — conditional IID Zipf exponent discovery order.
- **S27** — novelty-increment monotonicity no-go.
- **S28** — variance monotonicity no-go.

### C lane

- **C01** — inclusion-exclusion over absence events.
- **C02** — IID completion CDF.
- **C03** — permutation completion CDF.
- **C04** — completion iff V_t=K.
- **C05** — geometric completion-tail mean step.
- **C06** — hypergeometric hockey-stick sum.
- **C07** — IID expected completion time.
- **C08** — permutation expected completion time.
- **C09** — union bound for missing types.
- **C10** — completion stochastic ordering via S23.
- **C11** — top-two frequency completion no-go.
- **C12** — finite common-support TV maximal coupling.
- **C13** — IID prefix path TV stability.
- **C14** — minimum token relabel distance.
- **C15** — permutation prefix path TV stability.
- **C16** — completion event stability from prefix bounds.
- **C17** — small TV but divergent mean-completion ratio.
- **C18** — zero support/unknown tail no-promotion.

### A lane

- **A01** — original six SSSP linear extensions.
- **A02** — original pairwise nine-cell order sheets.
- **A03** — original six-to-three minimum quotient.
- **A04** — reversible original three-by-two tail codec.
- **A05** — actual S3 group and proper C3 subgroup.
- **A06** — S3 braid image vs analytic monodromy.
- **A07** — six orders share complete Heaps curve.
- **A08** — Heaps cannot recover first named type.
- **A09** — Heaps cannot recover tail orientation.
- **A10** — canonical signed-cube ↔ original LevelTwoCode round trips.
- **A11** — coordinate S3 ten-orbit classification.
- **A12** — coordinate C3 eleven-orbit classification.
- **A13** — value-label S3 five equality-orbit classification.
- **A14** — original seven endomorphism conjugacy shapes.
- **A15** — 162 value relabelings preserve full Heaps curves.
- **A16** — axis permutation changes full Heaps curve.
- **A17** — equal Heaps yet different conjugacy-shape no-go.
- **A18** — twenty-seven-to-five equality-pattern representatives.
- **A19** — five-pattern to four-Heaps exact factor.
- **A20** — S3 invariance and five-to-four no inverse.
- **A21** — uniform 27-word Heaps fibres 3/6/12/6.
- **A22** — conditional uniform six ABC orders.
- **A23** — general restricted-growth strings and value-Sq orbits.
- **A24** — Stirling falling factorial named-word total.
- **A25** — all-q,n number of distinct Heaps histories.
- **A26** — three-to-five vs five-to-three typed distinction.
- **A27** — nonuniform S2/S3 five-pattern four-Heaps PMF.
- **A28** — conditional K first draws all-distinct uniform K! order.
- **A29** — unconditional Plackett–Luce ranking distinct from conditional law.
- **A30** — no 720/Monster/RH/NS or equal-count object promotion.

### T lane

- **T01** — Zipf law.
- **T02** — 90-9-1 participation.
- **T03** — Benford digits.
- **T04** — Bradford zones.
- **T05** — brevity association.
- **T06** — demographic gravity.
- **T07** — word list.
- **T08** — Gibrat growth.
- **T09** — hapax.
- **T10** — Heaps/Herdan.
- **T11** — Hilberg entropy.
- **T12** — historical recurrence.
- **T13** — King effect.
- **T14** — long tail.
- **T15** — Lorenz/Gini.
- **T16** — Lotka.
- **T17** — Menzerath–Altmann.
- **T18** — Pareto Type I.
- **T19** — Pareto principle.
- **T20** — Price law.
- **T21** — least effort.
- **T22** — rank-size.
- **T23** — Stigler eponymy.
- **T24** — letter frequencies.
- **T25** — common English words.
- **T26** — Zipf–Mandelbrot.
- **T27** — Hurwitz zeta.

### B lane

- **B01** — existing 3D Fourier-shell cardinality.
- **B02** — actual labeled wavevectors to energy shells.
- **B03** — conditional sufficient Sobolev norm threshold.
- **B04** — two-sided spectra converse with assumptions.
- **B05** — divergence-free/reality preservation.
- **B06** — equal magnitude ranks not enough for nonlinear pressure.
- **B07** — uniform cutoff/time energy-envelope assumption.
- **B08** — strong-solution continuation under exact PDE norms.
- **B09** — correctly shifted analytic Hurwitz difference.
- **B10** — real geometric RG carrier/measure/refinement map.
- **B11** — Monster 3B same-object injective representation (not proved).

## Topological dependency order / gates

1. **R0 receipt:** freeze/reconcile PR #1275 against master; keep ESD surfaces unmodified. The acceptance runner currently names 26 Python test modules. Run every one against this checkout; run Agda 2.9 with its actual compatible experimental stdlib and log the full canonical `DASHI/Statistics/ZipfFamilyEverything.agda` import graph. Do not confuse historical green receipts with this HEAD.
2. **R1 algebra:** F01–F14, especially F03–F06 and positive-denominator F13b `positiveDenominatorAddHomomorphism`→`concreteHurwitzSourceWritten`→canonical PNF probability mass. Change the source-paid flag only after actual kernel verification.
3. **R2 source data/ABC:** A01–A10 import source-owned SSSP/27 cube and validate both round trips. H01–H08 all-prefix sharp witnesses; H14/H15 exact novelty/no-go.
4. **R3 non-weld:** A11–A30 show action-sensitive quotients and actual five→four Heaps factor; preserve S3≠C6, four different group actions, quaternion PR #1414 and Fourier PR #1407 as separate owners.
5. **R4 probability:** S01–S16 owner-backed independent IID vs fixed-multiset distributions, then S17–S24 positive HLP transfer, switch-time convexity/quantile, common draw schedule, conditional marginals and exact coupling gluing. S23 marginal dominance alone DOES NOT prove S24.
6. **R5 completion:** S25–S28 and C01–C18 completion/error, negative controls and zero-support gates, all with sampler scopes.
7. **R6 original 27:** T01–T27 finite diagnostic contracts, original primary-source owner/date and falsifiers; source-identified full data, tail, timestamp, tokenization, fixed train/holdout and plausible alternatives for *each empirical claim*. The current top-30 Moby-Dick fixture is NOT a whole corpus or temporal sequence.
8. **R7 publish:** archive exact hashes/Agda stdout, distinguish source-written vs executed vs kernel verified vs empirical replication vs historical proof ownership; merge finite release only after its actual acceptance gates. B01–B11 and F25–F27 are OPTIONAL independent scientific bridges, not release blockers.

## Attribution

Classical sources retain priority: Estoup/Zipf, Mandelbrot, Hurwitz, Herdan/Heaps, Pareto/Benford, Bradford, Lotka, Menzerath/Altmann, Price, Gibrat, Luce/Plackett, Hardy–Littlewood–Pólya, Strassen, Stirling/Burnside/Pólya and their primary-source dates. Earlier DASHI 1 September 2026 SSSP authors, existing PNF/ternary/conjugacy proof owners, PR #1414 polynomial monodromy/quaternion owners, PR #1407 Fourier owners, and original Ibrahim Monster 3B owners are not overwritten. This roadmap/document assembly was prepared for the user with OpenAI ChatGPT assistance, 28 October 2026.

**Stop status:** finite operational coverage exists; **release not fully complete** because exact-head Agda kernel, universal H08/S24/C closure and empirically sourced replication remain outstanding. No general analytic continuation, Navier–Stokes, RH, or Monster same-object representation is supplied by counting coincidences.


## Supplemental distinct owner: #1244 native ternary LOCAL gauge versus A-lane GLOBAL value symmetry

The user's clarified native balanced-ternary end model `K3=C3_sector×Trit^N` has a genuine addresswise phase action `G_n=Map(X_n,C3_phase)`. **Canonical #1244**, not this Zipf PR, owns the original local gauge and injective fibre refinement; it now also contains an additive semidirect/cylinder setoid extension. In the established A15/A19/A20 Zipf proofs, global value S3 (and its C3 subgroup) preserves equality patterns and the full Heaps curve. That is **strictly weaker** than invariance under the full independent `G_n` local translations. Root-sector example `(0,0,0)→(0,1,0)` changes complete Heaps from `(0,1,1,1)` to `(0,1,2,2)` when a local gauge acts at only the middle address; simultaneous global addition preserves the former curve. The original #1244 torsor transitivity and the new extension show an observable invariant under **all** local translations and respecting pointwise equality would be constant. This is a genuine typed NO-GO on equivariance, not a same-object match from `3^27`. See #1244's `Docs/topology/AlexanderHornedNativeTernaryLocalPhaseFibreMaxCut20261028.md`. No #1244 code is copied into #1275; A-lane obligations remain unchanged at 30, total remains 157, Agda and empirical gates remain pending. Distinct #1414 monodromy/spin and Ibrahim Monster 3B owners retained.


## 28 October 2026: actually proved orbit-transport crosswalk from canonical #1244 owner

The original A13/A18/A19 value-relabel quotient has a new structurally correct relationship to the native end-sign quotient on #1244. Let three labels carry the actual cyclic C3 chart. For any **n+1-letter** named word `w=(a0,a1,...,an)`, fix the first value as an anchor and calculate relative digits `δ_i=a_i−a0 mod3` for i=1,...,n. A global C3 translation of the word leaves all differences fixed; the remaining label reflection acts by simultaneous sign reversal of all n differences. Conversely, if two relative sequences agree up to sign s∈{±1}, the actual affine S3 translation `t=b0−s*a0` takes the whole first named word to the second. Thus **the orbit sets really are equivalent**: `T^(n+1)/S3_value ≅ T^n/C2_sign`, and `Σ_{k≤3} S(n+1,k)=(3^n+1)/2`. This explains the previously matching rank counts 1,2,5,14,41,122,365 structurally. It does NOT equate the raw orbit group actions, the source word measures, the Heaps curves, the horned exterior geometry, or any Monster/RH/Spin representation.

Canonical implementation owner is separately authored [#1244](https://github.com/chboishabba/dashi_agda/pull/1244): `AlexanderHornedS3WordSignOrbitTransportExact.agda`, with source-written `normaliseTranslate`, `normaliseReflection`, `signedRelativeSection`, and TWO reciprocal orbit-relation witnesses `signedOrbitToGlobalS3`/`globalS3ToSignedOrbit`. The attached exhaustive integer oracle verifies 9,840 named words and 59,040 value-S3 transformations, including an explicit inverse affine witness per word. The original 157-obligation Zipf/ABC roadmap count DOES NOT change, because this implements a stronger reusable A-lane crosswalk rather than a new empirical Zipf family or a new physical theorem. All Agda code is kernel-pending; no unmerged source copied into this branch; prior original ABC SSSP/Ibrahim ownership unchanged.
