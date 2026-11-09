# DASHI — Monster V2, Moonshine V0.4/V1 and YM B1/E1/B2: exact source-owner max-cut

Date: 2026-11-09. Source heads checked: Moonshine/Y443 PR #1472 `agent/y443-monster-vnatural-maxcut-20261106`; Yang–Mills/Clay PR #1444 `research/ym-voyager2026-completeness-crosswalk-20261101`.

## Authority, statuses and acceptance

- **SOURCE-WRITTEN** means a named proof term/module exists in the GitHub branch; no Agda kernel acceptance claimed without a pinned receipt.
- **CONDITIONAL** means an actual-source mathematical or physical witness still must be provided and cannot be replaced with a postulate or an arbitrary inhabitant.
- **OPEN** means the original endpoint does not follow.
- Use the same selected group, quotient, VOA, Wilson family and OS Hamiltonian in each claimed theorem. No same-cardinality/group-order shortcuts. No 3+1/KK/TSVF promotion to Euclidean YM Clay.
- Golden validation and Agda 2.9 safe-transitive checks required. Do not use CI as a substitute for source review. Keep ESD surfaces untouched.
- Attribution: Ivanov/Bray/TauCeti for Y443 presentations; James Michael DuPont (JMD/meta-introspector) for the ten-step two-generator source; Dong–Griess–Lam and FLM; Popov–Rastelli for their Lean VOA construction; Wilson, Bałaban and Osterwalder–Schrader for Yang–Mills.

## Phase M2: Universal original Monster quotient and selected group

| Exact declaration/target | Existing owner and status | Remaining proof/result |
|---|---|---|
| `Y443CoxeterPresentationExact.monsterRelators` | SOURCE-WRITTEN original 80 actual words (78 Coxeter + spider + central) | Kernel receipt and source interpretation |
| `Y443Universal80RelatorCongruenceExact._≈₈₀_` | SOURCE-WRITTEN least group congruence on **original signed node words** | Kernel acceptance |
| `least80Congruence`, `canonical80SetoidGroup`, `original80IsAdmissible` | SOURCE-WRITTEN leastness and explicit setoid group; not `Set` quotient | Kernel acceptance; identify with a permitted concrete quotient carrier if downstream needs definitional equality |
| `Interpretation.sound`, `interpretationProduct`, `interpretationInverse` | SOURCE-WRITTEN original-relator-compatible homomorphism into selected G | Kernel acceptance |
| `Interpretation.selectedSurjection` | CONDITIONAL on `PresentedByY443Nodes` | Inhabit *actual selected group* signed-word surjectivity |
| `Interpretation.NoExtraSelectedRelations.reflectsEquality` | **OPEN decisive M2-01** | For actual G, prove `eval x ≡ eval y → x ≈₈₀ y` for all original words, i.e. no extra kernel beyond the original presentation |
| `SelectedEquivalence.toAfterFrom`, `fromAfterTo`, `fromPreservesProductModulo80`, `fromPreservesInverseModulo80` | SOURCE-WRITTEN conditional on original surjectivity and `reflectsEquality` | Inhabit both sources and kernel-check |
| `Y443PublishedQuotientIsoCompositionExact.Selected.SamePublishedQuotient` | CONDITIONAL composition already existing | **M2-02:** Construct historical quotient-to-published Monster isomorphism from genuine Ivanov/Bray authority, not from relator counting |
| `Y443FLMCanonicalReferenceFromQuotientExact.Selected.SourceAuthority` | CONDITIONAL already exists | **M2-03:** Selected original group action identification, faithfulness and actual quotient-to-Monster comparison |

**M2 deliverable:** an actual original-source group isomorphism `G_selected ≅ Q_80 ≅ M_published`. The previous `Y443JMDPresentedVNaturalCapstoneExact.wholeGroupTwoGenerated` and `sameLiteralVNaturalActionWord` already cover conditional u/v representation/action and must not be rebuilt.

**Negative control:** the 79-relator Y443 spider presentation represents the historical Monster × C2, not the Bimonster (Monster × Monster) ⋊ C2; the 80th central quotient targets Monster. User-reported Y555 content should be inspected independently before new Y555 work, not inferred from the generic `FiniteWreathRefinementExact`.

## Phase V0.4: actual paired/orbifold VOA operators

| Exact current owner / proposed proof lemma | Status | Necessary source result |
|---|---|---|
| `VNaturalOrbifoldConstruction.SelectedPairedGradedModule.OriginalFixedVOAAndTwistedEvenSource` | CONDITIONAL | **V0.3-01:** actual twisted-even additive, inverse, scalar, grading and original-sector equivalence |
| `VNaturalOriginalPairedFourSectorModesExact.Selected.fixedModeIsOriginal` | SOURCE-WRITTEN | Original FF correctly reused; no new operator |
| `Selected.OriginalMixedSectorIntertwiners.fixedTwistedIsOriginal` | CONDITIONAL | **V0.4-01:** genuine twisted-module integer-index restriction and closure on original twisted-even sector |
| `Selected.OriginalMixedSectorIntertwiners.twistedFixed` | **OPEN V0.4-02** | Construct original TF intertwiner, with original-mode identities and actual Leech theta twist |
| `Selected.OriginalMixedSectorIntertwiners.twistedTwisted` | **OPEN V0.4-03** | Construct original TT intertwiner into fixed sector |
| `Selected.pairedVertexData`, `pairedModesAreNativeOriginalModes`, `fromNativeSources`, `nativeSourcesAfterFrom`, `fromAfterNativeSources` | SOURCE-WRITTEN structural transport | Kernel check; operators must have genuine source witnesses |
| `originalMixedModeLinearity`, `originalMixedModeGrading` | **OPEN V0.4-04/05**, proposed | Actual bilinearity and weight shift of all four channels |
| `originalMixedVacuumCreation`, `originalMixedTranslationCovariance` | **OPEN V0.4-06/07**, proposed | Actual creation/vacuum and translation for TF/TT |
| `originalMixedLocality`, `originalMixedJacobiIdentity` | **OPEN V0.4-08/09**, proposed | Every mixed-sector Jacobi/locality case, correct branch/twist indices |
| `originalMixedConformalLaws`, `originalPairedMoonshineVOA` | **OPEN V0.4-10/11**, proposed | Conformal structure and complete paired VOA from original sources |

**V0.4 deliverable:** one true linear/graded selected `V^natural`, with all four original mode channels and complete VOA axioms, not a tagged disjoint union or an abstract mode function.

## Phase V1: original all-mode FLM/Popov–Rastelli identification

Existing owners: `Y443FLMConcreteVOAGroupTransportExact.Transport.ExactFLMVOAIsomorphism`, `Y443DGLUniquenessSelectedFLMExact.Selected`, and `Y443FLMCanonicalReferenceFromQuotientExact.Selected`. They are conditional source consumption, not actual selected-object identity.

| Exact original obligation (proposed name) | Status |
|---|---|
| `selectedToFLMOriginalCarrier`; `flmToSelectedOriginalCarrier` | **OPEN V1-01/02**: actual maps |
| `selectedFLMLeftInverse`; `selectedFLMRightInverse` | **OPEN V1-03/04** |
| `selectedFLMVacuumPreserved`; `selectedFLMConformalPreserved` | **OPEN V1-05/06** |
| `selectedFLMAllModesPreserved` | **OPEN V1-07**: `∀ x y n, F (Y_selected x n y) ≡ Y_FLM (F x) n (F y)` |
| `selectedFLMTranslationAndLinearity` | **OPEN V1-08** |
| `selectedPopovFLMVOAIsomorphism` | **OPEN V1-09**, assemble the original `ExactFLMVOAIsomorphism` |
| `selectedCanonicalMonsterActionIntertwining` | **OPEN V1-10**, uses genuine M2 group identification and actual modes |
| `originalAutVNaturalMonster` | **OPEN V1-11**: full automorphism-group equality, not just embedding |

Use actual Dong–Griess–Lam published uniqueness hypothesis alternatives and certificates where these reduce the direct map proof. Do not silently interpret a finite weight-two match as all-mode equivalence.

## Yang–Mills: authoritative physical 23-producer / PH0–PH4 ledger

**Canonical full detail:** [YMClay23PhysicalProducersCurrentMaxCut20261109.md](https://github.com/chboishabba/dashi_agda/blob/research/ym-voyager2026-completeness-crosswalk-20261101/Docs/physics/YMClay23PhysicalProducersCurrentMaxCut20261109.md) on **PR #1444**. The YM ledger names 23 concrete physical producer IDs, more precise than this five-frontier summary. These are *proposed exact obligations* (not verified source declaration names). No term below is promoted from a conditional interface.

### E1 — 7 exact obligations (PH0/PH1/PH3)

- **E1.01** actual UV/IR-changing finite compact Haar/Wilson source and renormalization trajectory; owner `YMClaySUNVariablePhysicalCutoffFamilyExact`.
- **E1.02** fixed-physical-support local gauge-cylinder algebra, scaling/locality/adjoints; finite original arbitrary-length plaquette words already provided by `YMClayE1D1OriginalVariablePlaquetteWordsExact`.
- **E1.03** actual epsilon–N Wilson and multi-point Schwinger convergence; existing `YMClayE1VariableCutoffCylinderLimitExact` is a conditional compiler.
- **E1.04** real same-source reflection positivity from original full fine Wilson R445 data through continuum Gram limit.
- **E1.05** Euclidean covariance, symmetry, regularity, growth and locality for the original limit.
- **E1.06** reconstruct OS Hilbert, vacuum, translations and self-adjoint H of the very same E1 source.
- **E1.07** prove selected continuum is interacting four-dimensional Yang–Mills, not a generic OS-positive field theory.

### B1/D1 — 4 exact obligations (PH2/PH1)

- **D1.01** literal original CMP116 marked-derivative localization applicability on actual physical remote pairs and same full Gibbs family; owner `YMClayD1OriginalRealCMP116VariableCutoffExact`.
- **D1.02** original real mixed-log differentiated source equals true full-Wilson connected covariance; original finite jet and all-word identities are SOURCE-WRITTEN but original analytic source identity remains.
- **D1.03** actual uniform small+large original Gibbs covariance estimate, physical contraction `0 ≤ q < 1`, all required remote pairs, cutoff and volume independence. Need **both** large-field and small-field contributions. Existing conditional `originalWilsonRealCovarianceGeometricBound` is not producer evidence. Preserve `YMClayD1PhysicalRemoteCoverageNoGoExact.ActualPhysicalPairCoverage`.
- **D1.04** same-family original physical covariance convergence preserving exponential bounds; R583 requires literal OS Gram Wilson-product density, OS2 product meaning, source H1 and continuity.

### B2/D2 — 5 exact obligations (PH3)

- **D2.01** same actual reconstructed E1/H OS Hamiltonian and physical energy coordinate.
- **D2.02** positive physical spectral scale stable at UV/IR limits.
- **D2.03** complete nonvacuum spectral detection by dense selected gauge-invariant observables.
- **D2.04** spectral projection exclusion of all values in `(0, Delta)`; no invisible slow modes.
- **D2.05** vacuum, units, domain and no spectral-pollution Clay interpretation for the same H.

### N1 — 3 obligations (PH1)

- **N1.01** genuine fixed-physical-support renormalized local observable in the original continuum.
- **N1.02** noncollapsing nonzero variance/correlation **or** cumulant with true RG loss budget.
- **N1.03** prove the witness belongs to precisely the E1 continuum.

### G1 — 4 obligations (PH4)

- **G1.01** quantify over all externally specified compact simple groups, including relevant global forms.
- **G1.02** actual Haar/Wilson/CMP/RG quantitative original physics for each group.
- **G1.03** complete same-group E1, D2, N1 and route-dependent D1 construction.
- **G1.04** UV/volume estimates uniform within each fixed group; constants may depend on that group.

### YM five-phase exit criteria

| Phase | Completed only when |
|---|---|
| **PH0** | Genuine original finite measure/renormalization family selected |
| **PH1** | Nontrivial 4D interacting original continuum and OS prerequisites |
| **PH2** | Full nonvacuous physically uniform original-Wilson clustering, if using D1 route |
| **PH3** | Same-E1-Hamiltonian positive full-sector spectral gap |
| **PH4** | E1/D2/N1 per arbitrary compact simple G and final physically certified capstone |

## Highest-alpha execution order, no duplicate infrastructure

1. **Monster M2-01** obtain selected-group *kernel reflection* against the now-constructed universal 80-relator setoid group; then the original-to-published Monster identification M2-02.
2. **Moonshine V0.4-02/03/08/09** source TF/TT and mixed Jacobi/locality. Finish the actual paired VOA before pursuing V1 all-mode identification; DGL uniqueness may replace one direct iso route when real hypotheses are inhabited.
3. **YM E1.02/03 and D1.01/03 in parallel**: actual fixed-support cylinder limit, physically nonvacuous original CMP116 domain and small/large source estimates. These are the original high-uncertainty analytic tasks, not R583/R445/BCH transport.
4. **YM D2.01–05**, then **N1/G1**: same E1 source and spectral completeness. No finite-test-only gap promotions.
5. Exact-head Agda `--safe` / `parallel_checker`, transitive physical-source authority audit, numerical negative controls, synchronized docs and attribution.

Status at authoring: the universal 80-relator **setoid group and conditional selected-group two-sided correspondence** are source-written in `Y443Universal80RelatorCongruenceExact.agda`; their Agda kernel receipt is not observed, and **M2-01 kernel reflection remains OPEN**. The genuine TF/TT and physical YM estimates have not been established in this documentation pass.


## Latest source-only SU(2) B1/D1 refinement from #1444

[Original SU(2) Wilson one-link coherent-staple tail (9 November)](https://github.com/chboishabba/dashi_agda/blob/research/ym-voyager2026-completeness-crosswalk-20261101/Docs/physics/YMClaySU2OriginalOneLinkCoherentStapleTail20261109.md) derives an original one-link *conditional* bound `P(t(UV)≤0 | staples) ≤ 3 exp(-βR/2)` for staple resultant norm `R≤6`, and the genuine pointwise action penalty `D₆ ≥ 6-R`. It separately exhibits a bare-link ultraviolet Dobrushin limitation; that does **not** rule out blocked gauge-invariant CMP116 clustering. The missing D1.03 original full-Gibbs source is now sharp: prove a uniform frustrated-staple probability bound **and** distance-dependent connecting polymer/bridge entropy estimate for the full Wilson covariance. A conditional single-link tail is not this result.

This source audit was added after the original five-frontier inventory and does not change the open Clay physical status.


## 9 November 2026 — attached YM-worker reconciliation and new original-action bound

The user's attached worker audit is incorporated with the correct **minimal Clay endpoint**: **C1/E1** interacting 4D continuum QFT with its axioms; **C2/N1** genuine nontrivial local observable; **C3/D2** actual same-H full nonvacuum spectral gap; **C4/G1** all externally selected compact simple gauge groups; **V** trusted proof verification. **D1/B1** is a *proof-strategy intermediate* for our R320/R333/CMP116 clustering route, not a fifth official Clay axiom. The detailed 23 E1/D1/D2/N1/G1 proof-producer list remains a source-specific work inventory rather than 23 official requirements. No observer Hilbert/OS, KK, Lorentz 3+1 or Bishop transfer requirement is inserted into Clay.

**New original SU(2) same-measure analytic lemma (PR #1444):** for `0<r<6`, the original six-staple norm `R` and local six-plaquette Wilson deficit `D₆` satisfy `1_{R<r}≤D₆/(6-r)`, hence `P_original(R<r)≤E_original[D₆]/(6-r)`. Combining the already proved conditional Haar tail gives

```
P_original(t(UV)≤0)
  ≤ E_original[D₆]/(6-r) + 3 exp(−βr/2).
```

With periodic translation invariance and `p_L(β)=(1/N_p)log Z_L(β)` for the `exp(β∑_p t_p)` convention, `E_original[D₆]=6(1−p'_L(β))`, reducing *local frustration* to a genuine original plaquette/pressure slope. Original source proof: [SU(2) action derivation](https://github.com/chboishabba/dashi_agda/blob/research/ym-voyager2026-completeness-crosswalk-20261101/Docs/physics/YMClaySU2OriginalOneLinkCoherentStapleTail20261109.md). Its exact-rational regression `scripts/check_ym_su2_original_staple_frustration_action_20261109.py` passed **187,500** finite rational checks independently. This is a legitimate **finite local analytic reduction**, not the unproved cutoff/volume-uniform **distance-dependent full-Wilson connecting-polymer covariance bound**. A favorable `p'_L` or localized polymer suppression estimate is still missing.

### Cross-pollination without false dependencies

1. **Monster M2:** original 80 relators satisfied in the selected group gives a sound quotient homomorphism, **not** selected-kernel reflection. Same logical pattern as a real original-Wilson single-link tail giving a sound local reduction, **not** full spatial covariance decay.
2. **Moonshine V0.4/V1:** existing original FF/FT and four-sector pair mode adapters give literal same-object syntax, but TF/TT genuine operator identities and all-mode preservation need their own mathematical source. Do not substitute finite Griess/grade data.
3. **YM D2:** the attached worker's invisible-sector counterexample prevents inferring the full reconstructed-H gap from decay on a selected non-dense observable family. D2.03 source-specific spectral detection is essential to our chosen route.
4. **Observer/OS/KK #1460:** legitimate independent HIL07/HIL08/KK questions; not Clay prerequisites.
5. **Bishop K04d/K05 #104:** legitimate separate infinite-series and Agda carrier/Lean acceptance questions; no physical Yang–Mills dependency.

The terminal open results **remain** M2-01 selected-kernel reflection, V0.4 actual TF/TT and mixed Jacobi/locality, V1 all-mode original FLM equivalence, E1 actual interacting `R^4` limit, D1 optional original full-Wilson long-distance decay route, D2 full same-H spectral gap, N1 noncollapse, and G1 all compact simple groups. The source-readback and exact-rational regression do not certify those mathematical terminals.


## Latest original YM analytic cross-pollination — volume-uniform SU(2) pressure theorem

The D1 local frustrated-staple expectation obstruction identified above has been **partly paid by an original-measure theorem** on #1444: [SU(2) Wilson uniform plaquette deficit](https://github.com/chboishabba/dashi_agda/blob/research/ym-voyager2026-completeness-crosswalk-20261101/Docs/physics/YMClaySU2OriginalWilsonUniformPlaquetteDeficit20261109.md). For β≥16 and any periodic four-dimensional finite lattice, using the true normalized product SU(2) Haar/Wilson action, the Gibbs pressure lower bound from an identity-link cap and pressure convexity yields
`E[1−t(U_p)] ≤ [8+(2/3)log24+logβ]/β`, uniformly in volume. This gives explicit `P(R<r) ≤ 6[8+(2/3)log24+logβ]/[β(6-r)]` for a local six-staple frustration event, provided `0<r<6` (for nondegenerate local one-link conditional geometry choose sufficient periodic side lengths). The original one-link conditional Haar tail then has an entirely β-dependent probability upper bound.

**Not the terminal D1:** the bound is on one local event, whereas the needed physically scaled connecting-polymer/bridge estimate counts many adjacent UV sites. The probability of *one* link failure vanishing as β→∞ is insufficient to prevent a percolating network of bad blocks or certify uniform long-distance connected covariance. The next physical result is geometrically **connected** frustrated-polymer activity controlled against entropy on the SAME original Wilson measure, followed by original CMP116 physical marked-domain applicability. This is an exact scope sharpening, not a new Monster/FLM theorem. The 23 producer and minimal Clay docs on #1444 were updated together. Native SU(2) Agda kernel source remains to be established.


## 9 November source-specific proof advance — 80-relator F₂ character cut

New Golden-imported `DASHI/Moonshine/Y443Mod2OddEdgeCentralCharacterExact.agda` uses the *literal* original `Y443CoxeterPresentationExact.monsterRelators` and builds the actual `Bool = C₂` group. `dropSatisfied` selects all eleven original order-three Coxeter edge equations and the 80th original central word by their canonical source indexes. `oddEdgeWordParity` and `sourceCentralPowerNineParity` normalize the actual source words. The theorem `original80HasNoNontrivialMod2Character` then proves every 12-node `C₂` character satisfying the **original 80** relations is trivial. Without the central relator, the original 79 words retain the all-nodes-sign map. [Complete math/source/verification ledger](../support/reference/Y443Mod2RelatorCharacterCut20261109.md). Independently executed finite GF(2) check: all 4,096 assignments, rank 11 for 79 relations and rank 12 for 80.

For a group generated by involutions, this implies **trivial abelianization** of the universal 80-relator group once the source theorem is kernel-accepted. But **M2-01 nonabelian selected-group kernel reflection is still OPEN**: perfectness does not establish group identity or rule out a different perfect quotient. The original selected Y443 group and published Monster action also remain not identified. Agda 2.9 receipt is unavailable in the current environment.

## Parallel original-Wilson insight from #1444

The actual original SU(2) finite 4D Wilson pressure bound now also gives **bulk bad-plaquette density** estimates for `B_ε=(# {p:1−t(U_p)≥ε})/P`:
`E[B_ε]≤[8+(2/3)ln24+lnβ]/(βε)` and
`P(B_ε≥η)≤[8+(2/3)ln24+lnβ]/(βεη)`.
These are uniform in finite periodic volume, without independence. They **do not** prevent an arbitrarily long sparse connected bad path: a length-`n` path among `6n⁴` plaquettes has vanishing density `1/(6n³)`. Hence the original D1.03 **connected** polymer/physical-cube estimate remains open, as do E1.03, D2.03/04, N1.02 and G1.03. [Original-Wilson derivation](https://github.com/chboishabba/dashi_agda/blob/research/ym-voyager2026-completeness-crosswalk-20261101/Docs/physics/YMClaySU2OriginalWilsonUniformPlaquetteDeficit20261109.md).

**Max-cut next:** selected-group nonabelian kernel certificate (Monster); actual Leech TF/TT source (Moonshine); physical cluster-activity bound on original Wilson measure and interacting R4 source (YM). Source-written finite algebra is not terminal proof completion.


## 9 November: fail-closed actual-evaluation proof repair

The newly source-written Y443 `original80HasNoNontrivialMod2Character` proof was inspected again. The auxiliary `parityWord` normalization was **not** definitional equality with the real relator evaluator. Commit `fbca70f3bf1268c405cf369afb9be9eff8a4265c` adds the *actual* `boolEvaluationIsParity` induction, then `oddEdgeWordEvaluation` and `sourceCentralPowerNineEvaluation` so all eleven original edge and central-relator projections use `Pair.evaluateCoxeterWord` itself. The first `ab1` projection and explicit `zero` pattern were corrected in separate source commits. This fixes an identifiable proof-level mismatch, not a generic wrapper.

The original 79/80 finite source regression passes independently (ranks **11/12**; all **4,096** Boolean generator assignments; character counts **2/1**). The new Agda proof candidate has **NO pinned kernel acceptance receipt**. Do not promote it beyond source-written status or infer nonabelian `NoExtraSelectedRelations.reflectsEquality`. All remaining Monster, mixed Leech TF/TT, FLM all-mode, and physical YM endpoints in this master ledger are unchanged.


## 9 November 2026 — decisive M2 strategy change: published simplicity and one moved state

The earlier max-cut phrasing `NoExtraSelectedRelations.reflectsEquality` as a standalone all-pairs word-rewriting project is **superseded** by the mathematically shorter simple-quotient argument. Historical Ivanov/Bray identifies *the actual original 80-relator quotient* with the nonabelian simple Monster; do not substitute the Lean/TauCeti **transcription-only** relator count as an Agda proof of that historical identification.

**New source-written owner:** `DASHI/Moonshine/Y443Universal80SimpleQuotientKernelReflectionExact.agda`, imported by the focused Y443 Golden root. It constructs
- `Selected.originalSelectedKernel` as an `AdmissibleCongruence` on the true original `Y443Universal80RelatorCongruenceExact.Expr`, using original `Pair.RelatorsSatisfied`;
- `Original80SimpleCongruenceAuthority.everyGroupCongruenceIsTrivialOrTotal` as the *precise external historical simplicity consequence*, explicitly **not yet supplied**;
- `Selected.nonidentityNodeFromMovingState` as an actual identity-law-based proof of nontrivial node image from a *single moved selected VOA state*, not an arbitrary faithful-action claim;
- `Selected.simpleQuotientAndOneNonidentityNodeReflectsAllWords` and `actualKernelReflectionFromPublishedSimplicity` producing all-word kernel reflection from those genuinely smaller sources;
- `Selected.selectedImageSetoidGroup` and `simpleSourceIdentifiesOriginalAndImageSetoids` identifying the universal 80-quotient with the **selected node-generated image**, *without* assuming the selected nodes generate the entirety of `G`. This is the highest-alpha subgroup route.
- `Selected.WithOriginalSources` derives equivalence to *all selected G* only when original signed-word generation is genuinely supplied.

**Exact remaining M2 proof owners are now** M2-SIMPLE: historical quotient↔Monster isomorphism and its simple-congruence elimination on the same 80 words; M2-MOVE: one concrete original Y443 node moving a real selected **weight-two** state (not vacuum); M2-GEN: actual whole selected `G` signed-word generation only for the stronger equality-to-`G` claim; M2-AUT: every VOA automorphism is in the selected image, with actual all-mode action laws. The standalone 80-word equal-pair reflection is now a **derived** target rather than an independently assumed oracle.

**Recovered 71+9 / 72+8 content** (exact user-cited prior art) is accounted for in [Y44371Plus9And72Plus8SimpleKernelResolution20261109.md](../support/reference/Y44371Plus9And72Plus8SimpleKernelResolution20261109.md). The new `Y443Original72Plus8RelatorPartitionExact.agda` gives literal `72=55+8+8+1`, `8=4+3+1` by original source categories. The independent script `scripts/check_y443_original_72_plus_8_partition_20261109.py` and local literal enumeration confirm the **complete original 80-word multiset** is preserved (79 source word length 400; 80 length 463). The `71+9=80` and `71+10=81` SSP/jCoarseFine roles remain separate from a Y443-equivariant group representation. `72=9×8`, `80=10×8` fits an F9 projective **index/codec**, but does not entail one original Monster action. No artificial 71/72 group-iso assumption is accepted.

**No terminal status promotion:** historical M2-SIMPLE transport, selected moved state, V0.4 original TF/TT, V1 FLM all-mode iso, YM E1/D1/D2/N1/G1 physical producers remain open. Source-written modules and local finite checks have no exact-head Agda 2.9 acceptance receipt yet.


### 9 November direct original-source integration and symmetry negative control

Code commit `00e5ff496cccad971b0c292abeb916feeeadf70c` adds `OriginalSelectedJMDSource` to `Y443Universal80SimpleQuotientKernelReflectionExact.agda`. It imports the **existing** `Y443JMDPresentedVNaturalCapstoneExact.PresentedY443VNaturalSource` and consumes its literal original `groupWithInverse`, `nodes`, `relatorsHold` and `presentationSurjective`. The nested `FromHistoricalAndMovedState.originalKernelReflection`, `actualSelectedToAfterFrom` and `actualPresentedFromAfterTo` are now source-written exactly on that existing selected object. No alternative group/action carrier and no duplicate JMD generation lemma have been constructed. The uninhabited source authority remains the true published Ivanov/Bray Q80 ≅ M/simple quotient and one actual moved selected weight-two state.

Code commit `ad77c670dbc23d777e40a7452cd3cc35b5171a62` adds an exact **negative graph-symmetry test** `this72SplitNotLongArmEquivariant`: swapping the two length-four Y443 arms takes core square `e1` to residual square `e2`. Therefore the convenient literal original **72+8** relator partition is **not invariant even under this actual Coxeter graph automorphism**, much less automatically a Monster-equivariant (mathbb P^1(mathbb F_9)) projective representation. Use the 71+9/72+8 sources for bookkeeping and test indexing only until a real original action-preserving transport is supplied. This prevents numerical coincidences from being upgraded to Monster isomorphism hypotheses.

Kernel-check of the new Agda modules and original selected-object source instantiation remains OPEN. None of Moonshine V0.4/V1 or Yang–Mills E1/D1/D2/N1/G1 changes status.


## 9 November — new concrete V0.4 TF from existing original FT; M2 literal moved-state

**New source owner** `DASHI/Moonshine/VNaturalOriginalFTToTFSkewFiniteExact.agda` (imported by the focused Y443/Vnatural golden root). This does **not** assume an independent TF map: for `n:ℤ`, it constructs an actual finite coefficient sum on the **original selected twisted-even carrier** using `N.twistedAddOriginal`, `N.twistedScaleOriginal`, the existing *literal original* Leech FT mode, and iterated selected twisted translation. The mathematical VOA skew-symmetry formula used is
`t_(n) a = Σ_{j≥0} (-1)^(n+j+1)/j! T^j (a_(n+j) t)`.
Its `OriginalFTSkewData.originalFTVanishesAtAndAboveBound` is a genuine **truncation proof premise**; the chosen finite cutoff is not accepted without verifying actual FT vanishing. `Derive.withOriginalTT` builds the existing `OriginalMixedSectorIntertwiners` with this **constructed** TF, leaving only the genuine original Leech TT as an independent mixed-channel function, and `originalTFUniqueFromSameFTSkew` proves pointwise uniqueness among candidates satisfying this exact formula.

**Remaining exact V0.4 original-source proof cut:**
- **V04-FTSKEW-01:** instantiate the actual original `signedFactorialCoefficient n j = (-1)^(n+j+1)/j!` over the Leech fixed-VOA characteristic-zero scalar carrier, including signed integer mode convention and scalar inverses.
- **V04-FTSKEW-02:** original theta-twisted-even `twistedTranslation` is genuine `L_{-1}), with linearity, zero preservation and graded action.
- **V04-FTSKEW-03:** prove the **selected original FT upper-truncation bound** and the original Leech skew-symmetry identity equating its actual TF operator with this finite formula; the weak `VOA.LowerTruncation.modeVanishesAboveBound : Set` does not provide a theorem by itself.
- **V04-TT-01:** construct actual original twisted×twisted→fixed intertwiner from Leech cocycles/invariant pairing and twisted vertex operators, proving its closure in the selected fixed even sector.
- **V04-AXIOMS-01/02:** original mixed Jacobi/locality, translation/vacuum, grading and linear laws for the resulting original four-mode paired VOA. Only these support V1 FLM all-mode comparison.

**New Monster M2 source reduction:** `Y443Universal80SimpleQuotientKernelReflectionExact.OriginalSelectedJMDSource.oneOriginalMovedStateImpliesNontrivialNode` uses precisely `JMD.action source`, `JMD.nodes source`, `JMD.groupWithInverse source` and the literal selected `VNaturalConstruction.Vnatural` carrier. It turns **one selected state moved by a Y443 node** plus the identity law at the same state into `ActualSelectedNontrivialNode`—without choosing a second group action, or assuming globally faithful automorphisms. **M2-MOVE** still demands a concrete weight-two state/vector from the original selected Leech/Griess construction; the unrefined `VOAGroupAction.actionIdentity : Set` does not itself supply a typed equality.

These source-written constructors and the original finite SU2 large-deviation theorem are *not* their own missing mathematical axioms. Agda 2.9 kernel acceptance, genuine original source instantiation, nonabelian Monster historical simplicity transfer, Leech TT and all-mode VOA remain outstanding.


## 9 November — D2 physically minimal dense-test spectral max-cut (new original proof note)

[The YM #1444 original OS D2 dense-test theorem and exact unpaid source](https://github.com/chboishabba/dashi_agda/blob/research/ym-voyager2026-completeness-crosswalk-20261101/Docs/physics/YMClayOriginalOSDenseTestAutocorrelationGapCut20261109.md) sharpens D2.03/D2.04: for a *single reconstructed nonnegative E1-Hamiltonian H*, norm density of the actual OS nonvacuum cylinder vectors `D` and one common exponential decay exponent `m>0` for `<psi,e^{-tH}psi>` for each `psi∈D` imply `sigma(H|Omega^perp)⊆[m,∞)`. The constants `C_psi` can vary by test. This follows by bounding positive spectral projections `e^{-lambda t}||E_[0,lambda]psi||²` and taking `t→∞`, then using density. The already-owned `BalabanOSExponentialClusteringImpliesHamiltonianGapExact` is the intended compiler, not a new artificial spectral law.

**True physical unpaid cut:** source original E1 Euclidean limit/OS H, full nonvacuum OS cylinder density, a genuine common physical-time autocorrelation exponent on those source tests (potentially from original Wilson D1 space-time clustering), and vacuum uniqueness/no hidden zero-energy states. D2.04 no longer needs a separate independent analysis when these are proven. The previous invisible-sector negative control remains decisive for why a mere *proper selected observable subspace* cannot substitute for the dense OS family.

The current Moonshine V0.4 original FT-derived finite skew constructor is source-written and *not* a proof of the native Leech skew-symmetry law or actual TT modes. Likewise, Monster M2 literal selected moved-state still has no genuine nonfixed weight-two vector and original Ivanov/Bray formal simplicity certificate. All original terminal gates remain open.
