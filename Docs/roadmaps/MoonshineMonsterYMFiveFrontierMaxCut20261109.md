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
