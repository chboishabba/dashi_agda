# Y443: reuse of 71+9, 72+8 and the shortest nonabelian kernel proof

**Date:** 9 November 2026. **Ownership:** Ivanov, Bray and TauCeti for the original Y443/Monster presentation; JMD (meta-introspector) for the independently obtained u/v generating trace; Katz–Mazur, Duncan–Ono, Conway–Norton and DASHI Biology/Moonshine for separate SSP/jCoarseFine/Ogg and modular-`j` donor calculations. No attribution to these sources for an unproved bridge or group action.

## 0. What the two numerical constructions ACTUALLY are

**71+9:** in the existing `DASHI/Biology/SSP15JCoarseFineIntegratedExact.agda` (and its `JCoarseFineEvaluationFibreExact`, `SSP15NineObserverAtlasExact` and `OggPrimeNonaryAddressExact` owners), `71+5×2=81` is a **number/prime-specific SSP complement interface**; a 9-state `jCoarse` / (3^9) `jFine` distinction is also explicit. Thus (71+9=80) and (71+10=81) are arithmetically true but **not** canonical Y443 relation partitions or isomorphic representations of the Monster. The Ogg prime (71) is an *external prime*, not a node orbit of the Y443 Coxeter graph. The separate 9→5/27→13 symmetry reduction and `jCoarse/jFine` observers can be reused for finite checks only after a genuine action-compatible transport is built.

**72+8:** the earlier (mathbb P^1(mathbb F_9)=mathbb F_9\cup\{\infty\}) analogy has ten projective points, each with eight optional nonzero multiplier labels, giving (10×8=80=72+8). Separately, (|\operatorname{AGL}(1,9)|=9×8=72), and (|mathbb F_9^\times|=8). These are cardinality/coordinate roles, **not** direct-sum group structures or a Monster action. The ATLAS documents the 10-point action of (mathrm{PGL}_2(9)), not a selected Y443 equivariant action: https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/PGL29G1-p10B0.

**NEW TRUE ORIGINAL RELATOR SPLIT:** `Y443Original72Plus8RelatorPartitionExact.agda` constructs an explicit 72+8 partition from literal `Y443CoxeterPresentationExact` source words:

| Original Y443 relation type | Selected 72 | Residual 8 | Original total |
|---|---:|---:|---:|
| Involution squares | 8 | 4 | 12 |
| Odd Coxeter edges (order 3) | 8 | 3 | 11 |
| Nonedge pairs (order 2) | 55 | 0 | 55 |
| Spider | 1 | 0 | 1 |
| Central (f_{312}) | 0 | 1 | 1 |
| **Total** | **72** | **8** | **80** |

The eight retained node squares are (a,b_1,c_1,d_1,e_1,b_2,c_2,d_2). The eight retained tree edges are (a-b_1,b_1-c_1,c_1-d_1,d_1-e_1,a-b_2,b_2-c_2,c_2-d_2,a-b_3). The residual has four remaining square relators, three remaining edges and the central quotient. This is an explicit *combinatorial partition*, not a canonical graph-invariant decomposition: it breaks the two long-arm swap. The `originalNonedges` function selects the **55 actual nonedges** from the original `Y.pairs` graph. `actualOriginal72Count`, `actualOriginal8Count`, `original80ReorganizedCount` prove source-level counts; `scripts/check_y443_original_72_plus_8_partition_20261109.py` independently validates full multiset equality to the original 80 words, totals 400/463. Neither file claims a (mathbb P^1(mathbb F_9))-to-relator equivariant bijection.

## 1. Highest-alpha theorem: simplicity collapses an all-word equality problem

Let (Q_{80}) be the *actual* universal 80-relator quotient group, represented here as the original `Y443Universal80RelatorCongruenceExact.canonical80SetoidGroup`. The external published theorem of Ivanov (1999), Section 3.9, identifies this quotient with the Fischer–Griess Monster (M), which is nonabelian simple. The TauCeti Lean source transcribes the 80 relators but explicitly does **not** independently kernel-check a full `PresentedGroup ≅ M` theorem; the actual historical-to-formal bridge is still a source owner.

For the original *selected* Y443 node interpretation (n↦g_n) in the selected group (G), the 80 relator identities yield a homomorphism (phi:Q_{80}\to G). Its kernel is a normal subgroup of (Q_{80}). **If** the historical source really identifies *this exact* quotient with the simple Monster, then either (kerphi=\{1\}) or (kerphi=Q_{80}). One source-valid **nonidentity node** (g_n\ne1_G) excludes the latter, giving (kerphi=\{1\}), hence (orall x,y,operatorname{eval}(x)=operatorname{eval}(y)\implies x\approx_{80}y). Combined with actual selected signed-word surjectivity `PresentedByY443Nodes`, this gives (G\cong Q_{80}\cong M).

**NEW Agda:** `Y443Universal80SimpleQuotientKernelReflectionExact.agda` now source-writes this argument at the exact 80-word setoid:
- `originalSelectedKernel : U.AdmissibleCongruence` constructs the selected semantic kernel from **the actual original 80 relator satisfaction**, including group equations, not from a free arbitrary relation.
- `Original80SimpleCongruenceAuthority.everyGroupCongruenceIsTrivialOrTotal` is the correct congruence version of **historical quotient simplicity**. It is an **unpaid published-theorem transport**, not a new assumption that selected (G) has no extra kernel.
- `ActualSelectedNontrivialNode` requests one concrete original node with image not equal to the identity.
- `nonidentityNodeFromMovingState` reduces that to a **single moved state under the same typed selected group action**, using a proved identity action law. Use a nonvacuum **weight-two Griess state**, because genuine VOA automorphisms fix the vacuum and cannot move it.
- `simpleQuotientAndOneNonidentityNodeReflectsAllWords` then constructs **all-word kernel reflection** without an all-word equality oracle.
- `actualKernelReflectionFromPublishedSimplicity` directly inhabits the existing `U.Interpretation.NoExtraSelectedRelations`.
- `WithOriginalSources.selectedToAfterFrom` and `presentedFromAfterTo` consume real selected word generation to produce the two-sided setoid equivalence.

**This is not the final historical/selected-group theorem:** two inputs are not yet inhabited on the *actual selected objects*: the exact formal Ivanov–Bray/TauCeti published quotient/simple-group authority, and an original selected node whose *literal* action moves an actual weight-two vector. Plus the already-known actual `PresentedByY443Nodes` generation witness. All three must be checked before promoting `Aut_{VOA}(V^natural)≅M`; full action surjectivity and all modes are additional V1/V2 obligations.

## 2. Proof-level route to closing the remaining inputs (in order)

**M2.01 historical:** reuse `Y443CoxeterPresentationExact.monsterRelators` and `Y443Universal80RelatorCongruenceExact._≈₈₀_`, then transport the *actual published* presentation theorem `Y443_{443}/⟨f_{312}⟩≅M` along the exact 12-generator encoding, without supplying an unrelated `Simple` oracle. This yields `Original80SimpleCongruenceAuthority` by the normal-subgroup/congruence correspondence and Monster simplicity. The current TauCeti code merely transcribes the presentation; its bare relator counts or 72+8 codec cannot do this.

**M2.02 selected nontriviality:** select a named original generator (g_n), the *actual* selected VOA action on (V^natural_2), and one concrete weight-two vector (x) with (g_n x\ne x). The imported `Y443TwoGeneratorSameVOAActionExact.ActualGroupAction` gives a typed identity law; `nonidentityNodeFromMovingState` then proves (g_n\ne1_G) directly. Do not use the vacuum, grade dimensions, mod-2 parity or an unrelated S12/S78 action as a substitute.

**M2.03 selected generation:** instantiate already-present `Y443JMDPresentedVNaturalCapstoneExact` JMD u/v word compilers on the *same original selected (G)*. Its signed-word-surjectivity field remains a source responsibility, rather than a free module-generated full-group theorem.

**M2.04 action/VOA:** only after the original group iso, use the actual mode-preserving selected↔FLM morphisms to transport the literal Monster action and prove automorphism surjectivity. Existing Griess/weight-two first products alone cannot establish all VOA modes.

## 3. Reuse for Moonshine/YM without unsupported mathematical transfers

- **V0.4 Leech:** use `VNaturalOriginalPairedFourSectorModesExact.Selected`, source FF/FT adapters, and the original selected linear pair. The genuinely missing data are native TF/TT intertwiners, their mixed Jacobi/locality and parity/translation source.
- **V1 FLM:** use `Y443DGLUniquenessSelectedFLMExact.Selected` and `Y443FLMConcreteVOAGroupTransportExact.Transport`, paying genuine DGL original hypotheses or all-mode maps. A 72+8 index cannot replace this.
- **YM:** `Y443` simplicity is unrelated to Yang–Mills mass gap. A mathematically parallel *proof strategy* is to replace a giant list of local checks with one adequate global original-source theorem: for D1 connected-polymer activity vs entropy, E1 original interacting continuum compactness/uniqueness, D2 same-H spectral completeness. The SU2 pressure and density results remain finite and cannot be promoted to long-distance covariance or Clay.

## 4. Acceptance/next exact source owners

1. **Kernel-check** the new `Y443Universal80SimpleQuotientKernelReflectionExact.agda`, `Y443Original72Plus8RelatorPartitionExact.agda` and their transitive import root on Agda 2.9 before calling them verified.
2. **Original historical bridge:** implement `publishedY443Simple80Congruence` from actual Ivanov/Bray/Monster simplicity and original word/congruence identification.
3. **Original moved-state:** implement `actualY443NodeMovesGriessState` from one concrete original `V^natural_2) action and state. No chosen fake action/empty carrier.
4. **Same selected generation:** produce original `PresentedByY443Nodes` from actual selected (G) source.
5. **Compose:** `actualKernelReflectionFromPublishedSimplicity`, selected-to-Q80 bidirectional setoid iso and published Monster iso; only then the Y443/FLM full action theorem.

Other terminal gates E1.03, D1.03, D2.03–04, N1.02, G1.03, V0.4 and V1 remain open; no prize claim. This is an explicit reduction to the shortest genuine source inputs, not a numerical proof of Monster.
