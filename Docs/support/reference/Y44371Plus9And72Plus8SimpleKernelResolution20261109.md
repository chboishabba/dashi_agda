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
3. **Original moved-state:** implement `actualY443NodeMovesGriessState` from one concrete original `V^natural_2` action and state. No chosen fake action/empty carrier.
4. **Same selected generation:** produce original `PresentedByY443Nodes` from actual selected (G) source.
5. **Compose:** `actualKernelReflectionFromPublishedSimplicity`, selected-to-Q80 bidirectional setoid iso and published Monster iso; only then the Y443/FLM full action theorem.

Other terminal gates E1.03, D1.03, D2.03–04, N1.02, G1.03, V0.4 and V1 remain open; no prize claim. This is an explicit reduction to the shortest genuine source inputs, not a numerical proof of Monster.


### 9 November direct original-source integration and symmetry negative control

Code commit `00e5ff496cccad971b0c292abeb916feeeadf70c` adds `OriginalSelectedJMDSource` to `Y443Universal80SimpleQuotientKernelReflectionExact.agda`. It imports the **existing** `Y443JMDPresentedVNaturalCapstoneExact.PresentedY443VNaturalSource` and consumes its literal original `groupWithInverse`, `nodes`, `relatorsHold` and `presentationSurjective`. The nested `FromHistoricalAndMovedState.originalKernelReflection`, `actualSelectedToAfterFrom` and `actualPresentedFromAfterTo` are now source-written exactly on that existing selected object. No alternative group/action carrier and no duplicate JMD generation lemma have been constructed. The uninhabited source authority remains the true published Ivanov/Bray Q80 ≅ M/simple quotient and one actual moved selected weight-two state.

Code commit `ad77c670dbc23d777e40a7452cd3cc35b5171a62` adds an exact **negative graph-symmetry test** `this72SplitNotLongArmEquivariant`: swapping the two length-four Y443 arms takes core square `e1` to residual square `e2`. Therefore the convenient literal original **72+8** relator partition is **not invariant even under this actual Coxeter graph automorphism**, much less automatically a Monster-equivariant (mathbb P^1(mathbb F_9)) projective representation. Use the 71+9/72+8 sources for bookkeeping and test indexing only until a real original action-preserving transport is supplied. This prevents numerical coincidences from being upgraded to Monster isomorphism hypotheses.

Kernel-check of the new Agda modules and original selected-object source instantiation remains OPEN. None of Moonshine V0.4/V1 or Yang–Mills E1/D1/D2/N1/G1 changes status.


## 9 November — original JMD trace provides an alternative one-node nonidentity certificate

The fresh M2 implementation `Y443Universal80SimpleQuotientKernelReflectionExact.Selected.originalJMDW5NonidentityFromRelators` consumes the **existing** `Y443JMDFromRelatorsToPowerExact.powerFromActualEightyRelators` and the literal `Y443JMDSourceWordInstantiationExact.wElement`. It proves:
```
(original beta^5 = 1 from true Y443 A4 path)
  and (original selected w^5 != 1)
    => original selected node x4=e1 != 1
    => selected 80-relator word-evaluation kernel reflects,
       IF actual original Q80 historical simplicity is imported.
```
The source term uses `Y443JMDConcretePairPowerCompilerExact.sourceX4Fifth` to identify the **same** selected `x4 = w^5` and transports a genuine `w^5 != identity` proof to `x4 != identity`. This is an alternative to a selected Griess moved-state matrix, not an additional independent Clay or Moonshine obligation.

The actual quoted JMD **order-ten report** would supply the needed `w^5 != identity` if it were an exact-order-ten theorem **for this selected group and literal w**, not merely a trace from a separate implementation. The native Agda record `Y443JMDTracePowerExact.JMDStepsTwoToFour` currently stores `x4=w^5` and `beta=w^6`, but **does not encode exact order ten or w^5 nonidentity**. Thus the route still needs the authentic selected-order certificate, and the native A4 path `beta^5=1` source. Neither is silently assumed proved.

**M2 smallest source options after this pass:** EITHER (a) literal selected Griess weight-two moved-state witness plus identity action at that state, OR (b) real original selected JMD order-ten `w^5!=1` plus the actual A4 beta^5 source. Both feed the **same** historical simplicity-to-kernel theorem. The historical Q80↔Monster published proof bridge remains common.


## 9 November — **actual source 80 ⇔ 72+8 RELATOR SATISFACTION** now source-written

The earlier 72+8 inventory was **only** a literal word-multiset count. New `DASHI/Moonshine/Y443Original72Plus8RelatorSatisfactionExact.agda` closes the stronger finite semantic transport, independently of Monster simplicity: `partitionAt` splits the *actual canonical* `Y443CoxeterPresentationExact.monsterRelators` list in its native order. It extracts precisely the eight residual source positions `8,9,10,11,68,75,77,79`: four generator squares, three original order-three edges and the 80th original Ivanov central relation. All other 72 words are retained without changing their meaning.

For **every** original `GroupWithInverse G` and node map, `UnderOriginalGroup.splitAll` and `mergeAll` are structural inductive proofs of

```
Pair.RelatorsSatisfied gi nodes Y.monsterRelators
  iff
Pair.RelatorsSatisfied gi nodes original72
  AND
Pair.RelatorsSatisfied gi nodes original8 .
```

`source72Count` and `source8Count` prove 72/8 on the **literal computed source**, not an independently rewritten relator list. `ExistingOriginalJMD.literalOriginal72Satisfied`, `literalOriginal8Satisfied`, and `recombinedSameOriginal80` instantiate this equivalence on the **same existing `PresentedY443VNaturalSource`**, reusing its group, node map and `relatorsHold` exactly. Added to focused Golden root `Y443VNaturalPairGenerationValidation.agda`.

An independent local Python check of the original 12 squares / 66 pairs / spider / central source enumeration confirmed the eight residual positions and their semantic types. The new Agda source has **not** received an Agda 2.9 kernel typecheck and therefore is SOURCE-WRITTEN, not kernel-certified. This proof **does not** settle the historical Q80 ≅ Monster theorem or the selected-group nonabelian kernel reflection, which require actual historical simplicity and real selected nontriviality. It does pay a previously missing **original relation-preservation** step for all further 72+8 source proofs. The 71+9 and projective F9 numerical codings remain independent from this now-exact actual-relator partition.


## 9 November continuation — exact historical 79→80 quotient step in original Agda source

The **same** new `Y443Original72Plus8RelatorSatisfactionExact.agda` now proves two exact original-list equivalences for all actual `TM.GroupWithInverse G` and node maps:

```
RelatorsSatisfied gi nodes Y.monsterRelators
  <=> RelatorsSatisfied gi nodes original72
      AND RelatorsSatisfied gi nodes original8

RelatorsSatisfied gi nodes Y.monsterRelators
  <=> RelatorsSatisfied gi nodes Y.doubleMonsterRelators
      AND (evaluateCoxeterWord gi nodes
              Y.centralInvolutionRelator ≡ Pair.identity gi).
```

The second uses structural `appendSatisfied` / `mergeAppendSatisfied` proofs on **Y._++_**, with `original79AndCentralFrom80` and `original80From79AndCentral`; no abstract postulated “central quotient” record. `ExistingOriginalJMD.literalOriginal79Satisfied`, `literalOriginalCentralSatisfied` and `reconstructedOriginal80From79AndCentral` consume precisely the existing JMD selected G, its original relators and the literal Ivanov `f312` word.

**Paid source-level**: the exact list-level historical presentation passage from 79 to 80 and the exact 72+8 relation satisfaction equivalence. **Still required**: prove the **group-theoretic** historic identification of the quotient of the 79-relator group by the normal closure of `f312` with the published Monster, and transfer its simplicity to `Original80SimpleCongruenceAuthority`. Satisfying the *same relations* alone does not prove a selected-group isomorphism. Agda kernel acceptance remains pending.


## 9 November source-level historical presentation isomorphism — 79+central congruence ≡ 80 congruence

**Important M2-SIMPLE progress beyond word counts or satisfaction transport:** `DASHI/Moonshine/Y443Original79CentralQuotientIs80Exact.agda` now constructs the least **group-congruence** `_≈₇₉⁺_` on the existing original `SignedNodeExpression` using only (i) the literal 79 source Coxeter/spider words `Y.doubleMonsterRelators`, and (ii) Ivanov's actual central source word `Y.centralInvolutionRelator`, with all original associativity, identity, inverse and multiplication-congruence laws. No new selected group or manufactured abstract quotient object is introduced.

The source-witness functions `membershipLeft`, `membershipRight` and `membershipSplit` are structural inductions over the *literal* `Y._++_` source relator list. Consequently `historicalTo80` and `original80ToHistorical` recurse over every proof constructor and establish, for **all** original signed node expressions `x,y`:

```
U._≈₈₀_ x y   iff   x ≈₇₉⁺ y .
```

The theorem `original80IffHistorical79Central` gives both directions, and `historical79PlusCentralSetoidGroup` constructs the matching historical quotient **group object in setoids**. The new module is imported into `Y443VNaturalPairGenerationValidation.agda`. This is a structural proof of **the actual presented group's quotient equivalence**, stronger than merely proving that selected group models satisfy the two lists.

**M2-SIMPLE remaining source:** transport the external published Ivanov/Bray theorem that the historical `Y443 / <f312>` group is the **published simple Monster** onto the **same actual setoid**; the source-level historical-presentation equivalence needed for that transport is now constructed. This does **not** itself build a canonical Monster group carrier, a closed term of `Original80SimpleCongruenceAuthority`, a nonidentity selected-node action, or the actual Vnatural all-mode isomorphism. Exact-head Agda 2.9 kernel acceptance remains unobserved. Updated highest-alpha next: published-source historical group iso and simple-congruence elimination, one selected JMD w5 nontriviality or moved-weight-two witness, then composition with existing `OriginalSelectedJMDSource`. Attribution: Ivanov, Bray, TauCeti and JMD preserved.


### Historical 79+central selected-group interpretation welded to original 80 semantics

Latest `Y443Original79CentralQuotientIs80Exact.OriginalHistoricalInterpretation` (source commit `af7cf1d3ea3746e5fa8e684d77232d2d0ce60892`) now consumes ONLY actual source satisfaction of Bray's first 79 Y443 relators plus the literal Ivanov central `f312` equation, derives `Y.monsterRelators` satisfaction via the newly proved append theorem, and uses the original `U.Interpretation` to prove `historicalWordSound`: **every equality under the constructed historical 79+central congruence evaluates as an equality in the exact same selected group**. No duplicate selected group or novel semantics. The universal `_≈₈₀_` and historical `_≈₇₉⁺_` equivalence is now source-written as a real two-sided group setoid congruence, not solely model satisfaction.

This pays the formal *presentation-to-presentation* identity needed to attach the external Ivanov/Bray theorem. **Unpaid M2-SIMPLE:** the original historical theorem's actual group isomorphism to the published canonical Monster and an Agda admissible-simple-congruence witness from that identification; **unpaid M2-NONTRIV:** original moved selected state or selected JMD `w^5≢1`. Source-written is not Agda kernel checked. All physical YM and original TT/FLM terminals remain unaffected.
