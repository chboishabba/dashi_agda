# 27 ternary cube × S3/C3 × Heaps: exact action-sensitive cross-pollination

Date: 28 October 2026. Source integration PR: [#1275](https://github.com/chboishabba/dashi_agda/pull/1275). Neighbor original formalization: [PR #1414](https://github.com/chboishabba/dashi_agda/pull/1414), [PR #1407](https://github.com/chboishabba/dashi_agda/pull/1407). **Nothing from the neighbor PR's branch is silently imported.** No protected ESD changes; previous Ibrahim Monster 3B proof ownership unchanged.

## Original mathematical and repository provenance

- Historical permutation-group and orbit-enumeration mathematics: Cauchy and Frobenius (19th-century orbit counting), William Burnside, George Pólya (1937 weighted orbit counting), and Dixon–Mortimer, *Permutation Groups* (1996), DOI **10.1007/978-1-4612-0731-3**. Burnside/Frobenius counting and the S3 group are inherited, **not** mathematical discoveries of this work.
- Existing DASHI originals: `Base369Ternary27HypervoxelFabricGeometryExact.Ternary27Point` (signed x/y/z cube); `SSPTritCarrier.SSPTrit` (−1,0,+1); `RecursiveFibreTower.LevelTwoCode` (exact three-output/three-input ternary endomorphism tables); `TernaryEndomorphismConjugacyExact` (S3 conjugation, seven actual functional-graph classes with orbit sizes 1,2,3,3,6,6,6); `TernaryPermutationS3LawsExact` (six actual S3 permutations); `SSSPThreeFrontierLinearExtensionQuotientBidiExact` (ABC/ACB/BAC/BCA/CAB/CBA); `ZipfABC6OrderHeapsQuotientExact` and the original H14/H15 Heaps owners.
- PR #1414 **owns** the separately source-written 28-Oct-2026 polynomial monodromy S3/C3, 3^5 versus 5^3, and rational quaternion u=(1+i+j+k)/2 with u³=−1, u⁶=+1. That source has not typechecked in Agda and its physical monodromy claim remains gated. PR #1407 owns independent 27×729 Fourier and 13/27 5/9 orbit work. Those proofs are **not imported** from unmerged branches or reassigned.
- This new statistics-only *observation adapter*: Johl Brown-directed, OpenAI ChatGPT-assisted, 28 October 2026. Its source-written Agda proof is **not kernel-certified**; bounded exhaustive Python arithmetic/orbits constitute separate evidence.

## Canonical carriers and four DIFFERENT group actions

Each of the following has exactly 27 coded values, but a different action/observation semantics:

```
Ternary27Point = (SSPTrit x, SSPTrit y, SSPTrit z)
              -- coordinates have signed polarity and geometric meaning

LevelTwoCode   = (TriTruth f(low), TriTruth f(mid), TriTruth f(high))
              -- entire function f: three-point set -> itself

interpreted word = (A/B/C token at coordinate x,
                    A/B/C token at coordinate y,
                    A/B/C token at coordinate z)
              -- explicit statistical interpretation, NOT a theorem that
                 the dialectic x/y/z axes are chronological observations
```

`ZipfTernary27ActionHeapsExact.agda` gives actual `cubeToCode` and `codeToCube` maps with source-written **27-case round trips in BOTH directions**, and reuses the source-owned permutation group without rebuilding it.

The actions on the same three-digit table are:

1. **Axis S3**: reorder the three positions of the code (permuting x/y/z). Burnside: identity fixes 27; three transpositions fix 9 each; two 3-cycles fix 3 each; orbit count `(27+3*9+2*3)/6=10`. Orbit sizes: three singleton diagonals, six 3-element two-equal multisets, one 6-element all-distinct set, **3+18+6=27**.
2. **Axis C3**: only the identity and the two three-cycles of the x/y/z axis positions. Burnside: `(27+3+3)/3=11` orbits, with three fixed diagonal codes plus eight 3-element cycles, **3+24=27**.
3. **Value-label S3**: apply the SAME permutation to each of the three code OUTPUT labels, but do not reindex which input is which. Burnside: identity fixes 27; each transposition fixes its sole fixed label word (1); each three-cycle fixes none. Orbit count `(27+3*1+2*0)/6=5`. Sizes `3+4*6=27`. These are the five equality-pattern classes `XXX, XXY, XYX, XYY, XYZ`.
4. **Endomorphism conjugacy S3**: `f ↦ p ∘ f ∘ p⁻¹` on the EXISTING source-owned `LevelTwoCode`. This simultaneously relabels the output AND reindexes the input. It is neither (1) nor (3). The repo already owns seven **functional graph** conjugacy classes with exact sizes `1+2+3+3+6+6+6=27`. The new code imports `shapeOrbitCountIsSeven` and `shapeOrbitSizesSumToTwentySeven`; it does **not** recreate the seven original classes.

An exact independent Python orbit enumeration (all 27 triples × all six actions, plus C3) reproduced **10/11/5/7** and all listed orbit-size distributions. This was an independently executed mathematical check; it is not an Agda kernel receipt. The committed `scripts/zipf_ternary27_action_heaps_exact.py` and its regression expose these full orbit and Burnside witnesses for replay.

## Exact Heaps observation / compatibility matrix

Let `V_t(w)` be the full observed distinct-type count for the first t of the **interpreted three-token word**. The four fibres of the full Heaps observation over 27 words are:

| Complete V0,V1,V2,V3 curve | Words | Probability under uniform measure |
|---|---:|---:|
| (0,1,1,1) | 3 | 1/9 |
| (0,1,1,2) | 6 | 2/9 |
| (0,1,2,2) | 12 | 4/9 |
| (0,1,2,3) | 6 | 2/9 |
| **Total** | **27** | **1** |

Every **value-label S3** action preserves the entire Heaps curve, because relabeling cannot change equality/novelty events. `all27CodesHeapsInvariantUnderValueRelabeling` supplies source-written explicit constructor normalizations for **6×27=162** cases. The full Heaps observation therefore descends through the **five value-label equality patterns** into **four Heaps curves**: it merges exactly the `XYX` and `XYY` patterns, but keeps `XXY` distinct.

By contrast, an **axis S3/C3** action can change the full Heaps curve. Example, `AAB -> ABA` by swapping y/z: `(0,1,1,2)≠(0,1,2,2)`. The source-written Agda theorem `coordinateSwapDoesNotPreserveAllHeaps` refutes the universal-invariance premise. Only the terminal number `V3`, not the whole V0..V3 curve, is invariant under reordering positions.

The endomorphism-conjugation action is likewise **not** the same quotient as full Heaps. Stronger negative theorem: two codes `AAB` and `AAC` have **the same entire Heaps curve** `(0,1,1,2)`, but the EXISTING source owner classifies their function graphs as respectively `rank2OneFixedShape` and `rank2TwoFixedShape`. The new `noFunctionalGraphShapeRecoveryFromHeaps` constructs the resulting impossibility of recovering `ShapeOrbit7` from complete Heaps histories alone.

### Exact interface to the original Zipf exponent-zero and ABC six-order laws

Conditional mathematical interpretation: independently sample the three label positions from the **uniform** finite rank-3 Zipf law at integer exponent s=0. Each positive rank has raw weight 1 and normalized mass 1/3; all 3³=27 labeled outcomes have mass 1/27. This is the SAME finite IID occupancy model already used by the repo, not a new empirical Zipf claim.

The **all-distinct** event has exactly six three-token outcomes (ABC/ACB/BAC/BCA/CAB/CBA), total mass `6/27=2/9`. Conditioned on this event, their probabilities are `1/6` each, and their full Heaps curve is **always** `(0,1,2,3)`. This is the precise interface to the earlier `ZipfABC6OrderHeapsQuotientExact` result.

**CRITICAL:** The conditional six-order distribution is NOT the unconditional IID distribution. The fixed-multiset six-word uniform permutation sampler and the IID sampler agree on these **conditional** named orders but have different unconditioned complete-prefix path laws. No hidden generalization to nonuniform Zipf exponents follows. The 27-cell semantics remain a chart interpretation only.

## Numerology / hyperfabric cross-pollination ledger (hard boundary)

```
3³  = 27  -- THREE trit coordinates; original hypervoxel or endomorphism table
3⁶  = 729 = 27²  -- TWO independent 27 cells, ONLY with product structure
3⁹  = 19683 = 27³ -- THREE independent 27-cells in trialectic hyperfabric
3⁵  = 243 -- FIVE trits; source-owned 3-adic/depth-5 carrier
5³  = 125 -- THREE five-valued slots; PR #1414 mode carrier
3!  = 6  -- permutations of three DISTINCT named types
C3  order = 3, S3 order = 6 -- groups not numerals or same action
```

`3⁵=243` and `5³=125` are **different cardinalities**, so their original types cannot be treated as the same finite set by a round trip. A map from 125 states into 243 states may be possible but must be supplied; equality of digit count, a root monodromy metaphor, or a character fingerprint cannot construct it.

The quaternion `u³=-1, u⁶=1` in PR #1414 is a *specific double-cover spin lift of a 120° coordinate/basis action*; this is **not** a statement that 6 word orders, 6 cube permutations or 6 Heaps fibres generate a physical (720^\circ) rotation. PR #1407's 27×729 Fourier counts similarly have their own typed owner. Import them only when the actual theorem carrier and transformation are available on a reconciled branch.

The dialectic x/y/z variables may represent two decision states and an interaction/synthesis relation, as in the user's `Trialectic369HypervoxelUltrametricExact`/hyperformal construction. **Coordinates have distinct roles by default**; an axis permutation is a mere *reorientation of the chart* unless a genuine semantic equivariance theorem is proved. Do not claim swapping thesis with synthesis preserves the original meaning merely because the trit grid is symmetric.

Finally, the source-owned **seven** endomorphism-shape orbits are not equivalent to **five** equality patterns, **ten** coordinate S3 orbits, **eleven** coordinate C3 orbits, or **four** full Heaps curves. Those are five distinct quotients. This is the project's existing PNF/observation-evidence **nonpromotion** discipline applied to exact finite numerology.

## Verification, further Pareto and attribution

- The committed `DASHI/Statistics/ZipfTernary27ActionHeapsExact.agda` uses existing repo type owners, and source-writes 54 cube/code round-trip constructor clauses, 162 value-label invariant clauses, C3-axis rotation-of-order-three, swap involution and two explicit Heaps nonfactorability theorems. **No Agda compiler was run**; this is not a kernel-certified theorem set.
- The independent `itertools.product/permutations` computation over the entire 27-state carrier checked all four action orbits, Burnside fixed-point counts, four Heaps fibres, non-invariance under axis/conjugation, and value-label invariance. Source calculations were executed in local Python; the committed GitHub script itself has not been executed in a byte-identical full checkout. The new focused tests are committed and registered in the existing acceptance runner.
- F13b source-written rational add/fold remains **kernel-pending**, despite prior exact arithmetic checks. S24 full-path constructive coupling has executable finite rational certificates but not an Agda theorem. H08 arbitrary-count majorization/extremal chronology still requires general formal proof.
- Next Pareto targets: (i) typecheck new 27 bridge and F13b on the repository's pinned Agda 2.9/std-stdlib toolchain, (ii) reuse prior shape/orbit typed receivers for explicit evidence provenance rather than composing unrelated group orders, (iii) complete S24's existing source mathematical coupling as an Agda theorem, (iv) extend H08 all-count sharpness where the source family permits it. CI is not the proof boundary. Respect original dated primary authors and earlier repository/PR proof ownership.

Source bibliography: Cauchy–Frobenius lemma and Pólya theorem (1937) in *Encyclopedia of Mathematics*, https://encyclopediaofmath.org/wiki/P%C3%B3lya_theorem ; Dixon & Mortimer (1996) *Permutation Groups* DOI 10.1007/978-1-4612-0731-3; Zimmerlin, Louail, Moussallam & Barthelemy (2025 preprint) *The dynamics of discovery and the Heaps-Zipf relationship*, https://arxiv.org/abs/2510.21481. Modern Heaps chronology is attributed to those original authors, not this numeric demonstration.
