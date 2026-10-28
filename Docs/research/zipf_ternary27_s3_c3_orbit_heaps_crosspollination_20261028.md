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

**CRITICAL:** The conditional six-order distribution is NOT the unconditional IID distribution. The fixed-multiset six-word uniform permutation sampler and the IID sampler agree on these **conditional** named orders but have different unconditioned complete-prefix path laws. A later exact conditioning theorem now **does** extend the uniform six-order conditional law to every strictly positive nonuniform IID distribution when the first three draws contain all three labels exactly once; see the additional subsection below. It does **not** extend the unconditional first-discovery Plackett–Luce law to a uniform distribution. The 27-cell semantics remain a chart interpretation only.

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


## Additional Pareto cut: general alphabet-by-length fibres

The action-sensitive cube result extends constructively to arbitrary finite **word length n and alphabet size q**, using the already-owned IID full-Heaps path law as the probability receiver.

A complete Heaps curve corresponds to a binary novelty event at each position: the first position is always novel, and the subsequent n−1 positions contain at most q−1 further novel events. Every such event pattern can be realized on a q-label alphabet. Therefore the **number of distinct full Heaps curves** is

```
H(q,n) = Σ_{j=0}^{min(q−1,n−1)} C(n−1,j).
```

The **number of named words that realize a particular curve** is an exact product: at a new-type event with s distinct types already seen, choose one of q−s unused labels; at a repeat event, choose one of s old labels. The product over all positions gives the fibre cardinality, and the fibres sum to q^n.

The new function `scripts/zipf_ternary27_action_heaps_exact.uniform_heaps_curve_multiplicities(q,n)` implements this *integer fibre-count* computation and compares its normalization against the pre-existing `zipf_full_heaps_path_distribution_exact.full_heaps_curve_law((1,)*q,n,"iid")`. Thus it **reuses** the canonical probability distribution, rather than introducing another IID statistical model. Executable resource bounds (q≤7,n≤10,q^n≤30000) are not claimed as a limitation on the combinatorial formula itself.

Distinct typed cases:

| Source interpretation | Total named words | Complete Heaps curves | Example fibre counts |
|---|---:|---:|---|
| 3 labels × 3 positions (3³) | 27 | 4 | 3,6,12,6 |
| 3 labels × 5 positions (3⁵) | 243 | 11 | 3,6,12,6,24,12,18,48,24,36,54 |
| 5 labels × 3 positions (5³) | 125 | 4 | 5,20,40,60 |

The 11 Heaps curves on 3⁵ words happen to match the **11 C3-coordinate orbits on 3³ words**. This equality is explicitly recorded as a **numerical coincidence between two different quotient sets**, not an observation-preserving bijection. The carrier cardinalities 243 versus 27, the positions and group actions differ. No 720° quaternion, Monster 3B representation or quintic polynomial result follows.

The expanded regression independently exhausts all q≤5 and n≤6 with q^n≤30000 and checks these named-word fibre counts against `itertools.product`. The exact integer count/multiplicity formula is classical occupancy combinatorics. It is not a new Zipf scaling law, an empirical proof of Heaps universality or an Agda kernel certificate. Historical origins remain with Cauchy/Frobenius/Burnside, Pólya, original Heaps/Zipf researchers and the separately credited repo source owners.


## Later exact Pareto cut: five equality patterns -> four Heaps histories

**This is an actual observation-factor construction, not a 5=4 cardinality claim.** New source-written `DASHI/Statistics/ZipfThreeDrawEqualityPatternFactorExact.agda` consumes the original `RecursiveFibreTower.LevelTwoCode` and `ZipfTernary27ActionHeapsExact.codeHeaps`. It defines an explicit quotient map into five value-relabel (S_3) equality-pattern classes:

```
AAA    -- all same
AAB    -- first two same
ABA    -- first and third same
ABB    -- last two same
ABC    -- all distinct
```

The module supplies 27 explicit source constructor clauses for `equalityPattern`, five canonical representatives, 27 literal proof cases that **the actual source Heaps observable factors through that quotient**, and 162 source-written proof cases that the quotient is invariant under the already-owned six value-label permutations.

The resulting 5-to-4 observation sends `AAA -> (0,1,1,1)`, `AAB -> (0,1,1,2)`, **both `ABA` and `ABB` -> (0,1,2,2)**, and `ABC -> (0,1,2,3)`. The explicit no-go `noUniversalEqualityPatternRecoveryFromHeaps` uses the two different ABA and ABB constructors with the same complete Heaps curve. This is a rigorous source-level non-invertibility witness, not a speculative weld. The existing seven endomorphism **conjugacy** classes remain a separate action, unchanged.

Classical roots: finite set partitions, restricted growth encodings, Stirling/Bell partition counting, Cauchy–Frobenius/Burnside; original DASHI six-action, hypervoxel and Heaps owners preserve ownership. The adapter is a new Johl Brown-directed / OpenAI ChatGPT-assisted representation map dated 28 October 2026. It has **not** been Agda typechecked.

## Later exact Pareto cut: nonuniform weights and collision-moment closure

For any strictly positive finite IID distribution (p_1,ldots,p_q), define (S_2=Σ_i p_i²) and (S_3=Σ_i p_i³). The pushforward of the **complete three-draw IID word law** to the four Heaps curves is exactly

```
(0,1,1,1) : S3
(0,1,1,2) : S2 - S3
(0,1,2,2) : 2(S2 - S3)
(0,1,2,3) : 1 - 3 S2 + 2 S3.
```

The formulas follow by decomposing the three draws into all identical, first-two identical, first-two different and last repeats vs all-distinct outcomes. They sum to one, and are nonnegative. This is classical occupancy/symmetric-power-sum mathematics, NOT a new empirical law or independent probabilistic carrier.

The new `scripts/zipf_three_draw_moment_conditioning_exact.py` accepts the canonical source histogram weights, computes (S_2,S_3) using exact `Fraction`, and checks the resulting entire-prefix law against the PRE-EXISTING `zipf_full_heaps_path_distribution_exact.full_heaps_curve_law`. Its regression independently enumerates the weighted named words for **117** two-, three- and four-label configurations (5,985 exact three-token words in total); every equality passed in the separate local arithmetic check.

**Crucial measure distinction:** The Heaps curve and equality pattern are invariant under value-S3 relabelling as **deterministic observations**. A nonuniform IID measure is NOT invariant under arbitrary relabelling of sample labels; for (p=(6/11,3/11,2/11)), `AAA` and `CCC` have the same Heaps curve, but masses `216/1331` and `8/1331`. Their statistical *observation pushforward* is symmetric in the weights; this does not imply equality of the original word masses.

For the actual finite three-rank (s=1) Zipf masses `(1,1/2,1/3) / (11/6) = (6/11,3/11,2/11)`, the exact Heaps curve law is:

| Complete Heaps curve | Rational probability |
|---|---:|
| (0,1,1,1) | 251/1331 |
| (0,1,1,2) | 288/1331 |
| (0,1,2,2) | 576/1331 |
| (0,1,2,3) | 216/1331 |

**New general conditioning theorem (elementary IID product proof):** For any `K>=1` and strictly positive p on **K named types**, condition the FIRST K IID draws on **all K types appearing exactly once**. Each of the (K!) named permutations has the same *unconditional* mass (prod_i p_i), hence the conditioning-event mass is (K!prod_i p_i), and each permutation's conditional probability is exactly (1/K!). This holds even when Zipf exponent s≠0. The executable enumerates K≤7, but the product identity is valid for any finite K.

This conditional law is distinct from the **UNCONDITIONED eventual first-appearance order**, which has the original Plackett–Luce size-biased law. Under the `(6,3,2)` example, `P(ABC | first three all distinct)=1/6`, but `P_PL(ABC)=18/55`. Thus unconditional time/rank sampling cannot be replaced with the conditional order without explicit evidence.

**Attribution and limits:** This is elementary IID occupancy, symmetric power-sum and conditioning mathematics, with original Heaps/Herdan/Zipf and Luce (1959)/Plackett (1975) credits. Existing source proof ownership is unchanged. The three-draw moment algebra was independently verified with exact arithmetic, and new source/tests have been committed; the whole branch's tests and Agda kernel have **not** been executed. Zero or negative weights are rejected rather than extrapolating an unsupported uniform conditional law. No quaternion/Monster/NS/RH or 11-orbit coincidence becomes a same-object theorem.


## Restricted-growth refinement: Stirling orbit cardinalities, not numerology

The new `equality_pattern_heaps_fibres(q,n)` in the EXISTING `scripts/zipf_ternary27_action_heaps_exact.py` enumerates canonical **restricted-growth strings**. Each is a representative of a **value-label permutation orbit** on q-letter n-position words. It calculates that orbit's exact cardinality as the falling factorial `(q)_k=q(q−1)...(q−k+1)`, where the representative uses k distinct values. It pushes each orbit's count forward to the actual complete Heaps discovery curve and confirms **exact agreement with the existing** `uniform_heaps_curve_multiplicities`, which in turn checks the canonical `full_heaps_curve_law` owner.

For n=3 and q=3, the equality-pattern orbits are `AAA,AAB,ABA,ABB,ABC` (five), of respective cardinalities `3,6,6,6,6`. The full Heaps observation merges `ABA` and `ABB`, leaving FOUR curves. This is now an explicit source-written Agda 27-state factor map, not an assertion inferred from counts.

For q=3,n=5: the exact numbers of value-renaming orbits by used label count k are the classical Stirling values `S(5,1)=1`, `S(5,2)=15`, `S(5,3)=25`. There are **41** fine equality-pattern classes, which map to **11** complete Heaps curves. Weighting the orbits by the source label choices gives `1*3 + 15*6 + 25*6 = 243 = 3^5`.

For q=5,n=3: the corresponding `S(3,k)` values are `1,3,1`. There are **5** fine equality-pattern classes mapping to **4** complete Heaps curves. The orbit-weight sum is `1*5 + 3*20 + 1*60 = 125 = 5^3`.

The general original combinatorial identity is

```
q^n = Σ_{k=1}^{min(q,n)} S(n,k) (q)_k.
```

This is a **true typed factorization** through set-partition patterns and Heaps novelty curves. It supplies **no** isomorphism between the 11 Heaps curves on 3⁵ words and the unrelated 11 coordinate-C3 orbits on the 27-state cube. Neither source group action nor the probability measure is transported by a coincident orbit count.

A separate local Python `Counter`/independent named-word enumeration checked **all 30 q,n configurations** for 1≤q≤5, 1≤n≤6 against canonical restricted-growth class cardinalities, covering **26,214 named words**, including 3³, 3⁵ and 5³. The newly committed focused regression includes the same checks; **the full exact-head checkout/runner was not executed**, and the source-written Agda factor was not Agda-kernel checked. Classical set partitions and Stirling numbers are inherited mathematics; new code/observation map under Johl Brown with OpenAI ChatGPT assistance is repository integration only.


## Exact five-pattern probability factor under nonuniform IID

The same genuine 27-code observation factor persists as a *probabilistic pushforward* under arbitrary nonuniform IID label probabilities, not as a measure-invariant action. The newly committed function `iid_three_draw_equality_pattern_law` computes the **fine five-equality-pattern distribution** using the existing (S_2,S_3) owners:

| Fine equality pattern | Probability |
|---|---|
| AAA | S₃ |
| AAB | S₂ − S₃ |
| ABA | S₂ − S₃ |
| ABB | S₂ − S₃ |
| ABC | 1 − 3S₂ + 2S₃ |

The already formalized observation map merges the **ABA** and **ABB** rows. Therefore its coarse full-Heaps law is `S₃, S₂−S₃, 2(S₂−S₃), 1−3S₂+2S₃`. The code checks this exact pushforward against the *pre-existing* canonical full-path law; its regression independently enumerates all named three-letter words for the 117 positive-weight cases. Distinct named words (e.g., AAA and CCC) generally have unequal probability; it is the **marginalized equality-pattern class**, not the raw word, that has the stated symmetric probability.

This factor is a genuine observation-space map with type-preserving probability aggregation. The 720° spin lift in PR #1414, Fourier fibres in #1407, seven source-owned endomorphism shapes, and Ibrahim Monster 3B remain separate and cannot be inferred from this arithmetic. The mathematical formulas are classical IID occupancy/symmetric-polynomial identities. New repository code is source-written and independently enumerated; its full exact-HEAD pytest/Agda kernel status remains unverified.
