# Hatcher stage injective-but-unsplit tower: word stretching, residual solvability, SU3 false positive
**Date:** 2026-10-27 Australia/Brisbane
**Branches:** Agda hyperfabric PR #1249; Lean4 cross-prover PR #84.
**Source owners:** Hatcher original Alexander sphere group; existing original three-arm geometry PR #1244; original selected-neutrino SU3 W PR #1247; Deicyde/hatcher-at upstream group results.

## Source roots, attribution, and exact claims

Allen Hatcher, *Algebraic Topology*, Example 2B.2, printed pp171–172, original author PDF https://pi.math.cornell.edu/~hatcher/AT/AT-doublepage.pdf (actual P89/P90 screenshots inspected), **originally constructs** injective finite free stages F_(2^n) and their generator-to-commutator inclusions; the three-sector direct product* of these systems is a *free product* of three copies, NOT a direct group product. Stage maps and commutator norm arithmetic are classical group theory, not newly discovered here.

The Nielsen–Schreier theorem (Nielsen 1921 / Schreier 1927) states subgroups of free groups are free; a free group is residually nilpotent (classical Magnus; also follows from Iwasawa's stronger residual finite-p-group result). See current formal donor Mathlib Nielsen–Schreier documentation, and original mathematical articles where available. In particular, no nontrivial **perfect** group can map nontrivially into any residually solvable group. Proof: the image under every further solvable quotient must be perfect, hence trivial; residual solvability separates each nonidentity element, contradiction. This uses only Hatcher's source-perfect limit and classical residual theory. Don't present it as novel residual nilpotence.

**Repo authorship stays typed:** horn geometry, C3 permutation, abelian blind-observer and 2I original simulator belong to #1244. Explicit selected W and qutrit receiver belong to neutrino #1247. Previous #1249/#84 sharp source meridian and acyclic CW telescope mathematical consumers are separate. This cut contributes a short **source-matched consumer proof, explicit finite exact witnesses, and new regression**, with user-directed implementation and OpenAI ChatGPT assistance; native Lean kernels and geometry remain unverified.

## 1. Stage map injection with exact combinatorial length — original source restated constructively

At stage n the three-sector marked free group is F_(3*2^n) on basis e_(s,w). Its successor injection f_n is

    f_n(e_(s,w)) = [e_(s,w0),e_(s,w1)].

For **any freely reduced** word w in these parent generators, each signed parent letter expands to an oriented block of FOUR fresh child letters. Distinct parent basis letters have DISJOINT child alphabets. Two consecutive blocks could cancel only if the corresponding parent letters are inverse, but that is excluded by the parent reduced normal form. Identical consecutive signed parent letters cause no cancellation at their internal block boundary. Therefore

    |f_n(w)|_reduced = 4 * |w|_reduced.
    |f_(n+k-1) ... f_n(w)| = 4^k * |w|.

This proves the injectivity of the **specified combinatorial stage map** by immediate normal-form nonemptiness, without a novel proof of Hatcher's actual geometric ambient stage injection. Sector permutation R(e_(s,w))=e_((s+1)%3,w) commutes with f_n exactly.

An EXACT independent Python test enumerated all reduced words:
* F1 length ≤6: 13 distinct images;
* F3 length ≤5: 4,687 distinct images;
* F6 length ≤4: 17,569 distinct images;
and verified exact 4× reduced length, no collisions and C3 naturality at n=0..4.

This is **combinatorial word length**, not a Euclidean metric or number of independent physical gates; the parent loop can have a long whisker and the source still has unconstructed short wild meridians.

## 2. Stage maps never SPLIT

Each generator f_n(e_i) is a commutator, so the induced map on abelianization

    H1(F_(3*2^n); Z) → H1(F_(3*2^(n+1)); Z)

is EXACTLY ZERO. If there were any homomorphic r:F_(3*2^(n+1))→F_(3*2^n) with r∘f_n=id, abelianizing would give id=0 on the nonzero free abelian group Z^(3*2^n), contradiction.

The new Lean source `Integration/DASHITOE/HornHatcherStageNonsplittingCut.lean` REUSES `HornHopfClaspVsHatcherF2NoGoCut.anyAbelianDetectorKillsCommutator`. Its theorem is more general: ONE old meridian with nonzero abelian character and commutator successor excludes an induced-group retraction. It thereby rules out an actual continuous retraction of Hatcher Y_(n+1) to Y_n that splits the intended π1 inclusion, **if** the actual source-geometry group map is correct. The native topological map-to-π1 transport is not asserted as already completed.

This clarifies the existing #1249 C3 acyclic mapping telescope result: the bonding maps are monomorphisms but NOT split injections. No naive nested free-rose subgraph/retraction carrier can substitute for the actual Hatcher bonding geometry.

## 3. Strong all-depth obstruction: the perfect limit maps trivially to every residually solvable group

Hatcher proves the limiting group G_A is nontrivial and has trivial abelianization. More strongly, **every element of G_A is represented at some finite stage** and after sufficiently many refinements as products of arbitrarily deep commutators; hence G_A is perfect.

A homomorphism from a perfect group to a solvable group has a perfect solvable image, therefore trivial. For any residually solvable receiver R, composing an alleged nontrivial representation G_A→R with a solvable quotient that separates its nontrivial element contradicts the previous sentence. Thus

    Hom(G_A,R) = {trivial}
    for EVERY residually solvable group R.

This applies to ALL finite solvable groups, nilpotent groups and ordinary free groups (by classical residual nilpotence). In particular there are **no nontrivial homomorphisms G_A→F_r**, even though G_A is the direct limit of free stages F_(2^n). There can be no group-theoretic retraction from G_A to a nontrivial finite stage. A continuous geometric map from the actual E into a finite rose cannot induce nontrivial π1 under the Hatcher identification. This is a theorem of the original group's classical algebra, NOT a claim that such maps are nullhomotopic or cannot exist as continuous functions.

Any physical benchmark that only realises finite-stage representations in a nilpotent/solvable subgroup fails even the basic all-depth extension test. By contrast original Gotô's compact semisimple commutator surjectivity can supply abstract SU3 recursion, with no bounded Euclidean gauge conclusion.

## 4. SU3 positive first-commutator but negative second-commutator

Choose classical exact 3×3 clock/shift matrices

    ω = exp(2πi/3) = -1/2+i sqrt(3)/2,
    X = [[0,0,1],[1,0,0],[0,1,0]],
    Z = diag(1,ω,ω²).

Both lie in SU3, yet [X,Z]=ω²I≠I.
They generate the order-27 Heisenberg (extra-special) subgroup H3, with ALL commutators central and the derived subgroup contained in Z(H3). Thus for all a,b,c,d∈H3,

    [[a,b],[c,d]]=I.

A finite qutrit interferometer may therefore measure a nontrivial first-level phase with this EXACT genuine non-Abelian SU3 receiver while becoming TRIVIAL after ONE further Hatcher binary refinement. Such a demonstration does NOT certify a compatible all-depth representation of the perfect wild group.

The exact local program `/mnt/data/check_horn_nilpotent_clock_shift.py` (SHA256 `16d709fbbe738b90b4fb7f7199075d4823ce5d5e80c5b52bddc40da1a4a54eee`) was executed PASS using SymPy algebraic sqrt3. It verified exact unitarity, determinants, nonidentity ω²I commutator, and all 729 pairs of Heisenberg normal forms giving central commutators, plus depth-two vanishing.

New pushed script `scripts/check_horn_su3_nilpotent_clock_shift_extension.py` uses the same mathematical source and 27-element modular normal-form control, but its EXACT GitHub blob has not been byte-replayed locally. Lean #84 has source-written `HornNilpotentSU3ExtensionNoGoCut.lean`, a conditional depth-two source-group/no-nilpotent-receiver theorem. It was NOT Lean kernel checked. This does not identify the original selected W with the Heisenberg root ω²I.

## 5. Explicit Pareto / snowball / Ibrahim decision

* **Abstract group algebra P1:** increasingly complete. The new non-splitting proof, normal form stretching and finite-receiver obstruction close another mathematically meaningful dependency in the staged telescope, with the original Hatcher/Mathlib attribution.
* **Original 3D wild source P2:** still the most valuable missing geometry. PR #1244's latest owner branch adds `HatcherOpenExhaustionCompactAbsorption.lean` and then a **relative nested closed stage** consumer using original Mathlib compactness. The owner still has NOT supplied a concrete, fully matched Hatcher wild satellite carrying the relative annulus and exact meridian group map in the chosen C3 support.
* **Regularity P3:** a TRUE Euclidean short local meridian/systole and compatible bounded gauge or curvature-area hypothesis is still needed. Combinatorial exponential growth 4^k does NOT supply Euclidean L→0.
* **Physical P4–P5:** programmable SU3 clock/shift is a very strong phase and **false-positive** control, not a nontrivial perfect-group representation. Physical Wilson selection, matter anomaly cancellation, calibrated source geometry and independent experiment remain completely separate.
* **Kernel P6:** native Lean/Agda exact-head checks absent; source-written code cannot be called certified theorems.

The immediate **highest-fanout next deliverable** remains a source-original owner #1244 geometric marked-meridian relative correspondence, not another finite SU3 gate array or free-rose comparator. All mathematical priority, original PR ownership, independent execution and physical claims are kept distinct.
