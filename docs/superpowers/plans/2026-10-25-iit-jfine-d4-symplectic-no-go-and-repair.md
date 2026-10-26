# Source D4 and Heisenberg: full symplectic obstruction and minimal repair

**Date** 2026-10-25 (Brisbane). **Owner** [IIT / jFine PR #1148](https://github.com/chboishabba/dashi_agda/pull/1148). **Consumer** [geometry/consciousness PR #1246](https://github.com/chboishabba/dashi_agda/pull/1246). This note augments, rather than replaces, `2026-10-25-iit-jfine-4-1-4-s3-zeta-mixed-characters.md`.

## Original owners and attribution

- `DASHI/Biology/TernaryMonsterSymmetryCandidateExact.agda`: earlier raw nine-cell D4 permutation decomposition **3A1 + B1 + B2 + 2E**.
- `DASHI/Biology/D4NineCellOrbitCompressionExact.agda`: original D4 cell action, three site orbits and quotient/residual codec; distinct from five irrep species.
- `DASHI/Biology/IITJFineFourOneFourS3ZetaGaugeExact.agda`: PR #1148 literal 4+1+4 shell and balanced value-C3/S3 operators.
- `DASHI/Biology/IITJFineD4EquivariantHeisenbergGaugeExact.agda`: PR #1148 site-D4 equivariant chart and relative coordinates; *linear chart*, not a Heisenberg automorphism theorem.
- `DASHI/Biology/IITJFineHeisenbergFourPairSubgroupExact.agda`: PR #1148 selected `H4` multiplication, model `H6` coordinate embedding and source-specific negative witnesses.
- `DASHI/Moonshine/Monster3BFiniteHeisenbergCentralExtensionExact.agda` and `scripts/check_monster_3b_heisenberg_model.py`: prior six-pair model and Weyl evidence; **not** a literal source-JFine/Monster normalizer intertwiner.

Mathematical background for the finite-group decomposition: J.-P. Serre, *Linear Representations of Finite Groups* (1977); D4 character exercise https://www.maths.tcd.ie/~lebed/HW2.pdf. The actual obstruction and explicit repair below are new calculations from these pre-existing site actions, not results attributed to those texts.

## No-go for **every** possible H4 commutator compatible with the source D4

Set `V8=F3^{edge4} ⊕ F3^{corner4}`. Remove the centre's trivial D4 coordinate from the earlier nine-site decomposition:

```
V8 = 2 A1 + B1 + B2 + 2 E
quarter-turn r: order 4
vertical mirror m: order 2; m r m = r^{-1}
```

A Heisenberg central extension of exponent three with quotient `V8` needs a **nondegenerate alternating** form `ω`. If source D4 acts by group automorphisms it must obey `ω(gv,gw)=χ(g)ω(v,w)`, where `χ:D4→F3^×={±1}` is the induced action on its one-dimensional centre.

Over characteristic three, `3∤|D4|=8` so the representation is semisimple. For `χ=1`, each one-dimensional D4 character must occur with **even multiplicity** to admit an invariant alternating pairing: the unique B1 and unique B2 sectors fail this condition. For `χ≠1`, multiplicity of each character λ must equal that of `χλ` in a nondegenerate χ-valued form; the two A1 versus 0/1 occurrences of the other one-dimensional characters contradict that requirement. Thus **no compatible full-rank alternating form exists for any of the four χ**.

The independent `scripts/iit_jfine_d4_symplectic_obstruction_audit.py` converts exactly the source edge/corner site permutations into 8×8 F3 matrices, solves all 28-coefficient linear alternating-form invariance equations via F3 Gaussian elimination and **enumerates every solution**:

| χ(r),χ(m) | form-space dimension | total forms | ranks: multiplicities | max rank |
|---|---:|---:|---|---:|
| +,+ | 2 | 9 | 0:1, 2:2, 4:2, 6:4 | **6** |
| +,- | 4 | 81 | 0:1, 2:10, 4:34, 6:36 | **6** |
| -,+ | 3 | 27 | 0:1, 2:8, 4:2, 6:16 | **6** |
| -,- | 3 | 27 | 0:1, 2:8, 4:2, 6:16 | **6** |

This strengthens the earlier `mirror does not preserve chosen dot cocycle` counterexample: **no alternate nondegenerate cocycle rescues the source eight-trit D4 action**, even with a sign inversion allowed on the centre. This no-go is restricted to the same source D4 *linear quotient action*, with one-dimensional central multiplier. It does not assert that D4 cannot act on any other eight-dimensional module or on a different Monster representation.

## Explicit **minimal** D4-compatible H5 repair and H6-sized completion

Use these equivariant F3 coordinates of the source edge (N,E,S,W) and corner (NW,NE,SW,SE) shells:

```
tE = N+E+S+W,       bE = N-E+S-W
XE = N-S,            YE = E-W
tC = NW+NE+SW+SE,   bC = NW-NE-SW+SE
XC = NW+NE-SW-SE,   YC = -NW+NE-SW+SE
```

The source action becomes `2 A1 + B1 + B2 + 2 E`, with `r(bE)=-bE, m(bE)=bE` and `r(bC)=-bC, m(bC)=-bC`. Both E pairs transform by `r:(x,y)→(-y,x)`, `m:(x,y)→(x,-y)`.

Adjoin one auxiliary B1 coordinate `bE'` and one auxiliary B2 coordinate `bC'`. On the ten coordinates define

```
ω10 = tE ∧ tC + bE ∧ bE' + bC ∧ bC'
     + XE ∧ XC + YE ∧ YC .
```

Here `x ∧ y` means the alternating 2-form on these named coordinate axes. The script constructs the explicit 10×8 source injection, proves by exact F3 matrices that it intertwines *both* D4 generators, and checks `rank(ω10)=10` and `gᵀω10g=ω10` for r and m. The original eight-dimensional D4 subspace restricts to **rank six**, with radical precisely the two unmatched B1 and B2 directions.

The two new coordinates are **minimal** for this source D4 action: no 0- or 1-coordinate extension can make the resulting ten-dimensional-style invariant form symplectic, as the parity/matching of B1 and B2 requires two corrections. The resulting *different* H5 model has quotient dimension ten and nontrivial complex Schrödinger degree **3^5=243**. A further trivial symplectic pair yields a nondegenerate 12-dimensional model with D4 action and the same *symplectic dimension* as the earlier `H6` owner; `rank(ω12)=12`.

**Crucial non-promotion:** the original *chosen H4* can embed into H6 with a chosen non-equivariant pairing (previous PR), but the repaired **D4-invariant source shell is degenerate**. It is therefore *not* a D4-stable embedded H4. The repaired H6 form is abstractly standard symplectic, but no explicit intertwiner into the original six-pair coordinates, let alone the actual Monster normalizer or its `W`, has been constructed in Agda.

## S3 / ζ / ζ²: anti-automorphism rather than automorphism

In the chosen first-four-pair H4 coordinates `(a,c,b)`, the source group law is

```
(a,c,b) (a',c',b') = (a+a', c+c'+b·a', b+b').
```

Source global value rotation `c→c+1` acts by *central left multiplication* (not a group automorphism). Source global sign `(a,c,b)→(-a,-c,-b)` cannot be a group automorphism for **any** nonzero alternating commutator: `ω(-v,-w)=ω(v,w)`, whereas it maps the centre by `-1`.

There is an exact **quadratically corrected anti-automorphism** of the *chosen group law*:

```
A(a,c,b)=(-a, -c+a·b, -b)
A(x y)=A(y) A(x),    A²=id.
```

It is not the source S3 reflection, which lacks the `a·b` correction. With symmetrised centre `t=c+a·b`, the map is simply `(t,v)→(-t,-v)`. The local audit checked all **19683** H4 states against the nine natural generators (**177147** generator-state anti-law checks), plus involutivity for every state; the anti-law also follows algebraically from bilinearity. This clarifies the mathematical provenance of phase-conjugation analogies without identifying the physical/Monster ζ and ζ² eigenspaces.

## Acceptance, phases and priorities

1. **Finite calculation**: independent local F3 exact arithmetic confirms the four full solution-space histograms, rank-10 repair, rank-6 source restriction, rank-12 completion and 177147 anti-involution generator checks. The committed script is integrated into `scripts/iit_numeric_verification.py`.
2. **Formal kernel work OPEN**: extract the source 8×8 matrices as Agda finite-linear maps, formalise the **universal all-four-character rank≤6 theorem**, construct the concrete rank-10 and rank-12 forms, prove D4-equivariance and the corrected H4 anti-law. Existing Agda D4 chart and Monster H6 owners must be reused. No fresh exact-head Agda compiler receipt is asserted.
3. **Same-object Monster gate OPEN**: derive a certified symplectic basis-change into the existing H6 MODEL, and *separately* establish an actual 3B-normalizer action/character intertwiner from original Monster source data. Arithmetic `65610=90×729=810×81` is not this intertwiner.
4. **Physical consumer gate OPEN**: only after specified instrumentation/measurement of neural, optical, causal or quantum systems could a model be interpreted empirically; no consciousness, magnetism, or quantum-ζ effect follows from finite-character coincidences.

The main high-leverage discovery is **an actual incompatibility plus an explicit minimal repair**, rather than another numerological identification. The correct physical-interpretation boundary has not moved.

## Cross-lane correction: PR #1250 already has a different D4/H6 action

The adjacent owner [JFine 3B action-first PR #1250](https://github.com/chboishabba/dashi_agda/pull/1250) must **not** be mistaken for a counterexample to the rank-eight result. In `scripts/jfine_3b_d4_equivariant_chart.py`, a D4-stable **two-label × six-fibre rechart** gives a D4 action on the *chosen 12D Heisenberg quotient* by simultaneously permuting **six translation and six modulation** axes. That representation differs from the natural eight-relative-site D4 quotient in this audit. Its symplectic pairing can be nondegenerate and D4-invariant because it includes both each six-coordinate module and its dual.

The same PR's `reflect_heisenberg(a,b,t)=(-a,b,-t)` is a legitimate centre-inverting **automorphism** of the chosen H6 action: it is anti-symplectic on the quotient (multiplier -1). This does **not** equal the source H4 value-sign action `(a,c,b)→(-a,-c,-b)`, which acts by -I on *both* quotient blocks and is symplectic (multiplier +1). The source H4 sign is not an automorphism; the quadratic correction supplies an **anti**-automorphism. No contradiction exists once the actions, centres and charts remain separately typed.

More importantly, #1250's later source-aligned Monster character audit reportedly **rules out its original chosen geometric D4** on the actual 3B phase sector via published involution/order-six character values; it discusses a *distinct conditional signed-monomial 90-space repair* and the unresolved source-selected 6.Suz linear-character family. Our new 8→10→12 **finite symplectic repair does not repair that actual Monster character obstruction**, certify its signed 90-module, or identify the faithful 6.Suz 78-character. Keep the active discriminators independent:

- source eight-site D4-preserving Heisenberg extension: **NO**, all multipliers exhausted (this cut);
- finite D4-stable symplectic 10/12D completion: **YES**, chosen model (this cut);
- #1250 six-pair chosen geometric Heisenberg normalizer action: **YES at model level**, but **not the source eight-dimensional H4 action**;
- actual Monster 3B / 6.Suz source-selected D4/Hom character: **OPEN / source-dependent**, subject to #1250's separate no-go and more recent 6.Suz family qualification.

These are deliberately different proof objects. Use #1250's existing backend-free D4 character and actual-source screening producers rather than rebuilding or bypassing their authority checks.


## Explicit six-pair model weld and a group-structure discriminator

The companion source `scripts/iit_jfine_d4_heisenberg_h6_model_weld.py` closes the **abstract H6 model symplectic-coordinate** step that was previously left as an anticipated map. List the repaired 12D hyperbolic pairs as

`(tE,tC), (bE,bE'), (bC,bC'), (XE,XC), (YE,YC), (u,v)`.

Map to the original standard six translation/modulation pairs by taking **translation coordinates to be the six second entries** and **modulation coordinates to be the six first entries**. The source H6 form `ω((a,b),(a',b'))=b·a'−b'·a` then agrees exactly with the repaired D4 form, coefficient by coefficient. This is an **explicit symplectic basis permutation**, not an inference from equal dimensions.

With source H6 multiplication (a,b,c)(a',b',c')=(a+a',b+b',c+c'+b·a'), the symmetrised chart t=c+a·b gives a formal quadratic correction a·b−(La)·(Lb). **For these repaired D4 generators that correction is identically ZERO**: the same signed orthogonal L acts on both translations and modulations, preserving the actual cocycle b·a' as well as its commutator. Thus the original source centre coordinate remains fixed, and the eight-site D4 action intertwines the repaired H3×C3² group law. This is different from the incompatible extraspecial H4 group law; the previous requirement of a nonzero D4 central correction is superseded.

The invariant source eight-plane's restricted commutator has rank six and radical dimension two. Consequently its central preimage in the repaired H6 MODEL is an exponent-three group with

```
group order: 3^9 = 19683
centre order: 3^(1+2) = 27
group type: H3 × C3^2  (NOT extraspecial H4)
```

This is a decisive **group nonisomorphism** even though the underlying pointed chart still has the same cardinality `3^9`. More sharply, the nontrivial complex irreducible dimensions differ:

| Same-order mathematical model | Linear irreps | Nonlinear irreps | Degree-square sum |
|---|---:|---|---:|
| Previous chosen extraspecial H4 | 6561 | **2 × degree 81** | 19683 |
| New source-D4-stable H3 × C3² | 6561 | **18 × degree 27** | 19683 |

The two models have the same **6561** linear-character count and the same order; neither matches the other's nonlinear representation spectrum. This is a stronger acceptance discriminator than 19683 or zeta-sector dimension coincidences. The repaired H6 same-model symplectic map is now finite-verified, but **actual source Monster H6 subgroup attachment and the actual Monster W/intertwiner remain unproved**. Kernel formalisation of this exact chart and central correction is the next Agda-specific cut.


## Source-written Agda necessary-condition elimination (proof-assistant boundary)

Added `DASHI/Biology/IITJFineD4SymplecticMultiplicityObstructionExact.agda` and imported it from the existing IIT integration aggregate. It **reuses** the pre-existing `TernaryMonsterSymmetryCandidateExact.D4IrrepKind` and `rawNineMultiplicity` owners (it does not introduce competing D4 species). The new typed source shell records `2A1+B1+B2+2E`.

The concrete theorem `noCompatibleNecessaryMultiplicity` eliminates all four central-multiplier cases using Agda's impossible patterns: `EvenMultiplicity 1` is empty in the untwisted case; `MatchedMultiplicity 2 0` or `MatchedMultiplicity 2 1` is empty in the three nontrivial cases. These are nonvacuous, source-irrep-indexed **necessary conditions**. The module explicitly does **not** claim to have kernel-derived the representation-theoretic implication from a full-rank alternating matrix to those conditions. The universal semisimple nondegenerate χ-valued pairing lemma and finite matrix interpretation remain Agda proof obligations. New Agda module and aggregate import are source-written but **not typechecked** in the present runtime; the exhaustive independent Python invariant-form matrix calculation remains the primary locally executed certificate.


## 25 October exact-head executable audit and strengthened concrete group isomorphism

**Correction to first committed H6 script:** the initial `iit_jfine_d4_heisenberg_h6_model_weld.py` referred to undefined helper attributes `x.eye/x.mm/x.tr/x.R8/x.M8`. The owner module exports `identity/product/transpose/R/M`; these imports/references have now been corrected in the committed branch. The first version was **not executable as committed**, regardless of the correctness of an independent equivalent local calculation. Do not treat the older local receipt as exact-head script execution evidence.

An independent local F3 reconstruction on 25 October then passed *all four* alternating-form solution-space distributions, `rank(T)=8`, exact D4 source intertwiners, rank 10 and 12 repairs, 144 basis-pair form comparisons, 338 D4 lifted Heisenberg generator-pair products, and the new **177147 source subgroup–generator products**. This checks the mathematical algorithm, **not yet an exact GitHub checkout execution**. The same checks are integrated into `iit_numeric_verification.py`.

**Explicit proof of `H3 × C3²`, not just counts.** Use source D4 character coordinates `s=(tE,tC,bE,bC,XE,YE,XC,YC)`. Under the repaired 12D form and its standard six-pair Heisenberg coordinates, the D4-stable source subgroup is
```
a6 = (tC,0,0,XC,YC,0)
b6 = (tE,bE,bC,XE,YE,0)
c  = original central trit
```
and its inherited group law is
```
(s,c)(s',c') =
  (s+s', c+c' + tE*tC' + XE*XC' + YE*YC').
```
Hence the literal group isomorphism
```
toH3xC3sq(s,c) =
  ((tC,XC,YC), (tE,XE,YE), c, (bE,bC))
```
with a literal two-sided inverse and separately additive last two central trits. The committed H6 script tests *every* 3^9 source element against nine generators (177147 compatibility checks). The centre order 3^3=27 and nonlinear degree-27 spectrum then follow from the standard extraspecial H3 × abelian-C3² character law. Unlike the original selected H4 (centre order3, nonlinear degree81), these are genuinely **nonisomorphic** group objects.

**Elementary algebraic rank-bound proof without relying on enumeration alone:** in characteristic three, 3 does not divide 8=|D4|. The source shell is semisimple `2A1+B1+B2+2E`. The 4D sum of one-dimensional sectors `U=2A1+B1+B2` is orthogonal to the 4D E-isotypic part under every χ-valued alternating form. For χ=trivial, B1 and B2 are radical; for χ=A2, the two A1 directions are radical; for χ=B1, B2 is radical and the two A1 copies can pair with only one B1 direction, leaving another radical direction; χ=B2 is analogous. Thus `dim(rad ω)≥2` and `rank ω≤6` in every case. This argument upgrades the finite enumeration into a general proof for **the specified source D4 module**. The Agda file currently formalises the necessary multiplicity contradictions; the invariant-form-to-necessary-condition implication and concrete rank matrices are NOT Agda kernel-certified.

**Proof boundary:** source-written Python and Agda are committed and locally reconstructed arithmetic was executed; Agda full typecheck and exact-head GitHub checked-out scripts have not been executed here. No inference about the literal Monster 3B normalizer, its 6.Suz faithful-family restriction, or any quantum/biological physical mechanism is made.

## 25 October corrected D4/H6 source action

The earlier proposed *required quadratic central correction* was an error. The generic symplectic lift recipe may contain a quadratic term, but the specific simultaneously orthogonal D4 repair makes that term vanish. The H6 model audit now checks the common six-coordinate orthogonal action and **354294** source-state/generator D4 group-homomorphism instances, with unchanged source centre. It also checks **177147** concrete H3×C3² product compatibility instances. Independent local F3 reconstruction passed; execution of exact committed checkout and Agda kernel remains unobserved.

This is a genuine **chosen finite-model D4 automorphism** of the repaired H3×C3² subgroup, not a D4 automorphism of the earlier extraspecial H4. The separate quadratically corrected global S3 sign **anti**-automorphism remains valid; the two corrections must not be conflated. Existing Monster 3B normalizer, 6.Suz family and physical evidence gates are unchanged.


## 25 October: exact source chart and additional Agda subcarrier

The original `Gauge.FourOneFour` relative sheet (raw edge tuple N,E,S,W; corner tuple NW,NE,SW,SE; independent centre c) maps by the literal F3 matrix `T` to `(tE,tC,bE,bC,XE,YE,XC,YC)`. An independent local F3 reconstruction verified `T Tᵀ=diag(1,1,1,1,2,2,1,1)`, hence **the explicit two-sided inverse** is `Tᵀ diag(1,1,1,1,2,2,1,1)`; all **6561** eight-trit relative states and both D4 generators were checked, hence **19683** nine-trit source states with centre. The committed `iit_jfine_d4_symplectic_obstruction_audit.py` now performs this same finite regression, and the existing IIT numeric aggregate requires it.

The new source-written `DASHI/Biology/IITJFineD4H3RadicalSourceH6Exact.agda` defines the nine-coordinate character chart, directly embeds it into the prior `Monster3BFiniteHeisenbergCentralExtensionExact.Heisenberg6` source, supplies an explicit inherited product and a proposed source-level closure equality, and gives a two-sided record-level codec to `H3TimesC3Squared`. This is a genuine **typed-model reuse** of the six-pair H6 owner, not a second invented Heisenberg law. It is imported by `IITPhiIntegrationEverything`.

**Formal admission remains careful:** the Agda *original* Gauge.FourOneFour → character-T conversion and its two-sided source proof, the literal matrix rank≤6 theorem and the D4 product preservation are not yet kernel-certified; the new Agda closure and codecs are also source-written only pending typecheck. Python independently checked the finite source chart and 177147 H3×C3² + 354294 D4 source-group generator laws. The actual Monster-normalizer action and characteristic-zero representation selection remain separate.


## 25 October source-typed orientation bypass supersedes the apparent universal 8D obstruction

**Clarified quantifier:** the existing rank≤6 theorem is only for the *literal original geometric* site-D4 representation `2A1+B1+B2+2E`. It does not preclude **a modified, non-geometric D4 action on the same original nine-trit carrier**. The original `TernaryMonsterSymmetryCandidateExact` already describes the orientation/pseudoscalar expansion as a distinct representation, and `D4IrrepFiniteFrickeEquivariantExact` already owns oriented-sector C2 charts. These authors/code owners retain credit. Our NEW smallest-action-change answer is `docs/superpowers/plans/2026-10-25-iit-jfine-d4-orientation-bypass-pareto-ibrahim-snowball.md`.

One-character-line edit gives `2A1+2B1+2E` (flip original corner-B2 reflection) or `2A1+2B2+2E` (flip original edge-B1 reflection). Each differs from the original eight-dimensional raw matrix at rank ONE, preserves the original 19683 underlying states, supports a rank-eight D4-invariant symplectic form and retains the genuine four-pair extraspecial H4 **under the MODIFIED D4 action**. Neither reindexes the original site-permutation mirror; both change the operation. The original geometric action + new 10/12D symplectic completion + degenerate H3×C3² subgroup remains valid and separately source-typed.

Python source `scripts/iit_jfine_d4_single_line_orientation_bypass.py` and Agda source `DASHI/Biology/IITJFineD4OrientationLineH4BypassExact.agda` are now committed to #1148 and consumed by the existing numeric and formal aggregates. Independent local Python reconstructs 354294 B2→B1 H4 automorphism generator checks and 177147 B1→B2 checks. The exact newly committed GitHub Python script, and the new Agda module, are not verified by an exact-head runtime here (Agda/GAP not installed in the local runtime).

**Actual Monster discriminator:** the pointed phase class characters for both modified D4 actions have involution values `162, 2916, 324`, not in PR #1250's source-backed necessary Monster 3B values `{66,90,1458}`. Hence these finite-model repairs CANNOT be promoted to the selected Monster phase-preserving D4 action. The source-favourable signed-multiplicity 90-space and full 6.Suz/Hom class-selection gate are the Pareto priority, not yet another geometric count. The five-orbit D4/Ibrahim acquisition lane is also a different representation type. See the new Pareto/attribution ledger for all original sources and stop conditions.
