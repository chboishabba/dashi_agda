# 25 October 2026 — D4/JFine orientation-line bypass: Pareto, snowball and Ibrahim attribution

**Original mathematical-source owner:** [DASHI IIT PR #1148](https://github.com/chboishabba/dashi_agda/pull/1148), branch `agent/iit-phi-integration-maxcut-20261013`. **Separate actual Monster character owner:** [JFine/Monster PR #1250](https://github.com/chboishabba/dashi_agda/pull/1250). **Original source facts** remain owned by their authors and source publications; finite repo models do not retroactively establish authorship of earlier theorems.

## Precise question and quantifiers

The old claim "source D4 and extraspecial H4 are incompatible" needs its actual quantifier:

> For the ORIGINAL literal 3×3 positional D4 action on the eight centre-relative F3 coordinates, no D4-equivariant nondegenerate alternating commutator (for any one-dimensional character on the central C3) exists.

This is already shown by the `2A1 + B1 + B2 + 2E` semisimple obstruction and exhaustive four multiplier matrices (ranks ≤6). It is NOT a no-go for every action of the same abstract D4 on the same 3^8-element underlying set.

## Reuse archaeology (source roots, not name matches)

1. `DASHI/Biology/TernaryMonsterSymmetryCandidateExact.agda` — earlier geometric nine-cell character `3A1+B1+B2+2E`; explicitly warns that orientation/pseudoscalar refinement changes the representation and does not follow from the unmodified nine-cell permutation.
2. `DASHI/Biology/D4NineCellOrbitCompressionExact.agda` — literal quarter/vertical-mirror action and source site orbit quotient, prior independent of this bypass.
3. `DASHI/Biology/D4IrrepFiniteFrickeEquivariantExact.agda` — existing ten oriented D4 irrep labels and a finite C2-equivariant Fricke-style chart. **NOT** an already-proved rank-one mirror or geometric-shell H4 operator.
4. `DASHI/Biology/IITJFineFourOneFourS3ZetaGaugeExact.agda`, `IITJFineD4EquivariantHeisenbergGaugeExact.agda` — owner PR #1148: existing original nine-site, centre-relative, and D4-equivariant sheet codecs. New T and inverse reuse these exact ordered coordinates.
5. `DASHI/Biology/IITJFineHeisenbergFourPairSubgroupExact.agda` — prior chosen extraspecial H4 law on the original underlying 3^9 carrier. Old geometric D4 mirror **does not** preserve that chosen law.
6. `DASHI/Moonshine/Monster3BFiniteHeisenbergCentralExtensionExact.agda` — existing standard six-pair Heisenberg group/cocycle; no new stand-alone group multiplication introduced. `OggSSPP2WeilHeisenbergNativeBidiExact.agda` is a prior **same-law cocycle-coordinate transport** for H1. It cannot repair a rank-deficient commutator for an unchanged representation.
7. `DASHI/Wikimedia/IbrahimMonsterFiveOrbitD4KernelCharacterExact.agda` and `IbrahimMonsterFiveOrbitD4N3BCharacterAcquisitionExact.agda` — earlier **five-orbit quotient** character `(5,5,1,3,3)=3A1+B1+B2`; this is NOT the eight-trit source D4 action or a 3B subgroup. `SnowballAttributionProvenanceInvariantExact.agda` governs attribution-role persistence. Ibrahim-labelled repo work is an acquisition/snowball *lane*, NOT original authorship of Serre's representation theory or Barraclough–Wilson's character table.
8. [JFine/Monster PR #1250](https://github.com/chboishabba/dashi_agda/pull/1250): existing actual Monster involution-character discriminator and more productive source-selected Suzuki/Hom-space route. Its 90-dimensional signed representation and source-filtering operations must not be replaced with a new geometric 90-permutation assertion.

**Foundational original sources:** J.-P. Serre, *Linear Representations of Finite Groups*, Springer (1977), DOI `10.1007/978-1-4684-9458-7`; R. W. Barraclough and R. A. Wilson, *The Character Table of a Maximal Subgroup of the Monster*, LMS J. Comput. Math. 10 (2007) 161–175, DOI `10.1112/S1461157000001352` (https://www.rwb.me.uk/table/index.html has original tables); ATLAS of Finite Group Representations, https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M/; T. Breuer, K. Magaard and R. A. Wilson, *Some steps in the verification of the ordinary character table of the Monster group*, reproducible GAP documentation at https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/htm/ctblm.htm. Source-derived class data are **inputs**, never results authored by these Python scripts. OEIS sequences are transcriptions/search coordinates, not a second independent original Monster source.

## New exact mathematical bypass: change ONE representation line, not the carrier

Keep the same centre and original ordered eight relative-coordinate sheet. Prior explicit source matrix `T` has invertible inverse
`T^{-1}=T^transpose diag(1,1,1,1,2,2,1,1)` over F3.
In character coordinates `(tE,tC,bE,bC,XE,YE,XC,YC)`, the old source vertical mirror acts by `bE→bE`, `bC→−bC`. The original D4 rotation acts by minus on both these one-dimensional B species.

**Refinement I:** flip JUST the mirror sign of bC. The new 8D D4 module is
`2A1 + 2B1 + 2E`. The matrix difference on ORIGINAL source positions is exactly rank one: `M_new−M_site = −p_B2` where `p_B2` is the rank-one B2 corner-mode projector. The D4 presentation is preserved. The unchanged trit carrier now has full-rank D4-invariant alternating form pairing
`(tE,tC), (bE,bC), (XE,XC), (YE,YC)`.
With existing standard H4 cocycle and translation `(tC,bC,XC,YC)`, modulation `(tE,bE,XE,YE)`, both D4 generators act by the SAME 4×4 signed orthogonal matrix on translation and modulation; hence they preserve the FULL unsymmetrised cocycle, not merely its commutator, with the centre fixed. The resulting H4 has order 19683, centre 3 and nontrivial central irrep degree 81.

**Refinement II (dual):** flip JUST the edge B1 mirror sign, producing `2A1+2B2+2E`. This is also a rank-one defect and preserves the same full H4 cocycle. Axis/diagonal reflection signatures exchange. These are minimal by nonzero operator-edit rank: rank zero is the obstructed original geometry; rank one suffices.

**Semantics:** both refinements are NEW LINEAR source-carrier actions, not the original site-permutation action. No new trits or hidden external orientation bit is required; the representation law itself is changed. A Fricke C2 label correspondence or an SO(3) character equalities from elsewhere in the repo do not make it a physical orientation field.

## Exact finite checks / numerical discriminator

`scripts/iit_jfine_d4_single_line_orientation_bypass.py`, wired into `scripts/iit_numeric_verification.py`, checks original 6561 relative-chart roundtrips, the D4 presentation, rank-one original-coordinate mirror defect, full rank-eight invariant form, and the first 354294 / dual 177147 source-H4 generator product identities. An independent standalone local Python implementation (`/mnt/data/d4_orientation_bypass_audit.py`) was run on 25 Oct 2026 and passed the first family including all 354294 products. Exact newly committed GitHub checkout source and Agda are **not** claimed executed in this session. The Agda `IITJFineD4OrientationLineH4BypassExact.agda` defines an explicit typed NEW mirror, exhibits a counterexample showing it differs from the original mirror, and embeds into the previous H6 owner; it is source-written, NOT kernel-checked.

For *actual moving* 10-marker pointed states (not ten inert marker copies), the first and second refinements give:
| Fingerprint | bC:B2→B1 | bE:B1→B2 |
|---|---:|---:|
| F3^9 states | 19683 | 19683 |
| Fine D4×global-value S3 orbits | 535 | 535 |
| Moving-marker pointed D4×S3 orbits | 4576 | 4576 |
| Phase-ζ character 1 | 65610 | 65610 |
| Phase-ζ character r² | 162 | 162 |
| Phase-ζ character r or r³ | 18 | 18 |
| Phase-ζ character axis mirror | 2916 | 324 |
| Phase-ζ character diagonal mirror | 324 | 2916 |

The *previous original* geometric-source joint orbit counts are 490 fine and 4396 pointed. These are different group-action objects. Global value C3 still acts freely in the centre and yields three complex eigenspaces each of degree 65610 (this is a character match only).

## Monster/normalizer discriminator — stop the wrong branch

PR #1250's source-backed involution method for a selected Monster 3B centralizer restricts each phase-preserving involution trace to `{66,90,1458}`, as derived from Monster degree196883 character values at 2A/2B and compatible 6B/6D/6E classes. Both new one-line bypasses have phase involution values `162, 2916, 324`: **NONE** is in that necessary Monster list. This is a **negative same-character result**, not a proof that the finite D4/H4 construction fails. It also does not disprove the original E-isotypic Monster Heisenberg restriction without D4.

The separate PR #1250 signed-multiplicity candidate has `[65610,1458,18,1458,1458]` on the five D4 classes, which passes this *necessary* local trace screen; selected actual normalizer subgroup, complete 6.Suz source-family selection, 12+78 action/cocycle and exact character-to-Hom weld remain OPEN. The published Barraclough–Wilson section 5.1 permits arbitrary irreducible 6.Suz factors; the former faithful-78 preselection in an old helper was corrected in PR #1250. Prior Suzuki source receipt machinery and PR #1098 actual Hom compiler, **not** a new D4 geometry variant, are the highest return real Monster route.

## Pareto/max-cut (impact × evidential leverage / duplication cost)

| Rank | Candidate | Feasible source | What it actually pays | Stop / promotion criterion |
|---:|---|---|---|---|
| 1 | Execute source-selected 6.Suz 78-family full-character matcher in existing #1250 | Existing CTblLib/Barraclough–Wilson source pipeline | Actual selected multiplicity character, central-C2 family discriminator | Require original table receipt, quotient descent and uniqueness; no unexecuted-script success |
| 2 | Actual 3B D4 class/subgroup and Hom normalizer lift using existing #1098/#1250 | Actual source N(3B) action and 12+78 characters | Whether a selected 2A/4B D4 exists with same action | Required class-fusion/action evidence, not arithmetic fingerprints |
| 3 | Original JFine→character-T and modified-mirror Agda same-object proof | Existing #1148 irrep/gauge owners | Kernel form of new finite H4 bypass and no-go contrast | Agda exact-head accepted theorem, no axiomatic booleans |
| 4 | Source geometric 8→10→12 D4-stable H3×C3² and its typed H6 bridge | Existing #1148 prior formalisation | Preserve literal site D4 at price of extra group coordinates | Already finite-model checked; no further cardinality work |
| 5 | More OEIS, 42d, modular j, Ferrocell, brain or physical reinterpretations | Search co-ordinates only | Hypothesis generation | Defer until shared measured/original source object exists |

## Ibrahim/snowball frontier

Preserve all independent first roots instead of collapsing repeated online tables or same counts into extra confirmations. Follow the existing Ibrahim five-orbit N(3B) acquisition route ONLY where original action/type matches: its `(5,5,1,3,3)` acts on a **five-point quotient**, whereas here the changed object is an **8D F3 module**. Monster ATLAS class `42D` and OEIS lower-case `42d` remain different *until original class-label reconciliation* (earlier Ibrahim owner explicitly warns this). More OEIS tail overlaps cannot rescue the Monster involution trace failure.

For any future snowball claim, record original author/source date, exact mathematical object and group action, carrier/lift, coefficient field, primary class character evidence, independent derived calculation, and proof/runtime status. A named literature result is not kernel acceptance; a new model-coded intertwiner is not the published normalizer; a computed character is not an observed quantum/optical effect.

**Roadmap conclusion:** The apparent original H4 obstruction can indeed be bypassed **without increasing carrier cardinality**, by paying exactly one changed representation line. Both possible minimal rank-one variants have now been investigated. They fail the current Monster phase-involution acceptance test. The Pareto-optimal remaining Monster work is existing source-selected 6.Suz/Hom full action certification, not yet another same-size geometric model.


## 25 October: stronger multiplier-A2 bypass matching the necessary Monster C4 fingerprint

**Important dated supersession of earlier stopping rule:** The two *one-line B1/B2* refinements above are exact but Monster-incompatible. They do **not** exhaust all finite-action bypasses. A new, slightly larger **operator edit with zero additional trits** achieves a correct *necessary phase-preserving C4 fingerprint*. This does NOT contradict the one-line negative controls: we are now changing the E representation and the Heisenberg centre multiplier.

The original source-relative character is `2A1+B1+B2+2E`. Modify the centre orientation, one trivial line and one E doublet:

```
2A1 + B1 + B2 + 2E
        |
        |  one A1 -> A2  (mirror sign on one invariant line)
        |  one E  -> B1+B2  (quarter-turn on this pair Q -> -I2)
        v
A1 + A2 + 2B1 + 2B2 + E
```

In original source character coordinates `(tE,tC,bE,bC,XE,YE,XC,YC)`, change the *mirror* sign on tC (operator delta rank1) and the *quarter-turn* on the corner E pair to `-I2` (operator delta rank2). The new centre character is `χ=A2`: rotations preserve the central C3, reflections invert it and therefore **exchange ζ and ζ² sectors**. The new eight-dimensional symplectic form uses four hyperbolic pairs

```
(tE,tC), (bE,bC), (XC,YC), (XE,YE)
```

and obeys `RᵀΩR=Ω`, `MᵀΩM=-Ω`, with rankΩ=8. The **old** original site-D4 action is NOT preserved. The normalised Heisenberg centre `t=c+a·b` supports the exact GSp lift `(v,t)↦(gv,χ(g)t)`; translating back to the original existing H6 cocycle gives a quadratic central coboundary. Crucially, the chosen action has genuine D4 group laws, not merely matching dimensions.

The source-typed model is `DASHI/Biology/IITJFineD4OrientedC4HeisenbergSteelmanExact.agda` importing the pre-existing `IITJFineD4OrientationLineH4BypassExact.OrientedEight` and prior `Monster3BFiniteHeisenbergCentralExtensionExact`. The standard-library-only executable is `scripts/iit_jfine_d4_oriented_c4_monster_necessary_bridge.py` integrated with the IIT numeric verifier. An independent current-turn local Python implementation `/mnt/data/d4_monster_c4_orientation_lift.py` ran 354294 exact Heisenberg generator law checks and 59049 D4 presentation relation checks; all passed. **No Agda kernel/typecheck, exact committed GitHub script replay, or actual Monster subgroup operation is asserted.**

### Phase-preserving C4 character: strongest same-size candidate

The original pointed marker is allowed to move under site D4; its quarter and half turns each fix exactly TWO marker choices (centre and unmarked). Under the NEW quotient representation:

```
fixed shell dimension r   = 2  => χζ(r)  = 2·3² = 18
fixed shell dimension r²  = 6  => χζ(r²) = 2·3⁶ = 1458
identity                 = 10·3⁸       = 65610
```

Thus the selected `ζ` eigenspace restricted to the *phase-preserving rotations C4* has **necessary** class character `[65610,18,1458,18]`, identical to the C4 restriction of the candidate `[65610,1458,18,1458,1458]` in #1250 (D4 class order differs). Its complex C4 eigenspace multiplicities are

```
+1:16776,  -1:16758,  +i:16038,  -i:16038
```

All four are nonnegative integers, totaling 65610. An actual Monster selected-ζ representation could therefore be **compatible at this C4 character screen**, even though the previous one-line candidates are definitively excluded. The phase-inverting mirror has NO ordinary character on the individual ζ eigenspace: it maps ζ to ζ², so comparing its purported ζ trace against phase-preserving involution values `{66,90,1458}` would be a wrong-type calculation.

This is the **maximal honest promotion**: *the finite H4 source-carrier model shares a necessary C4 character with one source-compatible Monster phase pattern*. A corresponding subgroup in the **actual** N(3B), its class fusion, induced involution on ζ⊕ζ², the 6.Suz full multiplicity, and the Hom-cocycle/source action remain UNPROVED. No source-derived element word or full C4→D4 normalizer embedding has been supplied. Original Wilson/Barraclough character theory is NOT reauthored by this model.

### Revised Pareto and stop rules

1. **Actual 6.Suz full-character selected 78-family matcher** and quotient descent on #1250 remains the top payoff. Its output, faithful/nonfaithful C2 branch and 12+78 isotypic/Hom action have greater authority than any finite new D4 coordinate model.
2. **Actual phase-preserving C4 plus phase-inverting mirror in N(3B)** is now a focused actionable conditional target for the C4 steelman. Required source discriminator: element words/class fusion with `r²` in Monster 2A and `zr²` in 6D; (r) in 4B and (zr) in 12G as selected by #1250. Mirror must conjugate z to z⁻¹ and satisfy `mrm=r⁻¹` in the same selected normalizer. If this fails, the C4 steelman is excluded independently of its finite group laws.
3. **Agda actual Gauge→character T and explicit GSp/H4 finite laws**: source-written structural proof target. Do not claim CI/kernel success. Reuse existing finite-H6 and oriented-sector owners, not duplicate group axiom theory.
4. Ibrahim five-orbit and OEIS class42d echoes remain separate lower-leverage source acquisition. No group element/class data from a five-point quotient may be silently imported into eight-dimensional GSp modules.

**Updated inference boundary:** The initial rank-one B1/B2 models are negative Monster controls. The multiplier-A2 model is a **positive necessary C4 screen**. Neither is the actual Monster 3B representation, and no speculative physical, quantum, neural or phenomenal result is promoted.


## 25 October follow-on: Monster full D4 residual no-go and C3-signed character repair

**Cross-owner target:** [actual Monster-source PR #1250](https://github.com/chboishabba/dashi_agda/pull/1250), canonical [proof and original-source ledger](https://github.com/chboishabba/dashi_agda/blob/research/jfine-3b-character-steelman-20261024/Docs/support/reference/JFine3BOrientedFullD4ResidualMaxCut20261025.md). This cross-link supersedes any reading of the earlier C4 phase-character match as an actual 196830-dimensional *Monster-summand* statement.

**Exact full D4 negative discriminator for the unchanged product action.** If the modified A2-similitude eight-trit model, combined with a ten-marker representation, were embedded as a **D4-invariant 196830-dimensional summand** of the Monster 196883D module with 53D complement, and source r/r² classes 4B/2A, then a centre-inverting reflection with source Monster class 2A or 2B has bulk trace 81τ where τ is the 10D marker involution trace. Since τ is even and the true complement has dimension53, the only possible source involution is 2B with τ=4. The source full Monster character on these D4 classes is `[196883,4371,51,275,275]`; the entire unchanged source pointed permutation/regular H4 product has `[196830,4374,54,324,324]`. Their difference is **[53,-3,-3,-49,-49]**, with **A1 multiplicity -19**, so a genuine D4 complement is IMPOSSIBLE. This does not contradict the exact phase-preserving C4 restriction, but closes the proposed *whole* original product summand.

**Constructive positive CHARACTER bypass, different and weaker than H4:** On 10-marker × 3^8 centre-quotient, choose one existing D4-fixed orbit, nine reflection-axis-stabilized four-orbits, and nine diagonal-stabilized four-orbits. Introduce stabilizer **A2 sign characters**, extended evenly over the three centre trits. This is a genuine C3-compatible signed-monomial D4 representation on the same 196830 labels. Independent local Python confirms 73 quotient labels / 219 full fibre labels, **14016** group/cocycle/C3 tests, and reflection-character changes **-38,-38**. Its 53D hypothetical residual character becomes `[53,-3,-3,-11,-11] = 11A2+7B1+7B2+14E`, all nonnegative.

**NEW strongest obstruction:** This orbit-dependent sign representation is NOT an intertwiner for the original *regular left* H4 action. For any monomial D4 lift acting as `U_g δ_(j,x)=σ_g(j,x)δ_(gj,α_g x)`, the relation `U_g L_h=L_(α_g h) U_g` forces `σ_g(j,hx)=σ_g(j,x)`; because H4 acts transitively on each regular fibre, `σ_g` must be independent of x. Our repair has −1 versus +1 on two H4 points in the same marker fibre, providing an explicit negative witness. This **stops an untouched 10×Reg(H4)** direct-summand route even when the full D4 character is repaired and C3 centre transport works. The true Monster 729×90 Heisenberg/Hom route, with a **different** module structure, remains open.

**Pareto inversion:** highest-alpha next is the existing original-source `6.Suz` full selected 78-family/class quotient matcher and existing Ibrahim whole-character-isotypic/PR #1098 Hom consumers; **not** another pointed geometry/H4 extension of the same regular action. Existing original Serre, Barraclough–Wilson, ATLAS, Breuer/CTblLib, Ibrahim and prior code attributions must survive the snowball chain. The source scripts on PR #1250 are committed but not exact-head checkout executed; the independent local finite counterparts passed, while Agda and GAP receipts remain unobserved.


## 25 October latest PRs: explicit central-zeta H4 Fourier equivalence and GF729 source-word order

**Real new finite-module result — H4 only:** The prior Fourier/finite-Heisenberg donors (Serre/Terras, existing `Monster3BFiniteHeisenbergCentralExtensionExact` and #1098 six-pair Schrödinger) allow an actual *coordinate-level linear intertwiner*, rather than a dimensional or character-only claim. The current branch's `scripts/iit_jfine_h4_central_phase_fourier_intertwiner.py` implements:

```
  |x,eta> = sum_(b in F3^4) zeta^(eta.b) |a=x+eta,b>_zeta
  lambda(A,B,C)|x,eta> = zeta^(C+B.x)|x+A,eta>.
```

The inverse uses `1/81` times the opposite Fourier phase and exact orthogonality. The full source `10×Reg(H4)_ζ` has `10×81=810` copies of degree81 Schr4; the target `90×Res_H4 Schr6` has `90×9=810` copies. An explicit two-sided 810-slot indexing is provided. **Independent local Python:** 6,561 full 81-point Fourier Gram entries, 59,049 source/target generator equations, 810-slot bijection all PASS. These mathematical representations are concretely isomorphic **for the selected abstract H4 embedding**, without an actual selected-Monster E basis. **This does not pay the D4 or 6.Suz normalizer action, which has separate full-character -19/regular H4 obstructions.** Existing prior authors own the underlying Fourier and Heisenberg theorems.

**Source-level ATLAS correction from latest #1098:** The original vendored `2.Suz:2` 12D GF3 `g1` is order4 with square `−I` (source multiplier2), so **NOT** a literal D4 order2 mirror. The older field-source selected word `g2 g1 g2^-1 g1 g2^-1` has order6 and cube `−I` (its square has order3 Jordan partition `3²2²1²`), so **NOT** a literal D4 order4 rotation. These exact finite matrix statements were independently recomputed from original #1098 source bytes in the current turn. A distinct **ambient** D4 GSp12 exists from source-selected GF729 `gamma` by `R=diag(mul_(gamma^182),dual), M=diag(Frob^3,-dual)`, with group laws and inherited Heisenberg center coboundary; local 56,862 generator checks PASS. Its mirror is *not proven to belong to actual 2.Suz:2* and neither ATLAS source words nor ambient field matrices are yet actual Monster N(3B) element witnesses. Source [cross-owner ledger](https://github.com/chboishabba/dashi_agda/blob/agent/e6-f3-exterior-square-maxcut-20261006/Docs/support/reference/Monster3BField729D4SourceVsAmbientCut20261025.md).

**Maximum Pareto recut:** the abstract H4-module equivalence is now *constructively closed* (local finite tests, not Agda kernel); the old full D4/53 and signed-C3 H4-extension negative controls stand. **Do not reopen more model group laws.** Target actual source-selected full 6.Suz 78-family/MN3B quotient/Monster occurrence receipt on #1250 first, then actual E↔H6 source subgroup word and #1098/#1162 proof-relevant Hom/normalizer action. A source ATLAS word from 2.Suz:2 must be accompanied by actual group-operation, class-fusion and action evidence rather than similarities of field order or primitive phases.
