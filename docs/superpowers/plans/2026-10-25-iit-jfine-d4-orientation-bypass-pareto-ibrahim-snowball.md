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
