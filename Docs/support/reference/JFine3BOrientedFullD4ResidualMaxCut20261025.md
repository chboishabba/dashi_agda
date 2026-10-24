# JFine / Monster 3B — complete D4-character max-cut and central-phase monomial repair

**Date:** 25 October 2026. **Actual Monster/source owner:** [PR #1250](https://github.com/chboishabba/dashi_agda/pull/1250). **Finite source eight-trit model owner:** [PR #1148](https://github.com/chboishabba/dashi_agda/pull/1148). **Earlier actual Hom/cocycle interface owner:** [PR #1098](https://github.com/chboishabba/dashi_agda/pull/1098).

## Attribution and proof statuses

- R. W. Barraclough & R. A. Wilson, *The Character Table of a Maximal Subgroup of the Monster* (2007), DOI 10.1112/S1461157000001352, [original PDF](https://webspace.maths.qmul.ac.uk/r.a.wilson/pubs_files/CharmaxM.pdf), owns the original N(3B) character table, inertia-group extension, quotient, and class-fusion calculations, not our later geometric ansatz.
- ATLAS Monster power/class data, https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M/, and Thomas Breuer/CTblLib's independently reproducible Monster table documentation, https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/htm/ctblm.htm, provide the original 2A/2B/4B character values used by the existing PR #1250 class filters. The occurrence of values in both archives and OEIS copies does not create independent original proofs.
- Original Serre finite-group character theory, and original repo D4 irreps `D4SO3NineIrrepRestrictionExact.agda` and `TernaryMonsterSymmetryCandidateExact.agda`, are reused, not reauthored.
- Earlier repository `Monster3BPhaseTransportExact.agda` and `Monster3BCentralCharacterInertiaExact.agda` already distinguish the full central-generator normalizer from its ζ-preserving inertia subgroup; reflections that invert z exchange ζ and ζ².
- PR #1148's modified **non-geometric** `V8=A1+A2+2B1+2B2+E` action has D4 quarter-turn r preserving centre and reflection m inverting centre, full rank8 GSp pairing and original 19683 underlying group-state labels. This action is not the original literal 3×3 site permutation and is not an actual Monster action.
- NEW repository computations: `scripts/jfine_3b_oriented_h4_d4_residual_nogo.py`, `scripts/jfine_3b_signed_c3_orbit_repair.py`; `tests/test_jfine_3b_oriented_h4_d4_residual_nogo.py` and `tests/test_jfine_3b_signed_c3_orbit_repair.py`; a source-written Agda character file `DASHI/Moonshine/Monster3BJFineD4OrientedResidualCutExact.agda`. Independent **local** Python scripts have executed the arithmetic and signed central-phase calculations; the exact GitHub checkout scripts, GAP/CTblLib, and Agda typechecking have NOT been executed. Do not promote receipt booleans to proof terms or actual source-table run.

## Stage I: full D4-character obstruction to an unchanged 10×H4 regular/marker product

The prior C4 phase match [65610,18,1458,18] (1,r,r²,r³) is mathematically real but is **insufficient** to embed the full `10 × 3^9 = 196830` pointed source representation into the Monster degree196883 module with an invariant 53-dimensional residual.

Hypotheses to test, **NOT** conclusions:
1. a genuine selected D4 subgroup in actual N(3B) with r of Monster class 4B, r² of class 2A, and two reflection classes each order two;
2. the PR #1148 modified quotient action fixed dimensions `dim V8^(r)=2`, `dim V8^(r²)=6`, `dim V8^(m)=4`, and centre multiplier χ(r)=+1, χ(m)=-1;
3. the pointed 10-marker factor has rotation traces 2,2, and is a genuine ten-dimensional involution representation under either mirror;
4. the whole product action is a D4-stable summand of the actual Monster degree196883 representation with **53D genuine** complement, rather than an equality of dimensions/phase characters.

An inverting mirror has exactly one fixed centre trit over each fixed quotient point. Thus its bulk trace is **81 τ**, where τ is the ten-marker involution trace; τ must be even with |τ|≤10. The complementary genuine 53D representation would have mirror trace `χ_M(m)-81τ`, absolute value ≤53. With actual 2A trace 4371 no τ works; with actual 2B trace 275 the UNIQUE even τ is **4**, yielding residual mirror trace **−49**. This applies to *both* D4 reflection classes, even if the marker representation were signed linear instead of a literal permutation.

For the quarter-turn, class 4B gives Monster trace **51**, while the original whole pointed source has trace 2×3×3²=**54**, so residual r trace **−3**. For the half-turn, class 2A gives Monster trace **4371**, source bulk trace 2×3×3⁶=**4374**, so residual r² trace **−3**. Identity gives residual 196883−196830=**53**.

The forced *virtual* complement character is

```
                1      r²      r±       axis-m      diagonal-m
Monster         196883 4371    51       275         275
pointed bulk    196830 4374    54       324         324
difference      53     -3      -3       -49         -49
```

For the standard five ordinary D4 irreducibles (A1,A2,B1,B2,E), exact character inner products yield

```
    residual = -19 A1 + 30 A2 + 7 B1 + 7 B2 + 14 E.
```

A1 multiplicity **−19** is impossible for a genuine complex representation. Equivalently, the unmodified full pointed source has 25,326 D4 invariant vectors, whereas the sourced full Monster restriction in the asserted fusion has only 25,307. No equivariant injection can increase invariant dimension. **This rules out the specified untouched 10-marker×regular-H4 bulk splitting, NOT arbitrary phase-compatible extensions, actual Heisenberg isotypy or selected 6.Suz action.**

## Stage II: constructively repair the FULL D4 character without adding states

The source class difference shows a precise possible *character* repair: change both bulk mirror traces from 324 to **286** (−38 each), keeping identity/r/r² unchanged. This leaves

```
 residual = [53,-3,-3,-11,-11] = 11 A2 + 7 B1 + 7 B2 + 14 E
```

with **all** multiplicities nonnegative. Construct, rather than invent, a signed monomial D4 action on the *same original finite pointed basis*:

1. Pass to the 10-marker × F3^8 **centre quotient** of the previously constructed modified D4 action.
2. Select one existing singleton D4 orbit, nine distinct size-four orbits whose stabilizer is an axis reflection, and nine size-four orbits whose stabilizer is a diagonal reflection.
3. On each selected orbit, induce the sign character A2 of the stabilizer via an explicit coset-transversal cocycle. This makes exactly one fixed reflection basis element flip sign on the singleton (−2 trace in each reflection class), and two fixed elements flip sign on each respective reflection-stabilized size-four orbit (−4×9), totaling **−38** for each class.
4. Leave all other quotient orbits unchanged. Lift the sign weight **constant over all three centre translations** so the D4 semidirect action on the central C3 is preserved; source r commutes with z, source m conjugates z to z⁻¹.

The new producer exhaustively validates group multiplication and cocycle identity on all 73 selected quotient labels and all 8×8 D4 group-element pairs; it checks all three centre translations: **73×3×8×8 = 14,016** identities. Only 73 quotient labels (219 full labels) need changed signed action. The chosen 19 orbit local systems really exist in the earlier finite D4 carrier, not merely in an abstract character ring. The resulting full D4 *character* passes the necessary Monster classwise screen and has a mathematically valid 53D residual representation.

## Stage III: exact H4 compatibility gate—still FAILS for the signed repair

The signed orbit repair **does not** preserve the original source left-regular H4 action. This is not just a missing runtime check; there is a simple structural reason.

Let L_h be left translation on the same H4 basis labels, and suppose a monomial D4 symmetry acts as

```
 U_g δ_(j,x) = σ_g(j,x) δ_(g·j, α_g(x)).
```

For a genuine semidirect H4 ⋊ D4 action, require `U_g L_h = L_(α_g(h)) U_g`. On the basis vector (j,x), the two coefficients are respectively `σ_g(j,hx)` and `σ_g(j,x)`. Since H4 is transitive on its own regular orbit, **σ_g(j,x) must be independent of x** for each j. The signed repair instead has weight −1 for the chosen D4-fixed identity orbit and +1 for an unselected H4 group element at the same marker. The explicit witness is checked in the new Python producer.

Thus a mere orbit-dependent sign lift cannot both (a) repair the D4-Monster whole-character comparison and (b) preserve the **unchanged** left-regular H4 action on the source state factor. An honest bypass must change the actual Heisenberg action and/or the multiplicity fibre/evaluation map, or abandon the proposed direct 196830D invariant pointed-source summand. This does NOT obstruct the genuine prior Monster 729-dimensional Schrödinger constituent and its 90-dimensional multiplicity Hom space.

## Revised Pareto / Ibrahim / snowball max-cut

| Rank | Existing donor or candidate | What it can actually pay | Acceptance rule |
|---|---|---|---|
| **1** | PR #1250 source-driven full **6.Suz degree78 family** matcher, original Barraclough–Wilson/CTblLib tables | Actual selected degree90 multiplicity CHARACTER and central C2 faithfulness branch | Original executable class receipt; complete 6.Suz character; unique main→MN3B descent and positive Monster restriction. An unexecuted GAP script cannot pay this. |
| **2** | Existing `IbrahimMonster3BRecognitionRouteParetoExact`, `IbrahimMonster3BWholeCharacterConsumerSufficiencyExact` | **Whole-character-first** isotypic theorem, avoiding premature literal constituent enumeration | Source-consistent full class function + actual-kernel receipt + FDRep↔group-algebra seam theorem; fallback to constituent route if proof fails. |
| **3** | PR #1098 actual `Hom_E(H_ζ,W_ζ)`, inverse cocycle / 6.Suz normalizer action | Same-object full phase representation, not model-basis coincidence | Literal action or sufficient class/cocycle proof, actual selected 78 match. |
| **4** | This PR D4 monomial C3 repair | Explicit **positive full D4 character** control and **negative H4 regular** control | Use it for discriminating candidates. Do not promote to Monster action or H4 intertwiner. |
| **5** | PR #1148 geometric D4 no-go and modified GSp H4 | Exact independent finite geometry | Kernel weld from original cell coordinates remains optional; cannot override actual Monster source character. |
| Defer | OEIS 42d, pointed 10 coincidences, Ferrocell, neural/quantum claims | Navigational correlations only | Unique original matched source object/operational physical discriminator required. |

**Ibrahim/source-provenance rules:** retain the *original* separate ATLAS/BW/CTblLib source roots, and the original code authored on PR #1148 / #1098 / #1250. The five-orbit Ibrahim D4 permutation `(5,5,1,3,3)` acts on a DIFFERENT quotient from the eight-relative-trit module and cannot be substituted. Distinguish user-authored modelling from original mathematicians and independent verified source data; preserve publication date and exact coefficient-table/class label. A class trace is neither a group element nor a physical experiment.

**Actual remaining highest-value frontier:** source-selected 6.Suz family execution and whole-character consumer sufficiency using existing actual Hom tools. A new signed-pointed model that only matches 196883/196830/53 and the C4 trace must not consume further work unless it supplies an H4-compatible fibre, genuine full normalizer action, or actual Monster source element/class certificate.

## Local verification and reproducibility

Backend-free commands, when run in a checkout of the updated PR:

```sh
bash scripts/check_jfine_3b_d4_c3_character_maxcut.sh
```

The session independently executed finite Python arithmetic yielding **−19** and constructive quotient-local-system **14,016** checks, including the central conjugacy test. The exact committed scripts on GitHub were read back by GitHub integration but were **not executed from that checkout**; no Agda/GAP/AtlasRep/Monster computation has been claimed. The checked-in Agda source is imported by `Monster3BActualKernelCharacterRound4Validation.agda` but **not kernel typechecked**.
