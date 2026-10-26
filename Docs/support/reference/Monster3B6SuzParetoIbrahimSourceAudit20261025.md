> **25 OCT 2026 — LATEST BACKEND-FREE CUT:** Beyond the earlier C2/C3/parity screens, PR #1250 now contains a pure-Python **FULL-CLASS 6.Suz Sym²12/dual character verifier** with independent source class-size and group-order weighted irreducible orthogonality checks, exact `Q(zeta3)` coordinates, complete second-power map, and explicit first-class mismatch witness. An optional source GAP exporter uses the documented `CoeffsCyc(x,3)` extraction without approximation. Local finite-group C2×C3 positive/negative tests **passed**, including eight malformed-source controls. **An actual 6.Suz table export, selected Monster 78 matching receipt and Agda kernel check have NOT been observed.** This does not supersede the original main/MN3B/Monster source-selected quotient matcher; it independently audits its character-level `Sym²` claim. See [portable character audit / proof ledger](./Monster3B6SuzPortableCharacterAudit20261025.md), and keep `IbrahimMonster3B*` source/quotient ownership, Barraclough–Wilson (2007) and Nebe (2025) original attribution intact.

# 25 October 2026: Source-first Monster 3B / 6.Suz max-cut — Pareto, snowball, Ibrahim

## Exact task and provenance

User objective: advance the existing Monster (3B) source-selected (12\oplus78) multiplicity/Hom representation and quotient descent, maximize reuse of existing Agda/GAP/Lean owners, and do all sound work possible **without an observed local GAP/CTblLib receipt**. The "Ibrahim" work here refers to DASHI's pre-existing `IbrahimMonster3B*` source, phase, regular-spectrum and quotient correction modules; it is not new authorship or a new named mathematical theorem.

**Primary roots (distinct from transcriptions):**
- R. W. Barraclough and R. A. Wilson, *The Character Table of a Maximal Subgroup of the Monster*, LMS J. Comput. Math. 10 (2007) 161–175, DOI 10.1112/S1461157000001352. In §5.1 the source construction explicitly permits any `eta-hat in Irr(6.Suz)`. It distinguishes **splitting** from **outer fused-pair** cases. Our `113724=2×729×78` target belongs to the fused-pair case, so candidates must restrict from an irreducible degree156 character of `6.Suz.2` as `78_a+78_b`; there is NO justified prefilter by 78 faithfulness.
- Barraclough's own [archived GAP tables and fusion data](https://www.rwb.me.uk/table/index.html): names `3^1+12:6.Suz.2`, `3^1+12.2.Suz.2`, `3^12.6.Suz.2`; archive `N3BetcTables.tar.gz`, with `NotifyCharacterTable` instructions. This archive is not an independently observed runtime computation and need not be vendored.
- S. P. Norton and R. A. Wilson, *Anatomy of the Monster: II*, Proc. London Math. Soc. 84 (2002), 581–598: in the **3B centralizer**, the central involution `-1A` of `2.Suz` fuses to Monster **2B**, separately from class `+2A`, which also fuses to 2B. This is historical published group fusion, not a matrix realization of our chosen lift.
- Gabriele Nebe, *Symmetrizations of quadratic and Hermitian forms*, J. Algebraic Combin. 61 (2025), article 29, DOI 10.1007/s10801-025-01399-2 §6: a faithful 12 of `6.Suz` has irreducible symmetric square degree78 descending to `3.Suz`. This **does not prove** it is the 78 actually occurring in the Monster.
- Original Monster/ATLAS character values and power maps: commuting selected 3B centre `z`, Monster 2B involution `g` and order-six `zg`. Ordinary degree196883 character values 2B=275, 6B=77, 6E=5. Their derived `W_zeta` traces are 66 (6B) or 90 (6E) respectively, **conditional** on the exact 3B product-class fusion. McKay–Thompson OEIS are transcriptions, not original roots.
- Original group character/Fourier identities: Serre; Terras. The local Python results are only finite computations/consumers, not novel primary mathematical source material.

## Already owned; avoid duplication

- `scripts/monster_3b_suzuki_multiplicity_characters.g`: now **all** `Irr(6.Suz)` degree78 inventory, disjoint faithful/nonfaithful subsets and exact central C3 phases, including trivial phases. Its renderer and checker no longer assume two total degree78 characters.
- `scripts/monster_3b_suzuki_main_quotient_match.g`: original same-object route from `6.Suz` through `6.Suz.2`, main `3^1+12:6.Suz.2`, quotient `MN3B` and restricted Monster degree196883. Its **updated** code enumerates all eligible **outer degree156 fused** 78+78 pairs and requires correct degree113724 main decomposition, exactly-one quotient descent and positive restricted-Monster multiplicity. It fails closed when no unique pair survives.
- The same **source-selected** matcher now checks actual full class-function equality against `Sym²(12)` **and its contragredient**, using the exact second power map, and separately records central C2 and equal-C3-phase necessary constraints. Current runtime result is NOT observed.
- `DASHI/Wikimedia/IbrahimMonster3B*` (diagonal kernel, zeta phase gauge, full 12/78 character weld) and `DASHI/Moonshine/Monster3B*` (finite Heisenberg, Stone–von Neumann, character projector) already own abstract mathematics and source status.
- [Agda PR #1098](https://github.com/chboishabba/dashi_agda/pull/1098) already owns formal Schur/isotypic/Hom and normalizer-action machinery. [PR #1148](https://github.com/chboishabba/dashi_agda/pull/1148) owns original independent JFine nine-site/D4 model; its earlier *geometric* Monster-D4 identity is ruled out by the Monster involution character no-go. Neither should be duplicated in #1250.

## Source-based two-branch 729 parity and Monster-six-class cut

A concrete cheap group action model: on the 729-dimensional Schrödinger fibre with basis indexed by `u in F3^6`, the inversion operator `P(u)=|-u>` has trace **1** because its only fixed vector label is `u=0`. Both honest involutory lifts `P` and `-P` have traces +1 and -1. For **an actual** 6.Suz centre-C2 lift whose action on E is this symplectic `-I`, the fibre trace is **necessarily ±1**. This is a conditional geometric/Weil trace fact, not a certificate of which lift the original source chooses.

On the actual selected 3B `W_zeta`, for commuting Monster-2B involution `g`,
```
 tr(g|W_zeta) = [chi_196883(g)-chi_196883(zg)]/3.
```
Under the historically allowed `zg` classes 6B and 6E, the right-hand side is **66 and 90**. For the two currently considered Suzuki degree90 C2 signatures:
```
 Family faithful 12 + faithful 78:      eta_S(c2)=-90
 Family faithful 12 + C2-plus 78:       eta_S(c2)=+66
```
the exact product condition `tr(psi(c2))*eta_S(c2)=tr(g|W_zeta)` leaves only:

| Source η90 family | ψ729 inversion lift trace | Required Monster (g,zg) class | Selected phase trace |
|---|---:|---|---:|
| faithful78, C2=-90 | -1 | (2B,6E) | 90 |
| C2-plus78, C2=+66 | +1 | (2B,6B) | 66 |

The other two sign/family combinations predict negative selected-phase traces -90 or -66 and cannot match these inputs. **Both surviving cases remain CONDITIONAL**: an actual source word/class coordinate for g, its `zg` fusion, the chosen 729 extension parity sign and the correct selected multiplicity module must be obtained before selecting either. Neither c2=+66 nor norm8100 is sufficient to establish full `Sym²` character equality.

`scripts/monster_3b_suzuki_c2_parity_6class_conditional_gate.py` checks all four exact cases with standard-library Python. No GAP or dense Monster matrices required. Independent finite group 18-element adversarial control `scripts/monster_3b_full_character_centre_collision_counterexample.py` constructs two genuine representations of `C2×C3×C3` having the **same identity, C2 and designated C3** character values but different values on another C3 class. This strictly proves that a central fingerprint is a necessary screen, never full class-function equality. These local computations have no claim of an actual Monster representation being constructed.

## Revised Pareto priorities and acceptance criteria

| Cut | Outcome available WITHOUT GAP | Additional evidence needed | Why highest value |
|---|---|---|---|
| A. Source semantics | §5.1 splitting/fusion distinction, genuine original download, remove faithful78 preselection | None; audit done | Prevents wrong source claims |
| B. Full selected 78 selection | Deterministic finite candidate procedure, unique-survivor error and schema guards | An authentic CTblLib/source character execution receipt | Settles which representation Monster actually selects |
| C. Cheap centre and parity filters | C2 trace -90 vs +66, C3 equal-phase, 2B/6B/6E conditional gate, exact local tests | Source word fixing `zg` class and Weil lift sign | Narrows actual tests to two branches |
| D. Full Sym² / dual identification | Exact `(chi(g)^2+chi(g²))/2` **all-class** comparator implemented | Character-table outcome from B | Avoids false identification by degree/central signs |
| E. Same-object inertia / Hom / cocycle | Generic prior-art in PR #1098, existing kernel and centre source certificates | Selected actual outer/inertia lifts and classwise Hom action | Last true abstract normalizer weld |
| F. Concrete Monster basis `T` | Matrix-free sparse intertwiner prototype, finite Heisenberg codec | Actual generator matrices or equivalent selected source-coordinate action | Separate, more expensive optional deliverable |

### Explicit stop rules

A passing central-`C2` or cyclotomic-`C3` condition must **NOT** be promoted into a full character equality. A character equality must **NOT** be promoted to a concrete matrix intertwiner without supplying the group and same source-selected action. A sourced article/table must **NOT** be promoted to an observed successful GAP execution. Source-written Agda code is **NOT** an Agda-kernel proof without typechecking.

No `mmgroup` or GAP binary is needed for any local finite test above. **No actual local GAP/CTblLib runtime receipt exists in this turn**. No physical mechanism, quantum intervention, analytic zeta zero or experiment is inferred by these purely finite representation calculations.
