# WrongType relational depth: grid → hypervoxel → query-specific k

**Status:** Implemented as source-written Agda/Lean modules and a finite executable search.
Do **not** report kernel verification until exact-head checks exist.

## Origins and authority

- Rob McNamara, *A System of Wrong*, Episode 4, *The Grid*: the
  user-supplied 2026-09-30 transcript describes an ordered 3×3 of
  **frame violated** × **logic imposed**. The narrator attributes the
  broader framework to Forrest Landry, but this attribution is not an
  independent verification of authorship of the nine-cell taxonomy.
  Its alleged coverage of all serious legal wrongs remains unproved.
- Kimberlé Crenshaw, *Mapping the Margins* (1991),
  DOI **10.2307/1229039**: motivation to preserve intersectional
  positioning, not author of the factorisation mathematics.
- Robin Wall Kimmerer, *Braiding Sweetgrass* (2013): reciprocal relational
  knowledge/obligations; not a mathematical braid-group attribution.
- Two-Eyed Seeing (Etuaptmumk), associated with Mi'kmaw Elders Albert
  and Murdena Marshall and Cheryl Bartlett: coordinated distinct
  epistemic perspectives, not collapsed custodial authority.
- Luce Irigaray, *This Sex Which Is Not One*, particularly *Women on
  the Market* (English translation 1985): feminist critique of exchange
  and commodification; not identical to a nine-cell theorem.
- Lacan; Marxist/dialectical-materialist analysis: separate interpretive
  lenses, not proof of legal elements, offender intent or a universal
  stage sequence.
- DASHI authors the proposed hypervoxel carriers, exact finite
  factorisation witnesses, k-search algorithm, and typed evidence/gluing
  demands. Source identity is neither semantic equivalence nor authority.

## Typed model

Let `M = {Care, Transaction, Power}`. The original `XY = M^2`
preserves McNamara's roles (violated, imposed). Further ordered ternary
axes `XYZAB… = M^n` represent additional **explicitly declared**
relational roles or stages: their semantics are not assumed.

* `n=2`: 9 points.
* `n=3`: 27 points.
* `n=4`: 81 points.
* Three independently chosen 27-state blocks: `27^3=19683`
  distinct combinations, equivalent in count to nine ternary axes.
* A ternary-valued function on each 27-state input:
  `3^27=7625597484987` possible output tables. This is the next
  *function-space* tower level, **not** an XYZA hypervoxel.
* For `M^n`, the product growth law is `3^n`. Self-indexing
  `T_(h+1) = T_h -> M` is tetration: keep the two recurrences separate.

Each address may carry a legal/custodial/evidential fibre. Permitted
gluing of two fibres requires independently supplied identity/time,
authority-comparison and interface evidence. Combinatorial pants
gluing alone cannot establish any of these sources or legal outcomes.

## Minimal sufficient coordinate width

Given an actual finite situated domain `S ⊆ M^n`, consumer query
`Q: S -> O`, and a subset of axes `I`, let `pi_I` retain the
selected coordinates. Define:

`Adequate(I,Q) := exists f, Q = f ∘ pi_I`.

`k_min(S,Q) := min {|I| : Adequate(I,Q)}`.

**Finite decision rule:** `I` is sufficient precisely when no
`s,t ∈ S` have the same selected coordinates but different answers.
The exhaustive algorithm returns minimal sufficient subsets and an
actual counterexample collision for each rejected subset. This is
a query-specific result, *not* a universal dimension of a wrong.

Examples over the **full ternary four-axis carrier**:

| Query | `k_min` | Minimal axes |
| --- | ---: | --- |
| Original McNamara grid `(X,Y)` | 2 | `{X,Y}` |
| Last coordinate `A` | 1 | `{A}` |
| Whole situated XYZA tuple | 4 | `{X,Y,Z,A}` |
| Constant query | 0 | empty subset |

The same situation may have radically different query-specific widths.
`k_min` is a minimum sufficient *coordinate set*, not automatically
the algebraic interaction degree. Detecting irreducible k-way synergy
requires a separate interaction decomposition.

The Agda and Lean owners prove by explicit collisions that every
single-coordinate deletion from a four-axis situation fails to
reconstruct the *entire* four-axis state. They also reuse
`DASHI.Core.IntersectionalNonFactorability` in Agda to show any
postcomposition of a losing observer remains insufficient.
These results are conditional on their specified query and carrier,
not claims of sufficiency for real-world wrongdoing.

## Reuse and files

- `DASHI/Law/SensibLawWrongTypeCareTransactionPowerGridExact.agda`
- `DASHI/Law/SensibLawWrongTypePluralAdmissibilityGridExact.agda`
- `DASHI/Law/SensibLawWrongTypeRelationalDepthHyperfabricExact.agda`
- `DASHI/Core/IntersectionalNonFactorability.agda`
- `DASHI/Core/QueryIndexedProjectionAdequacyExact.agda`
- `DASHI/Cognition/RecursiveFibreTower.agda`
- `DASHI/Biology/SelfIndexingHyperfabricTetrationExact.agda`
- `DASHI/Topology/TernaryCylinderPantsGeometryExact.agda`
- `DASHI/Wikimedia/Ibrahim36927PantsColourTextileSweetgrassSnowballExact.agda`
- Lean mirror: `AgdaMirror/Law/WrongTypeRelationalDepth.lean`
- Executable finite search: `scripts/wrongtype_relational_depth.py`
- Regression suite: `scripts/test_wrongtype_relational_depth.py`

Run a focused empirical smoke check from repository root:
```bash
python -m unittest scripts.test_wrongtype_relational_depth -v
python -m scripts.wrongtype_relational_depth --axes 4 --query grid
python -m scripts.wrongtype_relational_depth --axes 4 --query identity
```

A proper source-level Agda/Lean type check and the original
`WrongType`/SensibLaw legal-rule consumer weld remain separate gates.
