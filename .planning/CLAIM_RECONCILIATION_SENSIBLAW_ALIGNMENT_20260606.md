# Claim Reconciliation / SensibLaw Alignment

Date: 2026-06-06

This note records the alignment between the DASHI Agda claim-reconciliation
carrier and the SensibLaw Python operational implementation in the sibling
repo:

`../ITIR-suite/SensibLaw`

## Agda Carrier

The Agda-side claim-reconciliation slice is:

- `ClaimReconciliationObjectLattice.agda`
- `LargerObjectClassificationLattice.agda`
- `DialecticalJourneyLoom.agda`
- `LoomRelationAlgebra.agda`
- `ClassificationDiscoveryLattice.agda`
- `ITIRPNFAssessment.agda`

`ClaimReconciliationObjectLattice.agda` defines the bounded carrier layer for:

- `ClaimAtom`
- `ResponseUnit`
- `ClaimRoot`
- `ClaimRelationAssessment`
- `TypedObjectAssertion`
- `WikidataQualifier`
- `WikidataReference`
- `WikidataRevisionWindow`
- `WikidataStatementRow`

The canonical examples include:

- `X walked the dog` versus `X did not walk the dog`, classified as
  `explicitDispute`;
- `6 is a 1-morphism`, represented as a witness-pending, non-promoting
  typed-object assertion;
- Wikidata QID/PID/value/qualifier/reference/revision rows with
  `truthClaimed ≡ false` and `liveEditAuthority ≡ false`.

`DialecticalJourneyLoom.agda` wires the claim-reconciliation lattice into the
larger loom. `LargerObjectClassificationLattice.agda` classifies the related
claim, Wikidata, and morphism-typing object families.

## SensibLaw Runtime Surface

The matching SensibLaw Python implementation is:

- `src/fact_intake/typed_claim_reconciliation.py`
- `tests/test_typed_claim_reconciliation.py`
- `docs/planning/affidavit_wikidata_typed_reconciliation_contract_20260606.md`
- `docs/planning/typed_claim_reconciliation_handoff_20260606.md`

SensibLaw emits Python dictionaries rather than Agda records. Field spelling is
snake case on the Python side and camel case / constructors on the Agda side.

| Agda concept | SensibLaw runtime field |
| --- | --- |
| `ClaimAtom` | `kind = "proposition"` |
| `ResponseUnit` | `kind = "response_unit"` |
| `TypedObjectAssertion` | `kind = "object_type_claim"` |
| `WikidataStatementRow` | `kind = "wikidata_claim_row"` |
| `Relation.LoomRelationType` | `relation_type` |
| `Relation.promotionFalse` | `promotion_state.promoted = false` |
| `truthClaimed ≡ false` | `truth_claimed = false`, `truth_claimed_is_false = true` |
| `liveEditAuthority ≡ false` | `live_edit_authority = false`, `live_edit_authority_is_false = true` |
| `TypedObjectWitnessStatus` | `witness_status` |
| `ReviewStatus` | `review_status` |

The Python implementation also marks caller-supplied relation hints with:

`relation_derivation = "caller_hint"`

Derived comparisons use:

`relation_derivation = "derived"`

This keeps caller hints from masquerading as dimensional reconciliation.

## Non-Promotion Boundary

Both repos preserve the same boundary:

- relation/support/dispute classification is evidence metadata;
- Wikidata rows are source substrate, not truth or live edit authority;
- object-type assertions require explicit context and witnesses before stronger
  typing use;
- no SensibLaw runtime row or Agda carrier promotes a claim to proof by
  default.

Preferred/normal Wikidata rank is observed evidence metadata only. Deprecated
rank is review metadata only. Neither rank nor deprecation creates proof,
contradiction, truth, or authority.

## Verification

Agda verification passed from this repo:

```bash
agda ClaimReconciliationObjectLattice.agda
agda LargerObjectClassificationLattice.agda
agda DialecticalJourneyLoom.agda
agda ClassificationDiscoveryLattice.agda
agda ITIRPNFAssessment.agda
agda LoomRelationAlgebra.agda
```

SensibLaw verification passed from `../ITIR-suite/SensibLaw`:

```bash
../.venv/bin/python -m pytest tests/test_typed_claim_reconciliation.py -q
../.venv/bin/python -m pytest tests/test_affidavit_coverage_review.py tests/test_story_pnf_receipts.py -q
```

Observed results:

- `tests/test_typed_claim_reconciliation.py`: 11 passed
- `tests/test_affidavit_coverage_review.py tests/test_story_pnf_receipts.py`:
  49 passed

## Commit Boundaries

Keep this work separate from unrelated dirty YM/clay sprint files.

Likely claim-reconciliation files in this repo:

- `ClaimReconciliationObjectLattice.agda`
- `LargerObjectClassificationLattice.agda`
- `DialecticalJourneyLoom.agda`
- `README.md`
- `.planning/CLAIM_RECONCILIATION_SENSIBLAW_ALIGNMENT_20260606.md`

Likely SensibLaw files:

- `src/fact_intake/typed_claim_reconciliation.py`
- `src/fact_intake/__init__.py`
- `tests/test_typed_claim_reconciliation.py`
- `docs/planning/affidavit_wikidata_typed_reconciliation_contract_20260606.md`
- `docs/planning/typed_claim_reconciliation_handoff_20260606.md`

## Next Step

The next useful integration step is a read-only fixture bridge:

1. Export the SensibLaw dog-walk, object-type, and Wikidata examples as JSON.
2. Map each JSON fixture to the corresponding canonical Agda example by name.
3. Assert that all fixture rows remain non-promoting and non-authoritative.
4. Defer any database migration until a concrete persisted consumer requires
   these fields.
