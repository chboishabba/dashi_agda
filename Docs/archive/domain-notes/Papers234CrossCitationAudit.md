# Papers 2-4 Paper 8 Tower Cross-Citation Audit

Date: 2026-05-29

Scope: Worker A5 audit plus Manager A integration. This file records whether
Papers 2-4 cite the required Paper 8 tower-instance modules.

## Required Cross-Citations

| Paper | Required module | Current state | Evidence |
|---|---|---|---|
| Paper 2: `Docs/Paper2GRGeometryDraft.md` | `DASHI.Physics.Closure.MillenniumTowerGRInstanceReceipt` | Present after Manager A integration | Added to the positive claim receipt anchors and the consolidated claim ledger. |
| Paper 3: `Docs/Paper3YangMillsGeometryDraft.md` | `DASHI.Physics.Closure.MillenniumTowerYangMillsInstanceReceipt` | Present | Present in the opening receipt list, Section 6, and receipt index. |
| Paper 4: `Docs/Paper4PhysicalHilbertSkeleton.md` | `DASHI.Physics.Closure.ColimitGapLiftOnHamiltonian` | Present after Worker A3 integration | Present in Section 9 as the Paper 8 bridge from finite Hamiltonian data to the tower schema. |

## Recommended Insertions

### Paper 2

Recommended insertion point: in `Docs/Paper2GRGeometryDraft.md`, Section
`0. Positive claim receipt anchors`, add this row after the Friedmann
instability/Temple authority boundary row:

```markdown
| Paper 8 GR tower instance | `DASHI.Physics.Closure.MillenniumTowerGRInstanceReceipt.canonicalMillenniumTowerGRInstanceReceipt`; `DASHI.Physics.Closure.MillenniumTowerGRInstanceReceipt.continuumGRAuthorityConstructedHereIsFalse`; `DASHI.Physics.Closure.MillenniumTowerGRInstanceReceipt.cosmologyPromotedIsFalse`; `DASHI.Physics.Closure.MillenniumTowerGRInstanceReceipt.millenniumTowerGRNoPromotion` | Paper 2 supplies the Gate 4 GR lane input to the Paper 8 tower schema; continuum GR authority, cosmology promotion, and GR promotion remain fail-closed. |
```

Recommended prose insertion point: after item 4 in Section
`0.1 Consolidated Paper 2 claim ledger`, add:

```markdown
Paper 2 is the GR lane instance cited by the Paper 8 tower schema. The
cross-paper tower witness is
`canonicalMillenniumTowerGRInstanceReceipt` in
`DASHI.Physics.Closure.MillenniumTowerGRInstanceReceipt`; it records the
current finite and authority-bound Gate 4 surfaces while keeping continuum GR
and cosmology promotion flags false.
```

### Paper 3

No insertion required. The required module path
`DASHI.Physics.Closure.MillenniumTowerYangMillsInstanceReceipt` is already
present, including in Section `6. Relation to the Yang-Mills Mass-Gap Tower`.

### Paper 4

Recommended insertion point: in `Docs/Paper4PhysicalHilbertSkeleton.md`, at
the end of Section `1. Scope And Claim`, add:

```markdown
This paper is also the Hilbert-completion lane referenced by the Paper 8 tower
schema. The relevant cross-paper boundary is
`DASHI.Physics.Closure.ColimitGapLiftOnHamiltonian`: the finite and
depth-indexed Hamiltonian staging can be related to the tower route, but the
physical Hilbert completion needed for the Yang-Mills Hamiltonian remains
fail-closed through `physicalStoneCarrierPromotedIsFalse`.
```

## Audit Result

Paper 2, Paper 3, and Paper 4 now satisfy the required Paper 8
cross-citation pass. The Paper 2 insertion uses the exact exported
`MillenniumTowerGRInstanceReceipt` identifiers:
`canonicalMillenniumTowerGRInstanceReceipt`,
`continuumGRAuthorityConstructedHereIsFalse`, `cosmologyPromotedIsFalse`, and
`millenniumTowerGRNoPromotion`.
