# BH4 Phase-4 quantitative max-cut runbook

## Current state

The exact 16-protein panel currently resolves to:

- 24 protein-to-Rhea catalytic links;
- 12 finite internal reaction columns;
- 3 non-finite MTOR protein/R-group residual reactions;
- 29 finite species;
- a 56-coordinate quantitative problem: 15 core state coordinates + 12 reaction-flux intervals + 29 exchange intervals;
- first joint feasibility outcome: `underdetermined`.

The first bounded PDBe/SIFTS run is now formally promoted from its machine-generated schema-v2 receipt:

- 38 PDB structures examined;
- 526 exact `_pdbx_sifts_unp_segments` rows;
- 14 proteins with UniProt PDB links;
- 13 proteins with at least one matching segment;
- PCBD1 and AGMO have no panel PDB links;
- PCBD1, AGMO and PAH have no matching segment in the bounded first-three-PDB sample;
- zero HTTP/parse errors.

These are structural mapping facts, not catalytic-site/function claims.

## One-command run

```bash
python3 scripts/run_bh4_phase4_maxcut.py
```

Default input:

```text
artifacts/biology/uniprot-kitzerow-bh4-panel-certificate.json
```

The runner refreshes Rhea/ChEBI chemistry, rebuilds `S`, writes the 56-coordinate template, acquires SABIO-RK kinetic candidates and PDBe/SIFTS mappings, runs interval feasibility and the aggregate regressions, then writes:

```text
artifacts/biology/bh4-phase4-maxcut-summary.json
```

The current summary schema is `dashi.bh4-phase4-maxcut-run.v3`.

## SABIO-RK current API

The historical `/sabioRestWebServices/*` endpoints now rewrite to the browser SPA/404 shell. HTTP 200 HTML is therefore explicitly **not** a zero-entry receipt.

The current acquirer uses the kinetic-law export API:

```text
https://sabio.h-its.org/export-api/sabio/kinlaw-entry/json
```

with queries of the form:

```text
UniProtKB_AC:"P30793"
```

and validates the required JSON export envelope:

```json
{"meta": {...}, "data": [...]}
```

It paginates until `meta.total_count`/`meta.total_pages` is satisfied, hashes every raw page, and preserves the raw SABIO entries for later condition/assay adjudication.

Run it independently with:

```bash
python3 scripts/acquire_bh4_sabio_kinetics.py \
  --panel artifacts/biology/uniprot-kitzerow-bh4-panel-certificate.json \
  -o artifacts/biology/bh4-sabio-kinetics.json
```

SABIO records are **candidate kinetic evidence only**. Km, kcat, Vmax, rate-law entries or an export match do not automatically become in-vivo reaction-flux bounds. Same-object, compartment, time, condition and unit translation remain required.

## PDBe/SIFTS

```bash
python3 scripts/acquire_bh4_pdbe_sifts.py \
  --panel artifacts/biology/uniprot-kitzerow-bh4-panel-certificate.json \
  --max-pdb-per-protein 3 \
  -o artifacts/biology/bh4-pdbe-sifts.json
```

Use `--max-pdb-per-protein -1` for exhaustive panel-linked PDB coverage. The current first-three-PDB receipt is owned formally by `DASHI.Biology.BH4ExecutedSIFTSReceiptExact`.

A SIFTS mapping pays sequence/residue identity between UniProt and a PDB model. It does not itself prove catalytic function, regulation, perturbational causality or same-cell biochemical state.

## Parameter manifest

```bash
python3 scripts/acquire_bh4_parameter_evidence.py \
  --template \
  --matrix artifacts/biology/bh4-stoichiometric-matrix.json \
  -o artifacts/biology/bh4-parameter-template-v2.json
```

A solver-usable row requires lower/upper bounds, one normalized flux unit, source, same-object, compartment and measurement-time coordinates, plus `usable_for_joint_flux_witness = true`. `unresolved` never means measured zero.

## Interval feasibility

```bash
python3 scripts/solve_bh4_flux_intervals.py \
  --matrix artifacts/biology/bh4-stoichiometric-matrix.json \
  --parameters artifacts/biology/bh4-parameter-normalized.json \
  -o artifacts/biology/bh4-interval-flux-feasibility.json
```

The bounded steady-state problem is:

```text
S*v + e = 0
```

using `scipy.optimize.linprog(method="highs")`.

Outcomes:

- `feasible`: one state exists inside the supplied intervals;
- `infeasible`: no state exists inside those supplied steady-state intervals;
- `underdetermined`: required intervals or normalized units are missing;
- `solver-unavailable`: SciPy is unavailable.

None of these automatically establishes or refutes the broader Kitzerow disease mechanism outside the modeled state/problem.

## Regressions

```bash
python3 scripts/check_kitzerow_bh4_priority_all.py
```

The aggregate checker covers the legacy evidence/identity lane, executed Phase-4 system-state lane, SABIO export-envelope contract, canonical SIFTS receipt, 56-coordinate manifest and interval-solver firewalls.

CI is not the completion gate for this tranche.
