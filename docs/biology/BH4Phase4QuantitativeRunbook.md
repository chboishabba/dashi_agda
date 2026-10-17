# BH4 Phase-4 quantitative max-cut runbook

## Purpose

This runbook starts from the exact 16-protein UniProt certificate and executes
the strongest current bounded pipeline without promoting database identity,
kinetic constants, structure mappings, or steady-state feasibility into disease
mechanism claims.

Current executed chemistry baseline (2026-10-17):

- 16 proteins;
- 24 protein-to-Rhea catalytic links;
- 12 finite reaction columns;
- 3 non-finite MTOR protein/R-group residual reactions;
- 29 finite species;
- first joint feasibility result: `underdetermined`.

The next-run quantitative problem has 56 coordinates:

- 15 core BH4/context coordinates;
- 12 `REACTION_FLUX:<RHEA-ID>` intervals;
- 29 `EXCHANGE:<species-id>` intervals.

## One-command run

```bash
python3 scripts/run_bh4_phase4_maxcut.py
```

Default input:

```text
artifacts/biology/uniprot-kitzerow-bh4-panel-certificate.json
```

The runner refreshes Rhea/ChEBI chemistry, rebuilds the stoichiometric matrix,
creates the 56-coordinate unresolved parameter template, acquires SABIO-RK
kinetic-law candidates, acquires bounded PDBe/SIFTS mappings, runs interval
steady-state feasibility, and executes the aggregate static regressions.

To use an edited/source-paid manifest:

```bash
python3 scripts/run_bh4_phase4_maxcut.py \
  --manifest artifacts/biology/bh4-parameter-paid.json
```

The supplied manifest is normalized against the current matrix before solving.

## Quantitative evidence discovery

### SABIO-RK

```bash
python3 scripts/acquire_bh4_sabio_kinetics.py \
  --panel artifacts/biology/uniprot-kitzerow-bh4-panel-certificate.json \
  -o artifacts/biology/bh4-sabio-kinetics.json
```

The script queries exact `UniProtKB_AC` coordinates, records SABIO entry IDs,
normalized SBML response hashes, parameter values/units and PubMed identifiers.
These records are **candidate kinetic evidence only**. Km, kcat, Vmax, or a rate
law do not automatically become an in-vivo reaction-flux interval.

SABIO-RK REST documentation:

- https://sabiork.h-its.org/sabioRestWebServices/
- https://sabiork.h-its.org/layouts/content/docuRESTfulWeb/manual.gsp

### PDBe/SIFTS

```bash
python3 scripts/acquire_bh4_pdbe_sifts.py \
  --panel artifacts/biology/uniprot-kitzerow-bh4-panel-certificate.json \
  --max-pdb-per-protein 3 \
  -o artifacts/biology/bh4-pdbe-sifts.json
```

PDB IDs come from the exact UniProt panel. The script fetches PDBe updated
PDBx/mmCIF files and extracts `_pdbx_sifts_unp_segments` rows for the exact
UniProt accession. Use `--max-pdb-per-protein -1` for exhaustive PDB coverage.

A SIFTS mapping pays sequence/residue identity between UniProt and a PDB model;
it does not by itself prove that a mapped residue is catalytic, regulatory, or
causally involved in the BH4 mechanism.

PDBe/SIFTS documentation:

- https://www.ebi.ac.uk/pdbe/pdbe-rest-api
- https://www.ebi.ac.uk/pdbe/docs/sifts/quick.html

## Parameter manifest

Generate the matrix-aware template directly:

```bash
python3 scripts/acquire_bh4_parameter_evidence.py \
  --template \
  --matrix artifacts/biology/bh4-stoichiometric-matrix.json \
  -o artifacts/biology/bh4-parameter-template-v2.json
```

A paid reaction or exchange row requires:

```text
payment_status
lower
upper
unit
source_reference
same_object_reference
compartment_reference
measurement_time_reference
usable_for_joint_flux_witness = true
```

`unresolved` never means measured zero.

All solver-facing reaction and exchange intervals must use one normalized flux
unit. Cross-unit conversion must be performed and attributed before setting a
row usable for the joint witness.

## Interval feasibility

```bash
python3 scripts/solve_bh4_flux_intervals.py \
  --matrix artifacts/biology/bh4-stoichiometric-matrix.json \
  --parameters artifacts/biology/bh4-parameter-normalized.json \
  -o artifacts/biology/bh4-interval-flux-feasibility.json
```

The solver searches the bounded linear steady-state problem

```text
S*v + e = 0
```

using `scipy.optimize.linprog(method="highs")`.

Outcomes:

- `feasible`: at least one supplied-interval steady-state witness exists;
- `infeasible`: no steady-state witness exists inside those paid intervals;
- `underdetermined`: required intervals or normalized units are missing;
- `solver-unavailable`: SciPy is not installed.

Even `feasible` does not establish allocator causality, disease mechanism, or
clinical action. `infeasible` rules out only the specified steady-state interval
problem; it does not rule out time-varying dynamics or alternative state spaces.

## Regressions

```bash
python3 scripts/check_kitzerow_bh4_priority_all.py
```

This now runs:

1. the legacy evidence/identity regression;
2. the Phase-4 executed system-state regression;
3. the quantitative acquisition / interval-solver regression.

CI is not required for this tranche.
