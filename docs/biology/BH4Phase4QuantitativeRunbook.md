# BH4 Phase-4 quantitative max-cut runbook

## Current state

The exact 16-protein panel currently resolves to:

- 24 protein-to-Rhea catalytic links;
- 12 finite internal reaction columns;
- 3 non-finite MTOR protein/R-group residual reactions;
- 29 finite species;
- a 56-coordinate quantitative problem: 15 core state coordinates + 12 reaction-flux intervals + 29 exchange intervals;
- first joint feasibility outcome: `underdetermined`.

The first bounded PDBe/SIFTS run is formally promoted from its machine-generated schema-v2 receipt:

- 38 PDB structures examined;
- 526 exact `_pdbx_sifts_unp_segments` rows;
- 14 proteins with UniProt PDB links;
- 13 proteins with at least one matching segment;
- PCBD1 and AGMO have no panel PDB links;
- PCBD1, AGMO and PAH have no matching segment in the bounded first-three-PDB sample;
- zero HTTP/parse errors.

The first successful SABIO export-API run is also formally promoted:

- 16 proteins requested/completed;
- 11 proteins with at least one kinetic-law row;
- 190 kinetic-law export rows;
- zero acquisition errors;
- exact per-protein counts owned by `DASHI.Biology.BH4ExecutedSABIOReceiptExact`.

The historical `kinetic_parameter_count = 0` from that run is **not** a scientific zero. The parser used pre-migration value-key spellings while the export payload uses fields such as `n_start_value`, `n_end_value` and `end_value`. Schema-aware parameter normalization is therefore the next execution/adjudication step.

## One-command run

```bash
python3 scripts/run_bh4_phase4_maxcut.py
```

Default input:

```text
artifacts/biology/uniprot-kitzerow-bh4-panel-certificate.json
```

The runner now:

1. refreshes Rhea/ChEBI chemistry with bounded three-attempt exponential-backoff network retries;
2. rebuilds `S`;
3. writes the 56-coordinate template;
4. acquires SABIO-RK export rows and schema-aware kinetic parameter candidates;
5. joins those candidates onto the finite Rhea reaction columns as a non-promoting adjudication worklist;
6. acquires PDBe/SIFTS mappings;
7. runs interval feasibility and aggregate regressions;
8. writes the final summary.

Artifacts:

```text
artifacts/biology/rhea-kitzerow-bh4-reactions.json
artifacts/biology/bh4-stoichiometric-matrix.json
artifacts/biology/bh4-parameter-template-v2.json
artifacts/biology/bh4-sabio-kinetics.json
artifacts/biology/bh4-sabio-adjudication.json
artifacts/biology/bh4-pdbe-sifts.json
artifacts/biology/bh4-interval-flux-feasibility.json
artifacts/biology/bh4-phase4-maxcut-summary.json
```

The current summary schema is `dashi.bh4-phase4-maxcut-run.v4`.

## SABIO-RK current API

The historical `/sabioRestWebServices/*` endpoints rewrite to the browser SPA/404 shell. HTTP 200 HTML is explicitly **not** a zero-entry receipt.

The current acquirer uses:

```text
https://sabio.h-its.org/export-api/sabio/kinlaw-entry/json
```

with exact queries such as:

```text
UniProtKB_AC:"P30793"
```

and validates the JSON export envelope:

```json
{"meta": {...}, "data": [...]}
```

It follows pagination, hashes every raw page, preserves raw entries, and now extracts explicit nested parameter objects using the current export value fields including `n_start_value`, `n_end_value` and `end_value`.

Run it independently with:

```bash
python3 scripts/acquire_bh4_sabio_kinetics.py \
  --panel artifacts/biology/uniprot-kitzerow-bh4-panel-certificate.json \
  -o artifacts/biology/bh4-sabio-kinetics.json
```

The executed acquisition receipt is:

```text
TPH2 75
PAH  44
TPH1 33
MTOR 13
PTS   6
SPR   6
GCH1  4
QDPR  4
TH    2
AGMO  2
TSC2  1
-----------
total 190
```

GCHFR, PCBD1, NOS1, NOS2 and NOS3 returned zero rows for this exact UniProt export query. That is an export-query observation, not proof that those proteins have no kinetic literature.

SABIO records remain **candidate kinetic evidence only**. Km, kcat, Vmax, specific activity, rate-law entries or an export match do not automatically become in-vivo reaction-flux bounds.

## SABIO → finite Rhea adjudication

The next-run pipeline automatically produces:

```text
artifacts/biology/bh4-sabio-adjudication.json
```

or independently:

```bash
python3 scripts/build_bh4_sabio_adjudication.py \
  --sabio artifacts/biology/bh4-sabio-kinetics.json \
  --rhea artifacts/biology/rhea-kitzerow-bh4-reactions.json \
  --matrix artifacts/biology/bh4-stoichiometric-matrix.json \
  -o artifacts/biology/bh4-sabio-adjudication.json
```

Each normalized parameter candidate records its exact panel protein, SABIO entry, name/type/SBO/value range/unit, protein-linked Rhea IDs and the subset that are finite matrix columns. It also emits a non-authoritative parameter-kind hint (`rate-like`, `turnover-like`, `affinity-like`, `unclassified`).

Every candidate remains:

```text
usable_for_flux_bound = false
```

until these obligations are paid:

- assay/context identity;
- same-object/compartment/time translation;
- normalized solver flux unit;
- justified kinetic-parameter-to-network-flux translation.

The worklist therefore measures **candidate coverage**, not quantitative payment.

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

None automatically establishes or refutes the broader Kitzerow disease mechanism outside the modeled state/problem.

## Regressions

```bash
python3 scripts/check_kitzerow_bh4_priority_all.py
```

The aggregate checker covers the legacy evidence/identity lane, executed Phase-4 system-state lane, Rhea retry contract, executed SABIO and SIFTS receipts, SABIO parameter normalization/adjudication contract, 56-coordinate manifest and interval-solver firewalls.

CI is not the completion gate for this tranche.
