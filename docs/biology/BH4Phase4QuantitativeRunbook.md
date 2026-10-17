# BH4 Phase-4 quantitative max-cut runbook

## Current executed state

The exact 16-protein panel resolves to 24 protein-to-Rhea links, 12 finite internal reaction columns, 3 non-finite MTOR residual reactions and 29 finite species. The current open-system problem has 56 coordinates: 15 core state/context coordinates + 12 reaction-flux intervals + 29 exchange intervals. The first steady-state attempt remains `underdetermined` because those solver bounds are not yet source-paid.

Executed evidence receipts:

- PDBe/SIFTS: 38 structures, 526 exact UniProt/PDB segment mappings, zero acquisition errors.
- SABIO-RK: 190 kinetic-law rows across 11/16 exact human UniProt queries, zero acquisition errors.
- Schema-aware SABIO recount: **932 explicit kinetic parameter objects**.
- SABIO -> finite Rhea adjudication: **875 parameter candidates map to 10 of 12 finite reaction columns**.
- The two exact-UniProt SABIO coverage holes are `RHEA:11920` (PCBD1) and `RHEA:19897` (NOS).

The first executed adjudication classified the 932 candidates as 237 affinity-like, 139 rate-like, 30 turnover-like and 526 unclassified. Those counts are historical receipt data from adjudication schema v1; schema v2 refines the hint vocabulary without promoting any candidate to a flux bound.

## One-command run

```bash
python3 scripts/run_bh4_phase4_maxcut.py
```

The runner refreshes Rhea/ChEBI chemistry with bounded retry/backoff, rebuilds `S`, writes the 56-coordinate template, acquires SABIO-RK export rows and normalized parameter objects, creates the SABIO-to-Rhea adjudication worklist, acquires PDBe/SIFTS mappings, runs interval feasibility and aggregate regressions, and writes `artifacts/biology/bh4-phase4-maxcut-summary.json`.

## SABIO-RK acquisition and adjudication

The live export API is `https://sabio.h-its.org/export-api/sabio/kinlaw-entry/json`; exact queries use `UniProtKB_AC`. The successful run returned 190 rows and 932 nested parameter objects. `build_bh4_sabio_adjudication.py` joins each parameter to the exact panel protein, protein-linked Rhea IDs and the subset present in the 12-column finite matrix.

Adjudication schema v2 emits `uncovered_finite_reactions` and refines parameter-kind hints, including `catalytic-constant-like`, `inhibitory-like`, `concentration-like`, `affinity-like`, `rate-like`, `turnover-like` and `unclassified`.

Every candidate remains `usable_for_flux_bound = false` until assay/context identity, same-object/compartment/time translation, normalized solver units, and a justified kinetic-parameter-to-network-flux translation are paid.

The executed coverage is **10 of 12 finite reactions**. `RHEA:11920` and `RHEA:19897` require external primary-literature evidence rather than weaker SABIO matching.

## Primary-literature gap evidence

`DASHI.Biology.BH4MissingReactionKineticsEvidenceExact` records bounded primary human evidence for the two SABIO-uncovered reactions.

For PCBD1 / `RHEA:11920`:

- Johnen et al., PNAS 1995, DOI `10.1073/pnas.92.26.12384`: human 4a-carbinolamine dehydratase shows cooperative/non-Michaelis-Menten behavior; the C82R mutant retains approximately 5 uM Km but has lower Vmax.
- Thony et al., Eur J Biochem 1995, DOI `10.1111/j.1432-1033.1995.tb20714.x`: purified human wild-type dehydratase strongly accelerates synthetic substrate dehydration.

For NOS / `RHEA:19897`:

- PMID `9224737`: recombinant human inducible NOS reports approximately 800 nmol NO min^-1 mg^-1 Vmax and 22 uM Km(L-Arg), with BH4 required during preparation.
- PMID `9089781`: human placental NOS3 reports BH4-sensitive activity, apparent Km(L-Arg) around 3.12 uM without added BH4 and 2.06 uM with 50 uM BH4, with Vmax increasing from 2.5-7.55 to 13.3-58.5 pmol min^-1 mg^-1 and half-maximal BH4 stimulation near 79 nM.

These are evidence candidates, not network-flux payments. PCBD1 mutant kinetics do not substitute for wild-type cellular flux, and NOS isoform/assay kinetics cannot be silently collapsed into one shared in-vivo `RHEA:19897` flux.

## PDBe/SIFTS

The bounded first-three-PDB receipt remains 38 structures / 526 exact mappings. SIFTS pays sequence/residue identity only; it does not establish catalytic or regulatory function. The live structural task is residue/site functional adjudication where needed.

## Solver payment

A solver-usable reaction or exchange row still requires lower/upper bounds in one normalized flux unit plus source, same-object, compartment and measurement-time coordinates and `usable_for_joint_flux_witness = true`. `unresolved` never means measured zero.

The steady-state problem is `S*v + e = 0` using `scipy.optimize.linprog(method="highs")`. `feasible`, `infeasible`, or `underdetermined` apply only to the specified bounded model and do not establish or refute the broader disease mechanism.

## Regressions

```bash
python3 scripts/check_kitzerow_bh4_priority_all.py
```

The aggregate checker covers the executed chemistry/network receipts, Rhea retry contract, executed SABIO/SIFTS receipts, 932/875/10-of-12 adjudication receipt, primary PCBD1/NOS gap evidence, 56-coordinate manifest and interval-solver firewalls.

CI is not the completion gate for this tranche.
