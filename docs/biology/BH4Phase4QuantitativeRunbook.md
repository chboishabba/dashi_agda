# BH4 Phase-4 quantitative max-cut runbook

## Current executed state

The exact 16-protein panel resolves to 24 protein-to-Rhea links, 12 finite internal reaction columns, 3 non-finite MTOR residual reactions and 29 finite species. The current open-system problem has 56 coordinates: 15 core state/context coordinates + 12 reaction-flux intervals + 29 exchange intervals. The first steady-state attempt remains `underdetermined` because those solver bounds are not yet source-paid.

Executed evidence receipts:

- PDBe/SIFTS: 38 structures, 526 exact UniProt/PDB segment mappings, zero acquisition errors.
- SABIO-RK: 190 kinetic-law rows across 11/16 exact human UniProt queries, zero acquisition errors.
- Schema-aware SABIO recount: **932 explicit kinetic parameter objects**.
- SABIO -> finite Rhea adjudication v2: **875 parameter candidates map to 10 of 12 finite reaction columns**.
- v2 parameter hints: 475 concentration-like, 160 affinity-like, 139 rate-like, 83 inhibitory-like, 30 catalytic-constant-like and only 45 unclassified.
- The two exact-UniProt SABIO coverage holes are `RHEA:11920` (PCBD1) and `RHEA:19897` (NOS).

The v2 classification is now the canonical executed classification receipt. It is descriptive triage, not a quantitative flux payment.

## One-command run

```bash
python3 scripts/run_bh4_phase4_maxcut.py
```

The runner now refreshes Rhea/ChEBI chemistry with bounded retry/backoff, rebuilds `S`, writes the 56-coordinate template, acquires SABIO-RK export rows and normalized parameter objects, creates the SABIO-to-Rhea adjudication worklist, ranks candidates per finite Rhea column by flux relevance, acquires PDBe/SIFTS mappings, runs interval feasibility and aggregate regressions, and writes `artifacts/biology/bh4-phase4-maxcut-summary.json` schema v5.

New ranking artifact:

```text
artifacts/biology/bh4-flux-candidate-ranking.json
```

Use `--top-kinetic-candidates N` to change how many ranked candidates are retained per reaction.

## SABIO-RK acquisition and adjudication

The live export API is `https://sabio.h-its.org/export-api/sabio/kinlaw-entry/json`; exact queries use `UniProtKB_AC`. The successful run returned 190 rows and 932 nested parameter objects. `build_bh4_sabio_adjudication.py` joins each parameter to the exact panel protein, protein-linked Rhea IDs and the subset present in the 12-column finite matrix.

Every candidate remains `usable_for_flux_bound = false` until assay/context identity, same-object/compartment/time translation, normalized solver units, and a justified kinetic-parameter-to-network-flux translation are paid.

The executed coverage is **10 of 12 finite reactions**. `RHEA:11920` and `RHEA:19897` use separately owned primary-literature evidence rather than weaker database matching.

## Flux-relevance ranking

`rank_bh4_flux_candidates.py` converts the large candidate worklist into a bounded per-reaction adjudication queue. It assigns one of five roles:

- `direct-rate-candidate`: Vmax / measured-rate-like evidence;
- `capacity-candidate`: kcat / turnover-like evidence that still requires enzyme abundance/activity/state;
- `kinetic-shape-candidate`: Km/Kd/Ki-like evidence;
- `assay-context-only`: substrate/effector/condition concentrations;
- `not-flux-informative`: unclassified at this layer.

The ranking score rewards flux relevance plus explicit numeric values, units, entry identity and parameter identity. It is a triage score, not a scientific confidence score and not a solver bound.

Every ranked candidate carries four explicit gates:

```text
assay_reaction_identity_paid
same_object_compartment_time_paid
normalized_solver_flux_unit_paid
kinetic_to_flux_translation_paid
```

Absent coordinates default to `false`. `usable_for_flux_bound` becomes true only when all four are explicitly true.

This is deliberate:

- a rate-like assay value is not automatically an in-vivo reaction flux;
- kcat alone is only a capacity candidate until enzyme abundance/state are paid;
- Km/Ki/Kd constrain kinetic shape, not flux magnitude by themselves;
- assay concentrations are context, not reaction bounds.

Run the ranking independently with:

```bash
python3 scripts/rank_bh4_flux_candidates.py \
  --adjudication artifacts/biology/bh4-sabio-adjudication.json \
  --matrix artifacts/biology/bh4-stoichiometric-matrix.json \
  -o artifacts/biology/bh4-flux-candidate-ranking.json
```

## Primary-literature gap evidence

`DASHI.Biology.BH4MissingReactionKineticsEvidenceExact` owns bounded primary human evidence for the two SABIO-uncovered reactions.

For PCBD1 / `RHEA:11920`:

- Johnen et al., PNAS 1995, DOI `10.1073/pnas.92.26.12384`: human 4a-carbinolamine dehydratase shows cooperative/non-Michaelis-Menten behavior; the C82R mutant retains approximately 5 uM Km but has lower Vmax.
- Thony et al., Eur J Biochem 1995, DOI `10.1111/j.1432-1033.1995.tb20714.x`: purified human wild-type dehydratase strongly accelerates synthetic substrate dehydration.

For NOS / `RHEA:19897`:

- PMID `9224737`: recombinant human inducible NOS reports approximately 800 nmol NO min^-1 mg^-1 Vmax and 22 uM Km(L-Arg), with BH4 required during preparation.
- PMID `9089781`: human placental NOS3 reports BH4-sensitive activity and BH4-dependent changes in apparent Km/Vmax.

These close the evidence-discovery gap, not the network-flux gap. PCBD1 mutant kinetics do not substitute for wild-type cellular flux, and NOS isoform/assay kinetics cannot be collapsed silently into one shared in-vivo `RHEA:19897` flux.

## Solver payment

A solver-usable reaction or exchange row still requires lower/upper bounds in one normalized flux unit plus source, same-object, compartment and measurement-time coordinates and `usable_for_joint_flux_witness = true`. `unresolved` never means measured zero.

The steady-state problem remains:

```text
S*v + e = 0
```

using `scipy.optimize.linprog(method="highs")` only after all solver-facing intervals are paid.

## Regressions

```bash
python3 scripts/check_kitzerow_bh4_priority_all.py
```

The aggregate checker now covers the executed chemistry/network receipts, Rhea retry contract, SABIO/SIFTS receipts, canonical schema-v2 932/875/10-of-12 classification counts, flux-relevance ranking boundaries, primary PCBD1/NOS gap evidence, the 56-coordinate manifest and interval-solver firewalls.

CI is not the completion gate for this tranche.
