# BH4 Phase-4 quantitative max-cut runbook

## Current executed state

The exact 16-protein panel resolves to 24 protein-to-Rhea links, 12 finite internal reaction columns, 3 non-finite MTOR residual reactions and 29 finite species. The open-system problem has 56 coordinates: 15 core state/context coordinates + 12 reaction-flux intervals + 29 exchange intervals. The first steady-state attempt remains `underdetermined` because the solver bounds are not yet source-paid.

Executed evidence receipts:

- PDBe/SIFTS: 38 structures / 526 exact mappings / zero acquisition errors.
- SABIO-RK: 190 kinetic-law rows, 932 explicit parameter objects.
- SABIO -> finite Rhea adjudication v2: 875 mapped candidate occurrences covering 10/12 finite columns.
- v2 classification: 475 concentration-like, 160 affinity-like, 139 rate-like, 83 inhibitory-like, 30 catalytic-constant-like, 45 unclassified.
- exact-UniProt SABIO holes: `RHEA:11920` (PCBD1) and `RHEA:19897` (NOS), both separately anchored by bounded primary human literature.
- ranked kinetic queue: 5 columns with rate-like candidates, 3 with turnover/capacity candidates, 2 with kinetic-shape-only candidates, 2 uncovered by SABIO.

## One-command run

```bash
python3 scripts/run_bh4_phase4_maxcut.py
```

The runner now writes summary schema `dashi.bh4-phase4-maxcut-run.v6` and adds:

```text
artifacts/biology/bh4-flux-candidate-ranking.json
artifacts/biology/bh4-flux-payment-preparation.json
```

## Flux payment preparation

`prepare_bh4_flux_payment.py` converts the ranked candidate queue into a fail-closed per-reaction payment ledger with four evidence classes:

- `assay-specific-capacity`: Vmax / specific-activity-like measurements;
- `turnover-capacity`: kcat / turnover values requiring enzyme abundance/activity state;
- `kinetic-shape-only`: Km/Kd/Ki-like evidence without a flux-magnitude anchor;
- `primary-literature-gap`: no direct SABIO candidate for the finite reaction, with PCBD1/NOS handled by the separate primary-literature owner.

This distinction is important. A Vmax expressed as `nmol/(min·mg)` is an assay capacity normalized by a protein-mass basis, not an intracellular compartment flux. Mapping it into the network requires the relevant enzyme/protein abundance, compartment volume or mass basis, assay-state translation, and one common solver flux unit. Likewise `kcat` requires enzyme abundance before `Vmax = kcat·[E]` can define a capacity.

Every reaction remains fail-closed behind:

```text
assay_reaction_identity_paid
same_object_compartment_time_paid
normalized_solver_flux_unit_paid
kinetic_to_flux_translation_paid
```

The payment-preparation artifact additionally records:

```text
enzyme_abundance_required_reactions
normalization_bridge_required_reactions
magnitude_anchor_missing_reactions
payable_reaction_count
```

No missing gate defaults to true, and no evidence class itself creates a solver bound.

## Current quantitative frontier

The next scientific work is no longer acquisition or candidate ranking. It is to pay the reaction-level normalization/context gates and emit the first justified `REACTION_FLUX:<RHEA-ID>` intervals. In parallel, the 29 `EXCHANGE:<species-id>` intervals, compartment-specific BH4/BH2/redox state, simultaneous AAAH/NOS/AGMO demand, NOS coupling transitions, and same-object upstream-to-TSC2 transport remain open.

## Solver

The bounded steady-state target remains:

```text
S*v + e = 0
```

using `scipy.optimize.linprog(method="highs")` only after every solver-facing interval is source-paid. `unresolved` never means zero; `feasible`/`infeasible` refer only to the supplied bounded model and do not establish or refute disease causation.

## Regressions

```bash
python3 scripts/check_kitzerow_bh4_priority_all.py
```

The aggregate checker now includes ranking and flux-payment-preparation firewalls. CI is not the completion gate for this tranche.
