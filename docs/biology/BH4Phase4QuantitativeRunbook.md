# BH4 Phase-4 quantitative max-cut runbook

## Current executed state

The exact 16-protein panel resolves to 24 protein-to-Rhea links, 12 finite internal reaction columns, 3 non-finite MTOR residual reactions and 29 finite species. The open-system problem has 56 coordinates: 15 core state/context coordinates + 12 reaction-flux intervals + 29 exchange intervals. The first steady-state attempt remains `underdetermined` because the solver bounds are not yet source-paid.

Executed evidence receipts include PDBe/SIFTS 38/526, SABIO-RK 190 kinetic rows / 932 parameter objects, 875 candidate occurrences covering 10/12 finite reactions, the refined v2 classification, ranked per-reaction kinetic queues, and xPollenation neighbourhoods for all 12 finite reactions. xPollenation remains navigation/enrichment only and never creates payment.

## One-command run

```bash
python3 scripts/run_bh4_phase4_maxcut.py
```

The runner now targets summary schema `dashi.bh4-phase4-maxcut-run.v8` and additionally writes:

```text
artifacts/biology/bh4-protein-abundance.json
artifacts/biology/bh4-exchange-context.json
artifacts/biology/bh4-joint-payment-ledger.json
```

Network acquisition is deliberately partial-tolerant: source errors are retained in the artifacts and summary rather than being interpreted as biological absence.

## Reaction-capacity context

`acquire_bh4_protein_abundance.py` queries ProteomicsDB's public OData `proteinexpression.xsodata` service by exact UniProt accession at MS levels 1 and 2, using tissue grouping and the iBAQ abundance-estimation mode. It preserves tissue/sample/project provenance, normalized intensity ranges, molecular weight from the exact UniProt certificate, request URLs and raw response digests.

This evidence is context for the Vmax/kcat normalization problem only. ProteomicsDB `NORMALIZED_INTENSITY` is a normalized protein-abundance estimate, not an independently calibrated molar intracellular enzyme concentration. Cross-tissue observations cannot be collapsed into one state, and protein abundance alone does not establish reaction flux.

## Exchange/state context

`acquire_bh4_exchange_context.py` uses the exact Rhea participant names associated with the 29 finite matrix species and queries the Metabolomics Workbench REST API:

- `refmet/name/<name>/all` for standardized metabolite identity/context;
- the documented `metstat` RefMet route with `Human` species for human-study occurrence/context.

Metabolite identity or occurrence in a human metabolomics study is not uptake/export/transport flux. Even a measured concentration would remain a state coordinate rather than an exchange rate unless a same-object transport/turnover model and time/compartment bridge are paid.

## Joint payment ledger

`build_bh4_joint_payment_ledger.py` combines the existing flux-payment preparation, protein-abundance context, exchange/metabolomics context, and the 56-coordinate parameter manifest. It reports three separate surfaces:

```text
reaction_flux_coordinates
exchange_coordinates
state_context_coordinates
```

For reactions it records whether abundance context exists while retaining `abundance_intensity_is_not_enzyme_concentration = true`. For exchange coordinates it reports RefMet/human-study context while retaining `concentration_context_is_not_exchange_flux = true` and `transport_or_turnover_evidence_required = true`.

Crucially, `solver_payable` is read only from the existing normalized parameter manifest's `usable_for_joint_flux_witness`. Context coverage never flips a payment gate.

## Live max-cut after the v8 run

The run should tell us exactly which reaction columns have abundance context and which exchange species have human metabolomics context. The scientific payment frontier is then:

1. convert suitable abundance evidence into a defensible same-tissue/compartment enzyme concentration or protein-mass/volume bridge;
2. combine that with assay Vmax or kcat only under a justified same-state translation to emit the first `REACTION_FLUX:<RHEA-ID>` intervals;
3. acquire explicit transporter/turnover or time-resolved source/sink evidence for `EXCHANGE:<species-id>` rather than inferring exchange from concentration;
4. pay BH4/BH2/redox and simultaneous consumer-demand state coordinates on one coherent object/time/compartment;
5. rerun `S*v + e = 0` interval feasibility;
6. only then advance to competing-mechanism discrimination.

## Regressions

```bash
python3 scripts/check_kitzerow_bh4_priority_all.py
python3 scripts/check_bh4_xpollenation.py
```

The aggregate checker includes acquisition, ranking, payment-preparation and joint-payment firewalls. CI is not the completion gate for this tranche.
