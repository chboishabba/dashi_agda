# Sprint 155 Model Validity Assembler

- Decision: `fail_closed_model_validity_not_promoted`
- Validation passed: `True`
- Fail closed: `True`
- Full Clay can promote: `False`
- Clay Navier-Stokes promoted: `False`

## Closed Obligations

| obligation | closed |
| --- | ---: |
| LocalizedEnstrophyIdentity | True |
| BiotSavartNonlocalClosure | True |
| SimultaneousConstants | True |
| AnnularLeakage | True |
| SourceBound | True |

## Promotion Gates

| gate | can promote |
| --- | ---: |
| ModelValidityForWidthODE | False |
| SymmetricHouLuoBKMFinite | False |
| full_clay_can_promote | False |
| full_clay_ns_solved | False |
| clay_navier_stokes_promoted | False |

## Rows

| row_id | sprint_span | normalized_name | category | status | closed | can_promote | blockers |
| --- | --- | --- | --- | --- | ---: | ---: | --- |
| localized_enstrophy_identity | 155 | LocalizedEnstrophyIdentity | upstream_obligation | CLOSED | True | False | none |
| biot_savart_nonlocal_closure | 154 | BiotSavartNonlocalClosure | upstream_obligation | CLOSED | True | False | none |
| simultaneous_constants | 154 | SimultaneousConstants | upstream_obligation | CLOSED | True | False | none |
| annular_leakage | 152-155 | AnnularLeakage | upstream_obligation | CLOSED | True | False | none |
| source_bound | 153-155 | SourceBound | upstream_obligation | CLOSED | True | False | none |
| model_validity_for_width_ode | 151-155 | ModelValidityForWidthODE | promotion_gate | DEFERRED_TO_SEPARATE_PROMOTION_RECEIPT | False | False | localized IBP identity alone does not promote the width ODE model; width_ode_extracted_from_ns=False |
| symmetric_hou_luo_bkm_finite | 151-155 | SymmetricHouLuoBKMFinite | promotion_gate | CANNOT_PROMOTE_FAIL_CLOSED | False | False | ModelValidityForWidthODE is deferred/fail-closed |
| full_clay | 151-155 | FullClayNavierStokes | hard_guard | HARD_GUARD_FALSE | False | False | assembler hard guard: full Clay must not promote; external Clay acceptance absent; full Navier-Stokes theorem translation absent |

## Source Presence

| source | exists | path |
| --- | ---: | --- |
| s151_identity | True | `outputs/ns_sprint151_localized_enstrophy_identity/ns_sprint151_localized_enstrophy_identity_summary.json` |
| s151_identity_rows | True | `outputs/ns_sprint151_localized_enstrophy_identity/ns_sprint151_localized_enstrophy_identity_rows.json` |
| s151_cutoff | True | `outputs/ns_sprint151_cutoff_error_budget/ns_sprint151_cutoff_error_budget_summary.json` |
| s151_width_ode | True | `outputs/ns_sprint151_width_ode_extraction/ns_sprint151_width_ode_extraction_summary.json` |
| s153_source | True | `outputs/ns_sprint153_localized_vortex_stretching_source/ns_sprint153_localized_vortex_stretching_source_summary.json` |
| s153_constant_scan | True | `outputs/ns_sprint153_core_source_constant_scan/ns_sprint153_core_source_constant_scan_summary.json` |
| s153_balance | True | `outputs/ns_sprint153_source_dissipation_balance/ns_sprint153_source_dissipation_balance_summary.json` |
| s155_identity | True | `outputs/ns_sprint155_localized_enstrophy_ibp_identity/ns_sprint155_localized_enstrophy_ibp_identity_summary.json` |
| s155_operator | True | `outputs/ns_sprint155_operator_boundary_term_checker/ns_sprint155_operator_boundary_term_checker_summary.json` |

## O/R/C/S/L/P/G/F

- O: Worker 4 owns scripts/ns_sprint155_model_validity_assembler.py and outputs/ns_sprint155_model_validity_assembler/.
- R: Assemble Sprint 151-155 obligation states for localized identity, Biot-Savart closure, simultaneous constants, annular leakage, source bound, model validity, BKM finiteness, and full Clay promotion.
- C: A deterministic Python stdlib script reads local summary/row JSON and writes rows JSON, rows CSV, summary JSON, Markdown, and manifest files.
- S: Sprint 151 and 153 artifacts are present as history. The supplied Sprint 154 premise closes Biot-Savart/nonlocal and simultaneous constants as route support. Sprint 155 records the localized IBP identity at scale delta.
- L: Scale-delta support rows may close from Sprint 154/155 receipts. Downstream model/BKM/Clay promotion remains separate and fail-closed.
- P: Use this as a normalized model-validity readiness ledger, not as an Agda proof, analytic theorem, BKM proof, or Clay solution.
- G: ModelValidityForWidthODE can promote only if all five named upstream obligations are closed and width_ode_extracted_from_ns is true. BKM requires model validity plus explicit BKM flags. Full Clay is hard guarded false in this assembler.
- F: Open blockers remain: downstream model-validity promotion, symmetric Hou-Luo BKM translation, and the structurally separate full Clay NS mechanism-exhaustion theorem.

## Guard

This assembler is fail-closed. It does not promote full Clay Navier-Stokes, even if an upstream evidence artifact is present.
