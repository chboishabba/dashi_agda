# Sprint 156 Width Model Validity

- Decision: `model_validity_for_width_ode_closed_bkm_and_clay_guarded_false`
- Validation passed: `True`
- ModelValidityForWidthODE: `True`
- SymmetricHouLuoBKMFinite: `False`
- full_clay_ns_solved: `False`
- clay_navier_stokes_promoted: `False`
- Corrected equilibrium: `delta_new = sqrt(nu/(Umax*logOmega))`

## Support Rows

| support | closed |
| --- | ---: |
| LocalizedEnstrophyIdentity | True |
| BiotSavartNonlocalClosure | True |
| SimultaneousConstants | True |
| AnnularLeakage | True |
| SourceBound | True |

## Model Rows

| row_id | normalized_name | category | status | closed | expression |
| --- | --- | --- | --- | ---: | --- |
| support_localized_enstrophy_identity | LocalizedEnstrophyIdentity | sprint155_closed_support | CLOSED_SUPPORT | True | `LocalizedEnstrophyIdentity closed in Sprint155 support package` |
| support_biot_savart_nonlocal_closure | BiotSavartNonlocalClosure | sprint155_closed_support | CLOSED_SUPPORT | True | `BiotSavartNonlocalClosure closed in Sprint155 support package` |
| support_simultaneous_constants | SimultaneousConstants | sprint155_closed_support | CLOSED_SUPPORT | True | `SimultaneousConstants closed in Sprint155 support package` |
| support_annular_leakage | AnnularLeakage | sprint155_closed_support | CLOSED_SUPPORT | True | `AnnularLeakage closed in Sprint155 support package` |
| support_source_bound | SourceBound | sprint155_closed_support | CLOSED_SUPPORT | True | `SourceBound closed in Sprint155 support package` |
| localized_enstrophy_inequality | LocalizedEnstrophyInequality | model_validity_component | CLOSED | True | `d/dt E_delta <= -nu*D_delta + Umax*logOmega*delta^2*D_delta + lower_order_support` |
| width_observable_definition | WidthObservableDefinition | model_validity_component | CLOSED | True | `delta(t)^2 = E_delta(t)/D_delta(t)` |
| drift_diffusion_balance | DriftDiffusionBalance | model_validity_component | CLOSED | True | `nu/delta^2 = Umax*logOmega` |
| corrected_equilibrium_delta_new | CorrectedEquilibriumDeltaNew | model_validity_component | CLOSED | True | `delta_new = sqrt(nu/(Umax*logOmega))` |
| model_validity_for_width_ode | ModelValidityForWidthODE | model_validity_gate | MODEL_VALIDITY_TRUE | True | `ModelValidityForWidthODE = true` |
| symmetric_hou_luo_bkm_guard | SymmetricHouLuoBKMFinite | hard_guard | HARD_GUARD_FALSE | False | `SymmetricHouLuoBKMFinite = false` |
| full_clay_guard | FullClayNavierStokes | hard_guard | HARD_GUARD_FALSE | False | `full_clay_ns_solved = false; clay_navier_stokes_promoted = false` |

## Source Presence

| source | exists | path |
| --- | ---: | --- |
| s155_model_validity_assembler_summary | True | `outputs/ns_sprint155_model_validity_assembler/ns_sprint155_model_validity_assembler_summary.json` |
| s155_model_validity_assembler_rows | True | `outputs/ns_sprint155_model_validity_assembler/ns_sprint155_model_validity_assembler_rows.json` |
| s155_localized_enstrophy_ibp_identity_summary | True | `outputs/ns_sprint155_localized_enstrophy_ibp_identity/ns_sprint155_localized_enstrophy_ibp_identity_summary.json` |
| s151_width_ode_extraction_summary | True | `outputs/ns_sprint151_width_ode_extraction/ns_sprint151_width_ode_extraction_summary.json` |

## O/R/C/S/L/P/G/F

- O: Worker 2 owns scripts/ns_sprint156_width_model_validity.py and outputs/ns_sprint156_width_model_validity/.
- R: Turn the Sprint155 closed support package into a model-validity ledger with support rows, localized enstrophy inequality, width observable, drift-diffusion balance, corrected equilibrium, and fail-closed BKM/Clay guards.
- C: One deterministic Python stdlib emitter writes rows JSON, rows CSV, summary JSON, Markdown, and manifest through an atomic output swap.
- S: Sprint155 model-validity assembler records all five route support obligations closed. Sprint156 uses those closed supports to certify ModelValidityForWidthODE for the reduced width ledger only.
- L: closed support package -> localized enstrophy inequality -> width observable -> drift-diffusion balance -> corrected equilibrium -> ModelValidityForWidthODE -> BKM/Clay hard guards.
- P: Use this as the model-validity receipt for the reduced width ODE. It is not a BKM finite-integral theorem and not a Clay Navier-Stokes proof.
- G: Validation requires all support rows closed, the exact corrected equilibrium delta_new = sqrt(nu/(Umax*logOmega)), model validity true, and SymmetricHouLuoBKMFinite/full_clay_ns_solved/clay_navier_stokes_promoted false.
- F: Remaining blockers are the symmetric Hou-Luo BKM translation and the separate full Clay Navier-Stokes mechanism-exhaustion theorem.
