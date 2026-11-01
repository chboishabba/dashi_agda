# Sprint 162 Critical Residual Boundary

- Surface: `CriticalResidualBoundary`
- Decision: `critical_residual_boundary_fail_closed`
- Residual-positive profile: `True`
- Residual depletion theorem: `False`
- Validation passed: `True`

| component | sign | boundary_status | open_lemma |
| --- | --- | --- | --- |
| LocalDefect | + | UNABSORBED_RESIDUAL_SOURCE | LocalDefectAbsorptionLemmaOpen |
| PressureFlux | + | SIGN_INDEFINITE_PRESSURE_SOURCE | PressureFluxSignClosureLemmaOpen |
| StretchingAlignment | + | ALIGNMENT_DEPLETION_NOT_ESTABLISHED | StretchingAlignmentDepletionLemmaOpen |
| Dissipation | - | INSUFFICIENT_TO_DOMINATE_SOURCES | DissipationDominanceLemmaOpen |
| NSCriticalResidual | + | POSITIVE_PROFILE_REMAINS | NSCriticalResidualDepletionTheoremOpen |

## O/R/C/S/L/P/G/F

- O: Sprint162 lane 1 owns the critical residual boundary summary.
- R: Record the residual-positive critical profile without promoting Clay Navier-Stokes or a residual depletion theorem.
- C: Single stdlib Python emitter writes outputs/ns_sprint162_critical_residual_boundary/summary.json.
- S: Residual terms are classified as boundary evidence only: LocalDefect, PressureFlux, StretchingAlignment, Dissipation, and NSCriticalResidual.
- L: local defect + pressure flux + stretching alignment - dissipation -> positive critical residual profile -> fail-closed theorem boundary.
- P: Use the artifact to block promotion until each residual-depletion lemma is supplied by a separate proof lane.
- G: Validation passes only when Clay/promotion flags are false and no required open lemma is asserted as closed.
- F: The residual depletion theorem remains false for Sprint162.
