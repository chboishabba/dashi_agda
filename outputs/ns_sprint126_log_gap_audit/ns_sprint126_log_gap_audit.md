# ns_sprint126_log_gap_audit

- verdict: PASS
- surface: `DASHI/Physics/Closure/NSSprint126LogGapAuditAndAxisymmetricPivot.agda`
- passed: 8 / 8
- blocked-marker hits: 0

| Check | Expected | Actual | Result | Evidence |
| --- | --- | --- | --- | --- |
| input surface present | DASHI/Physics/Closure/NSSprint126LogGapAuditAndAxisymmetricPivot.agda | present | PASS | `/home/c/Documents/code/dashi_agda/DASHI/Physics/Closure/NSSprint126LogGapAuditAndAxisymmetricPivot.agda` |
| conditional log gap closure | true | true | PASS | `vortexStretchingLogGapConditional=true` |
| unconditional log gap closure | false | false | PASS | `vortexStretchingLogGapUnconditional=false, vortexStretchingLogGapUnconditionalOpen=true` |
| unconditional log gap state | open | open | PASS | `surface-text` |
| hidden regularity record | true | true | PASS | `extraRegularityRequiredForLogGap=true` |
| clay Navier-Stokes promotion | false | false | PASS | `clayNavierStokesPromoted` |
| axisymmetric boundary gate | next | next | PASS | `surface-text` |
| blocked marker scan | zero hits | 0 | PASS | `[]` |
