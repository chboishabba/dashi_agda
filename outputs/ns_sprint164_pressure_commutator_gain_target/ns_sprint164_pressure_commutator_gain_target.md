# Sprint 164 Pressure Commutator Gain Target

- Surface: `PressureCommutatorGainTarget`
- Decision: `pressure_commutator_gain_target_recorded_fail_closed`
- Pressure representation: `p = R_i R_j(u_i u_j)`
- Angular projector: `Pi_plus(theta) near Sigma`
- Commutator: `[Pi_plus, R_i R_j]`
- CZ barrier: `alpha = 0 critical-scale boundedness only`
- Required gain: `alpha > 0 subcritical pressure-flux gain`
- AngularDegeneracyPressureCommutatorGain: `False`
- Validation passed: `True`

## Target Rows

| row | surface | object | status | target_role |
| --- | --- | --- | --- | --- |
| P01 | pressure_representation | p = R_i R_j(u_i u_j) | RECORDED | nonlocal pressure input |
| P02 | angular_projector | Pi_plus(theta) near Sigma | RECORDED | maximal-strain branch selector |
| P03 | pressure_commutator | [Pi_plus, R_i R_j] | TARGET_RECORDED_NOT_PROVED | candidate incoherence mechanism |
| P04 | calderon_zygmund_barrier | alpha = 0 | CRITICAL_BARRIER_RECORDED | known insufficient estimate |
| P05 | required_subcritical_gain | alpha > 0 | OPEN | missing Clay-relevant pressure gain |

## O/R/C/S/L/P/G/F

- O: Sprint164 lane 4 owns only the pressure-commutator gain target emitter.
- R: Record p=RiRj(uiuj), Pi_plus near Sigma, the commutator target, CZ alpha-zero barrier, and alpha-positive gain requirement.
- C: One stdlib Python script emits normalized JSON, CSV, Markdown, and manifest outputs.
- S: The pressure commutator is a theorem target; no depletion, local defect monotonicity, or Clay promotion is established.
- L: Riesz pressure + angular projector near Sigma -> commutator target -> CZ alpha=0 wall -> required alpha>0 gain.
- P: Fail-close AngularDegeneracyPressureCommutatorGain while recording the target and open pressure-flux gain.
- G: Promotion requires the three requested recorded/open flags true and all theorem/Clay flags false.
- F: The missing estimate is an alpha-positive pressure coherence loss near the angular-strain degeneracy set Sigma.
