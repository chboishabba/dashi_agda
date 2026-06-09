# ns_sprint136_hou_luo_symmetric_source_sign

## Summary

- Scenario: `CanonicalZReflectionSymmetricHouLuo`
- LogLossSourceLowerBound: `False`
- Source at `z=0`: `zero`
- Source sign under axial monotonicity: `nonpositive_away_from_z_equals_0`
- Viscous term at interior maximum: `nonpositive`
- BKM finite conditional on: `AxialMonotonicityOfSwirlProfile`
- Full Clay NS solved: `False`
- Clay Navier-Stokes promoted: `False`

## Sign Ledger

| row | assertion | site | sign/truth | consequence |
|---|---|---|---|---|
| 001_log_loss_lower_bound_false | LogLossSourceLowerBound | canonical z-reflection symmetric Hou-Luo profile | False | The Sprint 135 blowup gate LogLossSourceLowerBound is closed negatively for this symmetric scenario. |
| 002_source_zero_on_symmetry_plane | SourceAtZEqualsZero | z=0 symmetry plane | True | No positive source production is generated exactly on the canonical symmetry plane. |
| 003_source_nonpositive_away_from_plane | SourceNonpositiveUnderAxialMonotonicity | z != 0, same canonical symmetric branch | True | The source cannot supply the positive lower forcing needed for BKM divergence in this symmetric monotone branch. |
| 004_viscosity_nonpositive_at_interior_max | InteriorMaximumViscousTermNonpositive | interior positive maximum of omega1 | True | At the maximum point, viscosity does not create positive vorticity growth and therefore cannot rescue the false lower source bound. |
| 005_bkm_finite_conditional | BKMFiniteConditionalOnAxialMonotonicity | canonical symmetric Hou-Luo evolution class | conditional_true | BKM remains finite conditional on AxialMonotonicityOfSwirlProfile. |

## Interpretation

The canonical z-reflection symmetric Hou-Luo branch does not supply the positive source lower bound needed by the Sprint 135 blowup route. The signed source is zero on the symmetry plane and nonpositive under axial monotonicity away from it, while the viscous term is nonpositive at an interior positive maximum. The resulting BKM finiteness statement is conditional on axial monotonicity and is not a Clay promotion.
