# Sprint 142 Boundary/Annulus Concavity Ledger

- Contract: `ns_sprint142_boundary_annulus_concavity_ledger`
- Program: `HouLuoAxisymmetricWithSwirlBarrierProgram`
- Blocker: `GlobalConcavityOfPsi1`
- Parent gate: `AxialMonotonicityOfSwirlProfile`
- Decision: `fail_closed_boundary_annulus_concavity_blocker_open`
- Required theorem: `BoundaryCompatibleKernelSignCancellationForPsi1Concavity`
- Global concavity closed: `False`
- Global proof emitted: `False`
- Clay Navier-Stokes promoted: `False`

## Rows

| row_id | status | role | blocker effect | required input |
| --- | --- | --- | --- | --- |
| interior_local_support | supported_local_only | interior_local_patch | Boundary compatible: False; annulus compatible: False; global concavity closed: False. | uniform localization radius; proof that admissible first crossings remain inside the local patch |
| boundary_image_sign_hazard | open_sign_hazard | boundary_kernel_effect | Boundary compatible: False; annulus compatible: False; global concavity closed: False. | boundary-compatible signed kernel theorem; or boundary correction cancellation estimate; or domination bound uniform over admissible boundary layers |
| annular_shoulder_hazard | open_annular_hazard | annular_source_geometry | Boundary compatible: False; annulus compatible: False; global concavity closed: False. | annular exclusion theorem; annular signed-kernel dominance theorem; or cancellation estimate covering off-axis source mass |
| axis_regularity_compatibility | compatibility_unproved | axis_and_regular_boundary_interface | Boundary compatible: False; annulus compatible: False; global concavity closed: False. | axis-regular kernel theorem; boundary-condition compatibility proof; uniform statement over interior, axis-adjacent, and annular cases |
| missing_theorem | missing_boundary_compatible_kernel_sign_cancellation_theorem | required_theorem_interface | Boundary compatible: False; annulus compatible: False; global concavity closed: False. | BoundaryCompatibleKernelSignCancellationForPsi1Concavity; quantitative constants compatible with the monitored barrier route; formal promotion receipt that preserves no-gap assumptions |

## Validation

- No global proof is emitted.
- No Clay Navier-Stokes promotion is emitted.
- `GlobalConcavityOfPsi1` remains open unless the missing boundary-compatible theorem is supplied.
