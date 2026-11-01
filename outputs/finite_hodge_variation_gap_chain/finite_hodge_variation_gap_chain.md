# finite_hodge_variation_gap_chain

- generated_at: `2026-06-08T00:00:00+10:00`
- chain_rows: `12`
- support_modules: `5`
- terminal_promotion: `False`

## Gap chain

| order | stage | status | current gap | repo supports |
| ---: | --- | --- | --- | --- |
| 1 | finite_cochain_complex | supported_target_with_gap | Finite-depth BT carrier and incidence/coboundary package is named as a target, not fully promoted as a metric complex. | BTFiniteHodgeStarObligation |
| 2 | metric_hodge_star | blocked | Weighted primal/dual cells and metric Hodge star construction remain explicit blockers. | BTFiniteHodgeStarObligation, BTFiniteHodgeEffectiveActionTheoremBoundary |
| 3 | star_square_sign_law | blocked | The BT metric ** law is a named obligation and is not promoted. | BTFiniteHodgeStarObligation |
| 4 | weighted_pairing | partially_supported_with_gap | Finite selected lower pairing is calculated, but BT weighted pairing promotion is still false. | BTFiniteHodgeStarObligation, HodgeVariationPairingDepth9, YMStrictSelectedHodgeVariationPairing, YMStrictHodgeVariationBlockerIndex |
| 5 | finite_integration_by_parts | partially_supported_with_gap | Strict selected finite IBP lower law is inhabited, while BT finite IBP promotion remains false. | BTFiniteHodgeStarObligation, HodgeVariationPairingDepth9, YMStrictSelectedHodgeVariationPairing, YMStrictHodgeVariationBlockerIndex |
| 6 | maxwell_equations | partially_supported_with_gap | Symbolic dF support exists; inhomogeneous d*F=J, source conservation dJ=0, calibration, and empirical authority remain blockers. | BTFiniteHodgeStarObligation, BTFiniteHodgeEffectiveActionTheoremBoundary |
| 7 | yang_mills_curvature | supported_target_with_gap | Finite gauge-field and effective-action targets are named; physical nonzero sourced YM promotion is not supplied. | BTFiniteHodgeEffectiveActionTheoremBoundary, YMStrictSelectedHodgeVariationPairing |
| 8 | yang_mills_euler_lagrange | partially_supported_with_gap | Selected finite variation/IBP calculation is present, but matter-current authority and real D_A^*F_A=J remain exact blockers. | BTFiniteHodgeEffectiveActionTheoremBoundary, YMStrictSelectedHodgeVariationPairing, YMStrictHodgeVariationBlockerIndex |
| 9 | finite_hamiltonian | blocked | Finite effective action sum is named, but a self-adjoint real-carrier YM Hamiltonian is listed as not supplied. | BTFiniteHodgeEffectiveActionTheoremBoundary, YMStrictHodgeVariationBlockerIndex |
| 10 | gauge_invariant_spectral_gap | open_gap | No promoted self-adjoint Hamiltonian or finite spectral-gap theorem is supplied by the named Hodge variation supports. | YMStrictHodgeVariationBlockerIndex |
| 11 | uniform_lower_bound | open_gap | Uniform lower-bound transfer is outside the named Hodge supports and remains unpromoted for this chain. | BTFiniteHodgeEffectiveActionTheoremBoundary |
| 12 | continuum_transfer | open_gap | Continuum mass-gap, Clay YM, and terminal promotion remain false in the named boundary receipts. | BTFiniteHodgeEffectiveActionTheoremBoundary, YMStrictHodgeVariationBlockerIndex |

## Continuum transfer status

The finite Hodge/YM stack is organized as a promoted-target chain with explicit blockers. The named support modules do not promote Maxwell, physical Yang-Mills, Clay Yang-Mills, continuum mass gap, or terminal unification; the current output preserves those gaps.
