# NS Sprint 133 Universal Strategy Classifier

- Contract: `ns_sprint133_universal_strategy_classifier`
- Row count: `6`
- Selected Clay-adjacent target: `axisymmetric NS with swirl`
- Selected next strategy: `S5`
- Universal candidate strategy: `S3`
- Full Clay NS solved: `false`
- Clay Navier-Stokes promoted: `false`
- Complete: `true`
- Exit code: `0`

## Rows

| Strategy | Name | Status | Gap | Next Calculation | Clay Progress |
| --- | --- | --- | --- | --- | --- |
| `S1` | A priori estimates | `exhausted_in_known_energy_enstrophy_class` | The enstrophy estimate dZ/dt <= -nu D + C Z^3 is sharp in the Ladyzhenskaya class, so energy-only improvement requires extra structure outside the standard estimate. | No route-specific calculation currently changes the sharp energy-enstrophy barrier; use only as a comparison baseline. | `approximately_0_percent` |
| `S2` | Critical space contraction | `circular_for_large_data` | Fujita-Kato and Koch-Tataru control small critical data, while the Escauriaza-Seregin-Sverak L3 blowup criterion says that a global L3 bound would already close the Clay problem. | Find an energy-derived bound in a Serrin-Ladyzhenskaya class or prove that the programme's structural quantities control a critical norm without smallness. | `approximately_0_percent_until_large_data_bound` |
| `S3` | Monotone quantity plus comparison | `most_promising_unexplored_universal_route` | A viable Q[u] must be finite for every smooth finite-energy datum, monotone along NS flow, and strong enough to bound BKM-critical vorticity; no such quantity is currently proved. | Differentiate a vorticity-correlation functional Q[u] with kernel K(x-y)|x-y|^{-alpha}, isolate vortex-stretching, transport, pressure-free cancellations, and viscous terms, then test whether stretching has a coercive negative sign. | `nonzero_only_if_monotonicity_and_bkm_control_close` |
| `S4` | Convexity and duality | `conceptual_no_concrete_large_data_route` | There is no known convex dual certificate or relaxation whose large-data free-space NS optimum yields global smoothness. | Formulate a concrete dual certificate candidate and check whether its defect is controlled by energy plus viscosity. | `approximately_0_percent_without_candidate_certificate` |
| `S5` | Structure theorem | `live_for_axisymmetric_with_swirl_not_full_clay` | Axisymmetric no-swirl regularity has structure theorems, but axisymmetric with swirl still needs large-Re beta>0 control, the beta=0 marginal case, and an exhaustion theorem inside the symmetry class. | Pivot to axisymmetric NS with swirl: close large-Re beta>0 via PDE-level comparison, analyze beta=0 large-scale shear, and prove axisymmetric-class exhaustion using the reduced swirl/vorticity system. | `positive_for_clay_subcase_zero_for_full_clay_promotion` |
| `S6` | Conditional reduction | `open_no_easier_energy_verifiable_criterion` | Known continuation criteria such as Serrin and BKM are not verified from energy alone; a new criterion must be both strictly weaker to verify and strong enough to continue smooth solutions. | Search for a criterion below Serrin/BKM whose hypothesis is controlled by energy, viscosity, and a programme structural quantity already emitted in Sprint 130-132 surfaces. | `approximately_0_percent_until_new_criterion` |

## Highest-Alpha Next Calculations

- `AxisymmetricWithSwirlLargeReBetaPositivePDEComparison`
- `AxisymmetricMarginalBetaZeroShearAnalysis`
- `AxisymmetricClassExhaustionTheorem`
- `VorticityCorrelationMonotonicityDerivative`
- `SerrinEnergyConditionalReductionSearch`
- `ConvexDualCertificateFeasibilityCheck`

## Control Card

- O: Worker 1 owns only the Sprint133 universal strategy classifier script and generated output directory.
- R: Encode six universal regularity proof strategies with required row fields and explicit Clay non-promotion flags.
- C: Deterministic Python emitter writes CSV rows, JSON rows, JSON summary, and Markdown report.
- S: Full Clay remains unsolved; route-specific Sprint 130-132 work most directly supports the axisymmetric-with-swirl subcase.
- L: Progress lattice: classify strategies -> select tractable Clay-adjacent target -> keep full Clay promotion false.
- P: Treat structure theorem for axisymmetric NS with swirl as the next significant finite-scope target; keep monotone quantity as the only plausible universal positive route.
- G: Promotion requires universal smooth finite-energy regularity; this artifact explicitly does not claim that.
- F: Remaining gap is a universal argument or a finite exhaustion inside a symmetry class, not another route-specific receipt.
