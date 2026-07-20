# Systemic Crisis Signal Kernel

This family formalises a mechanism-first, signed-triadic state machine for systemic-risk monitoring and connects it to the repository's existing quotient-residual, MDL/action, PNF trading-boundary, and empirical-basin formalism.

It does **not** encode a deterministic crash countdown, nor promote a single-stock drawdown, technology hype cycle, valuation story, BAD-window alignment, or scenario label into a sovereign-crisis claim.

## Existing DASHI foundations reused

The implementation is an application bridge rather than a parallel algebra. It imports:

- `DASHI.Algebra.Trit` for the primitive carrier `{-1,0,+1}`;
- `DASHI.Core.MinimalKernelAlgebra` for symmetry actions, exact support/sign factorisation, quotient compatibility, RG/coarse-graining squares, and the rule that MDL/action descent is an additional proved law;
- `DASHI.Cognition.QuotientResidualDynamics` for the general quotient-residual theorem surface;
- `DASHI.Foundations.SSPTritCarrier` for the PNF signed structural-regime carrier;
- `DASHI.Promotion.TechSystemicStressScenarioBoundary` for source-bound stress axes, empirical-basin links, adverse interarrival windows, scenario attribution, capital posture, and fail-closed execution governance.

## Plumbing state machine

`CrisisObservation` records funding stress, liquidity impairment, cross-asset contagion, safe-haven failure, forced selling, policy backstop, and mechanical exhaustion.

The gates are:

- latent fragility: at least two of funding, liquidity, and contagion are positive;
- trigger proximity: funding stress, contagion, and safe-haven failure are positive;
- active dysfunction: funding stress, liquidity impairment, and forced selling are positive;
- mechanical recovery: policy backstop and exhaustion are positive while funding and liquidity are no longer positive.

`stepPhase` supplies hysteresis across `normalPhase`, `fragilityPhase`, `proximityPhase`, `activePhase`, and `abatingPhase`.

## Compression Stability bridge

`SystemicCrisisCompressionBridge` adds a residual-depth profile:

- shallow, middle, and deep activation;
- side-information growth;
- quotient failure;
- model mismatch.

A compression fracture requires deep activation, side-information growth, and quotient failure together. This formalises the Economic Compression Stability idea: a selected chart/model becomes structurally suspect when surprise migrates into deeper triadic scales while its quotient needs increasing side information and stops collapsing variation.

Residual energy remains diagnostic, not a Lyapunov function. Promotion requires a separate `ModelSelectionReceipt` covering deterministic decode, train/test separation, out-of-sample validation, side-information accounting, MDL improvement, and comparison against competitors.

## Explicit transmission chain

`TransmissionChain` separates:

```text
trigger asset shock
→ balance-sheet loss
→ margin tightening
→ synchronous deleveraging
→ Treasury liquidation
→ market-function failure
→ sovereign-funding stress
```

A trigger alone cannot activate the cascade. Sovereign transmission additionally requires the final sovereign-funding link; Treasury dysfunction does not silently promote itself into a sovereign crisis.

## Crosswalk with the tech/systemic scenario tranche

`SystemicCrisisScenarioCrosswalk` integrates PR #157's scenario vocabulary without collapsing distinct layers.

### Exact carrier reuse

The module proves an exact round-trip isomorphism between `SSPTritCarrier.SSPTrit` and `DASHI.Algebra.Trit.Trit`. This permits shared signed-triadic structure while preserving the existing rule that adverse/favorable structural sign is not price direction.

### Partial phase map

The phase correspondence is:

```text
latent fragility    ↦ fragility
trigger proximity   ↦ proximity
active dysfunction  ↦ active
stabilization       ↦ abating
unresolved          ↦ no mechanism phase
```

The final case is deliberately partial: insufficient evidence is not silently mapped to `normalPhase`.

### Axis projection

Funding, liquidity, correlation/contagion, Treasury functioning, and credit transmission have direct mechanism projections. Narrative instability, execution churn, technology concentration, capex revisions, hardware resale, and power/cooling constraints remain candidate explanatory axes until a separate transmission receipt links them to funding, liquidity, contagion, or forced selling.

Thus the AI-capex fixture can identify a coherent candidate scenario, but it cannot by itself establish Treasury dysfunction or sovereign transmission.

### BAD-window temporal geometry

`AdverseInterarrivalWindow` is retained as temporal geometry: the interval between adverse onsets may support replay, persistence, and hazard studies. A `WindowBridgeReceipt` still requires replay closure, calendar coverage, no causal promotion, and no execution promotion. Post-hoc Greece-style alignment remains evidence for replay alignment only.

### Posture and execution separation

The crosswalk preserves:

```text
observation → classification → capital posture → execution
```

`monitoringPosture` is derived from mechanism phase and compression fracture; `CapitalPosture` remains the separately governed scenario-layer output. Neither creates production-trading authority. Adverse state is not an automatic short signal, and arbitrary sign inversion remains rejected.

## Promotion ladder

`promotionLevel` distinguishes unsupported, diagnostic, observed-mechanism, and validated-model claims. An observed active mechanism therefore need not pretend that its forecasting model has passed MDL and out-of-sample gates.

## Gartner-style expectation boundary

`TechnologyExpectationObservation` records an expectation/adoption cycle separately from plumbing. `expectationCycleCannotPromotePlumbing` proves that expectation-cycle classification alone cannot establish funding, liquidity, liquidation, or sovereign transmission. Such frameworks may inform a technology-expectation prior, but are not market-plumbing models.

## Peak boundary

`peakMechanicsObserved` requires mechanical recovery plus normalisation of deep activation, side-information growth, and quotient failure. This means the forced-selling mechanism is abating; it does not claim the final price bottom.

## Verification

The focused Agda 2.9 lane checks the kernel, quotient/MDL bridge, PR #157 crosswalk, exact witness modules, and aggregate. Witnesses cover carrier round trips, partial phase mapping, compression fracture, MDL promotion boundaries, trigger/cascade separation, Treasury/sovereign separation, candidate-axis non-promotion, unresolved-state handling, expectation-cycle non-promotion, execution governance, and mechanical-abatement versus price-bottom separation.
