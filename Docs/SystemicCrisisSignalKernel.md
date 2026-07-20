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

`SystemicCrisisCompressionBridge` adds a residual-depth profile containing shallow, middle, and deep activation, side-information growth, quotient failure, and model mismatch.

A compression fracture requires deep activation, side-information growth, and quotient failure together. Residual energy remains diagnostic, not a Lyapunov function. Promotion requires a separate `ModelSelectionReceipt` covering deterministic decode, train/test separation, out-of-sample validation, side-information accounting, MDL improvement, and comparison against competitors.

## Explicit transmission chain

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

`SystemicCrisisScenarioCrosswalk` integrates the PR #157 scenario vocabulary without collapsing distinct layers.

### Carrier correspondence

The module proves exact round trips between `SSPTritCarrier.SSPTrit` and `DASHI.Algebra.Trit.Trit`. Shared signed-triadic structure therefore does not require a duplicated carrier, while adverse/favorable structural sign remains distinct from price direction.

### Partial phase correspondence

```text
latent fragility    ↦ fragility
trigger proximity   ↦ proximity
active dysfunction  ↦ active
stabilization       ↦ abating
unresolved          ↦ no mechanism phase
```

The unresolved case is deliberately partial: insufficient evidence is not silently classified as normal.

### Axis projection

Funding, liquidity, correlation/contagion, Treasury functioning, and credit transmission project directly into mechanism axes. Narrative instability, execution churn, technology concentration, capex revisions, hardware resale, and power/cooling remain candidate explanatory axes until a separate transmission receipt connects them to plumbing evidence.

Thus an AI-capex fixture may define a coherent candidate scenario without itself proving Treasury dysfunction or sovereign transmission.

### BAD-window geometry

`AdverseInterarrivalWindow` remains temporal geometry for replay, persistence, and hazard studies. `WindowBridgeReceipt` requires replay closure, calendar coverage, no causal promotion, and no execution promotion. Greece-style alignment therefore remains post-hoc replay evidence unless separately validated.

### Posture separation

The crosswalk preserves:

```text
observation → classification → capital posture → execution
```

Mechanism monitoring depends on phase and compression fracture. Capital posture remains a separately governed scenario-layer output. Neither creates production-trading authority; an adverse state is not an automatic short signal, and arbitrary sign inversion remains rejected.

## Promotion and peak boundaries

`promotionLevel` distinguishes unsupported, diagnostic, observed-mechanism, and validated-model claims. Gartner-style expectation cycles may inform a technology prior but cannot establish plumbing transmission.

`peakMechanicsObserved` means the forced-selling mechanism is abating after funding/liquidity and deep residual structure normalise. It does not claim a final price bottom.

## Verification

The focused Agda 2.9 lane checks the kernel, quotient/MDL bridge, scenario crosswalk, exact witness modules, and aggregate. Witnesses cover carrier round trips, partial phase mapping, unresolved-state handling, candidate-axis non-promotion, execution governance, compression fracture, MDL promotion boundaries, trigger/cascade separation, Treasury/sovereign separation, expectation-cycle non-promotion, and mechanical-abatement versus price-bottom separation.
