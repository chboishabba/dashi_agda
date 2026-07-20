# Systemic Crisis Signal Kernel

This family formalises a mechanism-first, signed-triadic state machine for systemic-risk monitoring and connects it to the repository's existing quotient-residual and MDL/action formalism.

It does **not** encode a deterministic crash countdown, nor promote a single-stock drawdown, technology hype cycle, or valuation story into a sovereign-crisis claim.

## Existing DASHI foundations reused

The implementation is an application bridge rather than a parallel algebra. It imports:

- `DASHI.Algebra.Trit` for the primitive carrier `{-1,0,+1}`;
- `DASHI.Core.MinimalKernelAlgebra` for symmetry actions, exact support/sign factorisation, quotient compatibility, RG/coarse-graining squares, and the rule that MDL/action descent is an additional proved law;
- `DASHI.Cognition.QuotientResidualDynamics` for the general quotient-residual theorem surface.

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

## Promotion ladder

`promotionLevel` distinguishes unsupported, diagnostic, observed-mechanism, and validated-model claims. An observed active mechanism therefore need not pretend that its forecasting model has passed MDL and out-of-sample gates.

## Gartner-style expectation boundary

`TechnologyExpectationObservation` records an expectation/adoption cycle separately from plumbing. `expectationCycleCannotPromotePlumbing` proves that expectation-cycle classification alone cannot establish funding, liquidity, liquidation, or sovereign transmission. Such frameworks may inform a technology-expectation prior, but are not market-plumbing models.

## Peak boundary

`peakMechanicsObserved` requires mechanical recovery plus normalisation of deep activation, side-information growth, and quotient failure. This means the forced-selling mechanism is abating; it does not claim the final price bottom.

## Verification

The focused Agda 2.9 lane checks the kernel, bridge, exact witness modules, and aggregate. Witnesses cover compression fracture, MDL promotion boundaries, trigger/cascade separation, Treasury/sovereign separation, expectation-cycle non-promotion, and mechanical-abatement versus price-bottom separation.
