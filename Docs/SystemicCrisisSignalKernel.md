# Systemic Crisis Signal Kernel

This family formalises a mechanism-first, triadic state machine for systemic-risk monitoring and connects it to the repository's existing quotient-residual and MDL/action formalism.

It does **not** encode a deterministic crash countdown, nor does it promote a single-stock drawdown, technology hype cycle, or valuation story into a sovereign-crisis claim. Narratives are deliberately separated from the observable mechanism state.

## Existing DASHI foundations reused

The implementation is an application bridge rather than a parallel algebra. It references:

- `DASHI.Algebra.Trit` for the primitive signed carrier `{-1,0,+1}`;
- `DASHI.Core.MinimalKernelAlgebra` for symmetry actions, exact support/sign factorisation, quotient compatibility, RG/coarse-graining squares, and the rule that MDL/action descent is an additional proved law rather than an automatic consequence;
- `DASHI.Cognition.QuotientResidualDynamics` for the repository's general quotient-residual theorem surface.

The economics layer therefore observes whether a selected chart, quotient, or predictive model remains compressive; it does not reinterpret binary masks or scalar scores as the primitive ontology.

## Triadic plumbing observables

Each signal is represented by `Trit`:

- `neg`: absent, normalising, or relieving;
- `zer`: unresolved or insufficient evidence;
- `pos`: stressed or present.

`CrisisObservation` contains funding stress, liquidity impairment, cross-asset contagion, safe-haven failure, forced selling, policy backstop, and mechanical exhaustion.

## Evidence gates and hysteretic phases

The state machine promotes only through explicit conjunctions:

- **latent fragility**: at least two of funding, liquidity, and contagion are positive;
- **trigger proximity**: funding stress, contagion, and safe-haven failure are positive;
- **active market-function break**: funding stress, liquidity impairment, and forced selling are positive;
- **mechanical recovery**: policy backstop and exhaustion are positive while funding and liquidity are no longer positive.

The phases are `normalPhase`, `fragilityPhase`, `proximityPhase`, `activePhase`, and `abatingPhase`. `stepPhase` supplies hysteresis: active dysfunction persists until a mechanical-recovery receipt is present.

## Compression Stability Index surface

`SystemicCrisisCompressionBridge` adds a signed triadic residual-depth profile:

- shallow, middle, and deep residual activation;
- side-information growth;
- quotient failure;
- model mismatch.

A **compression fracture** requires the conjunction

```text
deep activation
AND side-information growth
AND quotient failure.
```

This captures the earlier Economic Compression Stability idea: a regime becomes structurally concerning when surprise migrates into deeper triadic scales while the selected quotient requires increasing side information and ceases to collapse within-class variation.

The residual score is diagnostic. It is not called a Lyapunov function. Promotion to a validated model requires a separate `ModelSelectionReceipt` recording deterministic decode, train/test separation, out-of-sample validation, complete side-information accounting, MDL improvement, and comparison against competing models.

## Explicit transmission chain

`TransmissionChain` separates:

```text
trigger asset shock
→ balance-sheet loss
→ margin tightening
→ synchronous deleveraging
→ Treasury liquidation
→ market-function failure
→ sovereign-funding stress.
```

`triggerAloneDoesNotActivateCascade` proves that an isolated trigger value cannot activate the downstream cascade. `sovereignTransmissionObserved` additionally requires the final sovereign-funding link; active Treasury-market dysfunction therefore does not silently promote itself into a sovereign crisis.

## Promotion ladder

`promotionLevel` distinguishes:

1. `unsupportedLevel`;
2. `diagnosticLevel`;
3. `observedMechanismLevel`;
4. `validatedModelLevel`.

An active observed mechanism can be represented without pretending that its forecasting model has passed MDL and out-of-sample gates. This follows the repository's receipt and non-promotion conventions.

## Gartner-style expectation cycles

`TechnologyExpectationObservation` includes an expectation/adoption cycle and valuation/adoption stress. It is intentionally a separate observation layer. `expectationCycleCannotPromotePlumbing` proves that an expectation-cycle classification alone cannot establish funding, liquidity, liquidation, or sovereign transmission.

Thus a Gartner-style framework may contribute a technology-expectation prior, but it is not a market-plumbing model.

## Peak detection boundary

`peakMechanicsObserved` requires mechanical recovery plus normalisation of deep residual activation, side-information growth, and quotient failure. This means **the forced-selling mechanism is abating**. It does not mean that price has reached its final bottom; `priceBottomClaimed` is definitionally false.

## Operational interpretation

The combined `monitoringPosture` distinguishes ordinary monitoring, model review, proximity alert, active dysfunction, and mechanical abatement. These are formal control labels, not investment advice, price forecasts, or a claim that a sovereign crisis follows from an equity drawdown.

## Focused verification

The focused workflow checks:

- `SystemicCrisisSignalKernel.agda`;
- `SystemicCrisisSignalKernelTests.agda`;
- `SystemicCrisisCompressionBridge.agda`;
- `SystemicCrisisCompressionBridgeTests.agda`;
- `SystemicCrisisSignalAll.agda`.

The exact witnesses cover normal, fragility, proximity, active, and abating paths; compression fracture; MDL promotion boundaries; separation of Treasury dysfunction from sovereign transmission; expectation-cycle non-promotion; and the distinction between mechanical peak and price bottom.
