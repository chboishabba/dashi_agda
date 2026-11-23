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
latent fragility    ↦ fragility
trigger proximity   ↦ proximity
active dysfunction  ↦ active
stabilization       ↦ abating
unresolved          ↦ no mechanism phase
The unresolved case is deliberately partial: insufficient evidence is not silently classified as normal.
### Axis projection
Funding, liquidity, correlation/contagion, Treasury functioning, and credit transmission project directly into mechanism axes. Narrative instability, execution churn, technology concentration, capex revisions, hardware resale, and power/cooling remain candidate explanatory axes until a separate transmission receipt connects them to plumbing evidence.
Thus an AI-capex fixture may define a coherent candidate scenario without itself proving Treasury dysfunction or sovereign transmission.
### BAD-window geometry
`AdverseInterarrivalWindow` remains temporal geometry for replay, persistence, and hazard studies. `WindowBridgeReceipt` requires replay closure, calendar coverage, no causal promotion, and no execution promotion. Greece-style alignment therefore remains post-hoc replay evidence unless separately validated.
### Posture separation
The crosswalk preserves:
observation → classification → capital posture → execution
Mechanism monitoring depends on phase and compression fracture. Capital posture remains a separately governed scenario-layer output. Neither creates production-trading authority; an adverse state is not an automatic short signal, and arbitrary sign inversion remains rejected.
## Promotion and peak boundaries
`promotionLevel` distinguishes unsupported, diagnostic, observed-mechanism, and validated-model claims. Gartner-style expectation cycles may inform a technology prior but cannot establish plumbing transmission.
`peakMechanicsObserved` means the forced-selling mechanism is abating after funding/liquidity and deep residual structure normalise. It does not claim a final price bottom.
## Verification
The focused Agda 2.9 lane checks the kernel, quotient/MDL bridge, scenario crosswalk, exact witness modules, and aggregate. Witnesses cover carrier round trips, partial phase mapping, unresolved-state handling, candidate-axis non-promotion, execution governance, compression fracture, MDL promotion boundaries, trigger/cascade separation, Treasury/sovereign separation, expectation-cycle non-promotion, and mechanical-abatement versus price-bottom separation.
This family formalises a mechanism-first, triadic state machine for systemic-risk monitoring and connects it to the repository's existing quotient-residual and MDL/action formalism.
It does **not** encode a deterministic crash countdown, nor does it promote a single-stock drawdown, technology hype cycle, or valuation story into a sovereign-crisis claim. Narratives are deliberately separated from the observable mechanism state.
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
deep activation
AND side-information growth
AND quotient failure.
This captures the earlier Economic Compression Stability idea: a regime becomes structurally concerning when surprise migrates into deeper triadic scales while the selected quotient requires increasing side information and ceases to collapse within-class variation.
The residual score is diagnostic. It is not called a Lyapunov function. Promotion to a validated model requires a separate `ModelSelectionReceipt` recording deterministic decode, train/test separation, out-of-sample validation, complete side-information accounting, MDL improvement, and comparison against competing models.
`TransmissionChain` separates:
→ sovereign-funding stress.
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
`SystemicCrisisCompressionBridge` adds a residual-depth profile:
- shallow, middle, and deep activation;
A compression fracture requires deep activation, side-information growth, and quotient failure together. This formalises the Economic Compression Stability idea: a selected chart/model becomes structurally suspect when surprise migrates into deeper triadic scales while its quotient needs increasing side information and stops collapsing variation.
Residual energy remains diagnostic, not a Lyapunov function. Promotion requires a separate `ModelSelectionReceipt` covering deterministic decode, train/test separation, out-of-sample validation, side-information accounting, MDL improvement, and comparison against competitors.
`SystemicCrisisScenarioCrosswalk` integrates PR #157's scenario vocabulary without collapsing distinct layers.
### Exact carrier reuse
The module proves an exact round-trip isomorphism between `SSPTritCarrier.SSPTrit` and `DASHI.Algebra.Trit.Trit`. This permits shared signed-triadic structure while preserving the existing rule that adverse/favorable structural sign is not price direction.
### Partial phase map
The phase correspondence is:
The final case is deliberately partial: insufficient evidence is not silently mapped to `normalPhase`.
Funding, liquidity, correlation/contagion, Treasury functioning, and credit transmission have direct mechanism projections. Narrative instability, execution churn, technology concentration, capex revisions, hardware resale, and power/cooling constraints remain candidate explanatory axes until a separate transmission receipt links them to funding, liquidity, contagion, or forced selling.
Thus the AI-capex fixture can identify a coherent candidate scenario, but it cannot by itself establish Treasury dysfunction or sovereign transmission.
### BAD-window temporal geometry
`AdverseInterarrivalWindow` is retained as temporal geometry: the interval between adverse onsets may support replay, persistence, and hazard studies. A `WindowBridgeReceipt` still requires replay closure, calendar coverage, no causal promotion, and no execution promotion. Post-hoc Greece-style alignment remains evidence for replay alignment only.
### Posture and execution separation
`monitoringPosture` is derived from mechanism phase and compression fracture; `CapitalPosture` remains the separately governed scenario-layer output. Neither creates production-trading authority. Adverse state is not an automatic short signal, and arbitrary sign inversion remains rejected.
`promotionLevel` distinguishes unsupported, diagnostic, observed-mechanism, and validated-model claims. An observed active mechanism therefore need not pretend that its forecasting model has passed MDL and out-of-sample gates.
## Gartner-style expectation boundary
`TechnologyExpectationObservation` records an expectation/adoption cycle separately from plumbing. `expectationCycleCannotPromotePlumbing` proves that expectation-cycle classification alone cannot establish funding, liquidity, liquidation, or sovereign transmission. Such frameworks may inform a technology-expectation prior, but are not market-plumbing models.
## Peak boundary
`peakMechanicsObserved` requires mechanical recovery plus normalisation of deep activation, side-information growth, and quotient failure. This means the forced-selling mechanism is abating; it does not claim the final price bottom.
The focused Agda 2.9 lane checks the kernel, quotient/MDL bridge, PR #157 crosswalk, exact witness modules, and aggregate. Witnesses cover carrier round trips, partial phase mapping, compression fracture, MDL promotion boundaries, trigger/cascade separation, Treasury/sovereign separation, candidate-axis non-promotion, unresolved-state handling, expectation-cycle non-promotion, execution governance, and mechanical-abatement versus price-bottom separation.
