# Tech/Systemic Stress × Quotient-MDL Bridge

This note documents the bridge between the candidate-only technology/systemic
scenario surface and the mechanism-first systemic-crisis compression kernel.

The bridge is implemented in:

- `DASHI.Interop.TechSystemicStressCompressionBridge`
- `DASHI.Interop.TechSystemicStressCompressionBridgeRegression`

It cross-references rather than replaces:

- `DASHI.Promotion.TechSystemicStressScenarioBoundary`
- `DASHI.Economics.SystemicCrisisSignalKernel`
- `DASHI.Economics.SystemicCrisisCompressionBridge`
- `DASHI.Foundations.SSPTritCarrier`
- `DASHI.Core.MinimalKernelAlgebra`
- `DASHI.Cognition.QuotientResidualDynamics`

## Why a bridge is required

The two merged tranches answer different questions.

The technology/systemic scenario boundary asks:

> Where is an adverse structural regime concentrated, and what observation,
> attribution, posture, and execution boundaries apply?

The systemic-crisis compression kernel asks:

> Is a receipted market-plumbing mechanism active, is the selected quotient or
> model ceasing to compress the observations, and has an MDL model survived
> out-of-sample and competing-model checks?

These are related but not interchangeable.

A Greece-style news match is a replay attribution fixture. An AI-capex stress
classification is a concentration hypothesis. Neither is, by itself, evidence
of margin tightening, synchronous deleveraging, Treasury liquidation, market
function failure, or sovereign funding stress.

Conversely, a compression fracture is not an attribution. It says that deep
residual activation, side-information growth, and quotient failure coincide. It
does not say whether the source is AI capex, sovereign stress, a policy shock,
or model misspecification.

## Shared signed carrier

The scenario layer uses `SSPTrit`; the mechanism kernel uses the primitive
`DASHI.Algebra.Trit`. The bridge uses the existing exact map:

```text
SSP.sspNegOne -> neg
SSP.sspZero   -> zer
SSP.sspPosOne -> pos
```

The meanings remain layer-specific:

- scenario trit: adverse / unresolved / favorable structural condition;
- mechanism trit: absent-normalising / unresolved / stressed-present.

The map aligns the carrier, not every interpretation. In particular, `-1` is
not a price short instruction.

## Partial phase alignment

The bridge records:

```text
latent fragility   -> fragility
trigger proximity  -> proximity
active dysfunction -> active
stabilization      -> abating
unresolved         -> no mechanism-phase coercion
```

The unresolved scenario phase is deliberately not coerced to normal or active
crisis. This prevents missing evidence from becoming a positive claim.

## Three independent layers

The joined status keeps three pieces separate:

1. **Scenario attribution** — where stress appears concentrated.
2. **Compression regime** — whether the quotient/model remains compressive,
   enters watch, or fractures.
3. **Promotion level** — unsupported, diagnostic, observed mechanism, or
   validated model.

The combined status can therefore distinguish:

- attribution only;
- structural watch;
- compression fracture without mechanism proof;
- observed mechanism;
- validated mechanism;
- mechanical abatement.

## BAD days and Greece-style replay

An adverse-onset or BAD window is an event geometry carrier. A news match inside
that window can support post-hoc interpretation, but it cannot independently
promote a market-plumbing mechanism.

The bridge contains exact witnesses that both the canonical Greece-style replay
fixture and the canonical AI-capex attribution fixture remain at
`unsupportedLevel` when converted into a scenario-only systemic receipt.

This is the intended reading of the earlier experiment:

```text
bot emits BAD window
    -> inspect contemporaneous news
    -> record candidate alignment
    -> separately test funding/liquidity/transmission observables
    -> separately test quotient-residual and MDL receipts
```

The news event does not retroactively become the detector input unless a
separate, time-correct, receipted model explicitly includes it.

## Validated cross-layer gate

A validated joined claim requires all of:

- scenario source binding;
- mechanism source binding;
- aligned clocks and windows;
- no lookahead leakage;
- complete side-information accounting;
- attribution formed independently of the evaluated outcome;
- scenario attribution not substituted for transmission evidence;
- signed structural regime not substituted for price direction;
- closed MDL/model-selection gate;
- observed mechanism evidence.

This is intentionally stronger than any individual BAD day, headline,
single-stock drawdown, expectation-cycle position, compression fracture, or
active-phase classification.

## Posture cross-pollination

The bridge relates, but does not identify, the two posture surfaces:

```text
defensive     + preserve liquidity -> coherent preservation
defensive     + reduce risk         -> coherent reduction
observational + monitor             -> coherent monitoring
opportunity   + cautious reengage   -> coherent re-engagement
other combinations                  -> review required
```

This relation remains governance metadata. It is not production execution
authority or financial advice.

## Peak semantics

The scenario `stabilizationPhase` and the mechanism's mechanical-abatement
surface may corroborate one another. Neither proves the final price bottom.
The bridge retains an explicit `finalPriceBottomClaimed = false` witness.

## Empirical implementation sequence

A runtime implementation should emit separate receipts for:

1. signed CA/BAD-window and multi-scale statistics;
2. scenario-axis observations, including technology concentration, capex,
   secondary hardware, power/cooling, funding, credit, Treasury, and liquidity;
3. the explicit transmission ladder;
4. quotient-residual depth and side-information growth;
5. deterministic decode and total coded length, including model/context data;
6. train/test separation, holdout replay, and competing-model comparison;
7. joined clock, source, leakage, and attribution-independence checks.

Only the final joined receipt should be eligible for the strongest candidate
status. The current formal surface remains non-predictive, candidate-only, and
fail-closed.
