# Systemic Crisis Signal Kernel

This module formalises a mechanism-first, triadic state machine for systemic-risk monitoring.

It does **not** encode a deterministic crash countdown, nor does it promote a single-stock drawdown into a sovereign-crisis claim. A narrative is deliberately separated from the observable mechanism state.

## Triadic observables

Each signal is represented by `Trit`:

- `neg`: absent, normalising, or relieving;
- `zer`: unresolved or insufficient evidence;
- `pos`: stressed or present.

The observable record contains:

- funding stress;
- liquidity impairment;
- cross-asset contagion;
- safe-haven failure;
- forced selling;
- policy backstop;
- mechanical exhaustion.

## Evidence gates

The state machine promotes only through explicit conjunctions:

- **latent fragility**: at least two of funding, liquidity, and contagion are positive;
- **trigger proximity**: funding stress, contagion, and safe-haven failure are positive;
- **active market-function break**: funding stress, liquidity impairment, and forced selling are positive;
- **mechanical recovery**: policy backstop and exhaustion are positive while funding and liquidity are no longer positive.

## Phases

The phases are:

1. `normalPhase`
2. `fragilityPhase`
3. `proximityPhase`
4. `activePhase`
5. `abatingPhase`

`stepPhase` supplies hysteresis. In particular, an active phase does not disappear merely because one observation weakens; it remains active until a mechanical-recovery receipt is present.

## Narrative boundary

`PublicNarrative` records claims such as a single-asset drawdown, deterministic timeline, or sovereign-crisis story. `classifyWithNarrative` ignores those claims and classifies only the plumbing observations. The theorem `narrativeIrrelevance` proves that changing the story cannot change the mechanism phase.

`noPlumbingNoCrisis` proves that, with funding, liquidity, and contagion all normal, the instantaneous classifier remains normal regardless of the remaining narrative-adjacent fields.

## Operational interpretation

The diagnostic posture is intentionally modest:

- normal / fragility: monitor;
- proximity: reduce risk;
- active: preserve liquidity;
- abating: re-engage cautiously.

These are formal control labels, not investment advice, price forecasts, or a claim that a sovereign crisis follows from an equity drawdown.
