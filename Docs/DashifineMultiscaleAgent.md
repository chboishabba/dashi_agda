# Dashifine multiscale control contract

This tranche formalises the finite control core for composing several
`direction × actionability` cells into a memoryful short-horizon actuator.  It
is deliberately a typed control bridge, not a claim that a market, confidence
score, or real interval is literally a 3-adic number.

## State split

The formal carrier separates three different kinds of state.

1. **Direction evidence** is a pre-collapse pair of sell/buy support bits.
   Both bits may be present.  Conflict is observable and collapses to the
   neutral trit rather than being resolved by an arbitrary vote.
2. **Actionability** is unsigned.  The module uses the finite control-relevant
   quotient `low < middle < high`; an abstract `ActionabilityValuation` maps a
   raw evidence carrier into those bands and requires refinement monotonicity.
3. **Control state** is `HOLD | BUY | SELL` and is memoryful.

This places direction and actionability in the 3→6 evidence/control field.
The final supervisor closes that field into a Stage-9 actuator state.

## Exact hysteresis graph

The checked transition function is:

- `low`: exit to `HOLD` from every prior state;
- `middle`: preserve the prior state;
- `high + sell`: enter or flip to `SELL`;
- `high + buy`: enter or flip to `BUY`;
- `high + neutral/conflict`: preserve the prior state.

Consequently, the same instantaneous observation can yield different outputs
from different prior states.  Hysteresis is therefore an additional temporal
state dimension, not a synonym for `HOLD`.

## Vertical order planes

The actionability quotient has the monotone P/Q/N encoding:

- `001 = low`
- `011 = middle`
- `111 = high`

The planes are cumulative threshold masks, not GF(3) arithmetic digits.  They
are intended for classify/mask/route control kernels.  The module proves the
encode/decode round trip and exposes pointwise P, Q, and N mask projections.

## Multiscale composition

`ScaleCell` combines one direction-evidence object with one actionability
band.  Pairwise composition uses:

- a conservative actionability bottleneck (`minBand`);
- neutral-as-absence direction fusion;
- opposing nonzero directions returning unresolved neutral.

Only after composition does `closeCell` apply the hysteresis supervisor.
Canonical witnesses show:

- aligned high-actionability scales enter `BUY`;
- a middle-actionability scale prevents entry from `HOLD`;
- opposed high-actionability scales remain unresolved;
- middle-band observations preserve an existing position.

## Files

- `DASHI/Control/DashifineMultiscaleAgent.agda`
- `DASHI/Control/DashifineMultiscaleAgentTests.agda`

The tranche is focused and fail-closed.  It does not assert profitability,
market validity, calibration of any concrete valuation, or a theorem that
continuous actionability is itself p-adic.  Those require separate empirical
and analytic bridges.
