# DASHI Markov Compatibility

Declared surface level: `compatibility`.

This note records Markov machinery as a projection of DASHI state, not as a
foundation for DASHI. A lane becomes Markov only after its current typed joined
state is sufficient for the next admissible update.

The concrete Agda surfaces are:

- `DASHI.Core.DashiMarkov`: lightweight generic transition/sufficiency records.
- `DASHI.Process.DASHIMarkovCompatibility`: process-facing DASHI state,
  promotion status, multiscale join, and Markov compatibility projection.

## Native State

The relevant state is not a raw observation window. It is the current typed
slice:

```text
Sigma_t = (carrier_t, residual_t, obligations_t, authorities_t, boundary_t, promotion_t)
```

- `carrier_t`: the current formal carrier or lane slice.
- `residual_t`: pressure, residual, mismatch, or diagnostic state.
- `obligations_t`: open typed proof, provider, or validation obligations.
- `authorities_t`: accepted receipts, authority tokens, and provenance already
  admitted.
- `boundary_t`: the current admissibility boundary and non-promotion status.
- `promotion_t`: the lane's current promotion or non-promotion state.

## Structural Markov Condition

DASHI-Markov means:

```text
Sigma_{t+1} = T Sigma_t x_{t+1}
```

for a typed transition `T`, and raw history is relevant only through the
summary `Sigma_t`.

Equivalently, in optional probabilistic form:

```text
Pr(Sigma_{t+1}, y_{t+1} | H_t)
  = Pr(Sigma_{t+1}, y_{t+1} | Sigma_t)
```

The probability notation is optional. The core claim is sufficiency of the
typed joined state for future admissible updates.

## Compatibility

Classical Markov tools embed as special cases:

- Markov chain: finite/discrete `Sigma`, stochastic transition.
- HMM: typed carrier hidden, observations emitted as diagnostics.
- MDP: actions are admissible interventions; reward is replaced or extended by
  pressure, coherence, or promotion criteria.

For multiscale lanes, the state may first be joined across horizons:

```text
Sigma_t = join (lambda h -> Sigma_t[h])
```

The Markov-like claim is then about sufficiency of the joined state, not about
any single local horizon.

## Boundary

This surface constructs no stochastic model, stationarity theorem, global
latent oracle, or promotion receipt. It only names the structural condition
under which a finished DASHI lane can be viewed through Markov language.
