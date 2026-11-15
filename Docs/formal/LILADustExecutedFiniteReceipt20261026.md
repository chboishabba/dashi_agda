# Executed finite LILA-style Dust update (26 October 2026)

## Scope and attribution
First-party toy instance consuming the activation-credit, population-centering, forward-only probe and outer-product structure of Q Labs Dust, not an original Dust result or a GPU/transformer reproduction. Upstream mathematical and source owner: `DASHI.Reasoning.DustNoiseAlgorithmExact`; LILA semantic action source owners #1094/#1095. The code lives at `scripts/lila_dust_forward_exact_20261026.py`. Local stdlib Python execution completed with assertions passing.

## Literal finite task
4 assigned paired tokens: semantic sign `s ∈ {-1,+1}`, nuisance `n ∈ {-1,+1}`, target `s`, parameter vector `w=(w_s,w_n)`. Scalar activation `h=w_s s+w_n n`; token loss `(h-s)^2/2`. For each token, enumerate all 16 sign patterns of activation perturbations `a ∈ {-1,+1}^4` with scale `σ=1/8`; center the per-token losses over all draws; use identity causal-future weighting; recover activation credit `g_t=-(1/(Kσ)) Σ_k (meanLoss_t-loss_{k,t}) a_{k,t}`. Aggregate the outer-product update `∇̂_j = (1/4)Σ_t g_t x_{t,j}`; set `w'=w-(1/8)∇̂`.

**Exact local result:** at `w=(0,0)`, token activation credits `[+1,+1,-1,-1]`, aggregate direction `(-1,0)`, next weights `(1/8,0)`. Training loss `1/2 → 49/128`. Test tokens have nuisance `n∈{-2,+2}`, values not in training; their loss is also `1/2 → 49/128`. Invariance to nuisance sign is exact because trained `w_n=0`. These are exact rational identities, not sampled empirical success.

This deliberately implements **diagonal immediate rewards**, a restricted and simpler instance of source Dust with no future-token credit, attention-specific surrogate or cached logits. It does perform actual population-centred forward-only credit and parameter update rather than only asserting an interface.

## Boundaries and next concrete gap
The test examples are disjoint in nuisance coordinate, but drawn from the **same stipulated deterministic semantic-label rule**. Thus 'held-out' here means a fixed synthetic nuisance shift, not independent scientific generalisation. Exhaustive probes cost 16×4 token-loss evaluations, so no speedup or resource-efficiency claim follows.

Next owner-specific implementables: connect the actual `GeometricReasoningSemanticIntervention` / LILA paired-correctness objective to a trainable finite parameter chart; implement non-diagonal Dust temporal credit and compare to vanilla zeroth-order, backprop and Walsh probes at identical probe budgets and held-out target accuracy; collect exact source-revision and full-search cost. No new generic observer-refinement proof: existing `ObserverRefinementLatticeExact` suffices.

No CI or Agda kernel checks requested.
