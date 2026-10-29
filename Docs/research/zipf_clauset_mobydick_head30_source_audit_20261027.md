# Source-anchored rank-head severe test: Moby-Dick / Newman / Clauset

**Date:** 27 October 2026. **Original 27 Zipf-family topic scope unchanged.**
The experiment responds to the unpaid *real data root* phase without
inventing a full-text corpus or asserting a power law.

## Actual public data source and ancestry

- **Original work:** Herman Melville, *Moby-Dick* (1851).
- **Rank-frequency reference and empirical dataset catalogue:** Aaron Clauset,
  Cosma R. Shalizi and M. E. J. Newman, *Power-law distributions in empirical
  data*, SIAM Review 51(4), 661–703 (2009),
  https://doi.org/10.1137/070710111 .
- **Original public frequency series**, linked as entry #1 of the above
  researchers' source catalogue: https://aaronclauset.github.io/powerlaws/data/words.txt .
- **Dataset catalogue:** https://aaronclauset.github.io/powerlaws/data.htm .
  That catalogue cites M. E. J. Newman (2005), *Power laws, Pareto
  distributions and Zipf's law*. This citation does **not** by itself
  prove who tokenized this particular file. Keep Melville textual
  authorship, Newman bibliographic/statistical root and Clauset et al.
  catalogue/dataset publication separate.

## Executed bounded observation

Only the FIRST 30 integer rank counts from the displayed original data page
were manually transcribed; these sum to **75,648** tokens *across those 30
types only*, and begin `14086, 6414, 6260, 4573, 4484`. They are not
the first 30 word types in the original novel's chronological token order.
The dataset has many additional ranks that were NOT ingested. The
identification SHA256 is computed only over these 30 integers joined by
newlines and a trailing newline:
`75e3f03e3bb560bbf5c0ba7d8e09be505897fb9e7e3be1eeb581e991c42474ba`.

The exact empirical rank-head conditional mass vector is
`p_i=count_i / 75648` for `i=1..30`; it is NOT the full-corpus Zipf
law, nor a random held-out sample. The experiment tests finite
cumulative-distance `D=max_(1<=j<=30)|Σ_(i<=j)p_i−Σ_(i<=j)q_i|`
against *separately normalized rank-head candidate models*.

Result (descriptive, head-only, candidate choices exploratory):

| Model conditioned on first 30 ranks | Exact-rational CDF discrepancy (decimal display) |
|---|---:|
| Zipf `q_i ∝ 1/i` | ≈ **0.1072921785** |
| Truncated geometric `q_i ∝ (0.9)^(i-1)` | ≈ **0.0817777544** |

The geometric candidate has the smaller discrepancy **on this particular
30-rank head**. That does **not** prove the full corpus is geometric,
prove a universal rejection of Zipf, or make an independence/p-value
claim. The candidate ratio was chosen exploratorily and not
preregistered or selected using a valid held-out design. We have not
reproduced the original article's full fitted exponent, likelihood-ratio
or goodness-of-fit calculations.

## Repository status

`scripts/zipf_clauset_words30_source_receipt.py` and
`tests/test_zipf_clauset_words30_source_receipt.py` source-write the
finite observed prefix and fail-closed normalized rational comparisons.
Their executed local source blob SHA values match the exact GitHub files:
`a28f8da657a18b59b0f6d2c49c227b5556e33915` and
`7b183f3953230a43ca677595d11ee78930723c9f`.
The **five targeted tests passed**. The combined local archived suite
now reports **115 passed**; earlier files are NOT all byte-identical to
the current GitHub HEAD. No full-head CI / Agda kernel result is claimed.

## Original attribution and true next wall

The new work is repository-authored by Johl Brown with OpenAI ChatGPT
assistance on 27 October 2026; all prior mathematical authorship and
earlier Ibrahim Monster 3B proof ownership remain unaltered. This is
a source-linked observation, not a mathematical discovery of the laws.

For actual empirical verification: acquire the **whole** file and
verify its hash, original sampling/tokenization scheme, complete rank
count and data license; freeze training and heldout identifiers and
predeclared alternatives; compare fitted power laws with lognormal,
geometric and other models with proper parameter estimation and
uncertainty; do not demote rare tails from omitted head data. For
formal proof status: require exact-head GitHub CI and Agda kernel
typecheck before any theorem-promotion. No fractal/RH/NS/Monster
same-object result follows from these counts.
