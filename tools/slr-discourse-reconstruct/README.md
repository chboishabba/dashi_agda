# slr-discourse-reconstruct

Deterministic sidecar for the existing spaCy -> direct SLR stream.

It **does not** replace spaCy, SLR, PNF, or speaker admission. It consumes retained artifacts and emits candidate intra-sentence cut receipts.

## Reproducibility boundary

- Sentiment: `vader-parity = 0.1.0`, exact score-parity target `vaderSentiment 3.3.2`.
- No generative or remote inference.
- Candidate scoring is a transparent fixed heuristic (`slr-discourse-cut-v1`).
- `en_core_web_sm` itself contains trained weights. If the project anti-AI rule means *no learned weights at all*, do not treat the spaCy-derived features as policy-compatible. If the rule means *local, pinned and replayable only*, capture the exact spaCy/model versions and hashes alongside the run.
- Output is candidate-only: no cut, speaker, truth, legal, or causal promotion.

## Run the ABC specimen

```bash
cd tools/slr-discourse-reconstruct
cargo run --release -- \
  --parser /tmp/slr-specimens/9-sept-8-03pm/parser.tsv \
  --pnf /tmp/slr-specimens/9-sept-8-03pm/pnf.stdout \
  --source /tmp/slr-specimens/9-sept-8-03pm/source.txt \
  --source-sha /tmp/slr-specimens/9-sept-8-03pm/source.sha256 \
  --focus 42,45 \
  --top 30 \
  > /tmp/slr-specimens/9-sept-8-03pm/discourse-cuts.tsv \
  2> /tmp/slr-specimens/9-sept-8-03pm/discourse-cuts.stderr
```

If your original transcript has a different filename, point `--source` at that exact file. Exact source text is required because spaCy offsets are used to isolate left/right spans and VADER is punctuation-sensitive.

For an unblinded whole-transcript ranking, omit `--focus`.

## Optional deterministic speaker profiles

Pass `--profiles speaker-profiles.tsv`. Format:

```text
speaker<TAB>marker<TAB>weight
David Shoebridge<TAB>gaslighting<TAB>6
David Shoebridge<TAB>action<TAB>2
Julian Leeser<TAB>two-state<TAB>3
Julian Leeser<TAB>sanction<TAB>-1
```

Markers are matched against lower-cased token text/lemmas. Profiles should be built from separately sourced public statements, not from the held-out answer span, if you want a blind reconstruction benchmark.

The scorer reports the best left/right profile candidate but does not treat that ranking as identity proof.

## Features

For each possible token split inside a spaCy sentence:

- `dep_crossings`: number of dependency edges severed by the cut. Fewer is evidence for a syntactically natural boundary.
- `punctuation`: transparent 0/1/3 boundary strength.
- `discourse_marker`: right span starts with `but/however/well/yeah/yes/no/now/listen/so/although/yet`.
- `perspective_shift`: dominant local pronoun class changes across the cut.
- `residuals`: sentence residual count read directly from `pnf.stdout` `R` rows.
- `sentiment_delta`: absolute left/right VADER compound-score difference.
- optional `left_profile/right_profile` shift.

The v1 ranking is intentionally simple and visible in `src/main.rs`; tune it only by versioning the feature schema and retaining old benchmark receipts.

## Expected inspection targets

The first run should inspect, not presuppose, the already-formalised candidates:

- sentence 42: likely Wong -> Husic boundary around `for Israelis | we can't say...`
- sentence 45: likely Shoebridge -> Leeser boundary around `gaslighting from Labor | ... two-state solution...`

The benchmark is interesting only if the runtime ranking can recover those areas without using the held-out gold speaker labels.
