# slr-discourse-reconstruct

Deterministic sidecar for the existing spaCy -> direct SLR stream.

It **does not** replace spaCy, SLR, PNF, or speaker admission. It consumes retained artifacts and emits candidate intra-sentence cut receipts.

## Reproducibility boundary

- Sentiment: `vader-parity = 0.1.0`, exact score-parity target `vaderSentiment 3.3.2`.
- No generative or remote inference.
- `slr-discourse-cut-v2` is retained as a cheap structural proposal stage, not semantic authority.
- `slr-discourse-manifold-v2` lifts each proposed boundary into competing discourse-fibre points and keeps the Pareto frontier rather than selecting a scalar winner.
- `slr-discourse-spans-v1` emits a separate candidate segmentation; it never overwrites the source transcript.
- `en_core_web_sm` itself contains trained weights. If the project anti-AI rule means *no learned weights at all*, do not treat the spaCy-derived features as policy-compatible. If the rule means *local, pinned and replayable only*, capture the exact spaCy/model versions and hashes alongside the run.
- Output is candidate-only: no cut, speaker, truth, legal, or causal promotion.

## Local cut proposal

```bash
cd tools/slr-discourse-reconstruct
cargo run --release -- \
  --parser /tmp/slr-specimens/9-sept-8-03pm/parser.tsv \
  --pnf /tmp/slr-specimens/9-sept-8-03pm/pnf.stdout \
  --source /tmp/slr-specimens/9-sept-8-03pm/source.txt \
  --source-sha /tmp/slr-specimens/9-sept-8-03pm/source.sha256 \
  --focus 42,45 \
  --top 30
```

The v2 cut score is only a proposal coordinate. It uses dependency crossings, punctuation/discourse cues, perspective shift, capped VADER delta, optional speaker-profile compatibility, and PNF residual density for inspection.

## PNF/world boundary manifold

Run the transcript-wide manifold and graph compiler:

```bash
bash run_manifold_graph.sh /tmp/slr-specimens/9-sept-8-03pm
```

For every candidate boundary the manifold emits five points (`speaker`, `quote`, `nesting`, `asr`, `rhetorical`) over coordinates including syntax continuity, parser/PNF topology, PNF residual compatibility, attribution, speaker compatibility, world-model compatibility, ASR integrity, and rhetorical continuity. Componentwise non-dominated points form the live Pareto fibre. A multi-point frontier stays unresolved.

The PNF topology projection is derived from parser dependency families corresponding to the repo's candidate-PNF owners: subject/object, clausal attachment, coordination, negation-side shift and modality-side shift. This does not make parser dependency a discourse-role authority.

## Candidate span reconstruction

After `run_manifold_graph.sh`:

```bash
bash run_span_reconstruction.sh /tmp/slr-specimens/9-sept-8-03pm
```

This produces:

- `discourse-spans-transcript-wide.tsv`: provenance-bearing candidate span ledger;
- `source-reconstructed.txt`: separate candidate text projection for a controlled PNF rerun;
- `discourse-spans-transcript-wide.stderr`: reconstruction receipt.

The v1 hard-cut policy is intentionally conservative: only a **rank-1 singleton Pareto projection** of `speaker` or `quote` creates a candidate hard boundary. Unresolved, ASR, nesting and rhetorical fronts remain unsplit. A candidate speaker cut never verifies speaker identity.

## Raw vs reconstructed PNF experiment

Rerun the existing spaCy -> SLR/PNF pipeline on `source-reconstructed.txt` into a separate specimen directory. Do not replace the raw artifacts. Then compare the two retained PNF streams:

```bash
bash compare_pnf_runs.sh \
  /tmp/slr-specimens/9-sept-8-03pm/pnf.stdout \
  /tmp/slr-specimens/9-sept-8-03pm-reconstructed/pnf.stdout
```

`slr-pnf-comparison-v1` reports raw/reconstructed residual totals and normalized residual density plus candidate/symbol row counts. These are diagnostics only: lower residual density does not prove correct semantics or world truth. Attribution ambiguity, false proposition joins and world-model mismatch remain separate downstream comparison coordinates and require their own receipts.

## Optional deterministic speaker profiles

Pass `--profiles speaker-profiles.tsv`. Markers are matched against lower-cased token text/lemmas. Profiles should be built from separately sourced public statements, not from held-out answer spans, for a blind benchmark. Speaker-profile compatibility is a candidate world/speaker coordinate, not identity proof.

## Architectural rule

The semantic shape is:

```text
surface/parser observation
  -> cheap boundary proposal
  -> candidate discourse fibre/manifold
  -> Pareto/live residual fibre
  -> conservative candidate span projection
  -> reconstructed PNF rerun
  -> raw-vs-reconstructed diagnostic comparison
```

Source/world constraints may refine the live fibre; they do not silently erase residual alternatives or manufacture truth.
