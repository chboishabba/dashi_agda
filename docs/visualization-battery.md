# Source-backed visualisation battery

DASHI now separates three concerns that were previously easy to conflate:

1. **Agda semantic authority** — declarations, dimensions, closure conditions, and claim classes.
2. **Visual IR** — source-addressed samples, residuals, projection matrices, and invariant checks.
3. **Rendering** — camera, layout, colour, animation, and selection from a known battery of views.

The implementation was motivated by the seven SVGs in
`meta-introspector/meta-meme@60c6c092251251c30d3d73224626f783dd5cae12`.
Those artifacts demonstrate useful visual idioms—phase-plane vectors, residual
routes, an animated helix, ambient axis fans, and explicit exact-versus-
illustrative captions—but the commit itself contains generated SVG files rather
than a Lean-side generator or proof-linked intermediate representation.

## What DASHI already had

`scripts/dashi_visualize_agda.py` and
`scripts/materialize_dashi_agda_termflow.py` derive declarations, binders,
operator nodes, calls, and fibres from Agda source. That lane is strong on:

- source provenance;
- conservative parsing;
- open/fail-closed theorem authority;
- configuration by roots rather than hand-authored graph edges;
- auditable JSON before SVG rendering.

Its main limitation is visual monotony: nearly every source shape becomes the
same layered term-flow hyperfabric. The result is faithful but does not ask
which projection best exposes cyclicity, residual size, temporal lift,
high-dimensional coordinate structure, recursion, or branching search.

## What the meta-meme SVGs add

The referenced SVGs add a curated camera vocabulary:

- a complex phase plane and translated residual vectors;
- residual magnitude as a chord;
- a time-lifted helix;
- ambient coordinate fans for 4D, 5D, 12D, and 32D scenes;
- declarative SVG animation;
- a strong distinction between exact equations and illustrative recursion.

Their main limitation is the inverse of ours: the renderings are expressive,
but the commit does not expose a machine-checkable semantic IR connecting each
screen coordinate or animation path to a Lean declaration. The richer shape is
therefore curated rather than automatically selected or proof-emitted.

## Implemented bridge

`DASHI/Visualization/PhaseResidualProjection.agda` provides:

- a minimal algebraic theorem that phase closure implies zero residual;
- a zero-preserving projection contract proving that semantic zero remains
  screen zero;
- typed claim authority (`exact`, `derived`, `illustrative`, `observed`, and
  `candidate`);
- a typed introspective loop from Agda source to visual IR, SVG, image
  observation, reconstructed candidate, and explicit proof discharge;
- a view battery indexed by evidence features;
- source-readable scene descriptors for 2D, 3D, 4D, 5D, 12D, and 32D scenes.

`scripts/materialize_dashi_phase_visualisations.py` parses only those scene
descriptors. It derives all floating-point samples, residuals, screen axes,
paths, mosaics, and animation data downstream. The config names scenes, not
coordinates.

The higher-dimensional scenes use the conservative embedding

```text
θ ↦ (cos θ, sin θ, 0, …, 0) ∈ ℝⁿ.
```

This means the ordinary complex phase plane is embedded in an ambient real
coordinate space. The extra axes are shown as coordinate capacity and camera
structure; DASHI does not infer complex, quaternionic, octonionic, or other
multiplication on arbitrary `ℝⁿ` from the picture.

## View selection

The Agda battery currently maps evidence features to known views:

| Evidence feature | Candidate views |
| --- | --- |
| cyclic phase | phase plane, residual shadow, waveform |
| temporal lift | helix, waveform |
| high dimensional | axis fan, mosaic, spiral |
| scalar residual | waveform, residual shadow |
| coordinate matrix | mosaic, axis fan |
| branching search | search tree, mosaic |
| recursive growth | spiral, search tree, waveform |

This is intentionally a battery rather than an automatic creativity claim.
A person or a later selector names the mathematical feature that should be
exposed; the renderer provides multiple established projections for comparison.

## Introspective return loop

The desired loop is:

```text
Agda theory
  → source-addressed visual IR
  → SVG view battery
  → OpenCV/path/image observations
  → reconstructed candidate invariant
  → Agda proof obligation
  → authority promotion only after discharge
```

The current change implements the first three stages and formalises the
remaining authority boundary. A later image-analysis lane should emit a
separate observation artifact containing detector name, parameters, source SVG
hash, measured features, uncertainty, and the Agda obligation proposed for
reconstruction. It must not edit the theorem authority recorded in the source
IR.

## Materialisation

```bash
python scripts/materialize_dashi_phase_visualisations.py \
  --config config/dashi-euler-phase-visualisations.json \
  --check

python scripts/materialize_dashi_phase_visualisations.py \
  --config config/dashi-euler-phase-visualisations.json
```

Generated outputs:

- `artifacts/dashi-euler-phase-battery.json`
- `artifacts/dashi-euler-phase-battery.svg`

The JSON is the audit surface. The SVG is a downstream projection and never a
theorem-authority source.
