# Introspective visual proof loop

This experiment implements a four-stage introspective method without treating the visual stage as proof authority:

```text
formal Agda theory
  -> declared visual encoding
  -> raster rendering
  -> OpenCV structural observation
  -> machine-readable receipt
  -> Lean finite model of the observation
```

The exact kernel is `DASHI/Core/IntrospectiveVisualRoundTripExact.agda`. It proves a finite round trip for the declared semantic render/observe/reify contract and exposes `VisionObserverContract` for replacing the ideal observer with another observer whose soundness has actually been established.

The executable producer is `scripts/introspective_visual_roundtrip.py`. It renders four theory nodes and four relations into a 320x320 raster, uses OpenCV contour/corridor measurements to recover the expected structure, writes a JSON receipt, and emits a Lean model only when all expected edges are detected.

The committed fixtures in `Artifacts/introspective-visual/` were generated from a successful OpenCV run. The PNG itself is deliberately transient; the stable evidence is the structured receipt and emitted Lean source.

## Claim boundary

The method is intentionally asymmetric:

- Agda can prove that a *declared sound observer* recovers the finite theory.
- OpenCV can empirically produce observations from a raster.
- Lean can faithfully model the emitted observation.
- None of those facts alone proves that an arbitrary visualization semantically represents an arbitrary theory, or that OpenCV is a formally verified perception procedure.

The useful introspective signal is therefore disagreement. If the formal theory says relation `r` exists but the independently rendered/observed representation fails to recover `r`, the loop has found either a rendering defect, an observer defect, or a mismatch in the chosen representation. That disagreement becomes a concrete refinement target instead of being silently normalised away.

This is designed to compose with existing DASHI observer/fibre machinery: later rounds can render actual observer fibres, Pareto fronts, authority-routing graphs, wave fields, or proof-search hypergraphs and use independent visual observers to generate separating probes or counterexamples.
